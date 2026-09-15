import Mathlib
import BookProof.ChapterQgHermiteCore
import BookProof.ChapterFriedrichsExtension
import BookProof.ChapterQgHermiteFriedrichs.Part1

/-!
# The quantum-gravity one-particle Hamiltonian on the Hermite core: symmetry,
semiboundedness, and the Friedrichs extension

`CONSOLIDATED_PLAN.md` §10.6.1 asks for the one-particle gauge-fixed `R + αR²`
Hamiltonian `H = −Δ + W` to be realized as a genuine operator on the
Gauss–polynomial (Hermite) core of `L²(ℝᵈ)` — the basis the SIRK numerics work
in — and for a self-adjoint realization of it.  Target 1 (well-definedness:
`H` maps the core into `L²`) is `BookProof.ChapterQgHermiteCore`.  This module
takes the next step:

* the kinetic term is realized **algebraically** on the core.  Differentiating
  `pgFun p = p(x) e^{−‖x‖²/4}` in the coordinate `j` multiplies the polynomial by
  the *twisted derivative* `coreD j p = ∂ⱼ p − ½ xⱼ p` (`hasDerivAt_pgFun_coord`),
  so the Laplacian acts on the core as the polynomial map
  `kinPoly p = −∑ⱼ coreD j (coreD j p)` (`pgFun_kinPoly`);
* `coreD j` is **antisymmetric** for the Gaussian pairing (`gaussInt_coreD`),
  which is the polynomial form of integration by parts — the analytic input is
  the project's `gaussInt_pderiv`;
* consequently `H = −Δ + W` on the core (`hamCore`) is **symmetric**
  (`hamCore_symmetricOn`) and **bounded below by the lower bound of the
  potential** (`hamCore_quadForm_ge`, `hamCore_quadForm_nonneg`): the kinetic
  quadratic form is the sum of the squared norms of the first derivatives;
* since the core is dense (`polyGaussCore_dense`), the Friedrichs machinery of
  `BookProof.ChapterFriedrichsExtension` yields a **semibounded self-adjoint
  extension** with the same lower bound (`hermiteCore_friedrichs_extension`),
  and a *positive* one when the potential is nonnegative
  (`hermiteCore_friedrichs_extension_of_nonneg`).

The named instances are the ones §10.6.1 asks for: the one-variable **scalaron**
Hamiltonian `−Δ + V(φ)` (`qgOneParticleHermite_friedrichs`) — unconditional, no
finite-speed hypothesis, and with the exponentially growing potential the
temperate-growth theorems cannot reach — and the reduced two-variable sector
`(R_c, φ)` with the conformal-mode parabola
(`qgOneParticleSector_friedrichs`).

**Honest boundary.**  This is the *existence and canonical choice* of a
self-adjoint realization, not the *uniqueness* of one: essential
self-adjointness on the core (§10.6.1 target 4) is not proved here, and no
statement of this module asserts it.  It is proved elsewhere for the two cases
now available — the harmonic potential (`BookProof.ChapterQgHermiteOscillatorEsa`)
and the potential term alone, exponential growth included
(`BookProof.ChapterScalaronHermiteEsa`).
-/

namespace BookProof.QgHermiteFriedrichs

open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}

variable (W : Vd d → ℝ)
/-! ## Semiboundedness -/

/-- The quadratic form of the kinetic term is the sum of the squared norms of the
first derivatives — in particular it is nonnegative. -/
theorem re_gaussInt_kinPoly_self (p : MvPolynomial (Fin d) ℂ) :
    (gaussInt (cpoly p * kinPoly p)).re = ∑ j : Fin d, ‖pgLp (coreD j p)‖ ^ 2 := by
  rw [gaussInt_kinPoly]
  have h : ∀ j : Fin d, gaussInt (cpoly (coreD j p) * coreD j p)
      = ((‖pgLp (coreD j p)‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [← inner_pgLp_pgLp, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    norm_cast
  simp only [h, ← Complex.ofReal_sum, Complex.ofReal_re]

/-- The `L²` norm of a core vector, as an integral. -/
theorem norm_sq_pgLp (p : MvPolynomial (Fin d) ℂ) :
    ‖pgLp p‖ ^ 2 = ∫ x : Vd d, ‖pgFun p x‖ ^ 2 := by
  have h1 : (inner ℂ (pgLp p) (pgLp p) : ℂ) = ((∫ x : Vd d, ‖pgFun p x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_L2_eq, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [pgLp_coeFn p] with x hx
    rw [hx, conj_mul_self]
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at h1
  refine Complex.ofReal_inj.mp ?_
  push_cast
  exact h1

/-- `‖ψ‖²` is integrable against the potential: `W|ψ|²` is a product of two `L²`
functions. -/
theorem integrable_potential_normSq (hWc : Continuous W) (hWb : ExpBounded W)
    (p : MvPolynomial (Fin d) ℂ) :
    Integrable (fun x : Vd d => W x * ‖pgFun p x‖ ^ 2) (volume : Measure (Vd d)) := by
  have hu : MemLp (fun x : Vd d => ‖pgFun p x‖) 2 (volume : Measure (Vd d)) :=
    (memLp_pgFun p).norm
  have hv : MemLp (fun x : Vd d => W x * ‖pgFun p x‖) 2 (volume : Measure (Vd d)) := by
    refine (memLp_mul_pgFun_of_expBounded hWc hWb p).of_le
      ((hWc.mul ((continuous_pgFun p).norm)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (pgFun p x))]
  have hmul := hv.integrable_mul hu
  refine hmul.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]
  ring

/-- **The Hamiltonian is bounded below by the lower bound of its potential.** -/
theorem hamCore_quadForm_ge (hWc : Continuous W) (hWb : ExpBounded W) (c : ℝ)
    (hlb : ∀ x, -c ≤ W x) (x : (polyGaussCore (d := d))) :
    -c * ‖(x : L2d d)‖ ^ 2 ≤ quadForm (hamCore W hWc hWb) x := by
  obtain ⟨p, hp⟩ := x.2
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  subst hx
  -- the potential part, as a real integral
  have hpot : (inner ℂ (pgLp p) (potLp W hWc hWb p) : ℂ)
      = ((∫ y : Vd d, W y * ‖pgFun p y‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_pgLp_potLp, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hy : (starRingEnd ℂ) (pgFun p y) * (((W y : ℝ) : ℂ) * pgFun p y)
        = ((W y : ℝ) : ℂ) * ((starRingEnd ℂ) (pgFun p y) * pgFun p y) := by ring
    change (starRingEnd ℂ) (pgFun p y) * (((W y : ℝ) : ℂ) * pgFun p y)
        = ((W y * ‖pgFun p y‖ ^ 2 : ℝ) : ℂ)
    rw [hy, conj_mul_self]
    push_cast
    ring
  have hint : Integrable (fun y : Vd d => W y * ‖pgFun p y‖ ^ 2) (volume : Measure (Vd d)) :=
    integrable_potential_normSq W hWc hWb p
  have hint2 : Integrable (fun y : Vd d => -c * ‖pgFun p y‖ ^ 2) (volume : Measure (Vd d)) := by
    have h1 : MemLp (fun y : Vd d => ‖pgFun p y‖) 2 (volume : Measure (Vd d)) :=
      (memLp_pgFun p).norm
    have h2 := h1.integrable_mul h1
    refine (h2.const_mul (-c)).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.mul_apply]
    ring
  have hmono : ∫ y : Vd d, -c * ‖pgFun p y‖ ^ 2 ≤ ∫ y : Vd d, W y * ‖pgFun p y‖ ^ 2 := by
    refine integral_mono hint2 hint fun y => ?_
    have := hlb y
    nlinarith [sq_nonneg ‖pgFun p y‖]
  have hconst : ∫ y : Vd d, -c * ‖pgFun p y‖ ^ 2 = -c * ‖pgLp p‖ ^ 2 := by
    rw [integral_const_mul, ← norm_sq_pgLp]
  -- assemble
  have hquad : quadForm (hamCore W hWc hWb) ⟨pgLp p, pgLp_mem_core p⟩
      = (∑ j : Fin d, ‖pgLp (coreD j p)‖ ^ 2) + ∫ y : Vd d, W y * ‖pgFun p y‖ ^ 2 := by
    simp only [quadForm, hamCore_pgLp, hamPoly, inner_add_right, Complex.add_re]
    rw [inner_pgLp_pgLp, re_gaussInt_kinPoly_self, hpot, Complex.ofReal_re]
  rw [hquad]
  have hkin : 0 ≤ ∑ j : Fin d, ‖pgLp (coreD j p)‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => by positivity
  have hnorm : ‖((⟨pgLp p, pgLp_mem_core p⟩ : (polyGaussCore (d := d))) : L2d d)‖ = ‖pgLp p‖ := rfl
  rw [hnorm]
  linarith [hconst ▸ hmono]

/-- The nonnegative-potential case. -/
theorem hamCore_quadForm_nonneg (hWc : Continuous W) (hWb : ExpBounded W)
    (hW0 : ∀ x, 0 ≤ W x) (x : (polyGaussCore (d := d))) :
    0 ≤ quadForm (hamCore W hWc hWb) x := by
  have h := hamCore_quadForm_ge W hWc hWb 0 (by simpa using hW0) x
  simpa using h

/-! ## The Friedrichs extension -/

/-- **The one-particle Hamiltonian on the Hermite core has a semibounded
self-adjoint extension** with the lower bound of the potential. -/
theorem hermiteCore_friedrichs_extension (hWc : Continuous W) (hWb : ExpBounded W) (c : ℝ)
    (hlb : ∀ x, -c ≤ W x) :
    ∃ (Dom : Submodule ℂ (L2d d)) (A : Dom →ₗ[ℂ] L2d d),
      IsSemiboundedSelfAdjointExtension c (hamCore W hWc hWb) A :=
  friedrichs_extension_of_semibounded_below _ polyGaussCore_dense
    (hamCore_symmetricOn W hWc hWb) c (hamCore_quadForm_ge W hWc hWb c hlb)

/-- **The positive case**: for a nonnegative potential the extension is positive. -/
theorem hermiteCore_friedrichs_extension_of_nonneg (hWc : Continuous W) (hWb : ExpBounded W)
    (hW0 : ∀ x, 0 ≤ W x) :
    ∃ (Dom : Submodule ℂ (L2d d)) (A : Dom →ₗ[ℂ] L2d d),
      IsPositiveSelfAdjointExtension (hamCore W hWc hWb) A :=
  friedrichs_extension_exists
    ⟨_, hamCore W hWc hWb, hamCore_symmetricOn W hWc hWb,
      hamCore_quadForm_nonneg W hWc hWb hW0⟩ polyGaussCore_dense

/-! ## The scalaron instances -/

/-- The one-variable scalaron potential as a function on `ℝ¹`. -/
def scalaronW (M alpha : ℝ) (x : Vd 1) : ℝ := starobinskyV M alpha (x 0)

theorem continuous_scalaronW (M alpha : ℝ) : Continuous (scalaronW M alpha) := by
  change Continuous fun x : Vd 1 => starobinskyV M alpha (x 0)
  exact (continuous_starobinskyV M alpha).comp (by fun_prop)

theorem expBounded_scalaronW (M alpha : ℝ) (hM : 0 < M) : ExpBounded (scalaronW M alpha) := by
  change ExpBounded fun x : Vd 1 => starobinskyV M alpha (x 0)
  exact (expBounded_starobinskyV M alpha hM).comp_coord 0

theorem scalaronW_nonneg {M alpha : ℝ} (halpha : 0 < alpha) (x : Vd 1) :
    0 ≤ scalaronW M alpha x :=
  starobinskyV_nonneg halpha _

/-- **The quantum-gravity one-particle scalaron Hamiltonian on the Hermite core
has a positive self-adjoint (Friedrichs) extension** — unconditionally: no
finite-speed hypothesis, and with the exponentially growing potential that the
temperate-growth multiplication theorems cannot reach. -/
theorem qgOneParticleHermite_friedrichs (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) :
    ∃ (Dom : Submodule ℂ (L2d 1)) (A : Dom →ₗ[ℂ] L2d 1),
      IsPositiveSelfAdjointExtension
        (hamCore (scalaronW M alpha) (continuous_scalaronW M alpha)
          (expBounded_scalaronW M alpha hM)) A :=
  hermiteCore_friedrichs_extension_of_nonneg _ _ _ (scalaronW_nonneg halpha)

/-- **The reduced two-variable sector `(R_c, φ)`**: with the conformal-mode
parabola bounded below by `−c`, the full one-particle Hamiltonian on the Hermite
core of `L²(ℝ²)` has a self-adjoint extension bounded below by `−c`. -/
theorem qgOneParticleSector_friedrichs (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha)
    (V3 : Polynomial ℝ) (c : ℝ) (hV3 : ∀ t : ℝ, -c ≤ V3.eval t) :
    ∃ (Dom : Submodule ℂ (L2d 2)) (A : Dom →ₗ[ℂ] L2d 2),
      IsSemiboundedSelfAdjointExtension c
        (hamCore (scalaronSectorPotential M alpha V3)
          (continuous_scalaronSectorPotential M alpha V3)
          (expBounded_scalaronSectorPotential M alpha hM V3)) A := by
  refine hermiteCore_friedrichs_extension _ _ _ c fun x => ?_
  have h1 := hV3 (x 0)
  have h2 := BookProof.Starobinsky.starobinskyV_nonneg (M := M) halpha (x 1)
  simp only [scalaronSectorPotential]
  linarith

/-! ## The kinetic term really is the Laplacian -/

/-- Moving along the `j`-th coordinate line through `x`. -/
def coordLine (x : Vd d) (j : Fin d) (s : ℝ) : Vd d :=
  WithLp.toLp 2 (Function.update x.ofLp j s)

theorem coordLine_apply (x : Vd d) (j : Fin d) (s : ℝ) (i : Fin d) :
    (coordLine x j s) i = Function.update x.ofLp j s i := rfl

theorem coordLine_self (x : Vd d) (j : Fin d) (s : ℝ) : (coordLine x j s) j = s := by
  rw [coordLine_apply, Function.update_self]

/-- The squared norm along a coordinate line is `s² + const`. -/
theorem hasDerivAt_normSq_coordLine (x : Vd d) (j : Fin d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ‖coordLine x j s‖ ^ 2) (2 * t) t := by
  have hsplit : ∀ s : ℝ, ‖coordLine x j s‖ ^ 2
      = s ^ 2 + ∑ i ∈ Finset.univ.erase j, (x i) ^ 2 := by
    intro s
    rw [norm_sq_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), coordLine_self]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [coordLine_apply, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have h0 := (hasDerivAt_pow 2 t).add_const (∑ i ∈ Finset.univ.erase j, (x i) ^ 2)
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + ∑ i ∈ Finset.univ.erase j, (x i) ^ 2) (2 * t) t := by
    refine h0.congr_deriv ?_
    push_cast
    ring
  simpa only [hsplit] using h1

/-- The Gaussian weight along a coordinate line. -/
theorem hasDerivAt_gaussD_coordLine (x : Vd d) (j : Fin d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gaussD (coordLine x j s))
      (-(t / 2) * gaussD (coordLine x j t)) t := by
  have h : HasDerivAt (fun s : ℝ => -‖coordLine x j s‖ ^ 2 / 4) (-(2 * t) / 4) t :=
    ((hasDerivAt_normSq_coordLine x j t).neg).div_const 4
  have hexp := h.exp
  refine hexp.congr_deriv ?_
  rw [gaussD]
  ring

/-- The polynomial part along a coordinate line: the derivative is the partial
derivative `∂ⱼ p`. -/
theorem hasDerivAt_polyEval_coordLine (p : MvPolynomial (Fin d) ℂ) (x : Vd d) (j : Fin d)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => MvPolynomial.eval (fun i => (((coordLine x j s) i : ℝ) : ℂ)) p)
      (MvPolynomial.eval (fun i => (((coordLine x j t) i : ℝ) : ℂ)) (pderiv j p)) t := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t (a : ℂ)
  | add p q hp hq => simpa [map_add] using hp.add hq
  | mul_X p i hp =>
      have hcoord : HasDerivAt (fun s : ℝ => (((coordLine x j s) i : ℝ) : ℂ))
          (MvPolynomial.eval (fun k => (((coordLine x j t) k : ℝ) : ℂ))
            (pderiv j (X i : MvPolynomial (Fin d) ℂ))) t := by
        by_cases hij : i = j
        · subst hij
          have h1 : (fun s : ℝ => (((coordLine x i s) i : ℝ) : ℂ)) = fun s : ℝ => (s : ℂ) := by
            funext s
            rw [coordLine_self]
          have h2 : MvPolynomial.eval (fun k => (((coordLine x i t) k : ℝ) : ℂ))
              (pderiv i (X i : MvPolynomial (Fin d) ℂ)) = 1 := by simp
          rw [h1, h2]
          simpa using (hasDerivAt_id t).ofReal_comp
        · have h1 : (fun s : ℝ => (((coordLine x j s) i : ℝ) : ℂ))
              = fun _ : ℝ => ((x i : ℝ) : ℂ) := by
            funext s
            rw [coordLine_apply, Function.update_of_ne hij]
          have h2 : MvPolynomial.eval (fun k => (((coordLine x j t) k : ℝ) : ℂ))
              (pderiv j (X i : MvPolynomial (Fin d) ℂ)) = 0 := by
            simp [pderiv_X, Ne.symm hij]
          rw [h1, h2]
          exact hasDerivAt_const t _
      have hmul := hp.mul hcoord
      have hgoal : (fun s : ℝ =>
            MvPolynomial.eval (fun k => (((coordLine x j s) k : ℝ) : ℂ)) (p * X i))
          = fun s : ℝ => (MvPolynomial.eval (fun k => (((coordLine x j s) k : ℝ) : ℂ)) p)
              * (((coordLine x j s) i : ℝ) : ℂ) := by
        funext s
        simp [map_mul]
      rw [hgoal]
      simp only [Pi.mul_def] at hmul
      refine hmul.congr_deriv ?_
      simp only [pderiv_mul, map_add, map_mul, MvPolynomial.eval_X]

/-- **Differentiating the core in a coordinate**: `∂ⱼ (p e^{−‖x‖²/4}) =
(coreD j p) e^{−‖x‖²/4}` — the twisted derivative `coreD` really is the
coordinate derivative on the Gauss–polynomial core, so `kinPoly` really is `−Δ`. -/
theorem hasDerivAt_pgFun_coord (p : MvPolynomial (Fin d) ℂ) (j : Fin d) (x : Vd d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => pgFun p (coordLine x j s))
      (pgFun (coreD j p) (coordLine x j t)) t := by
  have hE := hasDerivAt_polyEval_coordLine p x j t
  have hg := (hasDerivAt_gaussD_coordLine x j t).ofReal_comp
  have hmul := hE.mul hg
  refine hmul.congr_deriv ?_
  simp only [pgFun, coreD, map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C,
    coordLine_self]
  push_cast
  ring

end

end BookProof.QgHermiteFriedrichs
