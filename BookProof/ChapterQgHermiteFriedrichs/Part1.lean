import Mathlib
import BookProof.ChapterQgHermiteCore
import BookProof.ChapterFriedrichsExtension

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

/-! ## The conjugate polynomial -/

/-- The polynomial with conjugated coefficients; on *real* points it computes the
complex conjugate of the value (`conj_pgFun`). -/
def cpoly (p : MvPolynomial (Fin d) ℂ) : MvPolynomial (Fin d) ℂ :=
  p.map (starRingEnd ℂ)

@[simp] theorem cpoly_add (p q : MvPolynomial (Fin d) ℂ) :
    cpoly (p + q) = cpoly p + cpoly q := by
  simp [cpoly]

@[simp] theorem cpoly_mul (p q : MvPolynomial (Fin d) ℂ) :
    cpoly (p * q) = cpoly p * cpoly q := by
  simp [cpoly]

@[simp] theorem cpoly_X (j : Fin d) : cpoly (X j : MvPolynomial (Fin d) ℂ) = X j := by
  simp [cpoly]

@[simp] theorem cpoly_C (a : ℂ) :
    cpoly (C a : MvPolynomial (Fin d) ℂ) = C (starRingEnd ℂ a) := by
  simp [cpoly]

theorem cpoly_pderiv (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    cpoly (pderiv j p) = pderiv j (cpoly p) := pderiv_map.symm

theorem conj_polyEval (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p)
      = MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (cpoly p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [cpoly]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp only [cpoly] at hp ⊢; simp [hp]

theorem conj_pgFun (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    (starRingEnd ℂ) (pgFun p x) = pgFun (cpoly p) x := by
  simp only [pgFun, map_mul, Complex.conj_ofReal, conj_polyEval]

/-! ## The twisted derivative: the Laplacian on the core, algebraically -/

/-- The **twisted derivative** `coreD j p = ∂ⱼ p − ½ xⱼ p`: differentiating
`p(x) e^{−‖x‖²/4}` in the coordinate `j` replaces `p` by `coreD j p`. -/
def coreD (j : Fin d) (p : MvPolynomial (Fin d) ℂ) : MvPolynomial (Fin d) ℂ :=
  pderiv j p - C (1 / 2 : ℂ) * (X j * p)

theorem coreD_add (j : Fin d) (p q : MvPolynomial (Fin d) ℂ) :
    coreD j (p + q) = coreD j p + coreD j q := by
  simp only [coreD, map_add, mul_add]
  ring

theorem coreD_smul (j : Fin d) (c : ℂ) (p : MvPolynomial (Fin d) ℂ) :
    coreD j (c • p) = c • coreD j p := by
  simp only [coreD, smul_eq_C_mul, pderiv_C_mul, mul_sub]
  ring

@[simp] theorem cpoly_sub (p q : MvPolynomial (Fin d) ℂ) :
    cpoly (p - q) = cpoly p - cpoly q := by
  simp [cpoly]

@[simp] theorem cpoly_neg (p : MvPolynomial (Fin d) ℂ) : cpoly (-p) = -cpoly p := by
  simp [cpoly]

theorem cpoly_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ) :
    cpoly (∑ i ∈ s, f i) = ∑ i ∈ s, cpoly (f i) :=
  map_sum (MvPolynomial.map (starRingEnd ℂ)) f s

theorem cpoly_coreD (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    cpoly (coreD j p) = coreD j (cpoly p) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by norm_num [Complex.ext_iff]
  unfold coreD
  rw [cpoly_sub, cpoly_pderiv, cpoly_mul, cpoly_mul, cpoly_X, cpoly_C, hhalf]

/-- The polynomial realization of `−Δ` on the Gauss–polynomial core. -/
def kinPoly (p : MvPolynomial (Fin d) ℂ) : MvPolynomial (Fin d) ℂ :=
  -∑ j : Fin d, coreD j (coreD j p)

theorem kinPoly_add (p q : MvPolynomial (Fin d) ℂ) :
    kinPoly (p + q) = kinPoly p + kinPoly q := by
  simp only [kinPoly, coreD_add, Finset.sum_add_distrib, neg_add]

theorem kinPoly_smul (c : ℂ) (p : MvPolynomial (Fin d) ℂ) :
    kinPoly (c • p) = c • kinPoly p := by
  simp only [kinPoly, coreD_smul, ← Finset.smul_sum, smul_neg]

/-! ## The Gaussian pairing -/

/-- The inner product of two core vectors is the Gaussian integral of the product
of the conjugate polynomial with the other. -/
theorem inner_pgLp_pgLp (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (pgLp q) : ℂ) = gaussInt (cpoly p * q) := by
  rw [inner_pgLp, gaussInt]
  refine integral_congr_ae ?_
  filter_upwards [pgLp_coeFn q] with x hx
  rw [hx, conj_pgFun]
  simp only [pgFun, map_mul, gaussWD_eq_sq]
  push_cast
  ring

/-- Gaussian integrals are additive on differences. -/
theorem gaussInt_sub (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by
  have h : r - s = r + (-1 : ℂ) • s := by module
  rw [h, gaussInt_add, gaussInt_smul]
  ring

theorem gaussInt_neg (r : MvPolynomial (Fin d) ℂ) : gaussInt (-r) = -gaussInt r := by
  have h : -r = (-1 : ℂ) • r := by module
  rw [h, gaussInt_smul]
  ring

/-- **Integration by parts on the core, algebraically**: the twisted derivative is
antisymmetric for the Gaussian pairing. -/
theorem gaussInt_coreD_raw (j : Fin d) (a b : MvPolynomial (Fin d) ℂ) :
    gaussInt (coreD j a * b) = -gaussInt (a * coreD j b) := by
  have hC2 : (C (1 / 2 : ℂ) : MvPolynomial (Fin d) ℂ) * 2 = 1 := by
    have h2 : ((2 : MvPolynomial (Fin d) ℂ)) = C (2 : ℂ) :=
      (MvPolynomial.ext _ _ (congrFun rfl)).symm
    rw [h2, ← C_mul]
    norm_num
  have hsum : coreD j a * b + a * coreD j b = pderiv j (a * b) - X j * (a * b) := by
    simp only [coreD, pderiv_mul, sub_mul, mul_sub]
    linear_combination (-(X j * a * b)) * hC2
  have h0 : gaussInt (coreD j a * b + a * coreD j b) = 0 := by
    rw [hsum, gaussInt_sub, gaussInt_pderiv, sub_self]
  rw [gaussInt_add] at h0
  linear_combination h0

/-- **Integration by parts on the core, algebraically**: the twisted derivative is
antisymmetric for the Gaussian pairing. -/
theorem gaussInt_coreD (j : Fin d) (p q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly (coreD j p) * q) = -gaussInt (cpoly p * coreD j q) := by
  rw [cpoly_coreD, gaussInt_coreD_raw]

theorem cpoly_kinPoly (p : MvPolynomial (Fin d) ℂ) :
    cpoly (kinPoly p) = kinPoly (cpoly p) := by
  simp only [kinPoly, cpoly_neg, cpoly_sum, cpoly_coreD]

/-- The kinetic pairing is the sum over the coordinates of the pairings of the
first derivatives — the discrete form of `∫ ∇ψ̄ · ∇φ`. -/
theorem gaussInt_kinPoly (p q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly p * kinPoly q) = ∑ j : Fin d, gaussInt (cpoly (coreD j p) * coreD j q) := by
  have hmul : cpoly p * kinPoly q = -∑ j : Fin d, cpoly p * coreD j (coreD j q) := by
    simp only [kinPoly, Finset.mul_sum, mul_neg]
  rw [hmul, gaussInt_neg, gaussInt_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gaussInt_coreD j p (coreD j q)]

/-- The same pairing, computed by moving the Laplacian to the *left* argument. -/
theorem gaussInt_kinPoly_left (p q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly (kinPoly p) * q) = ∑ j : Fin d, gaussInt (cpoly (coreD j p) * coreD j q) := by
  have hmul : cpoly (kinPoly p) * q = -∑ j : Fin d, coreD j (coreD j (cpoly p)) * q := by
    rw [cpoly_kinPoly]
    simp only [kinPoly, Finset.sum_mul, neg_mul]
  rw [hmul, gaussInt_neg, gaussInt_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gaussInt_coreD_raw j (coreD j (cpoly p)) q, cpoly_coreD, neg_neg]

/-! ## The potential term -/

variable (W : Vd d → ℝ)

/-- Multiplication of a core vector by the potential, as an element of `L²`
(well defined by `BookProof.QgHermiteCore.memLp_mul_pgFun_of_expBounded`). -/
def potLp (hWc : Continuous W) (hWb : ExpBounded W) (p : MvPolynomial (Fin d) ℂ) : L2d d :=
  (memLp_mul_pgFun_of_expBounded hWc hWb p).toLp _

theorem potLp_coeFn (hWc : Continuous W) (hWb : ExpBounded W) (p : MvPolynomial (Fin d) ℂ) :
    (potLp W hWc hWb p : Vd d → ℂ) =ᵐ[volume] fun x => ((W x : ℝ) : ℂ) * pgFun p x :=
  (memLp_mul_pgFun_of_expBounded hWc hWb p).coeFn_toLp

theorem potLp_add (hWc : Continuous W) (hWb : ExpBounded W) (p q : MvPolynomial (Fin d) ℂ) :
    potLp W hWc hWb (p + q) = potLp W hWc hWb p + potLp W hWc hWb q := by
  simp only [potLp]
  rw [← MemLp.toLp_add (memLp_mul_pgFun_of_expBounded hWc hWb p)
    (memLp_mul_pgFun_of_expBounded hWc hWb q)]
  congr 1
  funext x
  simp [pgFun_add, mul_add]

theorem potLp_smul (hWc : Continuous W) (hWb : ExpBounded W) (c : ℂ)
    (p : MvPolynomial (Fin d) ℂ) :
    potLp W hWc hWb (c • p) = c • potLp W hWc hWb p := by
  simp only [potLp]
  rw [← MemLp.toLp_const_smul c (memLp_mul_pgFun_of_expBounded hWc hWb p)]
  congr 1
  funext x
  simp [pgFun_smul, smul_eq_mul]
  ring

/-! ## The Hamiltonian on the core -/

/-- `H p = −Δ(p e^{−‖x‖²/4}) + W · (p e^{−‖x‖²/4})`, as an element of `L²(ℝᵈ)`. -/
def hamPoly (hWc : Continuous W) (hWb : ExpBounded W) (p : MvPolynomial (Fin d) ℂ) : L2d d :=
  pgLp (kinPoly p) + potLp W hWc hWb p

/-- The Hamiltonian as a linear map out of the polynomials. -/
def hamPolyMap (hWc : Continuous W) (hWb : ExpBounded W) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] L2d d where
  toFun := hamPoly W hWc hWb
  map_add' p q := by
    simp only [hamPoly, kinPoly_add, potLp_add]
    rw [← pgMap_apply, map_add]
    simp only [pgMap_apply]
    abel
  map_smul' c p := by
    simp only [hamPoly, kinPoly_smul, potLp_smul, RingHom.id_apply]
    rw [← pgMap_apply, map_smul]
    simp only [pgMap_apply]
    rw [smul_add]

/-- The core, as the isomorphic image of the polynomial ring. -/
def coreEquiv : MvPolynomial (Fin d) ℂ ≃ₗ[ℂ] (polyGaussCore (d := d)) :=
  LinearEquiv.ofInjective (pgMap (d := d)) pgMap_injective

theorem coreEquiv_apply (p : MvPolynomial (Fin d) ℂ) :
    ((coreEquiv p : polyGaussCore (d := d)) : L2d d) = pgLp p := rfl

theorem coreEquiv_symm_pgLp (p : MvPolynomial (Fin d) ℂ) :
    coreEquiv.symm ⟨pgLp p, pgLp_mem_core p⟩ = p := by
  apply coreEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  exact Subtype.ext rfl

/-- **The one-particle Hamiltonian `−Δ + W` on the Gauss–polynomial (Hermite)
core** of `L²(ℝᵈ)`. -/
def hamCore (hWc : Continuous W) (hWb : ExpBounded W) :
    (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (hamPolyMap W hWc hWb).comp (coreEquiv (d := d)).symm.toLinearMap

theorem hamCore_pgLp (hWc : Continuous W) (hWb : ExpBounded W) (p : MvPolynomial (Fin d) ℂ) :
    hamCore W hWc hWb ⟨pgLp p, pgLp_mem_core p⟩ = hamPoly W hWc hWb p := by
  simp only [hamCore, LinearMap.comp_apply, LinearEquiv.coe_coe, coreEquiv_symm_pgLp]
  rfl

/-! ## Symmetry -/

theorem conj_mul_self (z : ℂ) : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq z

/-- The `L²` inner product, written as an integral of the representatives. -/
theorem inner_L2_eq (f g : L2d d) :
    (inner ℂ f g : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) ((f : Vd d → ℂ) x) * (g : Vd d → ℂ) x := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [RCLike.inner_apply]
  ring

theorem inner_pgLp_potLp (hWc : Continuous W) (hWb : ExpBounded W)
    (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (potLp W hWc hWb q) : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) (pgFun p x) * (((W x : ℝ) : ℂ) * pgFun q x) := by
  rw [inner_pgLp]
  refine integral_congr_ae ?_
  filter_upwards [potLp_coeFn W hWc hWb q] with x hx
  rw [hx]

theorem inner_potLp_pgLp (hWc : Continuous W) (hWb : ExpBounded W)
    (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (potLp W hWc hWb p) (pgLp q) : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) (((W x : ℝ) : ℂ) * pgFun p x) * pgFun q x := by
  rw [inner_L2_eq]
  refine integral_congr_ae ?_
  filter_upwards [potLp_coeFn W hWc hWb p, pgLp_coeFn q] with x hx hy
  rw [hx, hy]

/-- Multiplication by a *real* potential is symmetric on the core. -/
theorem inner_potLp_symm (hWc : Continuous W) (hWb : ExpBounded W)
    (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (potLp W hWc hWb p) (pgLp q) : ℂ) = inner ℂ (pgLp p) (potLp W hWc hWb q) := by
  rw [inner_potLp_pgLp, inner_pgLp_potLp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-- **The Hamiltonian is symmetric on the core.** -/
theorem hamCore_symmetricOn (hWc : Continuous W) (hWb : ExpBounded W) :
    SymmetricOn (polyGaussCore (d := d)) (hamCore W hWc hWb) := by
  intro x y
  obtain ⟨p, hp⟩ := x.2
  obtain ⟨q, hq⟩ := y.2
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  have hy : y = ⟨pgLp q, pgLp_mem_core q⟩ := Subtype.ext hq.symm
  rw [hx, hy, hamCore_pgLp, hamCore_pgLp]
  change (inner ℂ (hamPoly W hWc hWb p) (pgLp q) : ℂ) = inner ℂ (pgLp p) (hamPoly W hWc hWb q)
  simp only [hamPoly, inner_add_left, inner_add_right]
  congr 1
  · rw [inner_pgLp_pgLp, inner_pgLp_pgLp, gaussInt_kinPoly_left, gaussInt_kinPoly]
  · exact inner_potLp_symm W hWc hWb p q

end

end BookProof.QgHermiteFriedrichs
