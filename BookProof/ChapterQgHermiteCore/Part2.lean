import Mathlib
import BookProof.ChapterHermiteFunctions
import BookProof.ChapterHermiteProductCore
import BookProof.ChapterStarobinskyPotential
import BookProof.ChapterQgHermiteCore.Part1

/-!
# The Gauss–polynomial (Hermite) core: the one-particle Hamiltonian is well defined on it

Plan item **§10.6.1, target 1** of `CONSOLIDATED_PLAN.md`: *well-definedness of the
gauge-fixed `R + αR²` one-particle Hamiltonian on the Gauss–polynomial core*.

The scalaron potential `V(φ) = (M⁴/16α)(1 − e^{−√(2/3)φ/M})²` grows **exponentially** as
`φ → −∞`, so it is not of temperate growth and the Schwartz-core multiplication theorem does
not apply to it.  The Gauss–polynomial core `p(x)e^{−x²/4}` — the basis in which the SIRK
numerics actually work — is nevertheless a legitimate domain for it, because its Gaussian
tail **dominates every exponential**.

## What is proved

**1. Gaussian dominance of exponentials.**  `exp_abs_le_const_mul_exp_sq`: for every `c ≥ 0`
and every `x`, `e^{c|x|} ≤ e^{2c²} e^{x²/8}`; hence `exp_abs_mul_gaussH_le`
`e^{c|x|}e^{−x²/4} ≤ e^{2c²}e^{−x²/8}`, and `tendsto_exp_abs_mul_gaussH_cocompact` — the
product tends to `0` at infinity.

**2. The exponential growth class.**  `ExpBounded f` says `|f x| ≤ C e^{c|x|}` for some
constants.  It contains every polynomial (`expBounded_poly`), is closed under sums and
scalar multiples, and contains the scalaron potential (`expBounded_starobinskyV`) — for
which no temperate bound exists.

**3. Multiplication by such a potential maps the core into `L²`.**
`memLp_gaussPoly` (the core lies in `L²`), `memLp_mul_gaussPoly_of_expBounded` (an
exp-bounded continuous potential times a core element is in `L²`), and the instances
`memLp_starobinskyV_mul_gaussPoly` and `memLp_scalaronFull1D_mul_gaussPoly` for the scalaron
potential and for the full one-variable potential `V₃ + V` (conformal-mode parabola plus
scalaron).

**4. The core is invariant under the kinetic term.**  `hasDerivAt_gaussPoly` shows the
derivative of a Gauss polynomial is the Gauss polynomial of `p' − x p / 2`
(`gaussPolyDeriv`), so `deriv_gaussPoly` and `deriv2_gaussPoly` stay in the core, and
`memLp_hamiltonian_gaussPoly` concludes: **`H ψ = −ψ'' + Wψ` lands in `L²` for every core
element `ψ`**, for every continuous exp-bounded potential `W`, in particular for the
scalaron one (`memLp_scalaronHamiltonian_gaussPoly`).

**6. Symmetry on the core.**  `gint_gaussPolyDeriv_antisymm` and
`gint_gaussPolyDeriv_two_symm` are the integration-by-parts identities at polynomial level
(the boundary terms vanish because of the Gaussian weight), and `integral_kinetic_symm` /
`integral_hamiltonian_symm` conclude that `−d²/dx² + W` is **symmetric** on the core for
every continuous exp-bounded `W` (`integral_scalaronHamiltonian_symm` for the scalaron).
This is the symmetric-operator half of the essential-self-adjointness question; the
deficiency half is not proved here (for the potential term alone it is proved, for
exponentially growing potentials too, in `BookProof.ChapterScalaronHermiteEsa`).

**7. Arbitrary dimension.**  `ExpBounded` is stated for any normed space, and
`memLp_mul_pgFun_of_expBounded` transports item 3 to the project's product Gauss–polynomial
core `pgFun` of `L²(ℝᵈ)` (`BookProof.HermiteProductCore`): multiplication by a continuous,
exponentially bounded potential maps that core into `L²(ℝᵈ)`.  `ExpBounded.comp_coord` and
`exists_exp_bound_mvPolyEval` are the two ingredients, and
`memLp_scalaronSectorPotential_mul_pgFun` is the instance for the **reduced two-variable
sector** `(R_c, φ)` with the potential `V₃(R_c) + V(φ)`.

This answers, in the Hermite basis, the domain question that §10.3 flags for the raw
operator.  It does **not** by itself give essential self-adjointness (targets 2–4 of
§10.6.1); those remain open.
-/

namespace BookProof.QgHermiteCore

open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky
/-! ## 6. Symmetry of the Hamiltonian on the core -/

/-- The `L²` pairing of two core elements is the Gaussian-weighted integral of the product
of their polynomials. -/
theorem integral_gaussPoly_mul (p q : Polynomial ℝ) :
    ∫ x : ℝ, gaussPoly p x * gaussPoly q x = gint (p * q) := by
  rw [gint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h := gaussH_sq x
  simp only [gaussPoly, Polynomial.eval_mul]
  rw [← h]
  ring

theorem integrable_gaussPoly_mul (p q : Polynomial ℝ) :
    Integrable (fun x : ℝ => gaussPoly p x * gaussPoly q x) := by
  refine (integrable_poly_mul_gaussW (p * q)).congr (Filter.Eventually.of_forall fun x => ?_)
  have h := gaussH_sq x
  simp only [gaussPoly, Polynomial.eval_mul]
  rw [← h]
  ring

/-- **Differentiation is antisymmetric on the core**, at the level of the polynomials: the
boundary terms of the integration by parts vanish because of the Gaussian weight. -/
theorem gint_gaussPolyDeriv_antisymm (p q : Polynomial ℝ) :
    gint (gaussPolyDeriv p * q) = - gint (p * gaussPolyDeriv q) := by
  have hL : gaussPolyDeriv p * q
      = Polynomial.derivative p * q - Polynomial.C (1 / 2) * (Polynomial.X * (p * q)) := by
    unfold gaussPolyDeriv
    ring
  have hR : p * gaussPolyDeriv q
      = p * Polynomial.derivative q - Polynomial.C (1 / 2) * (Polynomial.X * (p * q)) := by
    unfold gaussPolyDeriv
    ring
  have hibp := gint_ibp p q
  have hexp : p * (Polynomial.X * q - Polynomial.derivative q)
      = Polynomial.X * (p * q) - p * Polynomial.derivative q := by ring
  rw [hexp, gint_sub] at hibp
  rw [hL, hR, gint_sub, gint_sub, gint_C_mul]
  linarith

/-- Hence the second derivative is symmetric on the core. -/
theorem gint_gaussPolyDeriv_two_symm (p q : Polynomial ℝ) :
    gint (gaussPolyDeriv (gaussPolyDeriv p) * q)
      = gint (p * gaussPolyDeriv (gaussPolyDeriv q)) := by
  have h1 := gint_gaussPolyDeriv_antisymm (gaussPolyDeriv p) q
  have h2 := gint_gaussPolyDeriv_antisymm p (gaussPolyDeriv q)
  linarith

/-- **The kinetic term is symmetric on the Gauss–polynomial core.** -/
theorem integral_kinetic_symm (p q : Polynomial ℝ) :
    ∫ x : ℝ, gaussPoly p x * (-deriv (deriv (gaussPoly q)) x)
      = ∫ x : ℝ, (-deriv (deriv (gaussPoly p)) x) * gaussPoly q x := by
  rw [deriv2_gaussPoly, deriv2_gaussPoly]
  have hL : ∫ x : ℝ, gaussPoly p x * (-gaussPoly (gaussPolyDeriv (gaussPolyDeriv q)) x)
      = -gint (p * gaussPolyDeriv (gaussPolyDeriv q)) := by
    rw [← integral_gaussPoly_mul, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hR : ∫ x : ℝ, (-gaussPoly (gaussPolyDeriv (gaussPolyDeriv p)) x) * gaussPoly q x
      = -gint (gaussPolyDeriv (gaussPolyDeriv p) * q) := by
    rw [← integral_gaussPoly_mul, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hL, hR, gint_gaussPolyDeriv_two_symm]

/-- The potential term pairs two core elements integrably. -/
theorem integrable_potential_gaussPoly_mul {W : ℝ → ℝ} (hW : Continuous W)
    (hWb : ExpBounded W) (p q : Polynomial ℝ) :
    Integrable (fun x : ℝ => W x * (gaussPoly p x * gaussPoly q x)) := by
  obtain ⟨C, c, -, hb0⟩ := hWb
  have hC : 0 ≤ C := ExpBounded.nonneg_const hb0
  have hb : ∀ y : ℝ, |W y| ≤ C * Real.exp (c * |y|) := by
    simpa [Real.norm_eq_abs] using hb0
  set K : ℝ := C * Real.exp (2 * c ^ 2) with hK
  have hmaj : Integrable (fun x : ℝ => K * |(p * q).eval x * gaussH x|) :=
    ((integrable_poly_mul_gaussH (p * q)).abs).const_mul K
  refine hmaj.mono' ((hW.mul ((continuous_gaussPoly p).mul
    (continuous_gaussPoly q))).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  have hgH : 0 < gaussH x := gaussH_pos x
  have hstep : Real.exp (c * |x|) * gaussH x ≤ Real.exp (2 * c ^ 2) * Real.exp (-x ^ 2 / 8) :=
    exp_abs_mul_gaussH_le c x
  have he8 : Real.exp (-x ^ 2 / 8) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg x]
  have hlhs : ‖W x * (gaussPoly p x * gaussPoly q x)‖
      = |W x| * (|(p * q).eval x| * (gaussH x * gaussH x)) := by
    simp only [gaussPoly, Real.norm_eq_abs, Polynomial.eval_mul, abs_mul, abs_of_pos hgH]
    ring
  have hrhs : K * |(p * q).eval x * gaussH x| = K * (|(p * q).eval x| * gaussH x) := by
    rw [abs_mul, abs_of_pos hgH]
  rw [hlhs, hrhs]
  have hnn : (0:ℝ) ≤ |(p * q).eval x| * gaussH x := by positivity
  have h1 : |W x| * (|(p * q).eval x| * (gaussH x * gaussH x))
      ≤ (C * Real.exp (c * |x|)) * (|(p * q).eval x| * (gaussH x * gaussH x)) := by
    have hnn2 : (0:ℝ) ≤ |(p * q).eval x| * (gaussH x * gaussH x) := by positivity
    exact mul_le_mul_of_nonneg_right (hb x) hnn2
  have h2 : (C * Real.exp (c * |x|)) * (|(p * q).eval x| * (gaussH x * gaussH x))
      = C * (Real.exp (c * |x|) * gaussH x) * (|(p * q).eval x| * gaussH x) := by ring
  have h3 : C * (Real.exp (c * |x|) * gaussH x) * (|(p * q).eval x| * gaussH x)
      ≤ C * (Real.exp (2 * c ^ 2) * Real.exp (-x ^ 2 / 8)) * (|(p * q).eval x| * gaussH x) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hC) hnn
  have h5 : Real.exp (2 * c ^ 2) * Real.exp (-x ^ 2 / 8) ≤ Real.exp (2 * c ^ 2) := by
    nlinarith [Real.exp_pos (2 * c ^ 2), he8]
  have h4 : C * (Real.exp (2 * c ^ 2) * Real.exp (-x ^ 2 / 8)) * (|(p * q).eval x| * gaussH x)
      ≤ K * (|(p * q).eval x| * gaussH x) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hC) hnn
  linarith

/-- **The one-particle Hamiltonian is symmetric on the Gauss–polynomial core**: for every
continuous, exponentially bounded potential `W` and all core elements,
`⟪ψ, Hφ⟫ = ⟪Hψ, φ⟫`.  With item 4 (`H` maps the core into `L²`) and the density of the core
this is the symmetric-operator half of the essential self-adjointness question; the
deficiency half is not proved here. -/
theorem integral_hamiltonian_symm {W : ℝ → ℝ} (hW : Continuous W) (hWb : ExpBounded W)
    (p q : Polynomial ℝ) :
    ∫ x : ℝ, gaussPoly p x * (-deriv (deriv (gaussPoly q)) x + W x * gaussPoly q x)
      = ∫ x : ℝ, (-deriv (deriv (gaussPoly p)) x + W x * gaussPoly p x) * gaussPoly q x := by
  have hk1 : Integrable (fun x : ℝ => gaussPoly p x * (-deriv (deriv (gaussPoly q)) x)) := by
    rw [deriv2_gaussPoly]
    refine (integrable_gaussPoly_mul p (gaussPolyDeriv (gaussPolyDeriv q))).neg.congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.neg_apply]
    ring
  have hk2 : Integrable (fun x : ℝ => (-deriv (deriv (gaussPoly p)) x) * gaussPoly q x) := by
    rw [deriv2_gaussPoly]
    refine (integrable_gaussPoly_mul (gaussPolyDeriv (gaussPolyDeriv p)) q).neg.congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.neg_apply]
    ring
  have hv1 : Integrable (fun x : ℝ => gaussPoly p x * (W x * gaussPoly q x)) :=
    (integrable_potential_gaussPoly_mul hW hWb p q).congr
      (Filter.Eventually.of_forall fun x => by ring)
  have hv2 : Integrable (fun x : ℝ => (W x * gaussPoly p x) * gaussPoly q x) :=
    (integrable_potential_gaussPoly_mul hW hWb p q).congr
      (Filter.Eventually.of_forall fun x => by ring)
  have e1 : ∫ x : ℝ, gaussPoly p x * (-deriv (deriv (gaussPoly q)) x + W x * gaussPoly q x)
      = (∫ x : ℝ, gaussPoly p x * (-deriv (deriv (gaussPoly q)) x))
        + ∫ x : ℝ, gaussPoly p x * (W x * gaussPoly q x) := by
    rw [← integral_add hk1 hv1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have e2 : ∫ x : ℝ, (-deriv (deriv (gaussPoly p)) x + W x * gaussPoly p x) * gaussPoly q x
      = (∫ x : ℝ, (-deriv (deriv (gaussPoly p)) x) * gaussPoly q x)
        + ∫ x : ℝ, (W x * gaussPoly p x) * gaussPoly q x := by
    rw [← integral_add hk2 hv2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have e3 : ∫ x : ℝ, gaussPoly p x * (W x * gaussPoly q x)
      = ∫ x : ℝ, (W x * gaussPoly p x) * gaussPoly q x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [e1, e2, e3, integral_kinetic_symm]

/-- The scalaron instance of the symmetry. -/
theorem integral_scalaronHamiltonian_symm (M alpha : ℝ) (hM : 0 < M) (p q : Polynomial ℝ) :
    ∫ x : ℝ, gaussPoly p x
        * (-deriv (deriv (gaussPoly q)) x + starobinskyV M alpha x * gaussPoly q x)
      = ∫ x : ℝ, (-deriv (deriv (gaussPoly p)) x + starobinskyV M alpha x * gaussPoly p x)
        * gaussPoly q x :=
  integral_hamiltonian_symm (continuous_starobinskyV M alpha)
    (expBounded_starobinskyV M alpha hM) p q

/-! ## 7. Arbitrary dimension: the product Gauss–polynomial core of `L²(ℝᵈ)` -/

section MultiDim

open BookProof.HermiteProductCore

variable {d : ℕ}

/-- An exponentially bounded function of a single coordinate is exponentially bounded on
`ℝᵈ` — this is where `0 ≤ c` is used, through `|xᵢ| ≤ ‖x‖`. -/
theorem ExpBounded.comp_coord {f : ℝ → ℝ} (hf : ExpBounded f) (i : Fin d) :
    ExpBounded (fun x : Vd d => f (x i)) := by
  obtain ⟨C, c, hc, h⟩ := hf
  have hC : 0 ≤ C := ExpBounded.nonneg_const h
  refine ⟨C, c, hc, fun x => ?_⟩
  have hle : ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
  calc |f (x i)| ≤ C * Real.exp (c * ‖x i‖) := h (x i)
    _ ≤ C * Real.exp (c * ‖x‖) := by gcongr

/-- Every polynomial on `ℝᵈ` is dominated by an exponential of the norm. -/
theorem exists_exp_bound_mvPolyEval (p : MvPolynomial (Fin d) ℂ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ x : Vd d,
      ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ ≤ C * Real.exp (c * ‖x‖) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      refine ⟨‖a‖, 0, norm_nonneg a, le_rfl, fun x => ?_⟩
      simp
  | add p q hp hq =>
      obtain ⟨C1, c1, hC1, hc1, h1⟩ := hp
      obtain ⟨C2, c2, hC2, _, h2⟩ := hq
      refine ⟨C1 + C2, max c1 c2, by linarith, le_trans hc1 (le_max_left _ _), fun x => ?_⟩
      have e1 : C1 * Real.exp (c1 * ‖x‖) ≤ C1 * Real.exp (max c1 c2 * ‖x‖) := by
        gcongr
        exact le_max_left _ _
      have e2 : C2 * Real.exp (c2 * ‖x‖) ≤ C2 * Real.exp (max c1 c2 * ‖x‖) := by
        gcongr
        exact le_max_right _ _
      calc ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (p + q)‖
          ≤ ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖
            + ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q‖ := by
            rw [map_add]
            exact norm_add_le _ _
        _ ≤ C1 * Real.exp (c1 * ‖x‖) + C2 * Real.exp (c2 * ‖x‖) := add_le_add (h1 x) (h2 x)
        _ ≤ (C1 + C2) * Real.exp (max c1 c2 * ‖x‖) := by linarith
  | mul_X p i hp =>
      obtain ⟨C, c, hC, hc, h⟩ := hp
      refine ⟨C, c + 1, hC, by linarith, fun x => ?_⟩
      have hxi : ‖(((x i : ℝ)) : ℂ)‖ ≤ ‖x‖ := by
        rw [Complex.norm_real]
        exact PiLp.norm_apply_le x i
      have hnorm : ‖x‖ ≤ Real.exp ‖x‖ := by
        have := Real.add_one_le_exp ‖x‖
        linarith
      calc ‖MvPolynomial.eval (fun j => ((x j : ℝ) : ℂ)) (p * MvPolynomial.X i)‖
          = ‖MvPolynomial.eval (fun j => ((x j : ℝ) : ℂ)) p‖ * ‖(((x i : ℝ)) : ℂ)‖ := by
            rw [map_mul, MvPolynomial.eval_X, norm_mul]
        _ ≤ (C * Real.exp (c * ‖x‖)) * Real.exp ‖x‖ :=
            mul_le_mul (h x) (hxi.trans hnorm) (norm_nonneg _) (by positivity)
        _ = C * Real.exp ((c + 1) * ‖x‖) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 1
            ring

/-- **Multiplication by an exponentially bounded potential maps the product Gauss–polynomial
core of `L²(ℝᵈ)` into `L²(ℝᵈ)`** — the `d`-dimensional form of the well-definedness
statement, covering the reduced `(R_c, φ)` sector (`d = 2`) as well as the one-variable
scalaron sector. -/
theorem memLp_mul_pgFun_of_expBounded {W : Vd d → ℝ} (hW : Continuous W) (hWb : ExpBounded W)
    (p : MvPolynomial (Fin d) ℂ) :
    MemLp (fun x : Vd d => ((W x : ℝ) : ℂ) * pgFun p x) 2 (volume : Measure (Vd d)) := by
  obtain ⟨CW, cW, hcW, hW1⟩ := hWb
  have hCW : 0 ≤ CW := ExpBounded.nonneg_const hW1
  obtain ⟨Cp, cp, hCp, hcp, hp1⟩ := exists_exp_bound_mvPolyEval p
  have hmaj : MemLp (fun x : Vd d => ((CW * Cp : ℝ) : ℂ)
      * ((Real.exp ((cW + cp) * ‖x‖) * gaussD x : ℝ) : ℂ)) 2 (volume : Measure (Vd d)) :=
    (memLp_two_exp_norm_mul_gaussD (cW + cp)).const_mul _
  refine hmaj.of_le ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((Complex.continuous_ofReal.comp hW).mul (continuous_pgFun p)).aestronglyMeasurable
  · have hg : 0 < gaussD x := gaussD_pos x
    have hexp : Real.exp (cW * ‖x‖) * Real.exp (cp * ‖x‖) = Real.exp ((cW + cp) * ‖x‖) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hlhs : ‖((W x : ℝ) : ℂ) * pgFun p x‖
        = |W x| * (‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ * gaussD x) := by
      rw [pgFun, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hg]
    have hrhs : ‖((CW * Cp : ℝ) : ℂ) * ((Real.exp ((cW + cp) * ‖x‖) * gaussD x : ℝ) : ℂ)‖
        = CW * Cp * (Real.exp ((cW + cp) * ‖x‖) * gaussD x) := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ CW * Cp),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.exp ((cW + cp) * ‖x‖) * gaussD x)]
    rw [hlhs, hrhs]
    calc |W x| * (‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ * gaussD x)
        ≤ (CW * Real.exp (cW * ‖x‖)) * ((Cp * Real.exp (cp * ‖x‖)) * gaussD x) := by
          have h2 : ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ * gaussD x
              ≤ (Cp * Real.exp (cp * ‖x‖)) * gaussD x :=
            mul_le_mul_of_nonneg_right (hp1 x) hg.le
          exact mul_le_mul (hW1 x) h2 (by positivity) (by positivity)
      _ = CW * Cp * ((Real.exp (cW * ‖x‖) * Real.exp (cp * ‖x‖)) * gaussD x) := by ring
      _ = CW * Cp * (Real.exp ((cW + cp) * ‖x‖) * gaussD x) := by rw [hexp]

/-! ### The reduced `(R_c, φ)` sector -/

/-- The full potential of the reduced two-variable sector of the gauge-fixed `R + αR²`
Hamiltonian: the conformal-mode parabola `V₃` in the first coordinate plus the scalaron
potential in the second. -/
noncomputable def scalaronSectorPotential (M alpha : ℝ) (V3 : Polynomial ℝ) (x : Vd 2) : ℝ :=
  V3.eval (x 0) + starobinskyV M alpha (x 1)

theorem continuous_scalaronSectorPotential (M alpha : ℝ) (V3 : Polynomial ℝ) :
    Continuous (scalaronSectorPotential M alpha V3) := by
  unfold scalaronSectorPotential
  exact (V3.continuous_aeval.comp (by fun_prop)).add
    ((continuous_starobinskyV M alpha).comp (by fun_prop))

theorem expBounded_scalaronSectorPotential (M alpha : ℝ) (hM : 0 < M) (V3 : Polynomial ℝ) :
    ExpBounded (scalaronSectorPotential M alpha V3) :=
  ((expBounded_poly V3).comp_coord 0).add ((expBounded_starobinskyV M alpha hM).comp_coord 1)

/-- **The two-variable sector**: the full potential `V₃(R_c) + V(φ)` maps the product
Gauss–polynomial core of `L²(ℝ²)` into `L²(ℝ²)`. -/
theorem memLp_scalaronSectorPotential_mul_pgFun (M alpha : ℝ) (hM : 0 < M) (V3 : Polynomial ℝ)
    (p : MvPolynomial (Fin 2) ℂ) :
    MemLp (fun x : Vd 2 => ((scalaronSectorPotential M alpha V3 x : ℝ) : ℂ) * pgFun p x) 2
      (volume : Measure (Vd 2)) :=
  memLp_mul_pgFun_of_expBounded (continuous_scalaronSectorPotential M alpha V3)
    (expBounded_scalaronSectorPotential M alpha hM V3) p

end MultiDim

end BookProof.QgHermiteCore
