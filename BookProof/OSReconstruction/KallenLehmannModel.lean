import Mathlib
import BookProof.OSReconstruction.Clustering
import BookProof.OSReconstruction.Generator
import BookProof.OSReconstruction.TransferSemigroupRight

/-!
# Källén–Lehmann for matrix elements of the transfer semigroup

`OSReconstruction.Clustering` §7 defines `laplace ρ τ = ∫ e^{−τλ} dρ(λ)` and proves
`laplace_map_withDensity`: in a multiplication model the transform of the pushed-forward weighted
measure is the integral `∫ w x e^{−τ f x} ∂μ`, i.e. the measurable functional calculus
`e^{−τM_f} = M_{e^{−τ f}}`.  This module attaches that representation to the *physical* two-point
function `τ ↦ ⟪z, P(τ) z⟫` on `ℋ`.

The one structural input is the multiplication model itself: an isometry
`U : ℋ →ₗᵢ[ℝ] L²(ν)` in which `P(τ)` acts as multiplication by `e^{−τ f}`.  With it:

* `inner_toLp_eq_integral` — the `L²` matrix element of two `MemLp` representatives is the integral
  of their product;
* `integral_mul_exp_eq_laplace` — that integral is `laplace` of the pushed-forward density
  `z² dν`, by `laplace_map_withDensity`;
* `kl_twoPoint_multiplicationModel` — the two together: the matrix element is a Laplace transform;
* `kl_physEvol` — on `Hphys Λ`, `⟪z, P(τ)z⟫` is the Laplace transform of a finite measure, so the
  whole KL calculus of `Clustering` applies to the physical two-point function.  In particular
  `physEvol_twoPoint_nonneg` reads `0 ≤ ⟪z, P(τ)z⟫` for `τ ≥ 0` off `laplace_nonneg` (the OS
  positivity of the transfer matrix), and `laplace_le_of_massGap` /
  `measure_Iio_eq_zero_of_laplace_decay` transfer a gap in the support of the spectral measure to
  the rate of decay of the physical two-point function.

## Boundary

The multiplication model is a **hypothesis**.  Producing `U`, `ν` and `f` from `P` is the spectral
theorem for the generator — available here only as a symmetric `LinearPMap`
(`generator_isSymmetric`), not as a self-adjoint operator with a functional calculus.  What is
proved is the attachment: *given* a multiplication model, the KL representation of `Clustering` is
literally the matrix element of the transfer semigroup on `ℋ`, and not merely an analogy.  The
spectral theorem that would discharge the hypothesis is not in this reconstruction.

The model is stated for the forward semigroup `physEvolCompletionRightFun` under the one-sided
hypothesis `HinvRight`, so the degeneracy of `OSReconstruction.TransferSelfAdjoint` does not
arise here: that result says a *two-sided* contractive self-adjoint family is trivial
(`physEvolCompletion_eq_one`), which would force `f = 0`.  With `τ ≥ 0` only, `P(τ)` is a
contraction and not an isometry, `e^{−τf}` need not be unimodular, and `f` may be nontrivial —
which is what a Källén–Lehmann representation with a non-degenerate spectral measure needs.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity
open Filter MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-! ## `L²` matrix elements as integrals -/

/-- The inner product of two `L²` classes is the integral of the product of their
representatives. -/
theorem inner_toLp_eq_integral {X : Type*} [MeasurableSpace X] {ν : Measure X} {z u : X → ℝ}
    (hz : MemLp z 2 ν) (hu : MemLp u 2 ν) :
    ⟪hz.toLp z, hu.toLp u⟫ = ∫ x, z x * u x ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hz.coeFn_toLp, hu.coeFn_toLp] with x hx hy
  rw [hx, hy, RCLike.inner_apply', RCLike.conj_to_real]

/-- **The KL representation in a multiplication model.**  The two-point function of a weight
`z` against multiplication by `e^{−τ f}` is the Laplace transform of the pushed-forward spectral
measure `z² dν ∘ f⁻¹`, by `laplace_map_withDensity`. -/
theorem integral_mul_exp_eq_laplace {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {z : X → ℝ} (hzm : Measurable z) {f : X → ℝ} (hf : Measurable f) (τ : ℝ) :
    (∫ x, z x * (Real.exp (-(τ * f x)) * z x) ∂ν)
      = laplace ((ν.withDensity (fun x => ENNReal.ofReal ((z x) * (z x)))).map f) τ := by
  rw [laplace_map_withDensity hf ((hzm.mul hzm).ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  change z x * (Real.exp (-(τ * f x)) * z x)
      = (ENNReal.ofReal (z x * z x)).toReal * Real.exp (-(τ * f x))
  rw [ENNReal.toReal_ofReal (mul_self_nonneg (z x))]
  ring

/-- A bounded exponential multiple of an `L²` function stays in `L²`, for `f ≥ 0` and `τ ≥ 0`. -/
theorem memLp_exp_mul {X : Type*} [MeasurableSpace X] {ν : Measure X} {z : X → ℝ}
    (hz : MemLp z 2 ν) (hzm : Measurable z) {f : X → ℝ} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂ν, 0 ≤ f x) {τ : ℝ} (hτ : 0 ≤ τ) :
    MemLp (fun x => Real.exp (-(τ * f x)) * z x) 2 ν := by
  refine MemLp.of_le hz ?_ ?_
  · exact ((Real.measurable_exp.comp ((measurable_const.mul hf).neg)).mul hzm).aestronglyMeasurable
  · filter_upwards [hpos] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    have hle : Real.exp (-(τ * f x)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.2 (by nlinarith)
    calc Real.exp (-(τ * f x)) * |z x| ≤ 1 * |z x| :=
          mul_le_mul_of_nonneg_right hle (abs_nonneg _)
      _ = |z x| := one_mul _

/-- **Källén–Lehmann for a multiplication model, in `L²` form.** -/
theorem kl_twoPoint_multiplicationModel {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {z u : X → ℝ} (hz : MemLp z 2 ν) (hu : MemLp u 2 ν) (hzm : Measurable z)
    {f : X → ℝ} (hf : Measurable f) {τ : ℝ}
    (hueq : u =ᵐ[ν] fun x => Real.exp (-(τ * f x)) * z x) :
    ⟪hz.toLp z, hu.toLp u⟫
      = laplace ((ν.withDensity (fun x => ENNReal.ofReal ((z x) * (z x)))).map f) τ := by
  rw [inner_toLp_eq_integral hz hu]
  have h1 : (∫ x, z x * u x ∂ν)
      = ∫ x, z x * (Real.exp (-(τ * f x)) * z x) ∂ν :=
    integral_congr_ae (hueq.mono fun x hx => by
      change z x * u x = z x * (Real.exp (-(τ * f x)) * z x)
      rw [hx])
  rw [h1, integral_mul_exp_eq_laplace hzm hf τ]

/-! ## The physical two-point function -/

/-- **The KL representation of `⟪z, P(τ)z⟫` on `ℋ`.**  If an isometry `U` into `L²(ν)` turns the
transfer semigroup into multiplication by `e^{−τ f}`, then the physical two-point function *is* the
Laplace transform of the spectral measure `z² dν ∘ f⁻¹`. -/
theorem kl_physEvol (Λ : OSState) (T : TimeTranslation) (hinv : HinvRight Λ T)
    {X : Type*} [MeasurableSpace X] {ν : Measure X} {f : X → ℝ} (hf : Measurable f)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν) (z : Hphys Λ)
    {zh uh : X → ℝ} (hzh : MemLp zh 2 ν) (huh : MemLp uh 2 ν) (hzhm : Measurable zh)
    (hUz : U z = hzh.toLp zh) {τ : ℝ} (hτ : 0 ≤ τ)
    (hUev : U (physEvolCompletionRightFun hinv τ z) = huh.toLp uh)
    (huheq : uh =ᵐ[ν] fun x => Real.exp (-(τ * f x)) * zh x) :
    ⟪z, physEvolCompletionRightFun hinv τ z⟫
      = laplace ((ν.withDensity (fun x => ENNReal.ofReal ((zh x) * (zh x)))).map f) τ := by
  have hiso : ⟪U z, U (physEvolCompletionRightFun hinv τ z)⟫
      = ⟪z, physEvolCompletionRightFun hinv τ z⟫ :=
    U.inner_map_map z (physEvolCompletionRightFun hinv τ z)
  rw [← hiso, hUz, hUev]
  exact kl_twoPoint_multiplicationModel hzh huh hzhm hf huheq

/-- **Positivity of the physical two-point function**, read off the KL representation: it is a
Laplace transform of a positive measure (`laplace_nonneg`).  This is the OS positivity of the
transfer matrix on `ℋ`, in matrix element form and for every `τ ≥ 0`. -/
theorem physEvol_twoPoint_nonneg (Λ : OSState) (T : TimeTranslation) (hinv : HinvRight Λ T)
    {X : Type*} [MeasurableSpace X] {ν : Measure X} {f : X → ℝ} (hf : Measurable f)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν) (z : Hphys Λ)
    {zh uh : X → ℝ} (hzh : MemLp zh 2 ν) (huh : MemLp uh 2 ν) (hzhm : Measurable zh)
    (hUz : U z = hzh.toLp zh) {τ : ℝ} (hτ : 0 ≤ τ)
    (hUev : U (physEvolCompletionRightFun hinv τ z) = huh.toLp uh)
    (huheq : uh =ᵐ[ν] fun x => Real.exp (-(τ * f x)) * zh x) :
    0 ≤ ⟪z, physEvolCompletionRightFun hinv τ z⟫ := by
  rw [kl_physEvol Λ T hinv hf U z hzh huh hzhm hUz hτ hUev huheq]
  exact laplace_nonneg _ τ

end

end BookProof.OSReconstruction
