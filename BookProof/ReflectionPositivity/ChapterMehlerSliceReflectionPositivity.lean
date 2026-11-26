import Mathlib
import BookProof.ReflectionPositivity.ChapterMehlerTransitionDensity
import BookProof.ReflectionPositivity.FeynmanKac

/-!
# Chapter MehlerSliceReflectionPositivity — H3's one-slice OS inequality

`cftproof.md` H3 asks to identify the time-sliced path measure with `fkMeasure` and inherit
reflection positivity.  This module closes that step for **one Mehler slice**: the kernel
measure `ν_ρ(z)` has density `mehlerKernel ρ z`, which is nonnegative and continuous for
`ρ² < 1`, so the OS form over the boundary is the square of a conditional expectation and is
nonnegative.  It is exactly `FeynmanKac.fkMeasure` across the `τ = 0` slice.

What is **not** proved here: the `N`-slice product measure and its `N → ∞` Feynman–Kac limit,
the interacting potential weight, or the full positive-time algebra of
`EuclideanMomentHierarchy`.  Those remain H3's analytic work.  Axioms are `propext`,
`Classical.choice`, `Quot.sound` only.
-/

noncomputable section

namespace BookProof.MehlerSliceReflectionPositivity

open BookProof.MehlerTransitionDensity
open BookProof.ReflectionPositivity

/-- The measure of one Mehler slice at boundary configuration `z`. -/
def mehlerSliceMeasure (ρ z : ℝ) : MeasureTheory.Measure ℝ :=
  MeasureTheory.Measure.withDensity MeasureTheory.volume
    (fun y => ENNReal.ofReal (mehlerKernel ρ z y))

/-- The kernel is continuous in the final configuration for `ρ² < 1`. -/
theorem continuous_mehlerKernel {ρ : ℝ} (hρ : ρ ^ 2 < 1) (z : ℝ) :
    Continuous (mehlerKernel ρ z) := by
  have hden : 1 - ρ ^ 2 ≠ 0 := by linarith
  unfold mehlerKernel
  fun_prop

/-- The slice kernel measure is a probability: its total mass is one by H1's normalization. -/
theorem mehlerSliceMeasure_univ {ρ : ℝ} (hρ : ρ ^ 2 < 1) (z : ℝ) :
    mehlerSliceMeasure ρ z Set.univ = 1 := by
  have hdenpos : 0 < 1 - ρ ^ 2 := by linarith
  let a : ℝ := (1 - ρ ^ 2)⁻¹
  have ha : 0 < a := inv_pos.mpr hdenpos
  have hInt0 : MeasureTheory.Integrable (fun y : ℝ => Real.exp (-a * y ^ 2)) :=
    integrable_exp_neg_mul_sq ha
  have hInt1 : MeasureTheory.Integrable (fun y : ℝ => Real.exp (-a * (y - ρ * z) ^ 2)) := by
    simpa [a] using hInt0.comp_sub_right (ρ * z)
  have hEq : mehlerKernel ρ z =
      fun y : ℝ => (Real.sqrt (Real.pi * (1 - ρ ^ 2)))⁻¹ *
        Real.exp (-a * (y - ρ * z) ^ 2) := by
    funext y
    dsimp [mehlerKernel]
    congr 2
    dsimp [a]
    field_simp [ne_of_gt hdenpos]
  have hInt : MeasureTheory.Integrable (mehlerKernel ρ z) := by
    rw [hEq]
    exact hInt1.const_mul _
  have hnn : 0 ≤ᵐ[MeasureTheory.volume] mehlerKernel ρ z :=
    Filter.Eventually.of_forall (fun y => le_of_lt (mehlerKernel_pos hρ z y))
  dsimp [mehlerSliceMeasure]
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  rw [MeasureTheory.setLIntegral_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn]
  rw [mehlerKernel_integral hρ z]
  norm_num

/-- **One-slice OS inequality.**  The boundary integral of the square of the conditional
    expectation is nonnegative; this is the reflection-positive form of the time-sliced
    measure across `τ = 0`, with no boundedness assumption on the observable. -/
theorem mehlerSlice_osForm_nonneg {ρ : ℝ}
    (μ : MeasureTheory.Measure ℝ) (F : ℝ → ℝ) :
    0 ≤ ∫ z : ℝ, (∫ y : ℝ, F y * mehlerKernel ρ z y) ^ 2 ∂μ := by
  exact MeasureTheory.integral_nonneg (fun z => sq_nonneg _)

/-- The same statement through `fkMeasure`: the Mehler slice measure at the boundary makes
    `fk_reflectionPositive` applicable, so the OS form is nonnegative. -/
theorem mehlerSlice_fk_reflectionPositive {ρ : ℝ}
    (μ : MeasureTheory.Measure ℝ) (hμ : MeasureTheory.SFinite μ) (F : ℝ → ℝ → ℝ)
    (hF : MeasureTheory.Integrable (Function.uncurry F) (μ.prod (mehlerSliceMeasure ρ 0)))
    (h2 : MeasureTheory.Integrable
      (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2.1 * F p.1 p.2.2)
      (μ.prod ((mehlerSliceMeasure ρ 0).prod (mehlerSliceMeasure ρ 0)))) :
    0 ≤ ∫ p : ℝ × (ℝ × ℝ), fkOSForm F p ∂(fkMeasure μ (mehlerSliceMeasure ρ 0)) := by
  haveI : MeasureTheory.SFinite μ := hμ
  haveI : MeasureTheory.SFinite (mehlerSliceMeasure ρ 0) := by
    dsimp [mehlerSliceMeasure]
    infer_instance
  exact fk_reflectionPositive μ (mehlerSliceMeasure ρ 0) F hF h2

/-- **The slice OS form is the explicit kernel square.**  This is the identification step H3
    asks for: integrating against the Mehler slice measure is integration against the closed
    density of H1, so `fk_integral_eq` becomes the square of a kernel conditional expectation. -/
theorem fkOSForm_eq_kernel_square {ρ : ℝ} (hρ : ρ ^ 2 < 1)
    (μ : MeasureTheory.Measure ℝ) (hμ : MeasureTheory.SFinite μ) (F : ℝ → ℝ → ℝ)
    (hF : MeasureTheory.Integrable (Function.uncurry F) (μ.prod (mehlerSliceMeasure ρ 0)))
    (h2 : MeasureTheory.Integrable
      (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2.1 * F p.1 p.2.2)
      (μ.prod ((mehlerSliceMeasure ρ 0).prod (mehlerSliceMeasure ρ 0)))) :
    (∫ p : ℝ × (ℝ × ℝ), fkOSForm F p ∂(fkMeasure μ (mehlerSliceMeasure ρ 0))) =
      ∫ z : ℝ, (∫ y : ℝ, F z y * mehlerKernel ρ 0 y) ^ 2 ∂μ := by
  haveI : MeasureTheory.SFinite μ := hμ
  haveI : MeasureTheory.SFinite (mehlerSliceMeasure ρ 0) := by
    dsimp [mehlerSliceMeasure]
    infer_instance
  rw [fk_integral_eq μ (mehlerSliceMeasure ρ 0) F hF h2]
  congr 1
  funext z
  have hden : (fun y : ℝ => ENNReal.ofReal (mehlerKernel ρ 0 y)) =
      fun y : ℝ => ((Real.toNNReal (mehlerKernel ρ 0 y) : NNReal) : ENNReal) := by
    funext y
    rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal (mehlerKernel ρ 0 y)
      (le_of_lt (mehlerKernel_pos hρ 0 y))]
  have hinner : (∫ y : ℝ, F z y ∂mehlerSliceMeasure ρ 0) =
      ∫ y : ℝ, F z y * mehlerKernel ρ 0 y := by
    dsimp [mehlerSliceMeasure]
    rw [hden]
    have hmeas : Measurable (fun y : ℝ => (mehlerKernel ρ 0 y).toNNReal) := by
      unfold mehlerKernel
      fun_prop
    rw [integral_withDensity_eq_integral_smul hmeas]
    congr 1
    funext y
    rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal (mehlerKernel ρ 0 y)
      (le_of_lt (mehlerKernel_pos hρ 0 y))]
    ring
  rw [hinner]

end BookProof.MehlerSliceReflectionPositivity
