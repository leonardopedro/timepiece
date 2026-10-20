/-
prove2.me platform library module `Theorems.Thm_hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Kernel.Condexp
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

theorem hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero
    {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : m ≤ mΩ) {X : Ω → ℝ} {a b : ℝ}
    (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hc : μ[X | m] =ᵐ[μ] 0) :
    HasCondSubgaussianMGF m hm X ((‖b - a‖₊ / 2) ^ 2) μ := by sorry
