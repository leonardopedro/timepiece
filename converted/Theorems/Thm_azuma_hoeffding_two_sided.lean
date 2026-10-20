/-
prove2.me platform library module `Theorems.Thm_azuma_hoeffding_two_sided`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_azuma_hoeffding_two_sided.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

theorem azuma_hoeffding_two_sided
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {μ : Measure Ω}
    {Y : ℕ → Ω → ℝ} {cY : ℕ → ℝ≥0} {ℱ : Filtration ℕ mΩ}
    [IsZeroOrProbabilityMeasure μ] [IsFiniteMeasure μ]
    (h_adapted : StronglyAdapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ) (n : ℕ)
    (h_subG : ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, Y i ω|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) := by sorry
