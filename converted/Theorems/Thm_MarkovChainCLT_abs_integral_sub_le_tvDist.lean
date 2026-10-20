/-
prove2.me platform library module `Theorems.Thm_MarkovChainCLT_abs_integral_sub_le_tvDist`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_MarkovChainCLT_abs_integral_sub_le_tvDist.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_TotalVariationDist
import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open MarkovChainCLT

theorem MarkovChainCLT.abs_integral_sub_le_tvDist {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : X → ℝ) (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ tvDist μ ν := by sorry
