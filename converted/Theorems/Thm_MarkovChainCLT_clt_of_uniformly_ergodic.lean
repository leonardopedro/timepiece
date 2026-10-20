/-
prove2.me platform library module `Theorems.Thm_MarkovChainCLT_clt_of_uniformly_ergodic`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_MarkovChainCLT_clt_of_uniformly_ergodic.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Corollary 5** (Ibragimov–Linnik 1971; Tierney 1994): a uniformly ergodic
Harris chain with `E_π f² < ∞` satisfies the CLT for every initial distribution. -/

theorem MarkovChainCLT.clt_of_uniformly_ergodic {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (huni : UniformlyErgodic P π) (hL2 : MemLp f 2 π) :
    SatisfiesCLT P π f := by sorry
