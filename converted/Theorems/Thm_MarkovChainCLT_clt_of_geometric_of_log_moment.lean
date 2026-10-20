/-
prove2.me platform library module `Theorems.Thm_MarkovChainCLT_clt_of_geometric_of_log_moment`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_MarkovChainCLT_clt_of_geometric_of_log_moment.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Corollary 3**: a geometrically ergodic Harris chain with
`E_π[f² log⁺|f|] < ∞` satisfies the CLT for every initial distribution. -/

theorem MarkovChainCLT.clt_of_geometric_of_log_moment {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (hgeo : GeometricallyErgodic P π)
    (hmom : Integrable (fun x => f x ^ 2 * Real.posLog |f x|) π) :
    SatisfiesCLT P π f := by sorry
