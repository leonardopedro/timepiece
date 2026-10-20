/-
prove2.me platform library module `Theorems.Thm_MarkovChainCLT_isStrictlyStationary_chainMeasure`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_MarkovChainCLT_isStrictlyStationary_chainMeasure.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MixingCoefficients
import Mathlib.Probability.Kernel.Invariance

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem MarkovChainCLT.isStrictlyStationary_chainMeasure {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) :
    IsStrictlyStationary (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) := by sorry
