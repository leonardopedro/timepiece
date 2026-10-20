/-
prove2.me platform library module `Theorems.Thm_MarkovChainCLT_processSigma_Ici_eq_comap_shift`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_MarkovChainCLT_processSigma_Ici_eq_comap_shift.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_MixingCoefficients

open MeasureTheory MeasurableSpace
open MarkovChainCLT

theorem MarkovChainCLT.processSigma_Ici_eq_comap_shift {X : Type*} [MeasurableSpace X] (m : ℕ) :
    processSigma (fun i (ω : ℕ → X) => ω i) (Set.Ici m)
      = MeasurableSpace.comap (fun ω : ℕ → X => fun n => ω (m + n)) inferInstance := by sorry
