/-
prove2.me platform library module `Theorems.Thm_MarkovChainCLT_processSigma_Iic_eq_comap_restrict`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_MarkovChainCLT_processSigma_Iic_eq_comap_restrict.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_MixingCoefficients

open MeasureTheory MeasurableSpace
open MarkovChainCLT

theorem MarkovChainCLT.processSigma_Iic_eq_comap_restrict {X : Type*} [MeasurableSpace X] (k : ℕ) :
    processSigma (fun i (ω : ℕ → X) => ω i) (Set.Iic k)
      = MeasurableSpace.comap
          (fun ω : ℕ → X => fun i : Finset.Iic k => ω i.1) inferInstance := by sorry
