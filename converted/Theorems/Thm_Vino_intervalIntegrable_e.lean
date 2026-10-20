/-
prove2.me platform library module `Theorems.Thm_Vino_intervalIntegrable_e`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Vino_intervalIntegrable_e.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CircleMethod_char
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open Finset

namespace Vino

theorem intervalIntegrable_e (m : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun α : ℝ => CircleMethod.e (m * α)) MeasureTheory.volume a b := by sorry

end Vino
