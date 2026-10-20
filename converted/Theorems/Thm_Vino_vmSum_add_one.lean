/-
prove2.me platform library module `Theorems.Thm_Vino_vmSum_add_one`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Vino_vmSum_add_one.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_Vino_primes
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Finset

namespace Vino

theorem vmSum_add_one (α : ℝ) (N : ℕ) : vmSum (α + 1) N = vmSum α N := by sorry

end Vino
