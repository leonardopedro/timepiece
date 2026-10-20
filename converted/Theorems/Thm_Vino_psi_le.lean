/-
prove2.me platform library module `Theorems.Thm_Vino_psi_le`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Vino_psi_le.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_Vino_primes
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Finset

namespace Vino

theorem psi_le (N : ℕ) (hN : 1 ≤ N) : psi N ≤ (N : ℝ) * Real.log N := by sorry

end Vino
