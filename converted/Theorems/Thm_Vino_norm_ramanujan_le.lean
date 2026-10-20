/-
prove2.me platform library module `Theorems.Thm_Vino_norm_ramanujan_le`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Vino_norm_ramanujan_le.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_Vino_ramanujan
import Mathlib.Data.Nat.Totient
open Finset

namespace Vino

theorem norm_ramanujan_le (q : ℕ) (n : ℤ) : ‖ramanujan q n‖ ≤ (Nat.totient q : ℝ) := by sorry

end Vino
