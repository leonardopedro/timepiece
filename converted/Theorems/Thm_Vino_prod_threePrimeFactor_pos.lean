/-
prove2.me platform library module `Theorems.Thm_Vino_prod_threePrimeFactor_pos`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Vino_prod_threePrimeFactor_pos.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_Vino_ramanujan
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Ring.Finset
open Finset

namespace Vino

theorem prod_threePrimeFactor_pos {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p) {n : ℤ} (hn : ¬ (2 : ℤ) ∣ n) :
    0 < ∏ p ∈ s, threePrimeFactor p n := by sorry

end Vino
