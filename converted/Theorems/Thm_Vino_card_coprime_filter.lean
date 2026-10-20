/-
prove2.me platform library module `Theorems.Thm_Vino_card_coprime_filter`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Vino_card_coprime_filter.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_Vino_ramanujan
import Mathlib.Data.Nat.Totient
open Finset

namespace Vino

theorem card_coprime_filter (q : ℕ) :
    (((Finset.range q).filter (fun a => Nat.Coprime a q)).card) = Nat.totient q := by sorry

end Vino
