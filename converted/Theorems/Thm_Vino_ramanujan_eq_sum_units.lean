/-
prove2.me platform library module `Theorems.Thm_Vino_ramanujan_eq_sum_units`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Vino_ramanujan_eq_sum_units.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_Vino_ramanujan
import Mathlib.Data.ZMod.Units
open Finset

namespace Vino

theorem ramanujan_eq_sum_units (q : ℕ) [NeZero q] (n : ℤ) :
    ramanujan q n
      = ∑ u : (ZMod q)ˣ,
          CircleMethod.e (((((u : ZMod q).val : ℤ) * n : ℤ) : ℝ) / (q : ℝ)) := by sorry

end Vino
