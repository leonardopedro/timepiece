/-
prove2.me platform library module `Theorems.Thm_CircleMethod_rat_sep`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_CircleMethod_rat_sep.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CircleMethod_char
open Finset

namespace CircleMethod

theorem rat_sep {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') {a a' : ℤ}
    (hne : (a : ℝ) / (q : ℝ) ≠ (a' : ℝ) / (q' : ℝ)) :
    1 / ((q : ℝ) * (q' : ℝ)) ≤ |(a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ)| := by sorry

end CircleMethod
