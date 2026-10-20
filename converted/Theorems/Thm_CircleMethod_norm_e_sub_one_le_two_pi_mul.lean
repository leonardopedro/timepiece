/-
prove2.me platform library module `Theorems.Thm_CircleMethod_norm_e_sub_one_le_two_pi_mul`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_CircleMethod_norm_e_sub_one_le_two_pi_mul.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CircleMethod_char
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
open Finset

namespace CircleMethod

theorem norm_e_sub_one_le_two_pi_mul (x : ℝ) : ‖e x - 1‖ ≤ 2 * Real.pi * |x| := by sorry

end CircleMethod
