/-
prove2.me platform library module `Theorems.Thm_CircleMethod_nrm_eq_zero_iff`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_CircleMethod_nrm_eq_zero_iff.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CircleMethod_char
import Mathlib.Algebra.Field.GeomSum
open Finset

namespace CircleMethod

theorem nrm_eq_zero_iff (θ : ℝ) : nrm θ = 0 ↔ ∃ n : ℤ, θ = n := by sorry

end CircleMethod
