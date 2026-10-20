/-
prove2.me platform library module `Theorems.Thm_CircleMethod_integral_e_orthogonality`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_CircleMethod_integral_e_orthogonality.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CircleMethod_char
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open Finset

namespace CircleMethod

theorem integral_e_orthogonality (n : ℤ) : (∫ θ in (0:ℝ)..1, e ((n : ℝ) * θ)) = if n = 0 then 1 else 0 := by sorry

end CircleMethod
