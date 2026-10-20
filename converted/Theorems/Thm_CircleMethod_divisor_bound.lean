/-
prove2.me platform library module `Theorems.Thm_CircleMethod_divisor_bound`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_CircleMethod_divisor_bound.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CircleMethod_genfun
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Fintype.Pi
open Finset

namespace CircleMethod

theorem divisor_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ((n.divisors.card : ℝ)) ≤ C * (n : ℝ) ^ ε := by sorry

end CircleMethod
