/-
prove2.me platform library module `Theorems.Thm_CircleMethod_farey_cover_coprime`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_CircleMethod_farey_cover_coprime.lean` (platform Mathlib rev 0df444a360ea).
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

theorem farey_cover_coprime {Q : ℕ} (hQ : 0 < Q) (α : ℝ) :
    ∃ (a : ℤ) (q : ℕ), 0 < q ∧ q ≤ Q ∧ Nat.Coprime a.natAbs q ∧
      |α - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * ((Q : ℝ) + 1)) := by sorry

end CircleMethod
