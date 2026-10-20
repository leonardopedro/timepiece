/-
prove2.me platform library module `Theorems.Thm_CircleMethod_aux_sum_min_le`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_CircleMethod_aux_sum_min_le.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CircleMethod_char
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Divisors
open Finset

namespace CircleMethod

theorem aux_sum_min_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H N q : ℕ) (a : ℤ) (α : ℝ) (g : ℕ → ℝ), 0 < H → 0 < N → 0 < q →
      Nat.Coprime a.natAbs q → |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      (∀ k : ℕ, 0 ≤ g k) → (∀ k : ℕ, g k ≤ (N : ℝ)) →
      (∀ k : ℕ, 2 * nrm ((k : ℝ) * α) * g k ≤ 1) →
      (∑ k ∈ Finset.Icc 1 H, g k)
        ≤ C * ((H : ℝ) / (q : ℝ) + 1) * ((N : ℝ) + (q : ℝ)) * (1 + Real.log (1 + (q : ℝ))) := by sorry

end CircleMethod
