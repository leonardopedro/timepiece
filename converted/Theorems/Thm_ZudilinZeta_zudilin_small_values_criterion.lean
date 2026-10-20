/-
prove2.me platform library module `Theorems.Thm_ZudilinZeta_zudilin_small_values_criterion`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_ZudilinZeta_zudilin_small_values_criterion.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_ZudilinZetaArith

namespace ZudilinZeta
theorem zudilin_small_values_criterion (P : Params) (hr : P.r = 3)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ Lambda P n ≠ 0 ∧ |Lambda P n| < ε) :
    ∃ k ∈ Finset.Icc 1 ((P.q - P.r - 2) / 2), Irrational (zetaR (P.r + 2 * k)) := by sorry
end ZudilinZeta
