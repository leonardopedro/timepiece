/-
prove2.me platform library module `Theorems.Thm_CircleMethod_norm_sum_e_le_inv_nrm`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_CircleMethod_norm_sum_e_le_inv_nrm.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CircleMethod_char
import Mathlib.Algebra.Field.GeomSum
open Finset

namespace CircleMethod

theorem norm_sum_e_le_inv_nrm {θ : ℝ} (h : ¬ ∃ n : ℤ, θ = n) (N : ℕ) :
    ‖∑ x ∈ Finset.range N, e ((x : ℝ) * θ)‖ ≤ 1 / (2 * nrm θ) := by sorry

end CircleMethod
