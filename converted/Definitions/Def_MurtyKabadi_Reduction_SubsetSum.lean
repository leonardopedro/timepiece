/-
prove2.me platform library module `Definitions.Def_MurtyKabadi_Reduction_SubsetSum`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_MurtyKabadi_Reduction_SubsetSum.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace MurtyKabadi.Reduction

/-- Problem 5, the subset sum problem (p. 123): with data `d₀; d₁, …, d_n`, is there an integer
vector `y` with `∑ d_j y_j = d₀` and `0 ≤ y_j ≤ 1` for all `j`? -/
def SubsetSumSolvable {n : ℕ} (d : Fin n → ℕ) (d0 : ℕ) : Prop :=
  ∃ y : Fin n → ℤ, (∀ j, 0 ≤ y j ∧ y j ≤ 1) ∧ ∑ j, (d j : ℤ) * y j = d0

/-- The size `l` of the subset sum instance (p. 123): the total number of (decimal) digits in
all the data `d₀, d₁, …, d_n`. -/
def digitCount {n : ℕ} (d : Fin n → ℕ) (d0 : ℕ) : ℕ :=
  (Nat.digits 10 d0).length + ∑ j, (Nat.digits 10 (d j)).length

end MurtyKabadi.Reduction
