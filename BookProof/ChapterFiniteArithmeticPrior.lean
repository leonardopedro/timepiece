import Mathlib

/-!
# Finite arithmetic with a Bayesian prior beyond the truncation

This module gives a precise finite model of the book's proposal.  Arithmetic
results inside a bound `B` are stored exactly; results outside the finite table
are represented by a normalized nonnegative prior on a finite hypothesis space.
-/

namespace BookProof.ChapterFiniteArithmeticPrior

/-- A finite table for a binary arithmetic operation below a bound. -/
structure BoundedArithmetic (B : ℕ) where
  result : Fin B → Fin B → Fin B

/-- A Bayesian extension of bounded arithmetic by a finite hypothesis space. -/
structure BayesianArithmeticExtension (B : ℕ) (H : Type*) [Fintype H] where
  known : BoundedArithmetic B
  prior : H → ℝ
  prior_nonneg : ∀ h, 0 ≤ prior h
  prior_sum_one : ∑ h, prior h = 1

/-- The unknown part of a Bayesian arithmetic extension is a genuine finite
probability distribution. -/
theorem prior_is_probability {B : ℕ} {H : Type*} [Fintype H]
    (E : BayesianArithmeticExtension B H) :
    (∀ h, 0 ≤ E.prior h) ∧ ∑ h, E.prior h = 1 := by
  exact ⟨E.prior_nonneg, E.prior_sum_one⟩

/-- Every exact bounded arithmetic table admits the degenerate one-hypothesis
Bayesian extension. -/
def certainExtension {B : ℕ} (A : BoundedArithmetic B) :
    BayesianArithmeticExtension B PUnit where
  known := A
  prior := fun _ => 1
  prior_nonneg := by intro; norm_num
  prior_sum_one := by simp

/-- The extension preserves every result in the finite exact table. -/
theorem certainExtension_known {B : ℕ} (A : BoundedArithmetic B) :
    (certainExtension A).known = A := by
  rfl

end BookProof.ChapterFiniteArithmeticPrior
