/-
# S3 bookkeeping: the cost of an approximate solve, and why a compression is not a resolvent

`softmodes.md`'s S3 package makes two bookkeeping demands before any rational-approximation claim
can be compared with a spectral one, and both are pure linear algebra:

* **The defect bound.**  For an approximate solve of `(h_F + γ)y ≈ v` with defect `r`, the error
  against the exact resolvent is `R r`, hence `‖y − X_γ v‖ ≤ ‖r‖ / γ`: the defect is transported by
  the *resolvent*, so the constant is `γ⁻¹` and does not depend on how badly conditioned the
  unshifted problem is.  This is `norm_solve_error_le`, and `IsShiftInvert.solve_error_le` feeds it
  the shift bound `‖R‖ ≤ γ⁻¹` that `Sirk/ChapterHashimotoShiftInvert` proves from positivity alone.
* **The compression is not the resolvent.**  The natural truncated solve inverts the compression
  `P_Λ h_F P_Λ + γ`, while the object a spectral estimate controls is `P_Λ X_γ P_Λ`.  The plan warns
  that their equality "is not automatic", and Part 2 is a concrete two-dimensional witness: the
  rank-one `A x = (x₀ + x₁) • (1,1)` at shift `γ = 1` has resolvent value `2/3` on `e₀`, while the
  compressed operator is `2 x₀` there, so the compressed solve returns `1/2`.  The `1/6`
  discrepancy is a relative `25%` error at the first basis vector, and the compressed solve's defect
  is `(0, 1/2)` — exactly the quantity Part 1's bound has to absorb.

What is *not* claimed: no norm estimate for `P_Λ X_γ P_Λ − (P_Λ h_F P_Λ + γ)⁻¹` in general, and no
statement about the `m` admissible under a fixed shift budget.  Part 2 is over `ℚ`, so its
computations are exact; the operator is positive in the sense of `rankOne_inner_nonneg`, so the
shift bound of Part 1 applies to it.
-/
import BookProof.Sirk.ChapterHashimotoShiftInvert

namespace BookProof.HashimotoShiftInvertBookkeeping

open BookProof.FarisLavine BookProof.HashimotoShiftInvert

/-! ## Part 1 — the defect bound -/

/-- **The solve error is the defect through the resolvent.**  If `‖R‖ ≤ γ⁻¹` and the solver returns
`R (v + r)` for the right-hand side `v + r`, then the error against the exact solution `R v` is
`R r`, hence at most `‖r‖ / γ`.  Linearity supplies `R r`; the norm bound supplies the constant;
no invertibility of anything is used beyond the given bound. -/
theorem norm_solve_error_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {R : F →L[ℂ] F} {γ : ℝ} (hR : ‖R‖ ≤ γ⁻¹) (v r : F) :
    ‖R (v + r) - R v‖ ≤ γ⁻¹ * ‖r‖ := by
  have h : R (v + r) - R v = R r := by
    rw [map_add, add_sub_cancel_left]
  rw [h]
  exact (R.le_opNorm r).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg r))

/-- The same bound with the shift bound taken from `IsShiftInvert.opNorm_le`, i.e. from positivity
of the quadratic form of the unbounded operator and positivity of the shift — the only hypotheses
the corpus needs for `‖(A + γ)⁻¹‖ ≤ γ⁻¹`. -/
theorem IsShiftInvert.solve_error_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) (v r : F) :
    ‖R (v + r) - R v‖ ≤ γ⁻¹ * ‖r‖ :=
  norm_solve_error_le (h.opNorm_le hpos hγ) v r

/-! ## Part 2 — a compression of the resolvent is not the resolvent of the compression -/

/-- The first basis vector of `ℚ²`. -/
def e0 : Fin 2 → ℚ := fun i => if i = 0 then 1 else 0

/-- The rank-one operator `v vᵀ` with `v = (1,1)`, i.e. `x ↦ (x₀ + x₁) • (1,1)`. -/
def rankOne (x : Fin 2 → ℚ) : Fin 2 → ℚ := fun _ => x 0 + x 1

/-- Its compression to the first coordinate: `x ↦ x₀ • (1,0)`. -/
def rankOneCompressed (x : Fin 2 → ℚ) : Fin 2 → ℚ := fun i => if i = 0 then x 0 else 0

/-- The positive quadratic form of `rankOne`: `⟨x, A x⟩ = (x₀ + x₁)²`, the reason the shift bound
of Part 1 applies to this operator. -/
theorem rankOne_inner_nonneg (x : Fin 2 → ℚ) : 0 ≤ x 0 * rankOne x 0 + x 1 * rankOne x 1 := by
  simp only [rankOne]
  nlinarith [sq_nonneg (x 0 + x 1)]

/-- The exact solution of `(A + 1) y = e₀`: `(2/3, -1/3)`. -/
def exactSolve : Fin 2 → ℚ := fun i => if i = 0 then 2 / 3 else -1 / 3

/-- The compressed solve of `(P A P + 1) y = e₀`: `(1/2, 0)`. -/
def compressedSolve : Fin 2 → ℚ := fun i => if i = 0 then 1 / 2 else 0

/-- `exactSolve` really solves the shifted equation: `(A + 1) exactSolve = e₀`. -/
theorem exactSolve_solves : ∀ i, rankOne exactSolve i + exactSolve i = e0 i := by
  intro i
  fin_cases i <;> norm_num [rankOne, exactSolve, e0]

/-- `compressedSolve` really solves the compressed equation `(P A P + 1) y = e₀`. -/
theorem compressedSolve_solves :
    ∀ i, rankOneCompressed compressedSolve i + compressedSolve i = e0 i := by
  intro i
  fin_cases i <;> norm_num [rankOneCompressed, compressedSolve, e0]

/-- The defect of the compressed solve: `(A + 1) y − e₀ = (0, 1/2)`.  Nonzero, so the truncated
solve is genuinely inexact and Part 1's bound is what controls the resulting error. -/
theorem compressedSolve_defect :
    ∀ i, rankOne compressedSolve i + compressedSolve i - e0 i
      = (if i = 0 then 0 else 1 / 2) := by
  intro i
  fin_cases i <;> norm_num [rankOne, compressedSolve, e0]

/-- **The compression of the resolvent differs from the resolvent of the compression**, at the very
state the truncation is built for: the true resolvent value is `2/3`, the compressed solve returns
`1/2`.  So `P_Λ X_γ P_Λ` and `(P_Λ h_F P_Λ + γ)⁻¹` cannot be identified, and the gap is the
omitted coupling to the second coordinate. -/
theorem compression_ne_resolvent : exactSolve 0 ≠ compressedSolve 0 := by
  norm_num [exactSolve, compressedSolve]

/-- The discrepancy read as the error vector: the truncated answer is off by `(−1/6, 1/3)`. -/
theorem compressed_solve_error :
    ∀ i, exactSolve i - compressedSolve i = (if i = 0 then 1 / 6 else -1 / 3) := by
  intro i
  fin_cases i <;> norm_num [exactSolve, compressedSolve]

/-- Part 1 applied to this example: the defect transported by the resolvent is the error the
compressed solve commits, up to sign — `X (defect) = (−1/6, 1/3) = compressedSolve − exactSolve`,
with `X = (A + 1)⁻¹` and `defect = (0, 1/2)`.  This is the mechanism Part 1 bounds: the error is a
resolvent-sized multiple of the defect, not the defect itself. -/
theorem defect_image_eq_error :
    ∀ i, rankOne (fun j => if j = 0 then -1 / 6 else 1 / 3) i
        + (fun j => if j = 0 then -1 / 6 else 1 / 3) i
      = (fun j => if j = 0 then 0 else 1 / 2) i := by
  intro i
  fin_cases i <;> norm_num [rankOne]

/-- The same identity read on the error vector: `compressedSolve − exactSolve = (−1/6, 1/3)`. -/
theorem compressed_solve_error_eq_defect_image :
    ∀ i, compressedSolve i - exactSolve i = (if i = 0 then -1 / 6 else 1 / 3) := by
  intro i
  fin_cases i <;> norm_num [exactSolve, compressedSolve]

end BookProof.HashimotoShiftInvertBookkeeping
