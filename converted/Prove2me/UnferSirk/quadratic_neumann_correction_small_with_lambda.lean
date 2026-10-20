/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 608586f3-e74c-4fb6-8b0c-14edd04127f9
* original name       : `quadratic_neumann_correction_small_with_lambda`
* title               : None
* statement author    : Shuze Chen
* solution author     : Shuze Chen (submission 54c054b7-ac3a-441f-8088-57d61cc8bba3,
                        accepted 2026-07-04T14:25:14.073903+00:00)
* source              : Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.
* platform Mathlib rev: c5ea00351c28e24afc9f0f84379aa41082b1188f
* original file       : Downloads/unfer-sirk/quadratic_neumann_correction_small_with_lambda.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/quadratic_neumann_correction_small_with_lambda.diff`.
-/
-- (dropped self-import `Theorems.Thm_quadratic_neumann_correction_small_with_lambda`)
import Theorems.Thm_quadratic_neumann_all_equal_contribution_small_with_lambda
import Theorems.Thm_quadratic_neumann_first_index_distinct_contribution_small_with_lambda
import Theorems.Thm_quadratic_neumann_middle_index_distinct_contribution_small_with_lambda
import Theorems.Thm_quadratic_neumann_last_index_distinct_contribution_small_with_lambda
import Theorems.Thm_quadratic_neumann_all_distinct_contribution_small_with_lambda
import Theorems.Thm_quadratic_neumann_correction_from_index_partition_bounds
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Decompose Candes-Recht Lemma 4.6 by the five index-coincidence cases in
equation (6.20). -/
theorem _root_.Prove2me.Solution.quadratic_neumann_correction_small_with_lambda :
    ∃ C₂ c₂ : ℝ, 0 < C₂ ∧ 0 < c₂ ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              NeumannCertificateTermSpectralBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 2
                (C₂ * Real.rpow lam (-((3 : ℝ) / 2)))) ≥
          1 - c₂ * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases quadratic_neumann_all_equal_contribution_small_with_lambda with
    ⟨C0, c0, hC0, hc0, h0⟩
  rcases quadratic_neumann_first_index_distinct_contribution_small_with_lambda with
    ⟨C123, c123, hC123, hc123, h123⟩
  rcases quadratic_neumann_middle_index_distinct_contribution_small_with_lambda with
    ⟨C132, c132, hC132, hc132, h132⟩
  rcases quadratic_neumann_last_index_distinct_contribution_small_with_lambda with
    ⟨C112, c112, hC112, hc112, h112⟩
  rcases quadratic_neumann_all_distinct_contribution_small_with_lambda with
    ⟨Call, call, hCall, hcall, hall⟩
  refine ⟨(((C0 + C123) + C132) + C112) + Call,
    (((c0 + c123) + c132) + c112) + call, ?_, ?_, ?_⟩
  · exact add_pos (add_pos (add_pos (add_pos hC0 hC123) hC132) hC112) hCall
  · exact add_pos (add_pos (add_pos (add_pos hc0 hc123) hc132) hc112) hcall
  · intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
      ⟨hpNonneg, hpLeOne⟩
    have h0Prob :=
      h0 β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have h123Prob :=
      h123 β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have h132Prob :=
      h132 β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have h112Prob :=
      h112 β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have hallProb :=
      hall β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    exact quadratic_neumann_correction_from_index_partition_bounds S
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
      C0 C123 C132 C112 Call c0 c123 c132 c112 call β lam
      hpNonneg hpLeOne
      hc0 hc123 hc132 hc112 hcall h0Prob h123Prob h132Prob h112Prob hallProb

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open MatrixCompletion

theorem quadratic_neumann_correction_small_with_lambda :
    ∃ C₂ c₂ : ℝ, 0 < C₂ ∧ 0 < c₂ ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              NeumannCertificateTermSpectralBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 2
                (C₂ * Real.rpow lam (-((3 : ℝ) / 2)))) ≥
          1 - c₂ * Real.rpow (↑(max n₁ n₂)) (-β) := by
  first
  | exact _root_.Prove2me.Solution.quadratic_neumann_correction_small_with_lambda
  | (apply _root_.Prove2me.Solution.quadratic_neumann_correction_small_with_lambda <;> assumption)


end Prove2meStatement
