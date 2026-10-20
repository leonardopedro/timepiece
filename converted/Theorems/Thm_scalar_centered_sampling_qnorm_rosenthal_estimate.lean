/-
prove2.me platform library module `Theorems.Thm_scalar_centered_sampling_qnorm_rosenthal_estimate`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_scalar_centered_sampling_qnorm_rosenthal_estimate.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators

theorem scalar_centered_sampling_qnorm_rosenthal_estimate :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n₁ n₂ m : ℕ), 0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      ∀ (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ)
        (B : Matrix (Fin n₁) (Fin n₂) ℝ)
        (entryScale frobScale : ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Coeff Omega =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) →
        entrySupNorm B ≤ entryScale →
        frobeniusNorm B ≤ frobScale →
        ∀ q : ℕ, 1 ≤ q →
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega => |Coeff Omega| ^ q) ≤
            (C *
                (Real.sqrt
                    ((q : ℝ) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  frobScale +
                  ((q : ℝ) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entryScale)) ^ q := by
  sorry
