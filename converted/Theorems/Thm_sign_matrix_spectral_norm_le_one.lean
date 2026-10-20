/-
prove2.me platform library module `Theorems.Thm_sign_matrix_spectral_norm_le_one`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_sign_matrix_spectral_norm_le_one.lean` (platform Mathlib rev c5ea00351c28).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem sign_matrix_spectral_norm_le_one
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r) :
    spectralNorm (signMatrix S) ≤ 1 := by
  sorry
