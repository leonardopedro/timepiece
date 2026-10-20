/-
prove2.me platform library module `Theorems.Thm_quadratic_neumann_correction_from_index_partition_bounds`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_quadratic_neumann_correction_from_index_partition_bounds.lean` (platform Mathlib rev c5ea00351c28).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_correction_from_index_partition_bounds
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p C0 C123 C132 C112 Call c0 c123 c132 c112 call β lam : ℝ) :
    0 ≤ p → p ≤ 1 →
    0 < c0 → 0 < c123 → 0 < c132 → 0 < c112 → 0 < call →
    bernoulliEventProb p
        (fun Omega => spectralNorm (quadraticNeumannAllEqualContribution Omega S p) ≤
          C0 * Real.rpow lam (-((3 : ℝ) / 2))) ≥
        1 - c0 * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => spectralNorm (quadraticNeumannFirstIndexDistinctContribution Omega S p) ≤
          C123 * Real.rpow lam (-((3 : ℝ) / 2))) ≥
        1 - c123 * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => spectralNorm (quadraticNeumannMiddleIndexDistinctContribution Omega S p) ≤
          C132 * Real.rpow lam (-((3 : ℝ) / 2))) ≥
        1 - c132 * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S p) ≤
          C112 * Real.rpow lam (-((3 : ℝ) / 2))) ≥
        1 - c112 * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤
          Call * Real.rpow lam (-((3 : ℝ) / 2))) ≥
        1 - call * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega =>
          NeumannCertificateTermSpectralBound Omega S p 2
            (((((C0 + C123) + C132) + C112) + Call) *
              Real.rpow lam (-((3 : ℝ) / 2)))) ≥
        1 - (((((c0 + c123) + c132) + c112) + call) *
          Real.rpow (↑(max n₁ n₂)) (-β)) := by
  sorry
