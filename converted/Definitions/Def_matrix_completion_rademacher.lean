/-
prove2.me platform library module `Definitions.Def_matrix_completion_rademacher`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_matrix_completion_rademacher.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_matrix_completion_schatten

/-!
Rademacher signs used in the symmetrization step of Section 6.1.

The paper introduces an independent sign sequence `ε_ab` after symmetrizing
`p^{-1}(P_Omega - pI)X`.  We encode a sign realization by the finset of
coordinates where the sign is `+1`; all other coordinates have sign `-1`.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Uniform probability weight on all Rademacher sign assignments. -/
noncomputable def rademacherObservationWeight {n1 n2 : Nat}
    (_eps : Finset (Fin n1 × Fin n2)) : Real :=
  ((1 : Real) / 2) ^ Fintype.card (Fin n1 × Fin n2)

/-- Expectation over independent Rademacher signs on matrix coordinates. -/
noncomputable def rademacherExpectation {n1 n2 : Nat}
    (F : Finset (Fin n1 × Fin n2) → Real) : Real :=
  ∑ eps : Finset (Fin n1 × Fin n2),
    rademacherObservationWeight eps * F eps

/-- The sign `ε_ij`, encoded by membership in a sign-realization finset. -/
def rademacherSign {n1 n2 : Nat}
    (eps : Finset (Fin n1 × Fin n2)) (i : Fin n1) (j : Fin n2) :
    Real :=
  if (i, j) ∈ eps then 1 else -1

/-- The symmetrized sampled matrix
`p^{-1} ∑ ε_ij δ_ij X_ij e_i e_j^*` from Section 6.1. -/
noncomputable def rademacherSampledMatrix {n1 n2 : Nat}
    (Omega eps : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) : RealMatrix n1 n2 :=
  fun i j =>
    p⁻¹ * if (i, j) ∈ Omega then rademacherSign eps i j * X i j else 0

/-- Conditional Khintchine variance scale for the coordinate Rademacher series:
`p^{-1}` times the square root of the larger sampled row/column energy. -/
noncomputable def rademacherSampledVarianceScale {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) : Real :=
  p⁻¹ * Real.sqrt
    (max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X))

end MatrixCompletion
