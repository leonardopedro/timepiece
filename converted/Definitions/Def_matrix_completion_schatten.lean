/-
prove2.me platform library module `Definitions.Def_matrix_completion_schatten`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_matrix_completion_schatten.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_matrix_completion_tangent
import Prove2me.Shim.SingularValues  -- conversion shim (platform Mathlib API)

/-!
Schatten norms for finite real matrices.

Section 6.1 compares the operator norm to the Schatten `q`-norm and then
applies the noncommutative Khintchine inequality in Schatten norm.  Mathlib
already provides singular values for finite-dimensional linear maps; this file
packages the corresponding finite matrix norm used by the paper.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Schatten `q`-norm of a real matrix, written using the singular values of
the associated Euclidean linear map.  The exponent is real-valued so the paper's
`q ≥ log n` comparisons can be stated directly. -/
noncomputable def schattenNorm {n1 n2 : Nat} (q : Real)
    (X : RealMatrix n1 n2) : Real :=
  Real.rpow
    (∑ k : Fin n2,
      Real.rpow ((Matrix.toEuclideanLin X).singularValues k) q)
    q⁻¹

end MatrixCompletion
