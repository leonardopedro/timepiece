/-
prove2.me platform library module `Definitions.Def_matrix_completion_svd`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_matrix_completion_svd.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_matrix_completion_basic

/-!
SVD data and coherence assumptions from Candes-Recht Theorem 1.3.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Explicit rank-`r` SVD data for a matrix.  We carry the singular vectors as
plain coordinate functions so the theorem statement does not depend on extracting
an SVD from Mathlib. -/
structure SVD {n1 n2 : Nat} (M : RealMatrix n1 n2) (r : Nat) where
  sigma : Fin r → Real
  u : Fin r → (Fin n1 → Real)
  v : Fin r → (Fin n2 → Real)
  sigma_pos : ∀ k, 0 < sigma k
  u_orthonormal : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0
  v_orthonormal : ∀ k l, ∑ j, v k j * v l j = if k = l then 1 else 0
  decomp : M = ∑ k, sigma k • Matrix.vecMulVec (u k) (v k)

/-- Sign matrix `E = sum_k u_k v_k^T` associated to an SVD. -/
noncomputable def signMatrix {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) : RealMatrix n1 n2 :=
  ∑ k, Matrix.vecMulVec (S.u k) (S.v k)

/-- Coherence of the span of an orthonormal family, in the coordinate form used
by Definition 1.2. -/
noncomputable def coherence (N r : Nat) (u : Fin r → (Fin N → Real)) : Real :=
  (N : Real) / r * ⨆ i : Fin N, ∑ k, (u k i) ^ 2

/-- Assumption A0: both column and row spaces have coherence at most `mu0`. -/
def A0 {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (mu0 : Real) : Prop :=
  coherence n1 r S.u ≤ mu0 ∧ coherence n2 r S.v ≤ mu0

/-- Assumption A1: the sign matrix has uniformly bounded entries. -/
def A1 {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (mu1 : Real) : Prop :=
  ∀ i j,
    |signMatrix S i j| ≤
      mu1 * Real.sqrt ((r : Real) / ((n1 : Real) * (n2 : Real)))

/-- The crude A1 parameter forced by A0 via Cauchy-Schwarz in the paper. -/
noncomputable def defaultA1Parameter (mu0 : Real) (r : Nat) : Real :=
  mu0 * Real.sqrt (r : Real)

end MatrixCompletion
