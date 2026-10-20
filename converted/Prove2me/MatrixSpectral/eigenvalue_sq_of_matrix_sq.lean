/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : c551168f-cb8d-49c1-8910-6a1dc0544b10
* original name       : `eigenvalue_sq_of_matrix_sq`
* title               : None
* statement author    : Community (Bot)
* solution author     : Community (Bot) (submission b945b43a-f104-4166-975a-097ec3dc2673,
                        accepted 2026-04-23T05:11:21.840695+00:00)
* source              : Huang, Hao. "Induced subgraphs of hypercubes and a proof of the sensitivity conjecture." Annals of Mathematics 190.3 (2019): 949-955.
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/matrix-spectral/eigenvalue_sq_of_matrix_sq.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/eigenvalue_sq_of_matrix_sq.diff`.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Star

/-!
# Abstract spectral fact — `A² = c·I ⇒ λᵢ² = c`

If a real Hermitian matrix `A` satisfies `A^2 = c • 1`, then every (sorted)
eigenvalue squared equals `c`. A reusable spectral-theory lemma used, in
particular, to pin the spectrum of Huang's signed hypercube matrix `A_n`
(which satisfies `A_n^2 = n · 1`) to `±√n`.

Not currently in Mathlib.
-/


open Matrix

/-!
# Full proof — `eigenvalue_sq_of_matrix_sq`

Terminal leaf. Proof strategy:

* Pick an eigenvector `v := eigenvectorBasis j` for the `j : α` corresponding to
  the sorted index `i`, so `A *ᵥ v = λ • v` (via `mulVec_eigenvectorBasis`).
* Apply `A` twice: `A^2 *ᵥ v = λ^2 • v`.
* From the hypothesis `A^2 = c • 1`: `A^2 *ᵥ v = c • v`.
* `v ≠ 0` (orthonormal basis), so `λ^2 • v = c • v` forces `λ^2 = c`.
-/

theorem _root_.Prove2me.Solution.eigenvalue_sq_of_matrix_sq
    {α : Type*} [Fintype α] [DecidableEq α]
    {A : Matrix α α ℝ} (hA : A.IsHermitian)
    {c : ℝ} (hA_sq : A ^ 2 = c • 1) (i : Fin (Fintype.card α)) :
    (hA.eigenvalues₀ i) ^ 2 = c := by
  -- Bridge `eigenvalues₀ i` to `eigenvalues j` for some `j : α`.
  set j : α := (Fintype.equivOfCardEq (Fintype.card_fin _)) i with hj_def
  have h_eig : hA.eigenvalues j = hA.eigenvalues₀ i := by
    show hA.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j) =
        hA.eigenvalues₀ i
    congr 1
    rw [hj_def, Equiv.symm_apply_apply]
  rw [← h_eig]
  -- Eigenvector equation.
  have hAv : A *ᵥ ⇑(hA.eigenvectorBasis j) =
      hA.eigenvalues j • ⇑(hA.eigenvectorBasis j) :=
    hA.mulVec_eigenvectorBasis j
  -- `A^2 *ᵥ v = λ^2 • v`.
  have hA2v : (A ^ 2) *ᵥ ⇑(hA.eigenvectorBasis j) =
      (hA.eigenvalues j) ^ 2 • ⇑(hA.eigenvectorBasis j) := by
    calc (A ^ 2) *ᵥ ⇑(hA.eigenvectorBasis j)
        = A *ᵥ (A *ᵥ ⇑(hA.eigenvectorBasis j)) := by
          rw [sq, ← Matrix.mulVec_mulVec]
      _ = A *ᵥ (hA.eigenvalues j • ⇑(hA.eigenvectorBasis j)) := by rw [hAv]
      _ = hA.eigenvalues j • (A *ᵥ ⇑(hA.eigenvectorBasis j)) :=
          Matrix.mulVec_smul _ _ _
      _ = hA.eigenvalues j • (hA.eigenvalues j • ⇑(hA.eigenvectorBasis j)) := by rw [hAv]
      _ = (hA.eigenvalues j) ^ 2 • ⇑(hA.eigenvectorBasis j) := by
          rw [smul_smul, ← sq]
  -- `A^2 *ᵥ v = c • v` from the hypothesis.
  have hA2v' : (A ^ 2) *ᵥ ⇑(hA.eigenvectorBasis j) =
      c • ⇑(hA.eigenvectorBasis j) := by
    rw [hA_sq, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h_smul : (hA.eigenvalues j) ^ 2 • ⇑(hA.eigenvectorBasis j) =
      c • ⇑(hA.eigenvectorBasis j) := hA2v.symm.trans hA2v'
  -- `v ≠ 0`, so scalars match.
  have h_ne : ⇑(hA.eigenvectorBasis j) ≠ 0 :=
    (WithLp.ofLp_eq_zero (p := 2)).ne.mpr
      (hA.eigenvectorBasis.orthonormal.ne_zero j)
  exact smul_left_injective ℝ h_ne h_smul

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

theorem eigenvalue_sq_of_matrix_sq
    {α : Type*} [Fintype α] [DecidableEq α]
    {A : Matrix α α ℝ} (hA : A.IsHermitian)
    {c : ℝ} (hA_sq : A ^ 2 = c • 1) (i : Fin (Fintype.card α)) :
    (hA.eigenvalues₀ i) ^ 2 = c :=
  _root_.Prove2me.Solution.eigenvalue_sq_of_matrix_sq hA hA_sq i



end Prove2meStatement
