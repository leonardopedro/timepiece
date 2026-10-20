/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 14f3efe5-b829-47d8-9ff1-13ae99336095
* original name       : `nuclear_norm_dual_achiever_contraction`
* title               : None
* statement author    : Harry_Xu
* solution author     : Harry_Xu (submission a3c80c60-8cfd-420c-a148-113ae41afec8,
                        accepted 2026-06-21T22:07:39.091717+00:00)
* source              : Candès–Recht 2009, arXiv:0805.4471, Lemma 3.2 (p.15)
* platform Mathlib rev: c5ea00351c28e24afc9f0f84379aa41082b1188f
* original file       : Downloads/unfer-sirk/nuclear_norm_dual_achiever_contraction.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/nuclear_norm_dual_achiever_contraction.diff`.
-/
import Prove2me.UnferSirk.matrix_svd_exists  -- was `Theorems.Thm_matrix_svd_exists`
import Prove2me.UnferSirk.sign_matrix_inner_eq_nuclear_norm  -- was `Theorems.Thm_sign_matrix_inner_eq_nuclear_norm`
import Theorems.Thm_sign_matrix_spectral_norm_le_one
import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_svd

open MatrixCompletion

theorem _root_.Prove2me.Solution.nuclear_norm_dual_achiever_contraction {n₁ n₂ : ℕ} (N : Matrix (Fin n₁) (Fin n₂) ℝ) :
    ∃ Z : Matrix (Fin n₁) (Fin n₂) ℝ,
      spectralNorm Z ≤ 1 ∧ matrixInner Z N = nuclearNorm N := by
  obtain ⟨r, S, _⟩ := matrix_svd_exists N
  exact ⟨signMatrix S, sign_matrix_spectral_norm_le_one S, sign_matrix_inner_eq_nuclear_norm S⟩

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open MatrixCompletion

theorem nuclear_norm_dual_achiever_contraction {n₁ n₂ : ℕ} (N : Matrix (Fin n₁) (Fin n₂) ℝ) : ∃ Z : Matrix (Fin n₁) (Fin n₂) ℝ, spectralNorm Z ≤ 1 ∧ matrixInner Z N = nuclearNorm N := by
  first
  | exact _root_.Prove2me.Solution.nuclear_norm_dual_achiever_contraction N
  | (apply _root_.Prove2me.Solution.nuclear_norm_dual_achiever_contraction <;> assumption)


end Prove2meStatement
