/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 69199077-6c68-47f2-bde7-5efb72094444
* original name       : `matrix_trace_duality_inequality`
* title               : None
* statement author    : Harry_Xu
* solution author     : Harry_Xu (submission 4d47b0c9-efd5-4f02-9981-bd910218b333,
                        accepted 2026-06-21T20:44:42.67066+00:00)
* source              : Candès–Recht 2009, arXiv:0805.4471, Lemma 3.2 (p.15)
* platform Mathlib rev: c5ea00351c28e24afc9f0f84379aa41082b1188f
* original file       : Downloads/unfer-sirk/matrix_trace_duality_inequality.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/matrix_trace_duality_inequality.diff`.
-/
import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Prove2me.Shim.SingularValues  -- was `Mathlib.Analysis.InnerProductSpace.SingularValues`
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
C1 — von Neumann / matrix trace-duality inequality:
  `matrixInner A B ≤ spectralNorm A * nuclearNorm B`.

Source: Candès–Recht 2009 (arXiv:0805.4471), §3 Lemma 3.2 first inequality
(von Neumann's trace inequality, 1937; see also Mirsky 1975).

Proof outline (built from Mathlib's self-adjoint spectral theorem; the SVD
reconstruction `B = Σ σ_k u_k v_k^T` is NOT available ready-made in this env's
Mathlib, so it is constructed here):
  * `T := toEuclideanLin B`, `G := Tᵀ∘T` symmetric and PSD.
  * `v_k := eigenvectorBasis G` orthonormal, eigenvalues `μ_k ≥ 0`,
    `σ_k = √μ_k = singularValues T k`.
  * `⟪T v_i, T v_j⟫ = ⟪G v_i, v_j⟫ = μ_i δ_ij`, so `‖T v_k‖ = σ_k`.
  * Frobenius inner product = Hilbert–Schmidt inner `∑_j ⟪S e_j, T e_j⟫`,
    which is `trace(Sᵀ∘T)` — basis-independent — hence `= ∑_k ⟪S v_k, T v_k⟫`.
  * `⟪S v_k, T v_k⟫ ≤ ‖S v_k‖·‖T v_k‖ ≤ ‖S‖·1·σ_k`; sum gives `‖S‖·Σσ_k`.
  * `Σ σ_k = nuclearNorm B`, `‖S‖ = spectralNorm A`.
-/

open Module InnerProductSpace LinearMap Matrix
open scoped BigOperators

/-! ### Operator-level SVD reconstruction & von Neumann inequality. -/

namespace SVDProbe

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

private noncomputable abbrev gram (T : E →ₗ[ℝ] F) : E →ₗ[ℝ] E := adjoint T ∘ₗ T

private theorem gram_symm (T : E →ₗ[ℝ] F) : (gram T).IsSymmetric :=
  T.isSymmetric_adjoint_comp_self

private theorem gram_pos (T : E →ₗ[ℝ] F) : (gram T).IsPositive :=
  T.isPositive_adjoint_comp_self

private noncomputable def rsv (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) :
    OrthonormalBasis (Fin n) ℝ E :=
  (gram_symm T).eigenvectorBasis hn

private noncomputable def evals (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) : Fin n → ℝ :=
  (gram_symm T).eigenvalues hn

private theorem evals_nonneg (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    0 ≤ evals T hn k :=
  (gram_pos T).nonneg_eigenvalues hn k

private theorem inner_Tv (T : E →ₗ[ℝ] F) (a b : E) :
    inner ℝ (T a) (T b) = inner ℝ (gram T a) b := by
  unfold gram
  rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_left]

private theorem inner_Tv_eig (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (i j : Fin n) :
    inner ℝ (T (rsv T hn i)) (T (rsv T hn j))
      = if i = j then evals T hn i else 0 := by
  rw [inner_Tv]
  unfold gram rsv evals
  rw [show (adjoint T ∘ₗ T) ((gram_symm T).eigenvectorBasis hn i)
        = (gram T) ((gram_symm T).eigenvectorBasis hn i) from rfl]
  rw [(gram_symm T).apply_eigenvectorBasis hn i]
  rw [inner_smul_left]
  rw [orthonormal_iff_ite.mp ((gram_symm T).eigenvectorBasis hn).orthonormal i j]
  simp only [conj_trivial]
  by_cases h : i = j
  · subst h; rw [if_pos rfl, if_pos rfl, mul_one, RCLike.ofReal_real_eq_id]; rfl
  · rw [if_neg h, if_neg h, mul_zero]

private noncomputable def sval (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) : ℝ :=
  T.singularValues k

private theorem sval_nonneg (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    0 ≤ sval T hn k := T.singularValues_nonneg k

private theorem sval_sq (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    sval T hn k ^ 2 = evals T hn k := by
  unfold sval evals
  rw [T.sq_singularValues_fin hn k]

private theorem norm_Tv (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    ‖T (rsv T hn k)‖ = sval T hn k := by
  have heig : inner ℝ (T (rsv T hn k)) (T (rsv T hn k)) = evals T hn k := by
    have h := inner_Tv_eig T hn k k
    rw [if_pos rfl] at h
    exact h
  have h2 : ‖T (rsv T hn k)‖ ^ 2 = sval T hn k ^ 2 := by
    rw [@norm_sq_eq_re_inner ℝ, heig, sval_sq, RCLike.re_to_real]
  have hnn := sval_nonneg T hn k
  nlinarith [norm_nonneg (T (rsv T hn k)), h2, hnn]

private theorem hsInner_eq_trace {ι : Type*} [Fintype ι] (S T : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E) :
    (∑ j, inner ℝ (S (b j)) (T (b j))) = (adjoint S ∘ₗ T).trace ℝ E := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro j _
  rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_right S (b j) (T (b j))]

private theorem hsInner_basis_indep {ι : Type*} [Fintype ι] (S T : E →ₗ[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) {n : ℕ} (hn : finrank ℝ E = n) :
    (∑ j, inner ℝ (S (b j)) (T (b j)))
      = ∑ k, inner ℝ (S (rsv T hn k)) (T (rsv T hn k)) := by
  rw [hsInner_eq_trace S T b, hsInner_eq_trace S T (rsv T hn)]

private theorem vonNeumann_op {ι : Type*} [Fintype ι] (S : E →L[ℝ] F) (T : E →ₗ[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) {n : ℕ} (hn : finrank ℝ E = n) :
    (∑ j, inner ℝ ((S : E →ₗ[ℝ] F) (b j)) (T (b j))) ≤ ‖S‖ * ∑ k, sval T hn k := by
  rw [hsInner_basis_indep (S : E →ₗ[ℝ] F) T b hn]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hSle : ‖(S : E →ₗ[ℝ] F) (rsv T hn k)‖ ≤ ‖S‖ * ‖(rsv T hn k : E)‖ := S.le_opNorm _
  calc inner ℝ ((S : E →ₗ[ℝ] F) (rsv T hn k)) (T (rsv T hn k))
      ≤ ‖(S : E →ₗ[ℝ] F) (rsv T hn k)‖ * ‖T (rsv T hn k)‖ := real_inner_le_norm _ _
    _ ≤ (‖S‖ * ‖(rsv T hn k : E)‖) * ‖T (rsv T hn k)‖ := by
          apply mul_le_mul_of_nonneg_right hSle (norm_nonneg _)
    _ = ‖S‖ * sval T hn k := by
          rw [(rsv T hn).orthonormal.1 k, norm_Tv]; ring

end SVDProbe

/-! ### Matrix specialization to the platform statement. -/

namespace MatrixCompletion

open SVDProbe

variable {n1 n2 : ℕ}

theorem matrixInner_eq_hsInner (A B : RealMatrix n1 n2) :
    matrixInner A B
      = ∑ j, inner ℝ ((toEuclideanLin A) (EuclideanSpace.basisFun (Fin n2) ℝ j))
                      ((toEuclideanLin B) (EuclideanSpace.basisFun (Fin n2) ℝ j)) := by
  unfold matrixInner
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply]
  simp only [toEuclideanLin_apply]
  have hcol : ∀ (C : RealMatrix n1 n2),
      (C *ᵥ (EuclideanSpace.single j (1:ℝ)).ofLp) i = C i j := by
    intro C
    simp only [Matrix.mulVec, EuclideanSpace.ofLp_single, dotProduct_single, mul_one]
  rw [hcol A, hcol B]
  rw [show (⟪A i j, B i j⟫_ℝ : ℝ) = B i j * (starRingEnd ℝ) (A i j) from RCLike.inner_apply _ _,
      conj_trivial]; ring

theorem nuclearNorm_eq_sum_sval (B : RealMatrix n1 n2)
    (hn : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2) :
    nuclearNorm B = ∑ k, sval (toEuclideanLin B) hn k := by
  unfold nuclearNorm sval
  set T := toEuclideanLin B
  rw [Finsupp.sum_of_support_subset T.singularValues
      (s := Finset.range n2) ?_ (fun _ x => x) (by intro _ _; rfl)]
  · rw [Finset.sum_range fun k => T.singularValues k]
  · intro k hk
    rw [Finset.mem_range]
    by_contra hge
    push_neg at hge
    have hz : T.singularValues k = 0 := by
      apply T.singularValues_of_finrank_le
      rw [hn]; exact hge
    rw [Finsupp.mem_support_iff] at hk
    exact hk hz

theorem trace_duality_C1 (A B : RealMatrix n1 n2) :
    matrixInner A B ≤ spectralNorm A * nuclearNorm B := by
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2 := finrank_euclideanSpace_fin
  rw [matrixInner_eq_hsInner A B, nuclearNorm_eq_sum_sval B hn]
  show (∑ j, inner ℝ ((toEuclideanLin A) (EuclideanSpace.basisFun (Fin n2) ℝ j))
                     ((toEuclideanLin B) (EuclideanSpace.basisFun (Fin n2) ℝ j)))
      ≤ spectralNorm A * ∑ k, sval (toEuclideanLin B) hn k
  unfold spectralNorm
  exact vonNeumann_op (LinearMap.toContinuousLinearMap (toEuclideanLin A))
    (toEuclideanLin B) (EuclideanSpace.basisFun (Fin n2) ℝ) hn

end MatrixCompletion

open MatrixCompletion
open scoped BigOperators

/-- C1 — von Neumann / matrix trace-duality inequality.
Source: Candès–Recht 2009 (arXiv:0805.4471), §3 Lemma 3.2, first inequality
(von Neumann's trace inequality 1937; Mirsky 1975). -/
theorem _root_.Prove2me.Solution.matrix_trace_duality_inequality {n₁ n₂ : ℕ} (A B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    matrixInner A B ≤ spectralNorm A * nuclearNorm B :=
  MatrixCompletion.trace_duality_C1 A B

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open MatrixCompletion

theorem matrix_trace_duality_inequality {n₁ n₂ : ℕ} (A B : Matrix (Fin n₁) (Fin n₂) ℝ) : matrixInner A B ≤ spectralNorm A * nuclearNorm B := by
  first
  | exact _root_.Prove2me.Solution.matrix_trace_duality_inequality A B
  | (apply _root_.Prove2me.Solution.matrix_trace_duality_inequality <;> assumption)


end Prove2meStatement
