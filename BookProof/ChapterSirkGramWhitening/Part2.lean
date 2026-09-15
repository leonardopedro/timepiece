import Mathlib
import BookProof.ChapterSirkWhitening
import BookProof.ChapterSirkDiffusiveDecay
import BookProof.ChapterSirkTruncation
import BookProof.ChapterSirkGramWhitening.Part1

/-!
# Chapter SirkGramWhitening — the Gram whitening exists and *is* an orthonormalization

`CONSOLIDATED_PLAN.md` §12.2, **Gap 4c**.  `BookProof/ChapterSirkWhitening.lean`
proves that the reduced operator does not depend on *which* orthonormalization of
the retained Krylov vectors is used — but every statement there is conditional on
being handed an isometric embedding `V` (`V∗V = 1`) with the prescribed range.
The numerics does not orthonormalize by an abstract construction: it forms the
Gram matrix `G_{ij} = ⟪w_i, w_j⟫` of the raw (rational) Krylov vectors,
diagonalizes it, and whitens with a `T` such that `T∗ G T = 1`.

This module closes that gap from below: it builds the objects the numerics uses
and proves that they satisfy the hypotheses of `ChapterSirkWhitening`.

## Deliverables

* `synthesis w` — the coefficient-to-state map `c ↦ ∑ i, c i • w i` of the raw
  Krylov vectors, with `range_synthesis`: its range is exactly the retained
  subspace `span{w₀, …, w_{m−1}}`.
* `gramOp w = (synthesis w)∗ (synthesis w)` — the Gram operator, with
  `gramOp_apply` (its entries are the Gram matrix `⟪w i, w j⟫`),
  `gramOp_isSelfAdjoint`, `gramOp_nonneg`.
* `IsWhitening w T` — the numerics' defining property `T∗ G T = 1`; `whitened w T`
  the resulting embedding.
* `whitened_adjoint_comp_self` — **a whitening is an isometric embedding**, so
  every theorem of `ChapterSirkWhitening` applies to it; `range_whitened` — its
  range is the retained subspace as soon as `T` is surjective.
* `exists_isWhitening` — **a whitening exists** for linearly independent Krylov
  vectors (the non-degenerate case), and `exists_isometry_range_eq_span` — an
  isometric embedding of the retained subspace exists in general, with reduced
  dimension equal to the rank (the exact, lossless rank truncation).
* `sirkApprox_gram_whitening_eq`, `compress_gram_whitening_conj` — the end
  statements: the reconstructed SIRK operator is literally the same for any two
  whitenings of the same raw vectors, and the reduced `m × m` generators are
  unitarily conjugate, hence carry the same Ritz values.
* Matrix layer: `gramMatrix`, `gramMatrix_conjTranspose`, `IsWhiteningMatrix`
  (`Mᴴ G M = 1`, what the code computes from the Hermitian eigendecomposition of
  `G`) and `isWhitening_of_matrix`.
* `norm_defect_synthesis_le` — the quantified rank truncation: if every raw
  vector lies within `δ` of the retained subspace, a reduced state loses at most
  `δ √m ‖c‖`; and `sirk_end_to_end_truncated_gram`, the end-to-end bound with
  that term in place of the abstract defect of `ChapterSirkTruncation`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).

**Boundary.** The existence statement is about *some* whitening; the specific
inverse-square-root factor the code uses is one such, and `ChapterSirkWhitening`
shows the reduction does not depend on the choice.  The near-degenerate case is
covered only through the geometric parameter `δ` (the distance of the raw vectors
to the retained subspace): no relation between `δ` and the discarded Gram
eigenvalues, and no floating-point analysis, is claimed here.
-/

noncomputable section

namespace BookProof.ChapterSirkGramWhitening

open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
/-! ## 5. The consequences for the reduction -/

/-- **The reconstructed SIRK operator is the same for any two whitenings** of the
same raw Krylov vectors. -/
theorem sirkApprox_gram_whitening_eq {m : ℕ} (w : Fin m → E) (X : E →L[ℂ] E)
    {T₁ T₂ : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)}
    (hT₁ : IsWhitening w T₁) (hT₂ : IsWhitening w T₂)
    (hs₁ : Function.Surjective T₁) (hs₂ : Function.Surjective T₂) :
    (whitened w T₁).comp ((compress (whitened w T₁) X).comp
        (ContinuousLinearMap.adjoint (whitened w T₁)))
      = (whitened w T₂).comp ((compress (whitened w T₂) X).comp
        (ContinuousLinearMap.adjoint (whitened w T₂))) := by
  have hr₁ := range_whitened w hs₁
  have hr₂ := range_whitened w hs₂
  refine sirkApprox_eq_of_range_eq _ _ X (whitened_adjoint_comp_self w hT₁)
    (whitened_adjoint_comp_self w hT₂) ?_ ?_
  · intro y
    have hmem : whitened w T₁ y ∈ LinearMap.range (whitened w T₂ :
        EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E) := by
      rw [hr₂, ← hr₁]; exact ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, hz.symm⟩
  · intro z
    have hmem : whitened w T₂ z ∈ LinearMap.range (whitened w T₁ :
        EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E) := by
      rw [hr₁, ← hr₂]; exact ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := hmem
    exact ⟨y, hy.symm⟩

/-- The reduced `m × m` generators produced by two whitenings are unitarily
conjugate, hence carry the same Ritz values. -/
theorem compress_gram_whitening_conj {m : ℕ} (w : Fin m → E) (X : E →L[ℂ] E)
    {T₁ T₂ : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)}
    (hT₂ : IsWhitening w T₂) (hs₁ : Function.Surjective T₁) (hs₂ : Function.Surjective T₂) :
    compress (whitened w T₁) X
      = (whiteningEquiv (whitened w T₂) (whitened w T₁)).comp
        ((compress (whitened w T₂) X).comp
          (whiteningEquiv (whitened w T₁) (whitened w T₂))) := by
  have hr₁ := range_whitened w hs₁
  have hr₂ := range_whitened w hs₂
  refine compress_conj_whitening _ _ X (whitened_adjoint_comp_self w hT₂) ?_
  intro y
  have hmem : whitened w T₁ y ∈ LinearMap.range (whitened w T₂ :
      EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E) := by
    rw [hr₂, ← hr₁]; exact ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, hz.symm⟩

/-! ## 6. The matrix layer -/

/-- The **Gram matrix** `G_{ij} = ⟪w i, w j⟫` the code actually forms. -/
def gramMatrix {m : ℕ} (w : Fin m → E) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ⟪w i, w j⟫_ℂ

omit [CompleteSpace E] in
/-- The Gram matrix is Hermitian — the input the numerical eigendecomposition
assumes. -/
theorem gramMatrix_conjTranspose {m : ℕ} (w : Fin m → E) :
    (gramMatrix w)ᴴ = gramMatrix w := by
  ext i j
  simp [gramMatrix, Matrix.conjTranspose_apply]

/-- The Gram operator is the operator of the Gram matrix. -/
theorem gramOp_eq_toEuclideanCLM {m : ℕ} (w : Fin m → E) :
    gramOp w = Matrix.toEuclideanCLM (𝕜 := ℂ) (gramMatrix w) := by
  ext c i
  simpa [gramMatrix, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]
    using gramOp_apply w c i

/-- The matrix form of the whitening condition: `Mᴴ G M = 1`, exactly what the
code computes from the (rank-truncated) Hermitian eigendecomposition of `G`. -/
def IsWhiteningMatrix {m : ℕ} (w : Fin m → E) (M : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  Mᴴ * gramMatrix w * M = 1

/-- **A whitening matrix gives a whitening.** -/
theorem isWhitening_of_matrix {m : ℕ} (w : Fin m → E) {M : Matrix (Fin m) (Fin m) ℂ}
    (hM : IsWhiteningMatrix w M) :
    IsWhitening w (Matrix.toEuclideanCLM (𝕜 := ℂ) M) := by
  have hstar : ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℂ) M)
      = Matrix.toEuclideanCLM (𝕜 := ℂ) Mᴴ := by
    have : star (Matrix.toEuclideanCLM (𝕜 := ℂ) M)
        = Matrix.toEuclideanCLM (𝕜 := ℂ) (star M) := (map_star _ _).symm
    simpa [ContinuousLinearMap.star_eq_adjoint, Matrix.star_eq_conjTranspose] using this
  rw [IsWhitening, gramOp_eq_toEuclideanCLM, hstar]
  have hmul : ∀ P Q : Matrix (Fin m) (Fin m) ℂ,
      (Matrix.toEuclideanCLM (𝕜 := ℂ) P).comp (Matrix.toEuclideanCLM (𝕜 := ℂ) Q)
        = Matrix.toEuclideanCLM (𝕜 := ℂ) (P * Q) := by
    intro P Q
    exact (map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m)) P Q).symm
  rw [hmul, hmul, ← mul_assoc, hM]
  have hone : Matrix.toEuclideanCLM (𝕜 := ℂ) (1 : Matrix (Fin m) (Fin m) ℂ)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m)) := by
    exact map_one (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m))
  exact hone

/-! ## 7. Non-vacuity -/

omit [CompleteSpace E] in
/-- For an already orthonormal family the Gram matrix is the identity, so the
trivial matrix is a whitening: the construction is not vacuous. -/
theorem isWhiteningMatrix_one_of_orthonormal {m : ℕ} {w : Fin m → E}
    (hw : Orthonormal ℂ w) : IsWhiteningMatrix w 1 := by
  have hG : gramMatrix w = 1 := by
    ext i j
    rw [gramMatrix, orthonormal_iff_ite.mp hw i j]
    simp [Matrix.one_apply]
  simp [IsWhiteningMatrix, hG]

/-- …and the resulting embedding is the synthesis map itself. -/
theorem isWhitening_one_of_orthonormal {m : ℕ} {w : Fin m → E} (hw : Orthonormal ℂ w) :
    IsWhitening w (Matrix.toEuclideanCLM (𝕜 := ℂ) (1 : Matrix (Fin m) (Fin m) ℂ)) :=
  isWhitening_of_matrix w (isWhiteningMatrix_one_of_orthonormal hw)

/-! ## 8. Quantified rank truncation: how much a reduced state loses -/

omit [CompleteSpace E] in
/-- Cauchy–Schwarz in coordinates: `∑ |c i| ≤ √m ‖c‖`. -/
theorem sum_norm_coord_le {m : ℕ} (c : EuclideanSpace ℂ (Fin m)) :
    ∑ i, ‖c i‖ ≤ Real.sqrt m * ‖c‖ := by
  have h1 : (∑ i, ‖c i‖) ^ 2 ≤ (m : ℝ) * ∑ i, ‖c i‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m)))
      (f := fun i => ‖c i‖)
  have h2 : ‖c‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  have h3 : (0 : ℝ) ≤ ∑ i, ‖c i‖ := by positivity
  have h4 : (∑ i, ‖c i‖) ^ 2 ≤ (Real.sqrt m * ‖c‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ)), h2]
    exact h1
  have h5 : (0 : ℝ) ≤ Real.sqrt m * ‖c‖ := by positivity
  nlinarith [h4, h3, h5]

/-- **The truncation defect of a reduced state.**  If every raw Krylov vector is
within `δ` of the retained (rank-truncated) subspace `range V`, then the part of
any state assembled from the raw vectors that the truncation discards is at most
`δ √m ‖c‖`.  This is the quantitative companion of `range_whitened`: with `δ = 0`
nothing is lost, which is the exact rank truncation. -/
theorem norm_defect_synthesis_le {m d : ℕ} (w : Fin m → E)
    (V : EuclideanSpace ℂ (Fin d) →L[ℂ] E) {delta : ℝ}
    (hdelta : ∀ i, ‖w i - V (ContinuousLinearMap.adjoint V (w i))‖ ≤ delta)
    (c : EuclideanSpace ℂ (Fin m)) :
    ‖synthesis w c - V (ContinuousLinearMap.adjoint V (synthesis w c))‖
      ≤ delta * (Real.sqrt m * ‖c‖) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  have hd0 : 0 ≤ delta := le_trans (norm_nonneg _) (hdelta ⟨0, hm⟩)
  have hsplit : synthesis w c - V (ContinuousLinearMap.adjoint V (synthesis w c))
      = ∑ i, c i • (w i - V (ContinuousLinearMap.adjoint V (w i))) := by
    simp only [synthesis_apply, smul_sub, Finset.sum_sub_distrib, map_sum, map_smul]
  rw [hsplit]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ i : Fin m, ‖c i • (w i - V (ContinuousLinearMap.adjoint V (w i)))‖
      ≤ ‖c i‖ * delta := by
    intro i
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hdelta i) (norm_nonneg _)
  calc ∑ i, ‖c i • (w i - V (ContinuousLinearMap.adjoint V (w i)))‖
      ≤ ∑ i, ‖c i‖ * delta := Finset.sum_le_sum fun i _ => hterm i
    _ = delta * ∑ i, ‖c i‖ := by rw [← Finset.sum_mul]; ring
    _ ≤ delta * (Real.sqrt m * ‖c‖) :=
        mul_le_mul_of_nonneg_left (sum_norm_coord_le c) hd0

/-- **The end-to-end SIRK bound for a state built from the raw Krylov vectors,
under rank truncation.**  `ChapterSirkTruncation.sirk_end_to_end_truncated` pays
one additive term for the discarded part of the seed; when the seed is assembled
from raw vectors that all sit within `δ` of the retained subspace, that term is
at most `‖r(X)‖ δ √m ‖c‖`, and it vanishes for an exact (lossless) truncation. -/
theorem sirk_end_to_end_truncated_gram {m d : ℕ} (w : Fin m → E)
    (V : EuclideanSpace ℂ (Fin d) →L[ℂ] E)
    (rX : E →L[ℂ] E) (rB : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (flow psiX : E →L[ℂ] E) (psiB : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (C Dmin hrate : ℝ) (k : ℕ) {delta : ℝ}
    (hViso : ∀ x : EuclideanSpace ℂ (Fin d), ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖ContinuousLinearMap.adjoint V v‖ ≤ ‖v‖)
    (hflow : flow = psiX)
    (hcx1 : ‖psiX - rX‖ ≤ C * (Real.exp (-(hrate * k)) * Dmin))
    (hcx2 : ‖psiB - rB‖ ≤ C * (Real.exp (-(hrate * k)) * Dmin))
    (hdelta : ∀ i, ‖w i - V (ContinuousLinearMap.adjoint V (w i))‖ ≤ delta)
    (c : EuclideanSpace ℂ (Fin m))
    (hexact : rX (V (ContinuousLinearMap.adjoint V (synthesis w c)))
      = V (rB (ContinuousLinearMap.adjoint V
        (V (ContinuousLinearMap.adjoint V (synthesis w c))))))
    (hproj : ContinuousLinearMap.adjoint V (V (ContinuousLinearMap.adjoint V (synthesis w c)))
      = ContinuousLinearMap.adjoint V (synthesis w c)) :
    ‖flow (synthesis w c)
        - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB (synthesis w c)‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin hrate ‖synthesis w c‖ k
        + ‖rX‖ * (delta * (Real.sqrt m * ‖c‖)) := by
  have hbase := BookProof.ChapterSirkTruncation.sirk_end_to_end_truncated V rX rB flow psiX
    psiB C Dmin hrate k hViso hVadj hflow hcx1 hcx2 (synthesis w c) hexact hproj
  refine hbase.trans ?_
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left (norm_defect_synthesis_le w V hdelta c) (norm_nonneg rX))
    (BookProof.ChapterH6.sirkBound C Dmin hrate ‖synthesis w c‖ k)

end BookProof.ChapterSirkGramWhitening
