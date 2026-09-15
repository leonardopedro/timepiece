import BookProof.ChapterSirkGramWhitening.Part1
import BookProof.ChapterSirkGramWhitening.Part2

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
