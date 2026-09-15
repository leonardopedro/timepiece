import BookProof.ChapterH8.Part1
import BookProof.ChapterH8.Part2

/-!
# Chapter H8 — the SIRK approximation orders nest (plan `PLAN_LEAN_SPECIALIST_SIRK_NESTED.md`)

The Hashimoto SIRK approximations form a *nested tower of orders*: the order-`n+1`
approximation refines the order-`n` one.  This file proves the four ingredients of
that statement for the generic Krylov–Hashimoto machinery of `ChapterH4`–`ChapterH6`
(it is not Navier–Stokes specific — it constrains any SIRK evolution).

## Deliverables

* **(a) subspace nesting** — `sirk_krylov_tower`: `Kry n ≤ Kry (n+1)`, the tower
  form of `ChapterH5.krylovSpan_mono`;
* **(b) block compatibility (new)** — `sirk_compression_block` /
  `sirk_compression_submatrix`: for nested orthonormal bases
  (`Vₙ eᵢ = Vₙ₊₁ e_{castSucc i}`) the order-`n` reduced generator
  (`ChapterH6.reduceGenerator`) is the leading `n × n` block of the order-`n+1`
  one; between any two orders `m ≤ n` this is `sirk_compression_block_le` /
  `sirk_compression_submatrix_le`.  Its operator form is `sirk_compression_block_op`,
  `compress Vₙ X = J∗ (compress Vₙ₊₁ X) J` for the coordinate inclusion `J`
  with `Vₙ = Vₙ₊₁ ∘ J`;
* **(c) projection refinement (new, headline)** — `sirk_band_refinement`: on the
  order-`n` data (`v ∈ Kry n`, i.e. `Vₙ Vₙ∗ v = v`) the order-`n+1` approximant
  *equals* the order-`n` approximant, and `sirk_band_refinement_proj` states this
  as "project the finer approximant back into `Kry n`".  On the *whole* space the
  statement `sirk_approx_projection` needs `Kry n` to reduce `X` (invariant under
  both `X` and `X∗`); the intertwining engine is
  `compress_comp_intertwine` / `compress_pow_comp_intertwine`;
* **(c′) polynomial and rational refinement (new)** — the same refinement for the
  functions the SIRK method actually evaluates: `sirk_band_refinement_poly` for
  an arbitrary polynomial `p` of the reduced generator,
  `sirk_band_refinement_rational` for a rational function `p/q` (an invertible
  denominator and its invertible compression), and `sirk_approx_projection_poly`
  for the whole-space projection form, and `sirk_approx_projection_rational` for
  the whole-space form of the rational case (the subspace must reduce both the
  numerator generator and the denominator).  The transfer engines are
  `compress_aeval_comp`, `compress_aeval_transfer`, `compress_inv_transfer_apply`,
  `compress_rational_transfer`, the transposed intertwinings
  `compress_adjoint_intertwine` / `compress_adjoint_intertwine_poly` and the
  inverse-intertwining lemma `inv_comp_intertwine`;
* **(c″) the hypotheses are realized** — the refinement theorems here are stated
  for an abstract factorization `Vₘ = Vₙ ∘ J`; the companion module
  `BookProof/ChapterH8Bases.lean` shows the hypotheses are met by any nested pair
  of orthonormal families, and by the orthonormal Krylov bases themselves
  (`sirk_band_refinement_of_orthonormal`, `sirk_band_refinement_krylov`);
* **(d) band containment** — `sirk_band_contained`: the error bands nest,
  `[0, sirkBound (n+1)] ⊆ [0, sirkBound n]` (from
  `ChapterH6.sirk_error_bound_antitone`), and `sirk_bands_tendsto_zero` records
  that the nested family collapses to `{0}`
  (`ChapterH6.sirk_error_decay_exponential`);
* **the tower** — `sirk_nested_orders` assembles (a) and (d) for every `n`, and
  `sirk_nested_orders_le` / `sirk_band_contained_le` do so between any two orders
  `m ≤ n`.

## Correspondence

`ChapterH5.lean` supplies the Krylov span and its monotonicity, `ChapterH6.lean`
the reduced generator and the antitone/decaying bound, `ChapterH4.lean` the
compression `compress = V∗ X V` and its transfer identities
(`compress_pow`, `compress_transfer`, `compress_inv_transfer`).  The prose
counterpart is the nested-orders paragraph of `Book/FreeField.lean`
§"Dimensional Reduction".

## The exact boundary

Everything here is finite-dimensional linear algebra over the decidable skeleton:
no Crouzeix inequality, no infinite spectrum, no `EXTERNAL` hypothesis.  What is
**not** claimed is the numerical *width* of the bands — that the true error lies
inside `sirkBound n` is conditional on Crouzeix's inequality, which enters
`ChapterH4.sirk_error_bound_decay` as a *named hypothesis*, never an axiom.  The
nesting (a)–(d) holds whether or not Crouzeix is ever proved.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/
