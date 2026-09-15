import BookProof.ChapterTensorCompleteness.Part1
import BookProof.ChapterTensorCompleteness.Part2

/-!
# Pure tensors are total in `L²(μ ⊗ ν)`

`ChapterSolovayHilbertTensor` builds the elementary tensors `f ⊗ g` inside
`L²(μ ⊗ ν)` and proves the defining identity `⟪f₁⊗g₁, f₂⊗g₂⟫ = ⟪f₁,f₂⟫·⟪g₁,g₂⟫`.
What it explicitly did **not** claim is the *completeness* half — that these
elementary tensors exhaust the space.  This module proves it for finite
measures:

  `tensorSpan_eq_top` : the closed linear span of `{ f ⊗ g }` is all of
  `L²(μ ⊗ ν)`,

equivalently `pureTensors_dense` (the span is dense) and
`exists_tensor_approx` (every `L²` function of two variables is an `L²`-limit of
finite sums of products of one-variable functions — the separation of variables
statement).  Together with `inner_tensorLp` this says `L²(μ ⊗ ν)` *is* the
Hilbert tensor product of `L²(μ)` and `L²(ν)`, without a Hilbert tensor product
having to be available in the library.

The proof is the classical π–λ argument:

* `indicatorConstLp_prod` — the indicator of a measurable rectangle `s ×ˢ t` is
  the pure tensor `1_s ⊗ 1_t`;
* `indicator_mem_tensorSpan` — the family of measurable `E ⊆ α × β` whose
  indicator lies in the closed span contains the rectangles and is closed under
  complements and countable disjoint unions, hence is everything
  (`MeasurableSpace.induction_on_inter` against `generateFrom_prod`);
* `tensorSpan_eq_top` — indicators generate `L²` (`Lp.induction`), and the span
  is closed.

A final section draws the practical corollary.  `tensorOf u v` is the pure tensor
of two `L²` *elements*; `inner_tensorOf` and `norm_tensorOf` are its inner-product
and norm identities, `tensorOf_add_left`/`tensorOf_smul_left` (and the right-hand
versions) its bilinearity, `tensorRight`/`tensorLeft` the associated continuous
linear maps.  `orthonormal_tensorOf` says the products of two orthonormal families
are orthonormal, and `tensorFamily_span_eq_top` that the products of two *total*
families are total: the products of two orthonormal bases form an orthonormal
basis of `L²(μ ⊗ ν)`.  `tensorHilbertBasis` packages the two into the `HilbertBasis`
object itself, with `tensorHilbertBasis_repr_apply` (its coefficients are the
two-variable Fourier coefficients), `hasSum_tensorHilbertBasis` (the two-variable
expansion) and `hasSum_sq_norm_inner_tensorHilbertBasis` (Parseval in product
form).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/
