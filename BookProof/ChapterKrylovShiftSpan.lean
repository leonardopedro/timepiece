import BookProof.ChapterKrylovShiftSpan.Part1
import BookProof.ChapterKrylovShiftSpan.Part2

/-!
# Chapter KrylovShiftSpan — the multi-shift Krylov spaces

The SIRK/Hashimoto solver builds its subspace either from the **shifted products**
`v, (H − z₀)v, (H − z₁)(H − z₀)v, …` or from the **resolvent (rational Krylov)**
sequence `v, X₀v, X₁X₀v, …` with `Xᵢ = (H − zᵢ)⁻¹`, for a sequence of (possibly
distinct, possibly complex) shifts, while the theory is written for the plain Krylov
space `span{v, Hv, …, Hᵏv}`.

This chapter proves that all three descriptions agree, in the algebraic generality in
which they are true: no topology, no self-adjointness, an arbitrary module over an
arbitrary commutative ring, and an arbitrary shift sequence.

### Relation to the rest of the development

The *forward-sequence* half of the statement is already available analytically in
`BookProof/ChapterSirkMultiShift.lean` (`krylov_multiShift_eq_standard`,
`krylov_multiShift_span_eq_of_shifts`), over a field and for vectors of the sequence;
what is re-proved here is its purely algebraic operator-product form
(`forwardProd`, over a commutative ring), because the resolvent statement below needs
the products themselves, not just the vectors they produce.  The *resolvent* half is
new: `BookProof/ChapterHashimotoComplexShifts.lean` describes the rational Krylov space
as rational functions of one fixed resolvent (`sirkDen_rkVec`), whereas
`resolventSpan_eq_map_krylovSpan` below identifies it with the image of the ordinary
Krylov space of `H` itself under the product of the resolvents.

## Deliverables

* `shiftOp T z = T − z`, `forwardProd T z j = (T − z_{j−1}) ⋯ (T − z₀)` and
  `krylovSpan` / `forwardSpan` — the plain and the shifted Krylov subspaces.
* **`forwardSpan_eq_krylovSpan`** — the two spans coincide at every truncation level `k`:
  the shifted forward sequence spans exactly the Krylov space.  Hence
  `forwardSpan_eq_forwardSpan` : *the span does not depend on the shifts at all*, which is
  what makes the numerics' freedom to choose (and to reorder, or to repeat) the shifts
  harmless.
* `resProd X j = X_{j−1} ⋯ X₀` and `resolventSpan`; `commute_resolvent_shiftOp` and
  `resProd_mul_tailProd` — the resolvent of one shift commutes with every shifted
  operator, and the resolvents telescope against the shifted products.
* **`resolventSpan_eq_map_krylovSpan`** — the rational (resolvent) Krylov space is the
  image of the ordinary Krylov space under the product of all `k` resolvents:
  `span{v, X₀v, X₁X₀v, …, X_{k−1}⋯X₀v} = (X_{k−1}⋯X₀) '' span{v, Tv, …, Tᵏv}`.
  So the three subspaces the plan lists are the same subspace up to the invertible factor
  `X_{k−1}⋯X₀`.  (No permutation statement is claimed; what is proved is the description
  above, which is the form the compression arguments use.)  The bridge is
  `tailSpan_eq_krylovSpan`: the tail products `(T − z_{k−1}) ⋯ (T − z_j)`, `j ≤ k`, are
  the forward products of the *reversed* shift sequence, hence span the Krylov space too.
* `resProd_mul_forwardProd` / `forwardProd_mul_resProd` (the two products are mutually
  inverse) and hence `krylovSpan_eq_map_resolventSpan`, the inverse form of the identity
  above.
* `resVec` and `resolventSpan_eq_span_resVec` — the resolvent span written with the
  vectors the solver actually computes, `v, X₀v, X₁X₀v, …`, one resolvent solve at a time.
* **`resolventSpan_of_perm`** — *the rational Krylov space does not depend on the order in
  which the shifts are used*: for a permutation of `ℕ` fixing everything from `k` on,
  the reordered schedule reaches the same subspace (`resProd_of_perm`: the product of the
  resolvents is order-independent, since they commute).  The intermediate flag does
  change; the space at level `k` does not.

Everything is `sorry`-free and `axiom`-free.
-/
