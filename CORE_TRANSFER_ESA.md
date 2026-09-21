# The core transfer route: `dΓ(A)` for an essentially self-adjoint one-particle operator

**Date:** 2026-09-20.  **Modules:** `BookProof/ChapterGraphCoreTransfer.lean`,
`BookProof/ChapterTensorGraphCore.lean`, `BookProof/ChapterSecondQuantizationCoreEsa.lean`,
`BookProof/ChapterScalarDGammaEsa.lean`, audit `Work/GraphCoreTransferAudit.lean`.  All `sorry`-free and `axiom`-free (the audit
reports only `propext`, `Classical.choice`, `Quot.sound`).

## The obstacle this removes

If a one-particle operator `A` is only *essentially* self-adjoint on a domain `D`, then `D`
need not be invariant under the unitary group of the closure, and `(A ± i)⁻¹` is not defined
on all of `H` from `D` alone.  Nelson's invariant-domain argument therefore cannot be run on
`D` directly.  The route implemented here avoids the issue altogether: one works with the
domain `D₂` of the closure — where the self-adjoint theory is available — and comes back to
`D` by **graph-norm density**.

## What is proved

1. **Core transfer** (`BookProof.GraphCore`).
   `IsGraphCore D₁ T` says that every vector of the domain of `T` is approximated by vectors
   of `D₁` simultaneously in `‖·‖` and in `‖T ·‖`.  Then
   * `deficiencyTrivialAt_of_graphCore` — a vector annihilating the range of `T|_{D₁} - z̄`
     annihilates the range of `T - z̄`, because the defect
     `⟪T v, w⟫ - z⟪v, w⟫` is bounded by `(1 + |z|)‖w‖` times the graph distance from `v` to
     `D₁`;
   * `essentiallySelfAdjointOn_of_graphCore` — essential self-adjointness on the domain
     descends to every core.  No invariant domain, no resolvent on `D₁`, no spectral theorem.
   * `pushOp`, `isGraphCore_pushOp`, `symmetricOn_pushOp` transport the operator and the core
     property along a linear isometry, which is how a core of an incomplete space becomes a
     core inside its completion.

2. **Multilinear core estimate** (`BookProof.TensorCore`).
   `IPSpace.pow` is the `n`-fold algebraic tensor power (Mathlib's inner product on a binary
   tensor product, iterated), `inclPow` the isometric inclusion `D₂^{⊗n} → H^{⊗n}`, `derPow`
   the sector derivation `dΓ(A)⁽ⁿ⁾` defined by the Leibniz recursion
   `dΓ⁽ⁿ⁺¹⁾ = A ⊗ 1 + 1 ⊗ dΓ⁽ⁿ⁾`, and `corePow` the tensor power `D^{⊗n}` of the one-particle
   core.  Then:
   * `graphPow_tmul_mem_closure` — the telescoping step on an elementary tensor `a ⊗ b`:
     replacing `a` by a core vector `a'` costs `‖a - a'‖·‖b‖ + ‖A a - A a'‖·‖b‖` and replacing
     `b` costs `(‖a‖+δ)·(graph distance of b)`, both controlled by one parameter `δ`;
   * `graphPow_range_le_closure` / `exists_core_approx` — hence `D^{⊗n}` is graph-norm dense
     in `D₂^{⊗n}`, by span induction from the elementary tensors;
   * `isGraphCore_sectorCore` — the same statement for the operator `sectorOp` realized inside
     `H^{⊗n}`, in the form the transfer principle consumes;
   * `derPow_symm`, `symmetricOn_sectorOp` — the sector derivation is symmetric whenever `A`
     is.

3. **Assembly** (`BookProof.SecondQuantizationCore`).
   The Fock space is the ℓ²-direct sum of the *completed* sectors
   `𝓕ₙ = completion of H^{⊗n}`; the finite-particle domain over the core is `dsCore` of the
   sector cores, and `dGammaCoreOp` is `dΓ(A)` on it.  The gluing instrument is the existing
   `BookProof.DirectSumEsa.dsOp_essentiallySelfAdjointOn`.  Results:
   * `essentiallySelfAdjointOn_fockSectorCore` — sectorwise core transfer;
   * `dGamma_essentiallySelfAdjointOn_fockCore` — **`dΓ(A)` is essentially self-adjoint on the
     finite-particle domain built from the core `D` alone**;
   * `symmetricOn_dGammaCoreOp` — and it is symmetric there;
   * `exists_ne_zero_mem_dGammaCoreDomain` — non-vacuity: a nonzero vector of `D` gives a
     nonzero state of that domain.

4. **An unconditional instance** (`BookProof.ScalarDGamma`).
   For the scalar one-particle operator `A = c • id` (`c : ℝ`) on `D₂ = ⊤`, the sector
   hypothesis below is *proved*, not assumed:
   * `derPow_scalar` — the sector derivation of a scalar operator is the scalar `n · c`;
   * `sectorDom_top`, `dense_fockSectorDom`, `norm_fockSectorOp_scalar_le` — its domain is
     dense in the completed sector and it is bounded there;
   * `essentiallySelfAdjointOn_of_bounded_dense` (in `BookProof.GraphCore`) — a densely
     defined bounded symmetric operator is essentially self-adjoint;
   * `dGamma_scalar_essentiallySelfAdjointOn_fockCore` — hence, with no hypothesis carried,
     `dΓ(c • id)` is essentially self-adjoint on the finite-particle domain built from *any*
     dense subspace `D ⊆ H`.

## The hypothesis that is carried, not proved

`dGamma_essentiallySelfAdjointOn_fockCore` assumes, sector by sector, essential
self-adjointness of `dΓ(A)⁽ⁿ⁾` on the tensor power `D₂^{⊗n}` of the domain of the closure.
That is the statement for a *self-adjoint* one-particle operator (Nelson's analytic-vector or
invariant-domain argument); it is an input here, stated explicitly as a hypothesis, and is
**not** proved in these modules.  Everything that the essentially-self-adjoint hypothesis
actually obstructs — the passage from `D₂` to the small core `D`, sector by sector and then on
the whole Fock space — is proved.  For the scalar one-particle operators of item 4 the
hypothesis is discharged outright, so that statement is unconditional.

## Scope

The tensor powers used are the full powers `H^{⊗n}`, not the symmetric (bosonic) or
antisymmetric (fermionic) subspaces; the statements are about the derivation on those powers.
No claim about symmetrized Fock sectors is made here.

## Session note

All four modules and the audit build cleanly in this checkout:

```
lake build BookProof.ChapterGraphCoreTransfer BookProof.ChapterTensorGraphCore \
           BookProof.ChapterSecondQuantizationCoreEsa BookProof.ChapterScalarDGammaEsa \
           Work.GraphCoreTransferAudit BookProof
```

completes with no errors, no `sorry` in the new files, and the audit reports only the three
standard axioms for every new result.
