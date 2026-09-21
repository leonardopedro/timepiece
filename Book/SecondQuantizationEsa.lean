import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Second Quantization of an Essentially Self-Adjoint One-Particle Operator" =>
%%%
tag := "second-quantization-esa"
%%%

# Why This Chapter Exists: the Hamiltonian Is `dΓ(h)`

:::paragraph
Throughout the programme the final Hamiltonian of record is the outer
**second quantization** of an inner **one-particle** Hamiltonian,
$`H = \\sum_{i,j} h_{ij}\\, C^\\dagger(e_i)\\, A(e_j) = d\\Gamma(h)`, with creation on
the left and annihilation on the right — the same shape for QYM, QED, QG and
Navier–Stokes. A quartic nonlinearity, an exponential wall or a singular potential
enters only the one-particle matrix elements $`h_{ij}`; at the outer level the
operator is quadratic in the ladders. So the whole spectral question for the outer
Hamiltonian reduces to a question about the one-particle operator `h`, and it is
this reduction that this chapter makes rigorous.

This is not a convention the programme invented: the manuscript states it and the
recursive construction that justifies it. Its Navier–Stokes Hamiltonian is written
exactly in this enclosure form,
$`H = \int d^3\vec x\, a^\dagger(\vec x)\, H(\vec x)\, a(\vec x)` with
$`H(\vec x) = \pi^i(u_j u_{i,j} - \nu u_{i,jj}) + (h.c.)` — one-particle operator
inside, creation on the left and annihilation on the right — and the Fock space is
introduced recursively: *“Since the second-quantization procedure can be applied
recursively … in case the Hamiltonian acting in the Fock-space is not quadratic in
the creation/annihilation operators, then we can consider instead a **new Fock-space
where the base Hilbert space is the original Fock-space**. The new Hamiltonian is
quadratic in the creation/annihilation operators.”*  That sentence is the definition
of the **nested** (outer) Fock space this chapter works on: the inner one-particle
space is itself a Fock space, and the outer Hamiltonian is its second quantization,
quadratic in the outer ladders whatever the inner operator is.

Two consequences of that definition are used below and are worth stating here.
First, the inner space is where the fields and their **spatial derivatives** live —
in the manuscript's Navier–Stokes count, the derivative coordinates
$`u_{k,j} = \partial_j u_k` are among the $`\mathbb{R}^{15}` field degrees of freedom,
and the QG vielbein carries the same kind of derivative coordinates. Second, a
product of fields with a spatial derivative is **not** a differential operator once
the derivative has been eliminated: in momentum space it becomes a **convolution**,
$`\mathcal F[u_j\,\partial_j u_i](Q) = \int 2\pi i\,\langle q,m\rangle\,
\hat u_i(q)\,\hat u_j(Q-q)\,dq` (`BookProof.NsAdvectionConvolution.fourier_advection_convolution`,
`fourier_advection_sum`), with the same device for the QG vielbein derivative modes
(`ChapterQgFourierElimination`, `ChapterQgFullEliminated`).  That is what replaces the
constraining of the derivative variables: they are eliminated by the spatial Fourier
substitution and reappear as convolutions, not fixed by a gauge symmetry or a BRST
charge.

The specific question is the one the Faris–Lavine route keeps returning to:
**when is `dΓ(h)` essentially self-adjoint, and on what domain?** The answer proved
here is: whenever `h` is essentially self-adjoint on its own domain `D`, `dΓ(h)` is
essentially self-adjoint on the finite-particle domain built from `D` **alone** —
`D` is only a graph-norm core, not an invariant domain, and no resolvent of `h` on
`D` is ever used. The instrument that makes this possible is the *core transfer
principle*; the rest is multilinear bookkeeping.
:::

# The Core Transfer Principle

:::paragraph
Everything in the project renders essential self-adjointness of a symmetric
operator `T : D →ₗ[ℂ] F` by the vanishing of the deficiency spaces of its adjoint.
The criteria available elsewhere (Faris–Lavine, Nelson-type commutator bounds)
verify this on the domain on which the operator is given. What was missing was the
*domain-changing* instrument, and `IsGraphCore D₁ T` is it: `D₁` is a subspace of
the domain of `T` that is dense there for the **graph norm** $`\\|x\\| + \\|T x\\|`.
Then a deficiency vector is transferred from the domain to any core of it, because
the defect $`\\langle T v, w\\rangle - z\\langle v, w\\rangle` is bounded by
$`(1 + |z|)\\|w\\|` times the graph distance from `v` to `D₁`. Cores compose, a
domain is a core for its own operator, and the notion transports along a linear
isometry — which is how a core inside an incomplete space becomes a core inside its
completion.
:::

```
#check @BookProof.GraphCore.IsGraphCore
#check @BookProof.GraphCore.IsGraphCore.refl
#check @BookProof.GraphCore.IsGraphCore.trans
#check @BookProof.GraphCore.deficiencyTrivialAt_of_graphCore
#check @BookProof.GraphCore.essentiallySelfAdjointOn_of_graphCore
#check @BookProof.GraphCore.restrictOp
#check @BookProof.GraphCore.symmetricOn_restrictOp
#check @BookProof.GraphCore.pushOp
#check @BookProof.GraphCore.isGraphCore_pushOp
#check @BookProof.GraphCore.symmetricOn_pushOp
#check @BookProof.GraphCore.essentiallySelfAdjointOn_of_bounded_dense
```

:::paragraph
The last item is a useful unconditional criterion in its own right: a symmetric
operator that is *bounded* on a dense domain has trivial deficiency spaces at
$`\\pm i`, hence is essentially self-adjoint there. It is what discharges the
sectorwise input in the bounded cases below.
:::

# The Multilinear Core Estimate

:::paragraph
The core transfer is a one-variable statement; the sectors of a Fock space are
tensor powers, so it must be lifted to `n` variables. `IPSpace.pow` is the `n`-fold
algebraic tensor power of an inner product space, `inclPow` the isometric inclusion
$`D_2^{\\otimes n} \\to H^{\\otimes n}`, `derPow` the sector derivation
$`d\\Gamma(A)^{(n)} = \\sum_j 1 \\otimes \\cdots \\otimes A \\otimes \\cdots \\otimes 1`
defined by the Leibniz recursion, and `corePow` the tensor power $`D^{\\otimes n}`
of a one-particle core. The telescoping estimate `graphPow_tmul_mem_closure` on an
elementary tensor `a ⊗ b` — replacing `a` costs $`\\|a - a'\\|\\|b\\| + \\|Aa - Aa'\\|\\|b\\|`
and replacing `b` costs the graph distance of `b` — is the whole of the analysis;
span induction then gives `exists_core_approx` and `isGraphCore_sectorCore`: **if
`D` is a core for `A`, then `D^{⊗n}` is a core for the sector derivation**. Symmetry
transfers too.
:::

```
#check @BookProof.TensorCore.IPSpace.pow
#check @BookProof.TensorCore.derPow
#check @BookProof.TensorCore.corePow
#check @BookProof.TensorCore.graphPow_tmul_mem_closure
#check @BookProof.TensorCore.exists_core_approx
#check @BookProof.TensorCore.isGraphCore_sectorCore
#check @BookProof.TensorCore.derPow_symm
#check @BookProof.TensorCore.symmetricOn_sectorOp
```

# The Assembly on the Nested Fock Space

:::paragraph
The outer space is the $`\\ell^2`-direct sum of the *completed* sectors
$`\\mathcal F_n =` completion of $`H^{\\otimes n}`, the finite-particle domain over
the core is the direct sum of the sector cores, and `dGammaCoreOp` is `dΓ(A)` on it.
Gluing is the existing `BookProof.DirectSumEsa.dsOp_essentiallySelfAdjointOn`, so the
escaped-to-the-completion question is already settled; the new content is the
descent to the unsigned core, sector by sector. The hypothesis that is *carried*,
not proved, in this general statement is sectorwise essential self-adjointness of
the sector derivation on the tensor powers of the domain of the closure — the
classical statement for a self-adjoint one-particle operator, which the next section
discharges.
:::

```
#check @BookProof.SecondQuantizationCore.fockSector
#check @BookProof.SecondQuantizationCore.fockSectorDom
#check @BookProof.SecondQuantizationCore.fockSectorCore
#check @BookProof.SecondQuantizationCore.dGammaCoreOp
#check @BookProof.SecondQuantizationCore.essentiallySelfAdjointOn_fockSectorCore
#check @BookProof.SecondQuantizationCore.dGamma_essentiallySelfAdjointOn_fockCore
#check @BookProof.SecondQuantizationCore.symmetricOn_dGammaCoreOp
#check @BookProof.SecondQuantizationCore.exists_ne_zero_mem_dGammaCoreDomain
```

# The Carried Input, Discharged

:::paragraph
The sectorwise input is not an axiom and not an obstruction — it is a statement
about the one-particle operator, and the chapters below prove it outright in a
sequence of increasingly general cases. The list is the useful summary of this
chapter:

* **bounded symmetric `h`** — the tensor operator bound (`exists_orthonormal_repr`
  writes any tensor as `∑ xᵢ ⊗ eᵢ` with orthonormal right legs,
  `norm_sum_tmul_orthonormal` is Pythagoras for such sums, and `norm_map_le` gives
  `‖(S ⊗ T)u‖ ≤ ‖S‖‖T‖‖u‖` for arbitrary bounded — in particular *indefinite* —
  factors) run through the Leibniz recursion gives `‖dΓ(A)⁽ⁿ⁾‖ ≤ n‖A‖`. The
  conclusion `dGamma_bounded_essentiallySelfAdjointOn_fockCore` carries *no*
  hypothesis beyond a dense `D`; `dGamma_neg_id_essentiallySelfAdjointOn_fockCore`
  (minus the number operator) shows that no positivity is being smuggled in.
* **scalar `h`** (`h = c·id`) — the sector derivation is the bounded scalar `n·c`
  on a dense domain, so the criterion applies and
  `dGamma_scalar_essentiallySelfAdjointOn_fockCore` is unconditional for *any*
  dense `D`.
* **unbounded `h` with pure point spectrum** — `essentiallySelfAdjointOn_of_dense_eigenvectors`
  (a total family of eigenvectors with real eigenvalues kills both deficiency
  spaces), `derPow_eigTensor` and `dense_eigSpan` lift it to every sector, giving
  `dGamma_diagonal_essentiallySelfAdjointOn_fockCore` with no completeness and no
  self-adjointness of a reference operator assumed; `diagOp` builds such operators
  and `not_bounded_diagOp` shows they are genuinely unbounded.
* **every self-adjoint `h`** — `deficiencyTrivialAt_of_orbits` is Nelson's
  invariant-domain criterion in orbit form, `OneParticleFlow` bundles the unitary
  group with invariant domain (built from Stone's theorem, nothing supplied from
  outside), `hasDerivAt_tpow` is the Leibniz rule for the tensor flow, and
  `dGamma_selfAdjoint_essentiallySelfAdjointOn_fockCore` concludes: for any
  self-adjoint `A` and any graph-norm core `D`, `dΓ(A)` is essentially self-adjoint
  on the finite-particle domain over `D`. `dGamma_position_essentiallySelfAdjointOn_fockCore`
  is the unbounded instance (multiplication by `k` on `ℓ²(ℤ)`).
* **`h` only essentially self-adjoint on `D`** — the final weakening, and the one
  the programme actually needs. `closureSelfAdjoint` packages the graph closure of
  such an `h` as a genuine self-adjoint operator, `isGraphCore_clDom` shows `D` is
  a core of it, the self-adjoint theorem is applied to the closure, and `esa_graph_le`
  with the tensor lemmas `exists_pow_of_mem_corePow`, `sectorCore_graph_le`,
  `fockSectorCore_graph_le` brings the statement back to `h` **on `D` itself**.
  `dGamma_essentiallySelfAdjointOn_of_esa` is the main theorem; no domain of a
  closure appears in its statement. That the hypothesis is strictly weaker than
  self-adjointness is shown by `essentiallySelfAdjointOn_restrict` /
  `not_isSelfAdjointOn_restrict`, and by the concrete witness `positionCore` on
  `ℓ²(ℤ)`: symmetric, essentially self-adjoint, and provably **not** self-adjoint
  on the finitely supported vectors, with `dGamma_positionCore_essentiallySelfAdjoint`
  applying the theorem to it.
:::

```
#check @BookProof.TensorOpBound.exists_orthonormal_repr
#check @BookProof.TensorOpBound.norm_sum_tmul_orthonormal
#check @BookProof.TensorOpBound.norm_map_le
#check @BookProof.BoundedDGamma.norm_derPow_le
#check @BookProof.BoundedDGamma.dGamma_bounded_essentiallySelfAdjointOn_fockCore
#check @BookProof.BoundedDGamma.dGamma_neg_id_essentiallySelfAdjointOn_fockCore
#check @BookProof.ScalarDGamma.dGamma_scalar_essentiallySelfAdjointOn_fockCore
#check @BookProof.DiagonalDGamma.essentiallySelfAdjointOn_of_dense_eigenvectors
#check @BookProof.DiagonalDGamma.dGamma_diagonal_essentiallySelfAdjointOn_fockCore
#check @BookProof.DiagonalDGamma.not_bounded_diagOp
#check @BookProof.FlowDGamma.dGamma_selfAdjoint_essentiallySelfAdjointOn_fockCore
#check @BookProof.FlowDGamma.dGamma_position_essentiallySelfAdjointOn_fockCore
#check @BookProof.EsaOneParticle.closureSelfAdjoint
#check @BookProof.EsaOneParticle.isGraphCore_clDom
#check @BookProof.EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa
#check @BookProof.EsaOneParticle.essentiallySelfAdjointOn_restrict
#check @BookProof.EsaOneParticle.not_isSelfAdjointOn_restrict
#check @BookProof.EsaOneParticle.positionCore_essentiallySelfAdjoint
#check @BookProof.EsaOneParticle.positionCore_not_isSelfAdjointOn
#check @BookProof.EsaOneParticle.dGamma_positionCore_essentiallySelfAdjoint
```

# The Packaged Form

:::paragraph
For use in the route chapters, `ESAPair` bundles the three pieces of data — a
symmetric one-particle operator on the domain of its closure, a graph-norm core
`D`, and the sectorwise input — and `ESAPair.dGamma_essentiallySelfAdjoint` is the
main theorem over the package. `ESAPair.norm_sub_smul_sq` records the only
quantitative ingredient, $`\\|Ax - d\\,i\\,x\\|^2 = \\|Ax\\|^2 + d^2\\|x\\|^2`, valid
with no spectral lower bound, so no quadratic-form domain and no Friedrichs
extension is required. `ESAPair.ofBounded` produces packages for all bounded
symmetric one-particle operators — with the sectorwise input proved, not assumed —
and `esaPairOfSelfAdjoint` does the same for self-adjoint ones.
:::

```
#check @BookProof.EsaPair.ESAPair.dGamma_essentiallySelfAdjoint
#check @BookProof.EsaPair.ESAPair.norm_sub_smul_sq
#check @BookProof.EsaPair.dGamma_essentiallySelfAdjoint_ofBounded
#check @BookProof.FlowDGamma.esaPairOfSelfAdjoint
```

# What This Discharges for the Programme

:::paragraph
The plan's §D6b obligation (ii) was: *the lifted Hamiltonian `dΓ(H₁)` must be
proved essentially self-adjoint on the **lifted core**, and ESA does not lift for
free*. The results of this chapter are exactly the instrument that discharges it:
once `H₁` is essentially self-adjoint on the one-particle core `C₀`, the core
transfer principle descends the sectorwise statement to `C₀^{⊗n}`, the multilinear
estimate says `C₀^{⊗n}` is a core for the sector derivation, and the `ℓ²`-sum
assembly glues the sectors — giving essential self-adjointness of `dΓ(H₁)` on the
finite-particle domain built from `C₀` alone. Nothing about the *inner* model
(quartic, exponential, singular) enters: the inner nonlinearity only changes the
one-particle matrix elements, and the hypothesis is a property of `H₁`, not of the
outer ladders.

The carried input in the fully general case is the sectorwise statement for a
self-adjoint one-particle operator, and even that is now proved for every
self-adjoint `H₁` (`dGamma_selfAdjoint_essentiallySelfAdjointOn_fockCore`) — with
the bounded, scalar and diagonal cases unconditional as well. The remaining warning
worth keeping in view is the scope stated by the chapters themselves: the tensor
powers used are the **full** powers $`H^{\\otimes n}`, not the symmetric (bosonic)
or antisymmetric (fermionic) subspaces; the statements are about the derivation on
those powers, and no claim about the symmetrized Fock sectors is made here.
:::
