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
the bounded, scalar and diagonal cases unconditional as well. One scope caveat
survives, and it is a caveat about *this* chapter rather than about the theory:
the tensor powers used **here** are the full powers $`H^{\otimes n}`, not the
symmetric (bosonic) or antisymmetric (fermionic) subspaces. The statements above
are about the derivation on those powers. The passage to the symmetrized sectors
is not a further hypothesis — it is the subject of the next section, and it is
now proved.
:::

# The Symmetric and Antisymmetric Sectors, at Every Particle Number

:::paragraph
The enclosure $`H = d\Gamma(h)` is a statement about the *whole* nested Fock
space, but the physical content lives in the symmetric (bosonic) and
antisymmetric (fermionic) subspaces of each sector $`H^{\otimes n}`. That
passage was the honest boundary of the previous section. It has been executed,
in four steps that are worth reading as one argument, because each step is an
abstract instrument reusable far beyond this book.

**Step one — reduction.** `BookProof/ChapterReducingSubspaceEsa.lean`
(namespace `BookProof.ReducedEsa`): if $`P` is an idempotent symmetric
*reducing* projection that preserves the domain and commutes with $`T`, then
essential self-adjointness of $`T` descends to the sector $`D \cap P F`. The
proof is the deficiency argument in miniature — for $`w` in the range,
$`\langle T v, w \rangle = \langle P(Tv), w \rangle = \langle T(Pv), w \rangle` —
and needs no completeness, no closedness and no spectral theory
(`essentiallySelfAdjointOn_red`). Applied to a self-inverse isometry $`U`
preserving $`D` and commuting with $`T`, the two canonical projections
$`(1 \pm U)/2` (`symProj`, `asymProj`) are such projections, giving
`essentiallySelfAdjointOn_symSector` / `…_asymSector` on the eigenspaces
$`Ux = \pm x`.

**Step two — finite groups.** `BookProof/ChapterGroupAverageEsa.lean`
(namespace `BookProof.GroupAverage`) generalizes the single involution to any
finite group of symmetries: `UnitaryRep G F` is an action by inner-preserving
linear maps, `avgProj = |G|^{-1} \sum_g \rho(g)` is the Haar average, its range
is the joint fixed space (`mem_range_avgProj_iff`), it is again a reducing
projection (`isReducingProjection_avgProj`, by the reindexing
$`\sum_g\sum_h \rho(gh) = |G|\sum_k \rho(k)`), and hence
**`essentiallySelfAdjointOn_invariantSector`**: an operator commuting with the
action is essentially self-adjoint on the invariant sector as soon as it is on
its domain. This is the instrument the higher sectors need — the symmetric group
of $`n` factors, twisted by the sign character for the fermionic case.

**Step three — the permutation action.** `BookProof/ChapterTensorPermutation.lean`
(namespace `BookProof.TensorPerm`) builds it out of two elementary isometries
only: `swapFirst`, the exchange of the first two factors of $`E^{\otimes(n+2)}`
(associator ∘ commutor ∘ associator), and `liftTail u`, applied to the last $`n`
factors; `permOp n σ` follows `Equiv.Perm.decomposeFin`. Since every operator is
a composite of linear isometry equivalences, each is one, and
`permOp_purePow` is the familiar formula
$`U_\sigma(x_0 \otimes \cdots \otimes x_{n-1}) = x_{\sigma 0} \otimes \cdots \otimes x_{\sigma(n-1)}`,
from which the group law `permOp_mul` follows. `permRep` and `signRep` package
the action and its sign twist as `UnitaryRep`s.

**Step four — the two sectors.** `BookProof/ChapterPermutationSectorEsa.lean`
(namespace `BookProof.PermSector`) checks the three compatibilities of a pair of
operators — with the inclusion of the domain, with the sector derivation
$`d\Gamma(A)^{(n)}`, and with the core power $`D^{\otimes n}` — for the two
generators (`Good`, `good_swapFirst`, `good_liftTail`) and passes them along the
recursion (`good_permOp`). Through `essentiallySelfAdjointOn_invariantSector`
come the four headline statements: **`essentiallySelfAdjointOn_bosonic`** and
**`essentiallySelfAdjointOn_fermionic`** on $`D_2^{\otimes n}`, and
**`essentiallySelfAdjointOn_bosonic_core`** / **`essentiallySelfAdjointOn_fermionic_core`**
on the symmetrized and antisymmetrized one-particle core $`D^{\otimes n}`, for
any core $`D` of $`A`. `mem_bosonicSector_iff` / `mem_fermionicSector_iff`
identify the two sectors as the symmetric and the antisymmetric tensors;
`exists_ne_zero_bosonic` (the $`n`-th power $`a \otimes \cdots \otimes a` of a
core vector) and `exists_ne_zero_fermionic` (the Slater determinant, nonzero by
`inner_purePow` and orthogonality) are the non-vacuity witnesses.

Two companion chapters make the picture complete. The two-particle case in
isolation, from which the general construction checks itself
(`permOp_two_eq_swapH`), is `BookProof/ChapterTwoParticleSectorEsa.lean`
(namespace `BookProof.TwoParticleSector`), with its reducing projection the
swap $`(1 \pm \mathrm{swap})/2`. And `BookProof/ChapterFockStatisticsEsa.lean`
(namespace `BookProof.FockStatistics`) discharges the hypothesis the permutation
chapter *carries* — that the sector derivation is essentially self-adjoint on
$`D_2^{\otimes n}` — from essential self-adjointness of the one-particle
operator alone (`essentiallySelfAdjointOn_bosonic_of_esa`, …), assembling the
algebraic-tensor Fock statements `bosonicFock_esa` and `fermionicFock_esa`.
`BookProof/ChapterFockStatisticsCompletion.lean` then carries all of it across
to the *completed* sectors and takes the direct sum over particle numbers:
**`hbosonicFock_esa`** — $`d\Gamma(A)` is essentially self-adjoint on the
bosonic Fock space, the Hilbert space direct sum over all particle numbers of
the symmetric sectors — and **`hfermionicFock_esa`**, its fermionic twin, under
no hypotheses beyond essential self-adjointness of $`A` on a dense domain.
:::

```
#check @BookProof.ReducedEsa.IsReducingProjection
#check @BookProof.ReducedEsa.essentiallySelfAdjointOn_red
#check @BookProof.ReducedEsa.symmetricOn_redOp
#check @BookProof.ReducedEsa.symProj
#check @BookProof.ReducedEsa.asymProj
#check @BookProof.ReducedEsa.essentiallySelfAdjointOn_symSector
#check @BookProof.ReducedEsa.essentiallySelfAdjointOn_asymSector
#check @BookProof.GroupAverage.UnitaryRep
#check @BookProof.GroupAverage.avgProj
#check @BookProof.GroupAverage.mem_range_avgProj_iff
#check @BookProof.GroupAverage.isReducingProjection_avgProj
#check @BookProof.GroupAverage.essentiallySelfAdjointOn_invariantSector
#check @BookProof.GroupAverage.repOfInvolution
#check @BookProof.GroupAverage.avgProj_repOfInvolution
#check @BookProof.TensorPerm.permOp
#check @BookProof.TensorPerm.permOp_purePow
#check @BookProof.TensorPerm.permOp_mul
#check @BookProof.TensorPerm.permRep
#check @BookProof.TensorPerm.signRep
#check @BookProof.PermSector.good_permOp
#check @BookProof.PermSector.essentiallySelfAdjointOn_bosonic
#check @BookProof.PermSector.essentiallySelfAdjointOn_fermionic
#check @BookProof.PermSector.essentiallySelfAdjointOn_bosonic_core
#check @BookProof.PermSector.essentiallySelfAdjointOn_fermionic_core
#check @BookProof.PermSector.mem_bosonicSector_iff
#check @BookProof.PermSector.mem_fermionicSector_iff
#check @BookProof.PermSector.permOp_two_eq_swapH
#check @BookProof.TwoParticleSector.essentiallySelfAdjointOn_bosonic
#check @BookProof.TwoParticleSector.essentiallySelfAdjointOn_fermionic
#check @BookProof.FockStatistics.essentiallySelfAdjointOn_bosonic_of_esa
#check @BookProof.FockStatistics.bosonicFock_esa
#check @BookProof.FockStatistics.fermionicFock_esa
#check @BookProof.FockStatistics.hbosonicFock_esa
#check @BookProof.FockStatistics.hfermionicFock_esa
#check @BookProof.GroupAverage.UnitaryRep.completionRep
```

:::paragraph
**Honest boundary of the symmetrization.** The statements are about the two
sectors of $`H^{\otimes n}` for each *fixed* particle number $`n`, and — through
the completed-Fock chapter — about the direct sum that assembles them. Nothing
is claimed about a continuum of particle numbers beyond that sum, and essential
self-adjointness of $`d\Gamma(A)^{(n)}` on $`D_2^{\otimes n}` is carried as a
hypothesis through the reduction, discharged separately by the Fock-statistics
chapter as described above. The passage is *statistics*, not dynamics: it says
which vectors are physical, and that the physical subspace inherits the
essential self-adjointness — it says nothing about the spectrum.
:::

# The One-Particle Obligation, Discharged in General

:::paragraph
There are two obligations behind every Faris–Lavine route chapter, and it is
worth naming them separately because they are easy to confuse. Obligation (ii)
was that the *lifted* operator $`d\Gamma(N)` must be essentially self-adjoint on
the lifted core — that is what the core-transfer chain of the earlier sections
discharges. Obligation (i) is the *inner* one: the comparison operator $`N` of
record must itself be essentially self-adjoint on the core the proof actually
chooses. Two short chapters discharge it in general.

`BookProof/ChapterSelfAdjointCoreEsa.lean` (namespace
`BookProof.SelfAdjointCoreEsa`): if $`T` has a self-adjoint extension, then it
was already essentially self-adjoint on its own domain. At a non-real $`z` the
deficiency equation makes $`w` a domain vector with $`A w = z \bullet w`, and
symmetry then forces $`(\bar z - z)\langle w, w \rangle = 0`, so $`w = 0`
(`deficiencyTrivialAt_dom_of_isSelfAdjointExtension`); composing with the graph
transfer gives `essentiallySelfAdjointOn_of_graphCore_selfAdjoint`.

`BookProof/ChapterComparisonCoreEsa.lean` (namespace
`BookProof.ComparisonCoreEsa`) restates the same fact in the vocabulary the
route chapters use: `comparison_isSelfAdjointExtension` and
`comparison_essentiallySelfAdjointOn_dom` (a `Comparison` is self-adjoint, hence
essentially self-adjoint, on its own domain), `graphCore_of_isGraphCore` (the
two graph-core notions agree), **`esa_of_isGraphCore`** — obligation (i) — and
**`isGraphCore_iff_esa`**, the equivalence obtained with the already-proved
converse `ScalaronFiberFL.isGraphCore_of_esa`: *for a Faris–Lavine comparison
operator, "graph core" and "core of essential self-adjointness" are the same
notion.* Wherever a route chapter exhibits a graph core for its comparison
operator — `QgOuterFockFullFL.harmFried_isGraphCore`, the Gauss-polynomial core
of $`-\Delta + \lVert x\rVert^2/4` in every dimension, and
`ScalaronOuterFockFL.secN_isGraphCore`, the compactly-supported smooth core of
the scalaron-wall comparison — obligation (i) therefore needs no further work.
:::

```
#check @BookProof.SelfAdjointCoreEsa.deficiencyTrivialAt_dom_of_isSelfAdjointExtension
#check @BookProof.SelfAdjointCoreEsa.essentiallySelfAdjointOn_dom_of_isSelfAdjointExtension
#check @BookProof.SelfAdjointCoreEsa.essentiallySelfAdjointOn_of_graphCore_selfAdjoint
#check @BookProof.ComparisonCoreEsa.comparison_isSelfAdjointExtension
#check @BookProof.ComparisonCoreEsa.comparison_essentiallySelfAdjointOn_dom
#check @BookProof.ComparisonCoreEsa.graphCore_of_isGraphCore
#check @BookProof.ComparisonCoreEsa.esa_of_isGraphCore
#check @BookProof.ComparisonCoreEsa.isGraphCore_iff_esa
```

# Non-Interacting Degrees of Freedom: the Tensor Sum

:::paragraph
The last elementary situation the enclosure needs, and did not have, is the
tensor sum of two *different* operators — $`A \otimes 1 + 1 \otimes B`, the
Hamiltonian of two non-interacting degrees of freedom with potential
$`V(u,v) = V_1(u) + V_2(v)`. `BookProof/ChapterTensorSumEsa.lean` (namespace
`BookProof.TensorSumEsa`) puts it on the completed tensor product
$`H \hat\otimes K` with domain $`D_A \otimes D_B`: symmetry
(`symmetricOn_cpairOp`), density of that domain (`dense_cpairDom`), the product
flow $`U t \otimes V t` (`pflow`, `hasDerivAt_pflow`) which is isometric,
preserves the domain and obeys the Leibniz rule — hence solves the Schrödinger
equation of the tensor sum — and Nelson's invariant-domain criterion applied to
those orbits gives **`essentiallySelfAdjointOn_cpairDom_flow`**, with the
self-adjoint case `essentiallySelfAdjointOn_cpairDom_selfAdjoint` (Stone's
theorem supplying the flows: no boundedness, no positivity, no relative bound and
no assumption on either spectrum) and the weakest headline
**`essentiallySelfAdjointOn_cpairDom_esa`**, where both hypotheses are only
*essential* self-adjointness. The two-factor core estimate
`isGraphCore_pairCore` says a core of $`A` tensor a core of $`B` is a core of
the sum.

`BookProof/ChapterTensorSumChain.lean` (namespace `BookProof.TensorSumChain`)
iterates it: `EsaOp` bundles the data, `pair` is the two-factor step and `chain`
folds it along a list, so **`chain_esa`** covers
$`A_1 \otimes 1 \otimes \cdots + \cdots + 1 \otimes \cdots \otimes A_n` for an
arbitrary finite family of symmetric, essentially self-adjoint operators — the
Hamiltonian of $`n` non-interacting degrees of freedom — on the algebraic tensor
product of the $`n` domains, with the unitary group `chain_stone_flow`.

This is the theorem behind every *decoupled* realization in the programme: when
a final Hamiltonian of record is written as a sum of uncoupled one-particle
pieces — the TEGR shear fibres $`\oplus` the scalaron mass, say, in the
R² vielbein model's small-field limit — its essential self-adjointness follows
from `chain_esa` rather than from a bespoke argument per sector.
:::

```
#check @BookProof.TensorSumEsa.symmetricOn_cpairOp
#check @BookProof.TensorSumEsa.dense_cpairDom
#check @BookProof.TensorSumEsa.essentiallySelfAdjointOn_cpairDom_flow
#check @BookProof.TensorSumEsa.essentiallySelfAdjointOn_cpairDom_selfAdjoint
#check @BookProof.TensorSumEsa.essentiallySelfAdjointOn_cpairDom_esa
#check @BookProof.TensorSumEsa.isGraphCore_pairCore
#check @BookProof.TensorSumEsa.essentiallySelfAdjointOn_cpairCore
#check @BookProof.TensorSumEsa.tensorSum_stone_flow
#check @BookProof.TensorSumChain.EsaOp
#check @BookProof.TensorSumChain.chain
#check @BookProof.TensorSumChain.chain_esa
#check @BookProof.TensorSumChain.chain_symmetric
#check @BookProof.TensorSumChain.chain_dense
#check @BookProof.TensorSumChain.chain_stone_flow
```

:::paragraph
**Honest boundary.** The gluing is over a tensor product of finitely many
factors (by iteration); it is not the direct-integral step, and it says nothing
about a potential that is *not* a sum of a function of the first variable and a
function of the second. Interaction terms — the scalaron–vielbein coupling, the
$`B^2` pair terms, the advection convolution — are exactly what a tensor sum
does **not** cover; they live in the one-particle operator of a single factor
and enter the enclosure through the matrix elements $`h_{ij}`, as the doctrine at
the head of this chapter says.
:::
