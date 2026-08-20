import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Conditional Probability Is Parametrized by a Unitary" =>
%%%
tag := "conditional-unitary"
%%%

# The Question

:::paragraph
The Born rule ({ref "born-reproduces"}[the Born rule reproduces every
distribution]) parametrizes a single probability distribution by a wave-function:
$`p(x) = |\Psi(x)|^2`. The manuscript goes further. *Any joint probability density*
$`p(x,y)` between two standard measure spaces $`X, Y` can be written as
:::

$$`p(x,y) = |\mathcal{U}(y,x,0)|^2,`

:::paragraph
where $`\mathcal{U} : L^2(\mathbb{Z}) \to L^2(X \times Y)` is a *unitary* operator.
The book calls this "a commutative version of Wigner's theorem." Its consequence is
that any conditional probability measure in a standard measure space is parametrized
by a unitary operator — and therefore quantum processes are not exotic, they are
simply _more general_ than Markov processes. This chapter verifies the
finite-dimensional core of that statement, following the book's own proof: write the
joint density as a wave-function, build the unitary by Gram–Schmidt, bound the
wave-function as an operator, take its singular-value expansion, and read off the
marginal and conditional probabilities.
:::

# A Joint Probability Is a Wave-function

:::paragraph
Since $`p(x,y) \ge 0` and $`\sum_{x,y} p(x,y) = 1`, there is a normalized
wave-function $`\Psi \in L^2(X \times Y)` with $`|\Psi(x,y)|^2 = p(x,y)`: take
$`\Psi(x,y) = \sqrt{p(x,y)}`. The book then builds a unitary $`\mathcal{U}` whose
chosen column _is_ $`\Psi`, "through the Gram–Schmidt process." In finite dimension
this is the statement that every unit vector is a column of some unitary matrix —
extend it to an orthonormal basis:
:::

```
#check @exists_unitary_column
```

:::paragraph
Applying this to $`v(i) = \sqrt{p(i)}`, every finite probability distribution is the
squared modulus of a column of a unitary matrix:
:::

```
#check @exists_unitary_of_prob
```

:::paragraph
And in the book's exact two-space form: *every joint probability distribution*
$`p(x,y)` on a finite $`X \times Y` is $`|U|^2` on a column of a unitary matrix
indexed by $`X \times Y`:
:::

```
#check @exists_unitary_joint
```

# The Converse: an Operator Defines a Joint Probability

:::paragraph
The converse also holds, and it is the direction the book uses to define a
probability from an operator. Given any bounded operator $`B` with
$`\mathrm{tr}(B B^\dagger) = 1`, the squared modulus $`p(x,y) = |B(y,x)|^2` is a
genuine joint probability distribution:
:::

```
#check @sqAbs_isProb_of_frobenius_one
#check @frobenius_eq_trace
```

:::paragraph
So probability distributions and (trace-normalized) operators are two descriptions of
the same object. This is the algebraic backbone of the wave-function parametrization.
:::

# The Kernel Operator Is Bounded

:::paragraph
The book now views $`\Psi` as an *integral operator*
$`\Psi : L^2(X) \to L^2(Y)`, acting by
$`\Psi\{\Phi\}(y) = \int dx\, \Psi(x,y)\,\Phi(x)`. By Cauchy–Schwarz, this operator
is bounded, with operator norm at most the Hilbert–Schmidt norm of the kernel. In the
finite (discretized) model the kernel operator and its bound are explicit:
:::

```
#check @kernelOp
#check @kernel_row_bound
#check @kernel_l2_bound
```

:::paragraph
In particular, when the kernel has $`L^2` norm at most $`1` — which holds for a
normalized wave-function — the operator is a *contraction*:
:::

```
#check @kernel_contraction
```

:::paragraph
Boundedness is the prerequisite for the singular-value expansion: only a bounded
operator admits a polar decomposition.
:::

# The Singular-Value Expansion

:::paragraph
Because $`\Psi` is bounded, it admits a singular-value expansion (through the polar
decomposition) $`\Psi = W D U^\dagger`, with $`D \ge 0` diagonal and $`W, U` unitary.
In finite dimension this is the ordinary SVD, discharged by diagonalizing the
positive-semidefinite Gram matrix $`A^\dagger A` with the spectral theorem and taking
square roots of its eigenvalues:
:::

```
#check @gram_svd
#check @svd_completion
#check @denseCore_svd
```

:::paragraph
The factor $`V` that appears before completion to the unitary $`W` is a
*partial isometry*: $`V^\dagger V` and $`V V^\dagger` are orthogonal projections,
and $`V V^\dagger V = V`:
:::

```
#check @IsPartialIsometry
```

:::paragraph
The book then changes the marginal from a fixed reference $`p_0 > 0` to an arbitrary
$`p`, using $`T p T^\dagger = W D U^\dagger (p/p_0) U D W^\dagger`. This
change-of-marginal identity is verified at the operator level:
:::

```
#check @conditional_operator_identity
```

# Marginal and Conditional Probability

:::paragraph
Finally the book reads the probabilities back off the operator. For a bounded
operator $`B`, the joint distribution is $`p(x,y) = |B(y,x)|^2`, the *marginal* is
the diagonal of the Gram matrix $`B^\dagger B`, and the normalization is the trace:
:::

```
#check @pJoint
#check @pMarg
#check @pMarg_eq_diagBHB
#check @trace_gram_eq_one
```

:::paragraph
When the marginal is positive, $`p(x) = \{B^\dagger B\}(x,x) > 0`, the
*regular conditional probability* $`p(y|x) = p(x,y)/p(x)` is defined, is
non-negative, and sums to one over $`y`:
:::

```
#check @pCond
#check @pCond_sum_one
```

:::paragraph
And the joint distribution factors as marginal times conditional, exactly as the book
parametrizes it, $`p(x,y) = p(y|x)\,p(x)`:
:::

```
#check @pJoint_eq_cond_mul_marg
```

:::paragraph
The same marginal/conditional split is available for a *density matrix*. The
spectral decomposition $`\rho = U\,\mathrm{diag}(d)\,U^\dagger` has a diagonal
$`d` which is a probability distribution — the marginal of the initial state —
while the Born matrix $`\|U_{ij}\|^2` of the unitary is a *doubly stochastic*
conditional probability, and the final-state marginal is obtained from $`d` by
that conditional, $`\rho_{ii} = \sum_k \|U_{ik}\|^2 d_k`:
:::

```
#check @BookProof.DensitySpectral.bornKernel
#check @BookProof.DensitySpectral.bornKernel_row_sum
#check @BookProof.DensitySpectral.bornKernel_col_sum
#check @BookProof.DensitySpectral.density_diag_eq_kernel_apply
#check @BookProof.DensitySpectral.density_diag_isProbability
#check @BookProof.DensitySpectral.density_marginal_conditional
```

# What Is Verified and What Is Infinite-Dimensional

:::paragraph
Everything cited above is verified `sorry`-free, over *finite* index sets (the
discretized models used throughout `BookProof`). This is the concrete content of the
book's Gram–Schmidt, Cauchy–Schwarz, and singular-value arguments. The
manuscript states the result for arbitrary *standard* measure spaces, possibly with
continuous parts; the abstract measure-theoretic layer — the classification of
standard measure spaces, the identification of commutative von Neumann algebras with
$`L^\infty(X,\mu)`, and regular conditional probabilities via disintegration on a
standard Borel space — is the infinite-dimensional extension. Parts of that layer
are proved in `BookProof.ChapterSelectingEvents`: regular conditional probabilities
exist for any finite measure on a standard Borel space
(`exists_regular_conditional_probability`), singletons and finite sets are null in a
continuous space (`singleton_null_in_continuous`, `finite_set_null_in_continuous`),
every probability measure splits into a continuous and an atomic part
(`exists_continuous_atomic_decomposition`), and the finite type-$`\mathrm{I}_n` case
of the von Neumann classification is a theorem (`vonNeumann_abelian_classification_typeI`):
:::

```
#check @BookProof.ChapterSelectingEvents.exists_regular_conditional_probability
#check @BookProof.ChapterSelectingEvents.singleton_null_in_continuous
#check @BookProof.ChapterSelectingEvents.finite_set_null_in_continuous
#check @BookProof.ChapterSelectingEvents.exists_continuous_atomic_decomposition
#check @BookProof.ChapterSelectingEvents.selecting_events_not_rewriting_history
```

:::paragraph
The finite-dimensional algebraic core proved here is what makes the
parametrization work, and it is the part the book actually computes.
:::

# A Less Arbitrary Construction: the Unitary from the Dynamics

:::paragraph
The construction above builds the unitary $`\mathcal{U}` by completing the
wave-function $`\Psi = \sqrt p` to an orthonormal basis (Gram–Schmidt). That is
*correct* but *arbitrary*: the columns after the first are chosen by the completion,
not fixed by the probability data. The manuscript's own field-theoretic thread
(QFM.tex) supplies a construction that is *less arbitrary*, because the unitary is
*pinned down by the dynamics* rather than by a basis choice.
:::

:::paragraph
The point is the passage from a *function* to a *unitary*. A velocity field
$`v_t(x)` — a function on configuration space — determines a Hermitian generator by
the continuity (Weyl-symmetrized) prescription
:::

$$`\mathbf{H}_t = \tfrac12\bigl[\hat p\cdot v_t(\hat x) + v_t(\hat x)\cdot\hat p\bigr],`

:::paragraph
and hence a unitary $`\mathbf{U} = e^{i\mathbf{H}t}`. The unitary is *determined by
the function* $`v_t`; there is no free choice of extra columns. This is the
"function ↔ unitary" translation of QFM.tex, and it is the natural replacement for
the Gram–Schmidt completion: instead of arbitrarily extending a wave-function to a
unitary, one declares the *transition law* (a conditional probability) and lets the
dynamics build the unitary.
:::

# The Generalization: Conditional Probability and a Standard Hilbert Space

:::paragraph
The same construction generalizes to a *conditional probability* (a regular
conditional probability / Markov kernel) on continuous inputs, and it does so
without any Bochner-space machinery. Let $`p(y|x)` be a transition law from $`X` to
$`Z`, and let $`e_0 \in L^2(Z,\nu)` be a fixed *background* wave-function — for
concreteness the standard Gaussian state $`e_0(z) = \pi^{-1/4} e^{-z^2/2}`.
Form the joint space by the canonical tensor–product identification
:::

$$`L^2(X,\mu) \otimes L^2(Z,\nu) \;\cong\; L^2(X\times Z,\;\mu\times\nu).`

:::paragraph
Then $`\mathbf{H}` is a *standard* Hermitian operator on the scalar space
$`L^2(X\times Z)` — for instance a Schrödinger-type Hamiltonian
:::

$$`\mathbf{H} = -\tfrac12\,\Delta_z + V(x,z),`

:::paragraph
with $`x` acting as an external coordinate that modifies the potential felt by the
$`z` variable. Starting from the product wave-function $`\Psi_0(x,z) = f(x)\,e_0(z)`
and evolving by the unitary gives $`\Psi_1 = e^{i\mathbf{H}}\Psi_0`, and the
conditional probability is recovered by the *ordinary Born rule*:
:::

$$`P(x, B) = \int_B \bigl|\Psi_1(x,z)\bigr|^2\, d\nu(z).`

:::paragraph
This is the key simplification: no operator-valued inner products, no module
algebra. Any classical stochastic transition (regular conditional probability) is
simulated by an ordinary quantum system — a standard Hermitian $`\mathbf{H}` on a
standard $`L^2(X\times Z)`, a fixed background wave-function, and the Born rule.
The conditional probability ↔ unitary map of this chapter is thereby re-grounded in
standard quantum mechanics, and the arbitrary Gram–Schmidt completion is replaced
by a unitary that the dynamics determines.
:::

:::paragraph
The shift in viewpoint is the same one that makes the finite core of this chapter
honest: the Gram–Schmidt and SVD results record what *any* unitary must do with the
wave-function data; the dynamics-based construction records *which* unitary the
physics picks. Both are needed — the former is the algebraic backbone, the latter
the less-arbitrary physical selection.
:::

:::paragraph
The finite (discretized) form of this construction is formalized in
`BookProof.ChapterContinuityUnitary`, on the cyclic lattice with the
symmetric-difference momentum $`(\hat p\,\psi)_k = -\tfrac{i}{2}(\psi_{k+1} -
\psi_{k-1})`:
:::

```
#check @BookProof.ChapterContinuityUnitary.continuityHamiltonian
#check @BookProof.ChapterContinuityUnitary.continuityHamiltonian_hermitian
#check @BookProof.ChapterContinuityUnitary.momentum_mul_velocityOp_not_hermitian
#check @BookProof.ChapterContinuityUnitary.continuityUnitary
#check @BookProof.ChapterContinuityUnitary.continuityUnitary_unitary
#check @BookProof.ChapterContinuityUnitary.continuityUnitary_add
```

:::paragraph
The generator $`\mathbf{H} = \tfrac12(\hat p\,v + v\,\hat p)` is Hermitian, and the
unsymmetrized product $`\hat p\,v` is *not* — the Weyl symmetrization is exactly
what makes the generator an observable. The exponential $`\mathbf{U}_t =
e^{i t \mathbf{H}}` is then unitary and forms a one-parameter group, with no free
choice of columns anywhere: the function $`v` determines it.
:::

:::paragraph
The Born-rule recovery of the conditional probability, and the tensor–product
identification that keeps everything on the scalar space, are formalized as well:
:::

```
#check @BookProof.ChapterContinuityUnitary.bornRecover
#check @BookProof.ChapterContinuityUnitary.bornRecover_union
#check @BookProof.ChapterContinuityUnitary.bornRecover_univ
#check @BookProof.ChapterContinuityUnitary.condProb_of_continuity
#check @BookProof.ChapterContinuityUnitary.tensorIsom
#check @BookProof.ChapterContinuityUnitary.bornRecover_product_state
```

:::paragraph
`bornRecover` is $`P(x, B) = \sum_{z \in B} |\Psi_t(x,z)|^2`; it is nonnegative,
finitely additive, and of total mass $`1` (`bornRecover_univ`, a consequence of
unitarity alone). The capstone `condProb_of_continuity` packages this as a genuine
probability distribution on the lattice for *every* input $`x` — a Markov kernel
built from the dynamics rather than from a basis choice. `tensorIsom` is the finite
index-level identification $`L^2(X)\otimes L^2(Z)\cong L^2(X\times Z)`, and
`bornRecover_product_state` runs the recovery on a product initial state
$`\Psi_0(x,z) = f(x)e_0(z)`.
:::

:::paragraph
The same construction runs on the *infinite* lattice, with bounded operators on the
genuine Hilbert space $`\ell^2(\mathbb Z)` in place of matrices
(`BookProof.ChapterContinuityUnitaryInfinite`). The lattice translations are
unitaries, the symmetric-difference momentum and a bounded velocity field
$`v \in \ell^\infty(\mathbb Z)` are bounded self-adjoint operators, the
Weyl-symmetrized generator is again self-adjoint, and $`\mathbf{U}_t = e^{itH}` is
the Banach-algebra exponential of $`\ell^2(\mathbb Z)\to\ell^2(\mathbb Z)`:
:::

```
#check @BookProof.ChapterContinuityUnitaryInfinite.momentum_isSelfAdjoint
#check @BookProof.ChapterContinuityUnitaryInfinite.velocityOp_isSelfAdjoint
#check @BookProof.ChapterContinuityUnitaryInfinite.continuityHamiltonian_isSelfAdjoint
#check @BookProof.ChapterContinuityUnitaryInfinite.continuityUnitary_unitary
#check @BookProof.ChapterContinuityUnitaryInfinite.continuityUnitary_add
#check @BookProof.ChapterContinuityUnitaryInfinite.bornRecover_tsum_univ
#check @BookProof.ChapterContinuityUnitaryInfinite.condProb_of_continuity_infinite
```

:::paragraph
On the infinite lattice the Born recovery is *countably* additive: the total mass
$`\sum_{z\in\mathbb Z}|\Psi_t(z)|^2 = 1` is Parseval plus unitarity
(`bornRecover_tsum_univ`), and `condProb_of_continuity_infinite` packages it as a
probability distribution on $`\mathbb Z` for every input. What stays outside the
statement is unboundedness — the position and momentum operators of the continuum —
not infinite-dimensionality.
:::

:::paragraph
The discretization can be dropped entirely on the *probabilistic* side. On any
measure space $`(\alpha,\mu)` and for a state $`\Psi \in L^2(\mu)`, the Born
prescription $`P(B) = \int_B |\Psi|^2\,d\mu` is defined in
`BookProof.ChapterBornMeasure` as a *measure*, so countable additivity holds by
construction; it is a probability measure exactly when $`\Psi` is normalized, and it
is absolutely continuous with respect to $`\mu`:
:::

```
#check @BookProof.ChapterBornMeasure.bornMeasure
#check @BookProof.ChapterBornMeasure.lintegral_bornDensity
#check @BookProof.ChapterBornMeasure.isProbabilityMeasure_bornMeasure
#check @BookProof.ChapterBornMeasure.bornMeasure_absolutelyContinuous
#check @BookProof.ChapterBornMeasure.condProb_of_bounded_dynamics
```

:::paragraph
The capstone `condProb_of_bounded_dynamics` runs the whole construction on the
continuum: for a bounded self-adjoint generator $`H` on $`L^2(\mu)` and the unitary
group $`\mathbf{U}_t = e^{itH}`, the evolved state carries a Born law that is a
countably additive probability measure at every time, and it charges no
$`\mu`-null set. The integrability that the proof-plan appendix deferred is thus
settled; what remains open is the *unbounded* generator of the continuum.
:::

:::paragraph
That last layer is at least made precise. `BookProof.ChapterUnboundedPosition`
builds the lattice position operator $`\hat x\,\psi_k = k\,\psi_k` on its natural
domain $`D = \{\psi\in\ell^2(\mathbb Z) : \hat x\psi\in\ell^2(\mathbb Z)\}` and proves
that the domain is dense, that the operator is symmetric on it, and that it is
genuinely unbounded — not the restriction of any bounded operator:
:::

```
#check @BookProof.ChapterUnboundedPosition.mulDomain
#check @BookProof.ChapterUnboundedPosition.mulOp_symmetric
#check @BookProof.ChapterUnboundedPosition.mulDomain_dense
#check @BookProof.ChapterUnboundedPosition.position_unbounded
#check @BookProof.ChapterUnboundedPosition.position_not_boundedOperator
```

:::paragraph
That operator is not merely symmetric. Its adjoint domain is *exactly* the natural
domain and the adjoint acts by the same multiplication, so the lattice position
operator is a bona fide self-adjoint observable:
:::

```
#check @BookProof.ChapterUnboundedPosition.adjointDomain_eq_mulDomain
#check @BookProof.ChapterUnboundedPosition.adjoint_eq_mulOp
```

:::paragraph
And it generates its unitary group. The pointwise phase
$`(\mathbf{U}_t\psi)_k = e^{itf_k}\psi_k` is a surjective linear isometry of
$`\ell^2(\mathbb Z)` satisfying $`\mathbf{U}_0 = 1` and
$`\mathbf{U}_{s+t} = \mathbf{U}_s\mathbf{U}_t`; it is strongly continuous at $`0`
for *every* state, with no domain hypothesis; and on the natural domain its
difference quotient converges in $`\ell^2(\mathbb Z)` to $`i\hat x\psi`, which is
Stone's relation $`\tfrac{d}{dt}\mathbf{U}_t\big|_{t=0} = iA` for an unbounded
self-adjoint $`A`:
:::

```
#check @BookProof.ChapterUnboundedPosition.phaseUnitary
#check @BookProof.ChapterUnboundedPosition.phaseUnitary_add
#check @BookProof.ChapterUnboundedPosition.tendsto_phaseUnitary
#check @BookProof.ChapterUnboundedPosition.tendsto_slope_phaseUnitary
```

:::paragraph
None of that is special to the lattice. `BookProof.ChapterUnitaryTransport` proves
that the whole package is invariant under a unitary change of Hilbert space: for
any unitary $`W : H \to K` and any densely defined `A` on `D \subseteq H`, the
transported operator $`WAW^{-1}` on $`W(D)` has a dense domain, is symmetric when
`A` is, has adjoint domain $`W(\mathrm{dom}\,A^\dagger)` — so *self-adjointness*
transports — and the transported group $`WU_tW^{-1}` is strongly continuous with
$`WAW^{-1}` as its generator:
:::

```
#check @BookProof.ChapterUnitaryTransport.transport_isSelfAdjointOn
#check @BookProof.ChapterUnitaryTransport.tendsto_transportUnitary
#check @BookProof.ChapterUnitaryTransport.tendsto_slope_transportUnitary
```

:::paragraph
Combining the two halves: *every* operator unitarily equivalent to a lattice
multiplication operator — on any complex Hilbert space — is self-adjoint on a dense
domain and generates a strongly continuous unitary group satisfying Stone's
relation.
:::

```
#check @BookProof.ChapterUnitaryTransport.transported_position_domain_dense
#check @BookProof.ChapterUnitaryTransport.transported_position_isSelfAdjointOn
#check @BookProof.ChapterUnitaryTransport.transported_position_group
#check @BookProof.ChapterUnitaryTransport.tendsto_slope_transported_position
```

:::paragraph
So the boundary of the formalized theory is stated inside the theory, and it now
lies two layers further out than the proof plan first drew it. Bounded generators
give the unitary group and the Born law outright; the unbounded position
observable is densely defined, symmetric, self-adjoint, and does generate a
strongly continuous unitary group with itself as generator; and that conclusion is
inherited by anything unitarily equivalent to it. And the general Stone theorem
is itself proved in this development — not the spectral-theoretic diagonalization,
which still requires hypotheses on the spectrum, but the *existence* half: an
arbitrary unbounded self-adjoint operator on a (complete, separable) Hilbert space
generates a weakly measurable one-parameter unitary group `e^{-itA}` satisfying
the Schrödinger equation on its domain, and conversely every such group arises
from its self-adjoint generator (`ChapterStoneResolvent` through
`ChapterStoneSeparable`: `stoneU`, `stoneU_mem_domain`, `hasDerivAt_stoneU`,
`stone_bijection`, `stoneEquiv`, and the concrete `ℓ²(ℤ)` instance `stoneU_mulSA`).
The bridge from a *selected* self-adjoint extension to the flow is then packaged
by `ChapterStoneBridge` (`unboundedSelfAdjointOf`, `IsStoneFlow`,
`isStoneFlow_stoneU`, `exists_stone_flow_of_selfAdjointExtension` /
`of_positive` / `of_esa`), so the passage "essentially self-adjoint on a core ⇒
complete unitary flow" is a theorem rather than a promise. What a continuum
Laplacian would still need is the *spectral theorem* — the existence of the
diagonalizing unitary — which remains the recorded open step.
:::

```
#check @BookProof.ChapterStoneSeparable.stoneEquiv
#check @BookProof.ChapterStoneSeparable.stoneU_mulSA
#check @BookProof.StoneBridge.unboundedSelfAdjointOf
#check @BookProof.StoneBridge.IsStoneFlow
#check @BookProof.StoneBridge.isStoneFlow_stoneU
#check @BookProof.StoneBridge.exists_stone_flow_of_esa
#check @BookProof.StoneFlows.ym_fock_stone_flow
```

# Why This Matters Here

:::paragraph
This is the theorem that turns probability theory into quantum mechanics. A
conditional probability measure is parametrized by a unitary operator; a joint
probability is the squared modulus of a wave-function; the wave-function is a bounded
operator with a singular-value expansion; and the marginal and conditional
probabilities are read off its Gram matrix. None of this is a physical postulate — it
is the structure of probability itself, once we parametrize the simplex by the sphere.
The unitary time-evolution of
{ref "deterministic-transformations"}[the symmetry chapter] and the collapse of
{ref "collapse-kolmogorov"}[the collapse chapter] are both instances of this single
parametrization.
:::
