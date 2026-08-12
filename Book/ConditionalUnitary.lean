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
