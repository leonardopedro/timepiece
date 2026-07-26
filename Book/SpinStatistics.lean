import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Spin–Statistics Dichotomy" =>
%%%
tag := "spin-statistics"
%%%

# The Question

:::paragraph
The free-field parametrization of {ref "free-field"}[the previous chapter] builds a
uniform measure on an infinite-dimensional sphere; it relies on there being
_infinitely many_ degrees of freedom. But, the manuscript observes, "often we are
interested in a tensor product of sample spaces, some of which have finite degrees of
freedom," and one should be able to "repeat the exercise for
$`\mathbb{Z}_2^n \times \mathbb{R}^m`." This chapter is the finite, fully explicit
case: a sample space with just two degrees of freedom, $`\mathbb{Z}_2 \times
\mathbb{Z}_2`.
:::

:::paragraph
A single two-valued degree of freedom $`\mathbb{Z}_2` is parametrized by a
**fermionic** Fock space $`\Gamma^a(L^2(\mathbb{Z}_2))`. For a _product_
$`\mathbb{Z}_2 \times \mathbb{Z}_2` there is a subtlety. Taken naively, the two modes
would admit non-null products of creation operators, and that "is not a free field
parametrization." The fix is to take the **graded** tensor product
$`\Gamma^s(L^2(\mathbb{Z}_2)) \otimes \Gamma^a(L^2(\mathbb{Z}_2))` so that the two
fermionic modes **anticommute**. That anticommutation — as opposed to the
_communication_ of bosonic modes — is the algebraic content of the
**spin–statistics** correspondence the section is about.
:::

# Two Modes by Jordan–Wigner

:::paragraph
The two-mode fermionic Fock space is $`\mathbb{C}^4 \cong \mathbb{C}^2 \otimes
\mathbb{C}^2`, with basis $`|n_1 n_2\rangle` ordered as
$`|00\rangle, |01\rangle, |10\rangle, |11\rangle` and $`|00\rangle` the vacuum. The
two annihilation modes are realized by the **Jordan–Wigner** prescription:
:::

$$`b_1 = a \otimes I, \qquad b_2 = Z \otimes a,`

:::paragraph
where $`a = \begin{pmatrix}0&1\\0&0\end{pmatrix}` is the single-mode annihilation and
$`Z = \begin{pmatrix}1&0\\0&-1\end{pmatrix}` is the **fermion-parity string**. It is
the parity string $`Z` in the second mode that forces the two modes to anticommute.
As explicit $`4 \times 4` matrices, with creation operators the conjugate transpose:
:::

```
#check @fermiAnnih1
#check @fermiAnnih2
#check @fermiCreate1_eq
#check @fermiCreate2_eq
```

# Each Mode Is a Fermionic Oscillator

:::paragraph
Each mode separately satisfies the **canonical anticommutation relation** (CAR): the
anticommutator of an annihilation operator with its own creation operator is the
identity,
:::

$$`\{b_i, b_i^\dagger\} = b_i b_i^\dagger + b_i^\dagger b_i = 1.`

```
#check @fermi_CAR₁
#check @fermi_CAR₂
```

# The Modes Anticommute: Fermionic Statistics

:::paragraph
The point of the construction is what happens _between_ the two modes. Distinct
fermionic modes anticommute:
:::

$$`\{b_1, b_2\} = b_1 b_2 + b_2 b_1 = 0, \qquad \{b_1, b_2^\dagger\} = b_1 b_2^\dagger + b_2^\dagger b_1 = 0.`

```
#check @fermiAnticomm_annih
#check @fermiAnticomm_create
#check @fermi_CAR_cross
```

:::paragraph
This is the **fermionic statistics**. It is precisely what distinguishes the
fermionic parametrization from a bosonic (commuting) one, and it is exactly the
condition the manuscript demanded: with the graded tensor product, the two modes do
not produce spurious non-null products of creation operators. A bosonic pair would
_commute_ here; a fermionic pair _anticommutes_. The spin–statistics theorem is the
statement that certain symmetry transformations are representable by one or the
other but not both.
:::

# Pauli Exclusion

:::paragraph
Anticommutation has an immediate consequence. Setting the two modes equal in
$`\{b_i, b_i\} = 0` gives $`b_i^2 = 0`: applying the same annihilation (or creation)
operator twice gives zero. This is the **Pauli exclusion principle** — a single mode
cannot hold two fermions:
:::

```
#check @fermiAnnih₁_sq
#check @fermiCreate₁_sq
```

:::paragraph
The number operator $`N_i = b_i^\dagger b_i` counts the occupation of mode $`i`. The
relation $`b_i^2 = 0` forces its eigenvalues to be $`0` and $`1` only: each
$`N_i` is a Hermitian **projection** (idempotent and self-adjoint):
:::

```
#check @fermiNumber₁_hermitian
#check @fermiNumber₁_idem
```

:::paragraph
There is a pleasing contrast. The creation operators _anticommute_, but the number
operators — the actual observables — **commute**:
:::

```
#check @fermiNumber_commute
```

:::paragraph
So the observable algebra is commutative (as it must be for a probability theory),
even though the underlying creation operators are not. The anticommutation lives in
the parametrization, not in the measured quantities.
:::

# Why This Matters Here

:::paragraph
This is the finite-degree-of-freedom instance of the manuscript's tensor products of
sample spaces. The carrier $`\mathbb{C}^4 \cong \mathbb{C}^2 \otimes \mathbb{C}^2` is
literally a tensor product, and the **graded** (Jordan–Wigner) tensor product is what
encodes the statistics: it is the parity string $`Z` that turns a naive product of two
modes into an anticommuting pair. The same dichotomy — bosonic commutation versus
fermionic anticommutation, with the spin of the field selecting one — is what the
manuscript uses to reach the spin–statistics theorem and the unusual statistics of
ghost fields. Everything above is verified by explicit $`4 \times 4` matrix
computation, `sorry`-free and `axiom`-free.
:::
