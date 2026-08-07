import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Coherent State of Attention" =>
%%%
tag := "coherent-state-attention"
%%%

:::paragraph
The Softmax attention mechanism of the Transformer is usually introduced as an
engineering trick: a dot product measures compatibility between a query and a key,
and the exponential Softmax squashes those scores into a probability distribution.
This chapter argues that the trick is not arbitrary. When the objects being
measured are *coherent states* — the most classical-like states of a quantum
harmonic oscillator — the Softmax function and the quantum Born rule are the
*same equation*. The classical
sharpness of attention is the natural consequence of measuring the overlap of
Gaussian wave-packets in a quantum phase space.
:::

:::paragraph
This chapter is a conceptual bridge between the probability-theoretic core of the
book and machine learning. It reuses the tools already formalized in the
{ref "born-reproduces"}[Born-rule chapter] (a probability distribution is the
squared modulus of a wave-function), the {ref "free-field"}[free-field chapter]
(the Gaussian as the canonical rotation-invariant prior), and the
{ref "aligned-deep-learning"}[deep-learning chapter] (Bayesian updating as the
collapse of a posterior). The coherent-state identities themselves are *not yet
formalized*; this chapter states them precisely and gives proof plans in
{ref "proof-plans"}[the appendix], exactly as the book does for every open claim.
:::

# The Divergence: Classical Sharpness versus Quantum Flatness

:::paragraph
For years, the natural proposal for a "quantum attention" was to treat the dot
product $`q \cdot k` as a probability *amplitude* and apply Born's rule — the
normalized squared modulus:
:::

$$`P(q \to k) = \frac{|q \cdot k|^2}{\sum_j |q \cdot k_j|^2}.`$$

:::paragraph
This is beautiful but behaves differently from Softmax. Squaring creates a flat,
polynomial curve that spreads probability across many tokens; exponentiating
$`e^{q \cdot k}` creates a sharp, winner-takes-all distribution. The dichotomy
rests on a single assumption: that a word is a classical *point*. If instead a
word is a *wave-packet*, the two regimes coincide.
:::

# The Geometry of the Wave-packet

:::paragraph
Map the latent space of the network onto a Bosonic Fock space and represent each
query and key as the parameter of a *coherent state* $`|q\rangle, |k\rangle` —
a localized wave-packet, the "most classical" quantum state. The overlap of two
coherent states is Gaussian:
:::

$$`\langle q | k \rangle = \exp\!\Big(-\tfrac12 |q|^2 - \tfrac12 |k|^2 + q \cdot k\Big).`$$

:::paragraph
The baseline magnitudes $`|q|^2, |k|^2` pull the amplitude down; their alignment
$`q \cdot k` pushes it up. This is the *reproducing kernel* of the
Bargmann–Fock space, and it is the object the formalization will make precise.
:::

# Softmax Is the Born Rule on Coherent States

:::paragraph
Apply the Born rule to the overlap. Squaring the exponential multiplies its
exponent by two, and the laws of exponents split the result into three factors:
:::

$$`|\langle q | k \rangle|^2
  = \exp(-|q|^2)\cdot\exp(-|k|^2)\cdot\exp(2\,q \cdot k).`$$

:::paragraph
Normalizing across the keys completes the Born rule. The term $`\exp(-|q|^2)` is
constant for the row and cancels between numerator and denominator. In modern
Transformers the keys are normalized (LayerNorm or RMSNorm), so each
$`\exp(-|k_j|^2)` is also a fixed constant and factors out too. What remains is
exactly Softmax attention:
:::

$$`\text{Attention Weight} = \frac{\exp(2\,q \cdot k_j)}{\sum_l \exp(2\,q \cdot k_l)}.`$$

:::paragraph
This is the headline claim of the chapter. It is a finite algebraic identity about
Gaussians and normalization, and it is the natural first formalization target (see
{ref "proof-plans"}[the appendix]). The *verified* ingredients already in the
library are the two premises it rests on: the Gaussian as the rotation-invariant
prior (the free-field construction) and the fact that squaring a wave-function
produces a genuine probability distribution (the Born rule):
:::

```
#check @BookProof.ChapterFreeFieldGaussian.stdGaussian_map_linearIsometryEquiv
#check @BookProof.ChapterEulerNState.euler_reproduces
#check @BookProof.ChapterBornPhaseFiber.born_fiber_complex
```

# Temperature and the Thermal Bath

:::paragraph
In the standard Transformer, the dot product is divided by a temperature
$`\tau` that controls randomness. The derivation above produced a natural factor
$`2` in the exponent, so a standard LLM operates at a baseline temperature
$`\tau = 0.5`. The manuscript interprets this in two regimes. In the *pure quantum*
regime, the wave-packet variance is bounded by the Heisenberg limit
$`\sigma^2 = \hbar/2m\omega`, and lowering the temperature is increasing the
mass/frequency of the oscillator. In the *thermodynamic* regime — a displaced
thermal state at temperature $`T > 0` with $`\bar n` background thermal bosons —
the fidelity of the thermal states introduces the noise directly into the exponent:
:::

$$`\tau = \bar n + \tfrac12.`$$

:::paragraph
The $`\tfrac12` is the zero-point energy of the vacuum. This identity is a thermal
/ statistical-mechanics computation and is currently a documented proof plan rather
than a proved theorem.
:::

# Informational Superposition and the Unknown Output

:::paragraph
Attention ends with an aggregation of *Value* vectors:
:::

$$`\mathbf{o}_i = \sum_j a_{ij}\,\mathbf{v}_j.`$$

:::paragraph
The physics of this output is the physics of a datum before measurement. A
single patch of an image — a straight grey line — is ambiguous in isolation: it
could be the edge of a skyscraper, the leg of a table, or a shadow. The token's
initial embedding is a *prior state*: a high-entropy superposition of possible
structural meanings drawn from the global distribution of the training data. This
is precisely the manuscript's thesis that the *global topology of the surrounding
data acts as the measurement apparatus*: the query, broadcast across the sequence,
is measured against the keys by a Quantum Bayesian update. The verified content
here is the Bayesian machine itself — belief update by normalization, and the
transport of a prior along a mechanism:
:::

```
#check @BookProof.ChapterKernelTransport.kernel_transport_isProbability
#check @BookProof.ChapterKernelTransport.kernel_transport_apply
#check @BookProof.ChapterBayesInference.posterior
#check @BookProof.ChapterBayesInference.posterior_sum_one
#check @BookProof.ChapterBayesInference.exists_unitary_reproduces_posterior
```

# The Posterior: Observable Operators and Expectation Values

:::paragraph
To define the output physically, introduce the quantum notion of an *observable
operator*. By the spectral theorem an operator is fixed by its outcomes
$`|k_j\rangle` and their eigenvalues $`\mathbf{v}_j`:
:::

$$`\hat V = \sum_j \mathbf{v}_j\,|k_j\rangle\langle k_j|.`$$

:::paragraph
The environment acts as an informational observable: the keys are the eigenstates
of the apparatus, and the values are the multi-dimensional eigenvalues. Once the
Born-rule measurement yields the posterior $`p_j`, the expectation value of the
observable over that distribution is the probability-weighted sum of eigenvalues:
:::

$$`\langle \hat V \rangle = \sum_j p_j\,\mathbf{v}_j.`$$

:::paragraph
This is structurally identical to the attention output $`\mathbf{o}_i =
\sum_j a_{ij}\,\mathbf{v}_j`. The output of attention is the expectation value of
a contextual observable over the collapsed posterior — a *definite* vector where
before there was maximum relational uncertainty. The finite, verified core of this
is the conditional / expectation structure already in the library:
:::

```
#check @BookProof.ChapterConditional.pCond_nonneg
#check @BookProof.ChapterConditional.pCond_sum_one
#check @BookProof.ChapterConditional.pJoint_eq_cond_mul_marg
#check @BookProof.ChapterBayesInference.posterior_eq_joint_div_evidence
```

# The Deep Cascade: Successive Bayesian Updates

:::paragraph
If the uncertainty is neutralized in a single layer, why do deep networks need
many? Because reality is hierarchically complex. The definite output of layer one
becomes the certain input (the new prior) of layer two, which now faces a
*new*, higher-level uncertainty. The deep network is a *cascading succession of
complete Bayesian updates*: each layer collapses a wave-function over its context
and restores certainty as an expectation value. The verified facts that make this
coherent are the associativity of Bayesian updating and the collapse of a hierarchy
into a single kernel:
:::

```
#check @BookProof.ChapterSequentialBayes.sequential_eq_batch
#check @BookProof.ChapterSequentialBayes.posterior_sequential_eq_batch
#check @BookProof.ChapterHierarchicalBayes.outerPosterior_eq_bayesUpdate
#check @BookProof.ChapterHierarchicalBayes.outerPosterior_eq_sum_flat
#check @BookProof.ChapterHierarchicalBayesComposition.compKernel_assoc
```

# Summary

:::paragraph
The forward pass of a deep model is not an arbitrary sequence of matrix products.
Setting the objects being measured to be coherent states, the Softmax attention
weight is the Born rule, the aggregated output is the expectation value of a
contextual observable over a posterior, and stacking layers executes a cascade of
Bayesian updates. The two new identifiers this chapter contributes — the coherent
overlap with its Softmax consequence, and the temperature identity — are stated as
precise proof plans in {ref "proof-plans"}[the appendix]. Everything else here is
backed by existing theorems in `BookProof`.
:::