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
collapse of a posterior). The coherent-state identities themselves are now
formalized as well: the overlap, the Softmax–Born identity and the
expectation-value packaging of the attention output are theorems in `BookProof`,
and are cited section by section below. The one claim that remains a documented
proof plan is the thermal temperature identity; its statistical core is proved,
its physical derivation is not.
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

:::paragraph
Both halves of the dichotomy, and the resolution, are theorems.
`ampBorn_smul_query` is the flatness: the amplitude-squared rule is unchanged
when the query is amplified by any nonzero factor, so it has no temperature to
lower. `softmax_smul_query` says that amplifying the query in Softmax *is* a
change of inverse temperature; `scoreSoftmax_zero` is the flat extreme (at
$`\beta = 0` Softmax is uniform); and `tendsto_scoreSoftmax_max` /
`tendsto_scoreSoftmax_ne` are the sharp extreme: with a strictly best-aligned
key, its weight tends to $`1` and all others to $`0` as $`\beta \to \infty`.
Finally `tendsto_coherentBorn_smul_query` is the reconciliation: on *coherent*
states the Born rule is Softmax, so — unlike the classical rule — it does sharpen
under amplification:
:::

```
#check @BookProof.ChapterSoftmaxSharpness.ampBorn
#check @BookProof.ChapterSoftmaxSharpness.ampBorn_smul_query
#check @BookProof.ChapterSoftmaxSharpness.softmax_smul_query
#check @BookProof.ChapterSoftmaxSharpness.scoreSoftmax_zero
#check @BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_max
#check @BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_ne
#check @BookProof.ChapterSoftmaxSharpness.tendsto_coherentBorn_smul_query
#check @BookProof.ChapterSoftmaxSharpness.tendsto_coherentBorn_smul_query_ne
```

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
Bargmann–Fock space.
:::

:::paragraph
For real coherent-state parameters this is now a theorem. `coherentOverlap` is
the overlap; `coherentOverlap_eq` is its explicit coordinate formula;
`coherentOverlap_eq_gaussian` records the pleasant fact that the two baseline
penalties and the alignment reward recombine into minus one half the squared
distance, so the kernel *is* a Gaussian, `exp(-‖q-k‖²/2)`; and
`coherentOverlap_self` is the normalization `⟨q|q⟩ = 1` of a coherent state
(from which `coherentOverlap_unit` is the unit-parameter special case). The
overlap is always a strictly positive real number, never exceeding one, and
equals one exactly on the diagonal:
:::

```
#check @BookProof.ChapterCoherentOverlap.coherentOverlap
#check @BookProof.ChapterCoherentOverlap.coherentOverlap_eq
#check @BookProof.ChapterCoherentOverlap.coherentOverlap_eq_gaussian
#check @BookProof.ChapterCoherentOverlap.coherentOverlap_pos
#check @BookProof.ChapterCoherentOverlap.coherentOverlap_le_one
#check @BookProof.ChapterCoherentOverlap.coherentOverlap_self
#check @BookProof.ChapterCoherentOverlap.coherentOverlap_unit
#check @BookProof.ChapterCoherentOverlap.coherentOverlap_eq_one_iff
```

:::paragraph
The genuine Bargmann kernel takes *complex* coherent-state parameters, and then
the overlap is no longer a positive real: it acquires a phase
$`\exp(i\,\operatorname{Im}\langle q,k\rangle)`. That case is now formalized too.
`coherentOverlapC` is the complex kernel; `coherentOverlapC_eq_modulus_mul_phase`
factors it into a positive real Gaussian modulus times a pure phase, and
`norm_coherentOverlapC` computes the modulus. The real theory above is exactly
the restriction of this one to real parameters (`coherentOverlapC_ofReal`):
:::

```
#check @BookProof.ChapterCoherentOverlapComplex.coherentOverlapC
#check @BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_eq_sum
#check @BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_eq_modulus_mul_phase
#check @BookProof.ChapterCoherentOverlapComplex.norm_coherentOverlapC
#check @BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_self
#check @BookProof.ChapterCoherentOverlapComplex.norm_coherentOverlapC_le_one
#check @BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_ofReal
```

:::paragraph
The geometric reading the section relies on — a key is a wave-packet, and the
query interrogates the packets by *proximity* — is itself a theorem.
`neg_two_mul_log_coherentOverlap` says the kernel is a lossless readout of the
distance, $`-2\log\langle q|k\rangle = \|q-k\|^2`, and
`coherentOverlap_le_iff_dist_le` that the overlap is a strictly decreasing
function of that distance. Consequently the Born weight is a Softmax over minus
the squared distances — `bornWeight_eq_scoreSoftmax_neg_dist_sq`, an identity
with no hypothesis on the key norms, since the key penalties are exactly what the
squared distance absorbs — and the weights order the keys by proximity, so the
nearest key carries the largest attention:
:::

```
#check @BookProof.ChapterCoherentGeometry.neg_two_mul_log_coherentOverlap
#check @BookProof.ChapterCoherentGeometry.coherentOverlap_le_iff_dist_le
#check @BookProof.ChapterCoherentGeometry.coherentOverlap_lt_iff_dist_lt
#check @BookProof.ChapterCoherentGeometry.bornNumer_eq_exp_neg_dist_sq
#check @BookProof.ChapterCoherentGeometry.bornWeight_eq_scoreSoftmax_neg_dist_sq
#check @BookProof.ChapterCoherentGeometry.bornWeight_le_iff_dist_le
#check @BookProof.ChapterCoherentGeometry.bornWeight_max_of_nearest
#check @BookProof.ChapterCoherentGeometry.bornWeight_lt_of_nearest
```

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
This is the headline claim of the chapter, and it is now a theorem. It is a
finite algebraic identity about Gaussians and normalization.
`coherentBorn_sq_eq` is the three-factor split above. `bornWeight` is the
normalized squared overlap and `softmax` the usual attention weight at inverse
temperature `beta`; `bornWeight_sum_one` and `softmax_sum_one` say that each is
a genuine probability distribution over the keys. `coherentBorn_cancel_q` is the
cancellation of the query factor, and the headline
`coherentBorn_eq_softmax` states that under a constant key norm the two
distributions are *equal*, at inverse temperature `2`:
:::

```
#check @BookProof.ChapterSoftmaxBorn.coherentBorn_sq_eq
#check @BookProof.ChapterSoftmaxBorn.bornWeight_sum_one
#check @BookProof.ChapterSoftmaxBorn.softmax_sum_one
#check @BookProof.ChapterSoftmaxBorn.coherentBorn_cancel_q
#check @BookProof.ChapterSoftmaxBorn.coherentBorn_eq_softmax
#check @BookProof.ChapterSoftmaxBorn.coherentBorn_eq_softmax_of_unit_keys
#check @BookProof.ChapterSoftmaxBorn.coherentBorn_temperature_half
```

:::paragraph
The same headline holds for complex coherent-state parameters, and this is where
the phase earns its keep: the Born rule squares a *modulus*, so the phase of the
kernel is discarded and the surviving alignment score is the real part
$`\operatorname{Re}\langle q, k_j\rangle` — precisely the real-valued attention
logit. `bornNumerC_eq` is the complex three-factor split,
`coherentBornC_eq_softmax` the complex headline, and
`bornWeightC_phase_invariant` records that attention cannot see the phase at all:
:::

```
#check @BookProof.ChapterCoherentOverlapComplex.bornNumerC_eq
#check @BookProof.ChapterCoherentOverlapComplex.bornWeightC_sum_one
#check @BookProof.ChapterCoherentOverlapComplex.coherentBornC_cancel_q
#check @BookProof.ChapterCoherentOverlapComplex.coherentBornC_eq_softmax
#check @BookProof.ChapterCoherentOverlapComplex.coherentBornC_eq_softmax_of_unit_keys
#check @BookProof.ChapterCoherentOverlapComplex.bornWeightC_phase_invariant
#check @BookProof.ChapterCoherentOverlapComplex.bornWeightC_ofReal
```

:::paragraph
The two premises the identity rests on were already in the library: the Gaussian
as the rotation-invariant prior (the free-field construction) and the fact that
squaring a wave-function produces a genuine probability distribution (the Born
rule):
:::

```
#check @BookProof.ChapterFreeFieldGaussian.stdGaussian_map_linearIsometryEquiv
#check @BookProof.ChapterEulerNState.euler_reproduces
#check @BookProof.ChapterBornPhaseFiber.born_fiber_complex
```

:::paragraph
Between the two temperature extremes, the measurement has a rigid order
structure. `scoreSoftmax_shift` is its gauge invariance — adding a constant to
every score changes nothing, the abstract form of the cancellation of the query
penalty $`e^{-|q|^2}` in `coherentBorn_cancel_q`, so only score *differences* are
physical. `scoreSoftmax_le_iff` and `scoreSoftmax_lt_iff` say that at any
positive inverse temperature Softmax is a strictly increasing reparametrization
of the scores: it reorders nothing, and `scoreSoftmax_argmax` makes the winner
temperature-independent. `scoreSoftmax_const` is the converse warning — with no
score contrast there is nothing to sharpen, at any temperature:
:::

```
#check @BookProof.ChapterSoftmaxOrder.scoreSoftmax_sum_one
#check @BookProof.ChapterSoftmaxOrder.scoreSoftmax_le_one
#check @BookProof.ChapterSoftmaxOrder.scoreSoftmax_shift
#check @BookProof.ChapterSoftmaxOrder.scoreSoftmax_le_iff
#check @BookProof.ChapterSoftmaxOrder.scoreSoftmax_lt_iff
#check @BookProof.ChapterSoftmaxOrder.scoreSoftmax_inj_iff
#check @BookProof.ChapterSoftmaxOrder.scoreSoftmax_argmax
#check @BookProof.ChapterSoftmaxOrder.scoreSoftmax_const
#check @BookProof.ChapterSoftmaxOrder.softmax_le_iff_inner_le
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
The $`\tfrac12` is the zero-point energy of the vacuum. The *physical* derivation
of this identity — the quantum fidelity of two displaced thermal states on an
infinite-dimensional bosonic Fock space — remains a documented proof plan rather
than a proved theorem. Its *statistical core* is proved, however. For the thermal
occupation law $`\mathrm{Pr}(n) \propto (\bar n/(\bar n+1))^n`,
`thermalProb_tsum_one` says it is a probability distribution on the occupation
numbers, `thermalProb_mean` that its mean occupation really is $`\bar n`, and
`thermalProb_variance` that its variance is $`\bar n + \bar n^2` — strictly more
than the Poissonian variance $`\bar n` of a coherent state, which is the precise
sense in which the bath adds noise. At $`\bar n = 0` the temperature collapses to
the zero-point value $`\tau = 1/2`, matching the factor $`2` in the exponent of
the Softmax derived above:
:::

```
#check @BookProof.ChapterCoherentTemperature.thermalProb
#check @BookProof.ChapterCoherentTemperature.thermalProb_tsum_one
#check @BookProof.ChapterCoherentTemperature.thermalProb_mean
#check @BookProof.ChapterCoherentTemperature.thermalProb_second_moment
#check @BookProof.ChapterCoherentTemperature.thermalProb_variance
#check @BookProof.ChapterCoherentTemperature.thermalTemperature_eq_mean_add_half
#check @BookProof.ChapterCoherentTemperature.thermalTemperature_vacuum
#check @BookProof.ChapterCoherentTemperature.half_lt_thermalTemperature
```

:::paragraph
Two of the claims made in that paragraph are themselves theorems. The occupation
law of a *coherent* state is the Poisson law `p(n) = e^{-λ}λⁿ/n!`, whose variance
`coherentOccupation_variance` is exactly its mean $`\lambda` — the Poissonian
benchmark the thermal variance is compared against, and
`coherent_variance_lt_thermal_variance` records that the bath is strictly noisier
at equal mean occupation. And the split "mean occupation plus the zero-point
half" is the expectation of the harmonic-oscillator energy observable $`n +
\tfrac12`: `coherentOccupation_energy` gives $`\lambda + \tfrac12` in a coherent
state and `thermalOccupation_energy` gives $`\bar n + \tfrac12` in the thermal
state, so `thermalTemperature_eq_energy_expectation` identifies $`\tau` with a
genuine expectation value. Only the derivation of $`\tau` from the fidelity of
displaced thermal states stays a proof plan:
:::

```
#check @BookProof.ChapterCoherentOccupation.coherentOccupation
#check @BookProof.ChapterCoherentOccupation.coherentOccupation_eq_poissonPMFReal
#check @BookProof.ChapterCoherentOccupation.coherentOccupation_tsum_one
#check @BookProof.ChapterCoherentOccupation.coherentOccupation_mean
#check @BookProof.ChapterCoherentOccupation.coherentOccupation_second_moment
#check @BookProof.ChapterCoherentOccupation.coherentOccupation_variance
#check @BookProof.ChapterCoherentOccupation.coherentOccupation_energy
#check @BookProof.ChapterCoherentOccupation.thermalOccupation_energy
#check @BookProof.ChapterCoherentOccupation.thermalTemperature_eq_energy_expectation
#check @BookProof.ChapterCoherentOccupation.coherent_variance_lt_thermal_variance
```

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

:::paragraph
The "high-entropy superposition" and its collapse can be *measured*, with the
Shannon entropy $`H(p) = -\sum_j p_j \log p_j`. `shannonEntropy_le_log_card` is
Gibbs' inequality: no distribution over $`m` keys carries more uncertainty than
$`\log m`, and `shannonEntropy_uniform` shows the bound is attained. At infinite
temperature attention sits exactly there (`shannonEntropy_scoreSoftmax_zero`): the
query resolves nothing. `tendsto_shannonEntropy_scoreSoftmax` is the collapse —
when the scores have a strict maximizer, the entropy of the attention
distribution tends to zero as the temperature does — and
`tendsto_shannonEntropy_bornWeight_smul_query` states the same for the
coherent-state Born weights as the query is amplified:
:::

```
#check @BookProof.ChapterAttentionEntropy.shannonEntropy
#check @BookProof.ChapterAttentionEntropy.shannonEntropy_nonneg
#check @BookProof.ChapterAttentionEntropy.shannonEntropy_le_log_card
#check @BookProof.ChapterAttentionEntropy.shannonEntropy_uniform
#check @BookProof.ChapterAttentionEntropy.shannonEntropy_scoreSoftmax_zero
#check @BookProof.ChapterAttentionEntropy.shannonEntropy_scoreSoftmax_le_log_card
#check @BookProof.ChapterAttentionEntropy.tendsto_shannonEntropy_scoreSoftmax
#check @BookProof.ChapterAttentionEntropy.tendsto_shannonEntropy_bornWeight_smul_query
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
before there was maximum relational uncertainty. This too is now a theorem.
`observableExpectation` is the probability-weighted sum of eigenvalues, and
`attention_eq_expectation` states that the Born weights are a probability
distribution and that the attention output is exactly that expectation value.
`prob_weighted_sum_mem_convexHull` and `attention_mem_convexHull` express the
"definiteness": the output never leaves the convex hull of the possible outcomes:
:::

```
#check @BookProof.ChapterObservableExpectation.observableExpectation
#check @BookProof.ChapterObservableExpectation.observableExpectation_scalar
#check @BookProof.ChapterObservableExpectation.attention_eq_expectation
#check @BookProof.ChapterObservableExpectation.prob_weighted_sum_mem_convexHull
#check @BookProof.ChapterObservableExpectation.attention_mem_convexHull
#check @BookProof.ChapterObservableExpectation.attention_eq_softmax_expectation
#check @BookProof.ChapterObservableExpectation.bayes_posterior_expectation_mem_convexHull
```

:::paragraph
The observable itself can be built, not merely its spectral data. `observableOp`
is the finite-dimensional operator $`\hat V = \sum_j v_j |k_j\rangle\langle k_j|`;
`observableOp_isHermitian` says it is a genuine observable when the eigenvalues
are real; `bornProb` is the Born statistics $`p_j = |\langle k_j|q\rangle|^2` of
measuring it in the state $`|q\rangle`, a probability distribution whenever the
eigenvectors are an orthonormal basis and the state is a unit vector
(`bornProb_sum_one`, Parseval); and `observableOp_expectation` is the identity
$`\langle q|\hat V|q\rangle = \sum_j p_j v_j` for the operator itself:
:::

```
#check @BookProof.ChapterObservableOperator.observableOp
#check @BookProof.ChapterObservableOperator.observableOp_isHermitian
#check @BookProof.ChapterObservableOperator.expectation_outerProj
#check @BookProof.ChapterObservableOperator.bornProb_sum_one
#check @BookProof.ChapterObservableOperator.observableOp_expectation
#check @BookProof.ChapterObservableOperator.observableOp_expectation_real
#check @BookProof.ChapterObservableOperator.observableOp_expectation_mem_convexHull
#check @BookProof.ChapterObservableOperator.observable_expectation_born
```

:::paragraph
It rests on the conditional / expectation structure already in the library:
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
Bayesian updates. Of the two new identifiers this chapter
contributes, the first — the coherent overlap with its Softmax consequence — is
now proved, in `BookProof.ChapterCoherentOverlap`,
`BookProof.ChapterSoftmaxBorn` and `BookProof.ChapterObservableExpectation`. The
second, the temperature identity $`\tau = \bar n + \tfrac12`, is proved in its
statistical core (`BookProof.ChapterCoherentTemperature`) and in its
occupation-statistics reading (`BookProof.ChapterCoherentOccupation`: coherent
light is Poissonian with variance $`\bar n`, and $`\tau` is the expectation of the
energy observable $`n + \tfrac12`); its physical derivation from the fidelity of
displaced thermal states remains a precise proof plan in {ref "proof-plans"}[the
appendix]. The two caveats the first draft of this chapter carried have since been
discharged: the complex Bargmann kernel, with its phase, is formalized in
`BookProof.ChapterCoherentOverlapComplex`, and the observable is built as an
operator, not merely as spectral data, in
`BookProof.ChapterObservableOperator`. The surrounding structure — the
flat-versus-sharp dichotomy (`BookProof.ChapterSoftmaxSharpness`), the geometry of
the wave-packets (`BookProof.ChapterCoherentGeometry`), the order structure of the
measurement (`BookProof.ChapterSoftmaxOrder`) and the entropy of the collapse
(`BookProof.ChapterAttentionEntropy`) — is proved as well. Everything else here is
backed by existing theorems in `BookProof`.
:::