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

:::paragraph
Parametrized by the physical temperature the same law becomes the textbook one.
Writing $`x = \hbar\omega/kT` for the dimensionless inverse temperature, the mean
occupation is the Bose–Einstein function $`\bar n(x) = 1/(e^{x}-1)`, the level
probabilities are exactly the Boltzmann–Gibbs weights
$`\Pr(n) = (1-e^{-x})e^{-nx}`, and the chapter's temperature has the closed form
$`\tau(x) = \bar n(x) + \tfrac12 = \tfrac12\coth(x/2)`, decreasing to the pure
zero-point value $`\tfrac12` as the mode is cooled:
:::

```
#check @BookProof.ChapterBoseEinstein.boseEinstein
#check @BookProof.ChapterBoseEinstein.thermalRatio_boseEinstein
#check @BookProof.ChapterBoseEinstein.thermalProb_boseEinstein
#check @BookProof.ChapterBoseEinstein.boseEinstein_mean
#check @BookProof.ChapterBoseEinstein.boseEinstein_strictAntiOn
#check @BookProof.ChapterBoseEinstein.thermalTemperature_boseEinstein
#check @BookProof.ChapterBoseEinstein.thermalTemperature_boseEinstein_eq_coth
#check @BookProof.ChapterBoseEinstein.tendsto_thermalTemperature_boseEinstein
```

:::paragraph
Why *that* law, and not another distribution with the same mean? Because it is
the one of maximal Shannon entropy: among occupation distributions with a
prescribed mean occupation $`\bar n`, the thermal law maximizes
$`-\sum_n p_n \log p_n`. This is the variational reason the bath is a *thermal*
bath, and it is proved by the pointwise Gibbs inequality:
:::

```
#check @BookProof.ChapterThermalMaxEntropy.thermalEntropy
#check @BookProof.ChapterThermalMaxEntropy.thermalEntropy_eq
#check @BookProof.ChapterThermalMaxEntropy.thermalEntropy_boseEinstein
#check @BookProof.ChapterThermalMaxEntropy.gibbs_pointwise
#check @BookProof.ChapterThermalMaxEntropy.shannonEntropy_le_thermalEntropy
```

:::paragraph
The identity $`\tau = \bar n + \tfrac12` can now be read off the *physical*
parametrization rather than posited. Writing the occupation law through its
ratio $`r` instead of its mean, its first two moments are the geometric ones
($`\bar n = r/(1-r)`, variance $`r/(1-r)^2`), the energy expectation
$`\sum_n (n+\tfrac12)p_n` never drops below $`\tfrac12` — with equality exactly
at the vacuum, which is what the extra half measures — and the closed form
$`\tfrac12\coth(x/2)` *equals* the mean occupation plus that half:
:::

```
#check @BookProof.ChapterThermalTemperatureCore.geometricOccupancy
#check @BookProof.ChapterThermalTemperatureCore.geometricOccupancy_mean
#check @BookProof.ChapterThermalTemperatureCore.geometricOccupancy_variance
#check @BookProof.ChapterThermalTemperatureCore.half_integer_floor
#check @BookProof.ChapterThermalTemperatureCore.thermal_temperature_eq_mean_half
```

:::paragraph
The last step is the *physical* one: the temperature must come out of the state
itself, not out of a fit. Model the bath mode in phase space, where a displaced
thermal state is the vacuum's zero-point noise (variance $`\tfrac12`) convolved
with thermal noise of variance $`\bar n` and recentred at the displacement $`a`.
Convolution adds variances, so the width of the displaced thermal state is
$`\tau = \bar n + \tfrac12` — the mean occupation plus the zero-point half — and
it does not depend on where the state sits:
:::

```
#check @BookProof.ChapterDisplacedThermalOverlap.displacedThermal
#check @BookProof.ChapterDisplacedThermalOverlap.thermal_plus_zeroPoint_conv
#check @BookProof.ChapterDisplacedThermalOverlap.displacedThermal_mean
#check @BookProof.ChapterDisplacedThermalOverlap.displacedThermal_variance
```

:::paragraph
The overlap of two such states is then a Gaussian in the phase-space distance
alone, $`\exp(-(a-b)^2/4\tau)/\sqrt{4\pi\tau}`: it is strictly positive, and it
is strictly larger for the nearer of two keys. Normalizing the overlaps of a
query against a family of keys therefore reproduces the Softmax *exactly*, at
inverse temperature $`\beta = 1/(4\tau)` — which is maximal at the vacuum and
falls monotonically as the bath heats up. A hotter bath is a flatter attention.
:::

```
#check @BookProof.ChapterDisplacedThermalOverlap.dtOverlap_eq
#check @BookProof.ChapterDisplacedThermalOverlap.dtOverlap_pos
#check @BookProof.ChapterDisplacedThermalOverlap.dtOverlap_lt_of_dist_lt
#check @BookProof.ChapterDisplacedThermalOverlap.inverseTemperature
#check @BookProof.ChapterDisplacedThermalOverlap.inverseTemperature_zero
#check @BookProof.ChapterDisplacedThermalOverlap.inverseTemperature_strictAnti
#check @BookProof.ChapterDisplacedThermalOverlap.dtBorn_eq_softmax
#check @BookProof.ChapterDisplacedThermalOverlap.dtBorn_temperature_coth
```

:::paragraph
Nothing about this is one-dimensional. With $`n` modes the overlap factorizes
across modes, the exponent becomes the squared Euclidean distance of the
phase-space vectors, and the Born weights are again a Softmax at the same
inverse temperature. At zero occupation the bath disappears and the multi-mode
Born weights coincide — after the usual $`\sqrt2` change between the quadrature
variable and the dimensionless coherent parameter — with the coherent-state Born
weights this chapter began with. The thermal picture *contains* the pure one:
:::

```
#check @BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_eq_integral
#check @BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_eq
#check @BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_pos
#check @BookProof.ChapterDisplacedThermalMulti.dtBornMulti_eq_softmax
#check @BookProof.ChapterDisplacedThermalMulti.dtBornMulti_vacuum_eq_bornWeight
```

:::paragraph
Two states are compared, in quantum mechanics, by their *fidelity*: the
probability that a system prepared as $`|q\rangle` is found in $`|k\rangle`. For
coherent states the fidelity collapses to a single number — the Gaussian of the
distance between the two displacement parameters. The Bargmann phase cancels, and
so do the individual norms; the fidelity is symmetric, never exceeds one, equals
one only for identical parameters, and is unchanged when both states are
displaced together. Attention is exactly the normalized fidelity:
:::

```
#check @BookProof.ChapterCoherentFidelity.fidelityC
#check @BookProof.ChapterCoherentFidelity.fidelityC_eq_exp_neg_dist_sq
#check @BookProof.ChapterCoherentFidelity.fidelityC_symm
#check @BookProof.ChapterCoherentFidelity.fidelityC_eq_one_iff
#check @BookProof.ChapterCoherentFidelity.fidelityC_translation_invariant
#check @BookProof.ChapterCoherentFidelity.bornWeightC_eq_fidelity_normalized
```

:::paragraph
Once the temperature is a physical parameter one can *differentiate* by it. The
attention head has a partition function $`Z(\beta) = \sum_j e^{\beta s_j}`, and the
first derivative of its logarithm is the attention-weighted mean score. The
second is the variance. That is the fluctuation–response law: sharpening the
attention raises the mean alignment at a rate equal to the variance of the scores
under the current attention distribution — and the response is zero exactly when
all the keys already score alike.
:::

```
#check @BookProof.ChapterSoftmaxFluctuation.hasDerivAt_logPartition
#check @BookProof.ChapterSoftmaxFluctuation.hasDerivAt_scoreSoftmax
#check @BookProof.ChapterSoftmaxFluctuation.hasDerivAt_meanScore
#check @BookProof.ChapterSoftmaxFluctuation.varScore_eq_zero_iff
#check @BookProof.ChapterSoftmaxFluctuation.meanScore_monotone
```

:::paragraph
This also answers *why Softmax and not some other normalization*. Among all
attention distributions with a prescribed mean alignment score, the Softmax
distribution is the one of largest Shannon entropy — the least committed
distribution compatible with what the alignment says. Equivalently, it minimises
the free energy $`\beta\langle s\rangle_p - H(p)`, and the minimum is
$`-\log Z(\beta)`:
:::

```
#check @BookProof.ChapterSoftmaxMaxEntropy.shannonEntropy_le_crossEntropy
#check @BookProof.ChapterSoftmaxMaxEntropy.shannonEntropy_scoreSoftmax
#check @BookProof.ChapterSoftmaxMaxEntropy.shannonEntropy_le_of_meanScore_eq
#check @BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_le
#check @BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_eq
```

:::paragraph
And the entropy itself now has a law of motion. Differentiating the
thermodynamic identity $`H(\beta) = \log Z(\beta) - \beta\langle s\rangle_\beta`
gives $`dH/d\beta = -\beta\,\mathrm{Var}_\beta(s)`, so the attention entropy is
non-increasing for $`\beta \ge 0`: cooling the head can only destroy entropy. The
endpoints already computed — $`\log m` at infinite temperature, $`0` in the
argmax limit — are now joined by a monotone path:
:::

```
#check @BookProof.ChapterEntropyTemperature.attentionEntropy_eq
#check @BookProof.ChapterEntropyTemperature.hasDerivAt_attentionEntropy
#check @BookProof.ChapterEntropyTemperature.heatCapacity_nonneg
#check @BookProof.ChapterEntropyTemperature.attentionEntropy_antitoneOn
#check @BookProof.ChapterEntropyTemperature.attentionEntropy_le_log_card
```

:::paragraph
Two temperatures give two attention distributions over the same keys, and the
natural way to compare them is the relative entropy. It has a closed form: the
divergence between the heads at inverse temperatures $`\beta` and $`\gamma` is the
*Bregman divergence of the free energy*,
$`\mathrm{KL}(p_\beta \| p_\gamma) = \log Z(\gamma) - \log Z(\beta) -
(\gamma - \beta)\langle s\rangle_\beta`. Since a relative entropy is never
negative, the free energy lies above each of its tangent lines. The same variance
that measured the response is also the Fisher information of the family, so the
statistical curvature of attention and its physical fluctuation are one quantity:
:::

```
#check @BookProof.ChapterSoftmaxDivergence.klDiv
#check @BookProof.ChapterSoftmaxDivergence.klDiv_nonneg
#check @BookProof.ChapterSoftmaxDivergence.klDiv_scoreSoftmax
#check @BookProof.ChapterSoftmaxDivergence.logPartition_tangent_le
#check @BookProof.ChapterSoftmaxDivergence.fisherInformation_eq_varScore
```

:::paragraph
Reading the tangent inequality globally: the free energy is a convex function of
the inverse temperature — strictly convex as soon as two keys score differently —
and it is the Legendre transform of the entropy, the largest value of
$`\beta\langle s\rangle_p + H(p)` over all attention distributions:
:::

```
#check @BookProof.ChapterLogPartitionConvex.hasDerivAt_deriv_logPartition
#check @BookProof.ChapterLogPartitionConvex.convexOn_logPartition
#check @BookProof.ChapterLogPartitionConvex.strictConvexOn_logPartition
#check @BookProof.ChapterLogPartitionConvex.logPartition_isGreatest
```

:::paragraph
Finally, the kernel that started the chapter need not be taken on faith. Writing
the coherent state centred at $`a` as the position-space wave packet
$`\psi_a(x) = \pi^{-1/4}e^{-(x-a)^2/2}`, the packet is normalized, and its
$`L^2(\mathbb{R})` inner product with a second packet is
$`e^{-(a-b)^2/4}` — a Gaussian in the distance between the centres. Squaring it
recovers, exactly, the reproducing kernel taken as the definition above, so the
position-space Born weights of a query packet against a family of key packets are
Softmax attention over minus the squared distances:
:::

```
#check @BookProof.ChapterCoherentPositionSpace.gaussianPacket
#check @BookProof.ChapterCoherentPositionSpace.gaussianPacket_sq_integral
#check @BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner
#check @BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_sq_eq_coherentOverlap
#check @BookProof.ChapterCoherentPositionSpace.packetBorn_eq_scoreSoftmax
```

:::paragraph
One last property is needed before any of this is usable: the measurement must be
*stable*. If every alignment score is known only up to an error $`d`, no attention
weight can move by more than the factor $`e^{2|\beta| d}` — one factor of
$`|\beta| d` for the key's own score, one for the normalizing free energy — and
hence by no more than $`e^{2|\beta| d} - 1` in absolute terms. Cooling the head
(large $`\beta`) is exactly what makes it fragile:
:::

```
#check @BookProof.ChapterSoftmaxStability.abs_logPartition_sub_le
#check @BookProof.ChapterSoftmaxStability.abs_log_scoreSoftmax_sub_le
#check @BookProof.ChapterSoftmaxStability.scoreSoftmax_le_mul
#check @BookProof.ChapterSoftmaxStability.abs_scoreSoftmax_sub_le
```

:::paragraph
Stability in the scores has an exact differential form. Nudging the alignment
score of one key moves the free energy at the rate $`\partial \log Z/\partial s_i
= \beta p_i` — the attention weight of a key *is* the sensitivity of the free
energy to that key's score — and it moves the weights themselves by the Softmax
Jacobian $`\partial p_j/\partial s_i = \beta\,p_j(\delta_{ij} - p_i)`. That matrix
is symmetric (it is a Hessian), each of its rows sums to zero (a key can only
gain what the others lose), and its quadratic form is $`\beta` times an
attention-weighted variance — positive semidefinite for $`\beta \ge 0`, and equal
to $`\beta\,\mathrm{Var}_\beta(s)` on the scores themselves. This is the same
fluctuation that governed the temperature derivative, seen from the score
direction:
:::

```
#check @BookProof.ChapterSoftmaxJacobian.hasDerivAt_logPartition_score
#check @BookProof.ChapterSoftmaxJacobian.hasDerivAt_scoreSoftmax_score
#check @BookProof.ChapterSoftmaxJacobian.softmaxJacobian_symm
#check @BookProof.ChapterSoftmaxJacobian.softmaxJacobian_row_sum_zero
#check @BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form
#check @BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form_score
```

:::paragraph
The head also never attends to everything: a *mask* restricts the sum to an
admissible set of keys, the causal mask $`\{l \le i\}` being the standard case.
Masking is not a new ingredient — it is Bayesian conditioning. On the admissible
set the masked weight is the unmasked weight renormalized by the total unmasked
weight of that set, $`p(j\mid S) = p(j)/p(S)`; the odds between two admissible
keys are untouched, so a mask removes keys without re-ranking them; and
conditioning twice is conditioning once, so a composite mask is a single mask:
:::

```
#check @BookProof.ChapterAttentionMasking.maskedSoftmax_sum_one
#check @BookProof.ChapterAttentionMasking.maskedSoftmax_eq_conditional
#check @BookProof.ChapterAttentionMasking.maskedSoftmax_odds
#check @BookProof.ChapterAttentionMasking.maskedSoftmax_restrict
#check @BookProof.ChapterAttentionMasking.causalSoftmax_eq_zero_of_lt
```

:::paragraph
Two independent modes never entangle the measurement. If the alignment score of a
product key is the sum of its per-mode scores — which is what a product coherent
state gives — then the joint attention distribution is exactly the product of the
single-mode ones, its marginals are the single-mode distributions, and the
attention entropy is additive:
:::

```
#check @BookProof.ChapterAttentionFactorization.prodSoftmax_eq_mul
#check @BookProof.ChapterAttentionFactorization.prodSoftmax_marginal_left
#check @BookProof.ChapterAttentionFactorization.shannonEntropy_prodSoftmax
```

:::paragraph
Finally, the whole construction has a symmetry group, and it is the physical one.
The Bargmann kernel sees only norms and inner products, so a common unitary change
of frame on the query and every key changes no weight. Free harmonic evolution
$`\alpha \mapsto e^{-i\omega t}\alpha` is such a unitary: *attention is a constant
of the motion*. And a common Weyl displacement of query and keys leaves the
weights alone as well, so only relative positions in phase space are physical:
:::

```
#check @BookProof.ChapterCoherentDynamics.coherentOverlapC_isometry
#check @BookProof.ChapterCoherentDynamics.bornWeightC_isometry
#check @BookProof.ChapterCoherentDynamics.bornWeightC_evolution_const
#check @BookProof.ChapterCoherentDynamics.fidelityC_phaseRotate
#check @BookProof.ChapterCoherentDynamics.bornWeightC_translation_invariant
```

:::paragraph
Position is part of the same story. The rotary encoding rotates the $`i`-th
complex coordinate of a token by an angle proportional to its position,
$`q \mapsto (e^{i p \omega_i} q_i)_i`. It is a unitary, it composes additively in
the position, and — the property that makes it work — the alignment of a query at
position $`a` with a key at position $`b` depends on the two positions *only*
through the offset $`b - a`. Absolute position is unobservable; translating the
whole sequence changes no attention weight:
:::

```
#check @BookProof.ChapterRotaryPosition.norm_rotaryEncode
#check @BookProof.ChapterRotaryPosition.rotaryEncode_add
#check @BookProof.ChapterRotaryPosition.inner_rotaryEncode
#check @BookProof.ChapterRotaryPosition.coherentOverlapC_rotaryEncode
#check @BookProof.ChapterRotaryPosition.bornWeightC_rotaryEncode_shift
```

:::paragraph
The winner-takes-all law of the previous sections is a limit, and a memory that
only works in the limit is no memory. At a *fixed* temperature the same statement
is quantitative. Suppose the query beats every rival key by a score margin
$`\delta`. Then each distractor keeps at most $`e^{-\beta\delta}` of the
attention, the total leakage off the target is at most $`(m-1)e^{-\beta\delta}`,
the target itself holds at least $`1/(1 + (m-1)e^{-\beta\delta})`, and the head's
output differs from the stored value by at most $`2C(m-1)e^{-\beta\delta}`. An
attention head is an associative memory whose recall error decays exponentially in
$`\beta\delta`:
:::

```
#check @BookProof.ChapterAttentionRetrieval.scoreSoftmax_le_exp_neg_margin
#check @BookProof.ChapterAttentionRetrieval.one_sub_scoreSoftmax_le_of_margin
#check @BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_inv_of_margin
#check @BookProof.ChapterAttentionRetrieval.norm_headOutput_sub_le_of_margin
#check @BookProof.ChapterAttentionRetrieval.bornWeight_ge_of_dist_margin
```

:::paragraph
The converse bound is just as physical: at any finite temperature *nothing is ever
completely ignored*. If the scores lie within a spread $`D`, every key retains at
least $`e^{-\beta D}/m` of the attention. Collapse onto a single key is a
zero-temperature idealization, never an event at finite $`\beta`:
:::

```
#check @BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_of_spread
```

:::paragraph
The measurement is also blind to the order of the keys. Relabelling the key/value
pairs by a permutation relabels the weights the same way and leaves the output,
and the attention entropy, exactly where they were: a head reads its context as a
*set* of pairs, not as a list. This is the discrete half of the symmetry group
whose continuous half — unitary frame changes, free evolution, Weyl displacement —
appeared above:
:::

```
#check @BookProof.ChapterAttentionEquivariance.scoreSoftmax_perm
#check @BookProof.ChapterAttentionEquivariance.headOutput_perm
#check @BookProof.ChapterAttentionEquivariance.attentionOutput_perm
#check @BookProof.ChapterAttentionEquivariance.shannonEntropy_scoreSoftmax_perm
```

:::paragraph
A layer runs many heads at once, and a bank of heads is a *mixture* of Born
measurements. The mixture of attention distributions is again an attention
distribution; reading the values once against the mixed distribution is the same
as reading them head by head and averaging, which is what licenses the usual
"combine the heads" construction; and — by concavity of $`-x\log x` — the entropy
of the consensus is at least the mean entropy of the heads. Confident heads that
disagree produce an uncertain layer, never the reverse:
:::

```
#check @BookProof.ChapterAttentionMixture.mixture_isProb
#check @BookProof.ChapterAttentionMixture.observableExpectation_mixture
#check @BookProof.ChapterAttentionMixture.multiHead_output_eq_mean
#check @BookProof.ChapterAttentionMixture.le_shannonEntropy_mixture
```

:::paragraph
Finally, if attention is the Born rule then *training* it is fitting a Born
probability to an observed outcome. The criterion is the surprisal of the observed
key, $`L = \log Z_\beta(s) - \beta s_y = -\log p_\beta(y)` — the free energy minus
the energy of the realized outcome — which is nonnegative and vanishes exactly
when the layer already places all of its weight there. Its score derivative is the
textbook backpropagation rule $`\partial L/\partial s_i = \beta(p_i -
\delta_{iy})`, obtained here from the free-energy derivative above; the gradient
sums to zero over the keys, so learning *transfers* attention rather than creating
it, and the gauge freedom $`s \mapsto s + c` is never excited. In the temperature
the loss is convex, so temperature fitting has no spurious minima:
:::

```
#check @BookProof.ChapterCrossEntropyGradient.crossEntropyLoss_eq_neg_log
#check @BookProof.ChapterCrossEntropyGradient.crossEntropyLoss_nonneg
#check @BookProof.ChapterCrossEntropyGradient.hasDerivAt_crossEntropyLoss_score
#check @BookProof.ChapterCrossEntropyGradient.crossEntropyGradient_sum_zero
#check @BookProof.ChapterCrossEntropyGradient.convexOn_crossEntropyLoss
```

:::paragraph
How many keys is a head actually reading? The Shannon entropy answers in nats; the
practitioner's answer is a *count*, the participation ratio $`N_{\mathrm{eff}} =
1/\sum_j p_j^2`, the exponential of the Rényi-2 (collision) entropy. It behaves as a
count must: it lies between $`1` and the number of keys, it equals the number of
keys exactly at infinite temperature, and — because the collision entropy never
exceeds the Shannon entropy — it never overstates how much of the context is being
used:
:::

```
#check @BookProof.ChapterAttentionCollision.effectiveSupport_scoreSoftmax_mem_Icc
#check @BookProof.ChapterAttentionCollision.effectiveSupport_scoreSoftmax_zero
#check @BookProof.ChapterAttentionCollision.renyi2_le_shannonEntropy
```

:::paragraph
The same counting works from the other side. A Markov bound on the Born
distribution says that at most $`1/t` keys can carry weight $`t` or more, so only a
handful of keys can ever matter at once; some key always carries at least the
uniform share $`1/m`; and the min-entropy bound $`-\log p_{\max} \le H` says that a
low-entropy head necessarily has a dominant key, $`p_{\max} \ge e^{-H}`, whose
reciprocal is a lower bound for the participation ratio:
:::

```
#check @BookProof.ChapterAttentionConcentration.card_filter_le_inv
#check @BookProof.ChapterAttentionConcentration.exists_inv_card_le
#check @BookProof.ChapterAttentionConcentration.neg_log_le_shannonEntropy
#check @BookProof.ChapterAttentionConcentration.inv_le_effectiveSupport
```

:::paragraph
Read row by row, a layer is a *stochastic matrix*: row $`i` is the Born
distribution of the query at position $`i`. Pushing a belief about position through
the layer is then a Markov step, stacking layers composes the kernels, and a step
never increases the $`\ell^1` discrepancy between two beliefs. More: at a finite
temperature every entry of the kernel is bounded below, and the Doeblin argument
turns that into a strict contraction — with a score spread $`D` a layer contracts
by $`1 - e^{-\beta D}`. Deep stacks of attention *forget* their input geometrically
fast unless the scores are allowed to spread with depth:
:::

```
#check @BookProof.ChapterAttentionMarkov.attentionMatrix_isStochastic
#check @BookProof.ChapterAttentionMarkov.push_compose
#check @BookProof.ChapterAttentionMarkov.l1dist_push_le
#check @BookProof.ChapterAttentionMarkov.l1dist_push_attentionMatrix_le
```

:::paragraph
Finally, the $`1/\sqrt d` that every implementation writes into the score. Model an
unstructured query as a uniform sign pattern $`q \in \{\pm 1\}^d`. Against a fixed
key the raw score $`\langle q,k\rangle` has mean zero and mean square $`\lVert k
\rVert^2`, so for unit-size entries its root-mean-square is $`\sqrt d`. Dividing
every score by a constant is exactly dividing the inverse temperature by that
constant; so feeding *raw* dot products to the Softmax at a fixed $`\beta` is
running the head at $`\beta\sqrt d`, which freezes onto the arg-max as the width
grows. The $`1/\sqrt d` is the temperature-preserving normalization — with it the
score has mean square exactly $`1`, whatever the width:
:::

```
#check @BookProof.ChapterScaledDotProduct.rademacherMean_dot
#check @BookProof.ChapterScaledDotProduct.rademacherMean_dot_sq
#check @BookProof.ChapterScaledDotProduct.scoreSoftmax_scaled
#check @BookProof.ChapterScaledDotProduct.rademacherMean_scaledDot_sq_of_unit_entries
```

:::paragraph
The output carries a second moment as well as a first. Decomposing the
attention-weighted mean square of the values about any reference point into the
variance about the output plus the squared distance to the output — the
bias–variance identity — shows that the head output is the *least-squares summary*
of what it is reading: no other vector sits closer to the values in the
attention-weighted mean-square sense. König–Huygens then gives the Jensen bound
$`\lVert o\rVert^2 \le \sum_j p_j \lVert v_j\rVert^2`, and — because at a finite
temperature every weight is strictly positive — the output is *certain* exactly
when all the values agree:
:::

```
#check @BookProof.ChapterAttentionOutputVariance.sum_dist_sq_eq
#check @BookProof.ChapterAttentionOutputVariance.observableExpectation_minimizes
#check @BookProof.ChapterAttentionOutputVariance.outputVariance_eq_sub
#check @BookProof.ChapterAttentionOutputVariance.outputVariance_scoreSoftmax_eq_zero_iff
```

:::paragraph
The factorization $`s_{ij} = \langle q_i, k_j\rangle` through a head dimension $`d`
is itself a hard constraint. The whole $`m\times m` table of alignments a head can
produce has rank at most $`d`, so when $`d < m` no head can realize the pattern
"each position attends to itself and to nothing else" — its score matrix is the
identity, of rank $`m`. A single head is not a general router; the bound is sharp,
since orthonormal queries and keys realize that pattern as soon as $`d \ge m`:
:::

```
#check @BookProof.ChapterAttentionLowRank.rank_scoreMatrix_le
#check @BookProof.ChapterAttentionLowRank.not_exists_scoreMatrix_one
#check @BookProof.ChapterAttentionLowRank.exists_scoreMatrix_one_of_le
```

:::paragraph
Layer normalization, which every block applies before the head reads, is the gauge
fixing of this picture: it centres the activations and puts them on the sphere of
squared length $`d`, it is invariant under the affine reparametrizations $`x \mapsto
ax + c` with $`a > 0`, and it is idempotent — a projection. Cauchy–Schwarz then caps
every score of a normalized head by $`d`, so the scores span at most $`2d` and every
key keeps at least $`e^{-2\beta d}/m` of the attention. Normalization is what keeps
the temperature of the Born measurement bounded:
:::

```
#check @BookProof.ChapterLayerNorm.sum_sq_layerNorm
#check @BookProof.ChapterLayerNorm.layerNorm_smul_pos
#check @BookProof.ChapterLayerNorm.layerNorm_layerNorm
#check @BookProof.ChapterLayerNorm.scoreSoftmax_layerNorm_ge
```

:::paragraph
The rotary encoding above is not the only positional scheme with the offset
property. The original sinusoidal bank has it too: the alignment of two encoded
positions is $`\sum_a \cos(\omega_a(p-q))`, every encoded position has the same
squared length, and a global shift of all positions leaves every attention weight
untouched:
:::

```
#check @BookProof.ChapterSinusoidalPosition.peInner_eq_sum_cos
#check @BookProof.ChapterSinusoidalPosition.peInner_self
#check @BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_shift
#check @BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_ge
```

:::paragraph
Iterating the Markov step of a single layer gives the mixing law of a deep stack:
after $`n` layers two beliefs about position are $`(1-m\varepsilon)^n` times as far
apart as they began, the distance tends to zero, and there is at most one
stationary belief. For a genuine attention layer at $`\beta \ge 0` with score spread
$`D` the rate is $`(1 - e^{-\beta D})^n` — depth alone erases the initial state
unless the scores are allowed to spread:
:::

```
#check @BookProof.ChapterAttentionMixing.l1dist_pushIter_le
#check @BookProof.ChapterAttentionMixing.tendsto_l1dist_pushIter
#check @BookProof.ChapterAttentionMixing.eq_of_stationary
#check @BookProof.ChapterAttentionMixing.tendsto_l1dist_pushIter_attentionMatrix
```

:::paragraph
Between the two extreme temperatures there is a monotonicity nobody has to
compute: the odds of two keys are the pure exponential $`e^{\beta(s_i-s_j)}` of
their score gap, so cooling the head can only help the best key and only hurt the
worst one. At any $`\beta \ge 0` the winner already holds at least the uniform
share $`1/m` and the loser at most $`1/m`, and the gain is strict as soon as some
other key scores strictly lower. The converse bound closes the picture: if the
scores span at most $`D`, no weight exceeds $`e^{\beta D}/m` and the entropy of the
collapse never falls below $`\log m - \beta D` — a head with bounded scores cannot
be sharp at a finite temperature:
:::

```
#check @BookProof.ChapterAttentionTemperature.scoreSoftmax_odds
#check @BookProof.ChapterAttentionTemperature.scoreSoftmax_monotone_of_isMax
#check @BookProof.ChapterAttentionTemperature.scoreSoftmax_antitone_of_isMin
#check @BookProof.ChapterAttentionTemperature.inv_card_le_scoreSoftmax_of_isMax
#check @BookProof.ChapterAttentionTemperature.log_card_sub_le_shannonEntropy
```

:::paragraph
Trained heads reliably park a large share of their attention on one uninformative
position — the *attention sink*. The Born algebra says this is a gauge, not a
pathology: prepending one extra key multiplies every original weight by the single
factor $`1-w`, leaves all the odds between ordinary keys untouched, and turns the
output into the two-point average $`w\,v_0 + (1-w)\,o` of the sink value and the
sink-free output. Even the entropy splits cleanly, into the binary entropy of the
sink share plus $`(1-w)` times the entropy the head would have had:
:::

```
#check @BookProof.ChapterAttentionSink.scoreSoftmax_sink_succ
#check @BookProof.ChapterAttentionSink.scoreSoftmax_sink_odds
#check @BookProof.ChapterAttentionSink.headOutput_sink
#check @BookProof.ChapterAttentionSink.shannonEntropy_sink
```

:::paragraph
A head does not attend to positions but to what the positions stand for, and the
right bookkeeping for regrouping the context is the pushforward of the attention
distribution along a grouping map. If the values depend on a key only through its
group, the key-by-key output and the group-by-group output agree; and coarse
graining obeys the data-processing inequality — merging keys can only destroy
information, never create it. What is *not* invariant is the weight: if the scores
depend only on the group, each group's share is multiplied by its size, so
duplicating a key really does double its vote:
:::

```
#check @BookProof.ChapterAttentionCoarseGrain.observableExpectation_merge
#check @BookProof.ChapterAttentionCoarseGrain.headOutput_merge
#check @BookProof.ChapterAttentionCoarseGrain.shannonEntropy_mergeWeights_le
#check @BookProof.ChapterAttentionCoarseGrain.mergeWeights_scoreSoftmax_of_fiber_const
```

:::paragraph
Finally, the two learned projections of a head are not two objects. The score is
$`\langle W_Q x, W_K y\rangle = x^{\mathsf T}(W_Q^{\mathsf T}W_K)y`, so the pair
enters only through the single bilinear form $`W_Q^{\mathsf T}W_K` — the QK
circuit. Any two parameter pairs with the same circuit give the same weights and
the same output, and the substitution $`(W_Q,W_K)\mapsto(AW_Q,BW_K)` with
$`A^{\mathsf T}B = I` is an exact symmetry: a head's parameters are defined only up
to that $`GL(d)` action. The circuit has rank at most the head dimension, which is
where the score-table bottleneck comes from:
:::

```
#check @BookProof.ChapterAttentionQKCircuit.qkScore_eq_bilinear
#check @BookProof.ChapterAttentionQKCircuit.qkScore_gauge
#check @BookProof.ChapterAttentionQKCircuit.scoreSoftmax_qkScore_gauge
#check @BookProof.ChapterAttentionQKCircuit.rank_qkMatrix_le
```

:::paragraph
All of this is written into a stream that the block never replaces: the update is
$`x \mapsto x + f(x)`. A head whose values are bounded by $`C` moves the stream by at
most $`C`, and if the block is a contraction the residual map is not merely
injective but expansive by $`1-L` — the input of a layer can always be recovered
from its output, so nothing an earlier layer wrote can be overwritten by a later
one. A stack of $`n` such blocks drifts by at most $`nC`: depth moves the stream
linearly, not explosively:
:::

```
#check @BookProof.ChapterResidualStream.norm_residual_sub_self_le
#check @BookProof.ChapterResidualStream.norm_sub_residual_ge
#check @BookProof.ChapterResidualStream.residual_injective
#check @BookProof.ChapterResidualStream.norm_iterate_residual_sub_le
```

:::paragraph
The name *Softmax* is a claim about the free energy, and the claim is quantitative.
The log-partition function is squeezed between the largest score and that score
plus $`\log m`, so $`\tfrac1\beta\log Z(\beta)` is the maximum score up to
$`\log m/\beta`, and the attention-weighted mean score obeys the same bound: at a
low enough temperature the head reads (almost) the best-matching key, and both
quantities converge to the maximum as $`\beta\to\infty`. The whole gap between the
soft maximum and the hard one is the entropy of the collapse:
:::

```
#check @BookProof.ChapterAttentionFreeEnergy.le_logPartition
#check @BookProof.ChapterAttentionFreeEnergy.abs_logPartition_div_sub_le
#check @BookProof.ChapterAttentionFreeEnergy.sub_meanScore_le
#check @BookProof.ChapterAttentionFreeEnergy.tendsto_meanScore_atTop
```

:::paragraph
No long-context head looks at all of its keys: it keeps a shortlist — a top-$`k`
set, a sliding window, a block-sparse pattern — and renormalizes over it. Masking
is Bayesian conditioning, so the price of that shortcut can be computed exactly:
the sparse head differs from the dense head by $`2(1-P(S))` in $`\ell^1`, where
$`P(S)` is the attention mass the shortlist would have carried — no more and no
less. A shortlist that captures all but $`\varepsilon` of the mass is
$`2\varepsilon`-accurate, its output is within $`2\varepsilon C`, and
sparsification is lossless exactly when the discarded keys carried nothing:
:::

```
#check @BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_eq
#check @BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_le_of_mass
#check @BookProof.ChapterAttentionSparse.norm_headOutput_masked_sub_le
#check @BookProof.ChapterAttentionSparse.one_sub_attendedMass_le
```

:::paragraph
The gauge argument that collapses the query and key projections into the single QK
circuit applies verbatim on the writing side. Because the attention average is
linear, it commutes with every linear map, so the value and output projections act
only through their product $`W_OW_V` — the OV circuit — with its own $`GL(d)`
gauge freedom $`(W_O,W_V)\mapsto(W_OA, BW_V)`, $`AB = I`. That product has rank at
most the head dimension: a head reads through a rank-$`d` bottleneck and writes
through one too:
:::

```
#check @BookProof.ChapterAttentionOVCircuit.mulVec_headOutput
#check @BookProof.ChapterAttentionOVCircuit.ovOutput_eq_headOutput
#check @BookProof.ChapterAttentionOVCircuit.ovOutput_gauge
#check @BookProof.ChapterAttentionOVCircuit.rank_ovMatrix_le
```

:::paragraph
The Jacobian of the collapse also measures how teachable the head is. The total
absolute response of the attention distribution to a nudge of one score is exactly
$`2\beta p_i(1-p_i)` — never more than $`\beta/2`, and vanishing at both ends of
the scale. Once some key carries $`1-\varepsilon` of the attention, *every* score
has total influence at most $`2\beta\varepsilon`: a head that has made up its mind
is hard to teach, which is the algebraic content of the saturation that attention
temperature schedules are designed to avoid:
:::

```
#check @BookProof.ChapterAttentionSaturation.sum_abs_softmaxJacobian_row
#check @BookProof.ChapterAttentionSaturation.sum_abs_softmaxJacobian_le_half
#check @BookProof.ChapterAttentionSaturation.sum_abs_softmaxJacobian_le_of_confident
```

:::paragraph
Finally, heads are rarely scored on alignment alone: a learned per-key bias, a
relative-position bias or a repetition penalty is added to the logits first. Read
through the Born rule such a bias is not an extra ingredient but the *prior* of the
update — the biased head is literally the Bayes posterior with prior $`w` and
likelihood $`e^{\beta s}`, its odds are prior odds times likelihood ratio, and a
prior is exactly a score shift $`s_j \mapsto s_j + (\log w_j)/\beta`. Only the
ratios of the prior weights matter, and at infinite temperature the head returns
the normalized prior: with no evidence, the posterior is the prior:
:::

```
#check @BookProof.ChapterAttentionPrior.priorSoftmax_eq_posterior
#check @BookProof.ChapterAttentionPrior.priorSoftmax_odds
#check @BookProof.ChapterAttentionPrior.priorSoftmax_eq_scoreSoftmax_bias
#check @BookProof.ChapterAttentionPrior.priorSoftmax_zero
```

:::paragraph
Generation exploits the same algebra. Appending one key/value pair to a head
multiplies every cached weight by a single factor $`1-w`, so nothing already
computed has to be revisited, and the new output is the convex interpolation
$`(1-w)\,o_{\text{old}} + w\,v_{\text{new}}`. The KV cache is therefore not an
approximation but an identity, and a late token perturbs an established summary
exactly in proportion to the attention it wins:
:::

```
#check @BookProof.ChapterAttentionStreaming.scoreSoftmax_snoc_castSucc
#check @BookProof.ChapterAttentionStreaming.headOutput_snoc
#check @BookProof.ChapterAttentionStreaming.norm_headOutput_snoc_sub_le
#check @BookProof.ChapterAttentionStreaming.scoreSoftmax_snoc_odds
```

:::paragraph
Position can also enter as a penalty rather than as an embedding: subtract
$`\gamma` times the distance from each score. Such a head is provably *local* — the
weight of a key decays like $`e^{-\beta\gamma d}` in its distance, so the total
attention beyond distance $`R` is at most $`m\,e^{\beta\Delta}e^{-\beta\gamma R}`,
and the sliding-window head is within $`2C` times that of the full head. Locality
is a theorem about the penalty, not an architectural stipulation:
:::

```
#check @BookProof.ChapterAttentionLocality.scoreSoftmax_alibi_le
#check @BookProof.ChapterAttentionLocality.farMass_le
#check @BookProof.ChapterAttentionLocality.norm_headOutput_window_sub_le
```

:::paragraph
And when the shortlist must be chosen, the greedy choice is the right one. Among
all shortlists of a given size, the one holding the heaviest keys carries the most
mass, so — the price of sparsification being exactly the discarded mass — it also
minimizes both the $`\ell^1` error and the output error. At a positive temperature
the heaviest keys are the highest-scoring ones, so the selection can be made
before the Softmax is ever evaluated:
:::

```
#check @BookProof.ChapterAttentionTopK.attendedMass_le_of_isTop
#check @BookProof.ChapterAttentionTopK.l1dist_maskedSoftmax_le_of_isTop
#check @BookProof.ChapterAttentionTopK.isTopWeight_of_isTopScore
```

:::paragraph
Finally, the temperature itself is observable. For a head whose scores are not all
equal the attention entropy is a continuous, strictly decreasing function of the
inverse temperature, so distinct temperatures give distinct entropies and every
entropy level between $`H(B)` and the maximal $`\log m` is realized by exactly one
$`\beta \in [0,B]`. "Run this head at entropy $`h`" is a well-posed instruction:
:::

```
#check @BookProof.ChapterAttentionCalibration.attentionEntropy_strictAntiOn
#check @BookProof.ChapterAttentionCalibration.exists_beta_attentionEntropy_eq
#check @BookProof.ChapterAttentionCalibration.existsUnique_beta_attentionEntropy_eq
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
That expectation value has a temperature, too. Writing `headOutput` for the
output of the head at inverse temperature $`\beta`, the dial runs between two
extremes: at $`\beta = 0` the query is ignored and the head returns the plain
mean of the values, while if one key strictly maximizes the alignment the output
converges to that single value vector as $`\beta \to \infty` — the soft average
becomes a hard table lookup. Everything in between stays inside the convex hull of
the values, and the output is $`\ell^1`-stable in the weights:
:::

```
#check @BookProof.ChapterAttentionOutput.headOutput_zero
#check @BookProof.ChapterAttentionOutput.tendsto_headOutput
#check @BookProof.ChapterAttentionOutput.headOutput_mem_convexHull
#check @BookProof.ChapterAttentionOutput.norm_observableExpectation_sub_le
#check @BookProof.ChapterAttentionOutput.attentionOutput_eq_headOutput
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
energy observable $`n + \tfrac12`); the law is further identified with the
Boltzmann–Gibbs law at inverse temperature $`x = \hbar\omega/kT` and given its
$`\tfrac12\coth(x/2)` closed form in `BookProof.ChapterBoseEinstein`, and
characterized variationally — maximal entropy at fixed mean occupation — in
`BookProof.ChapterThermalMaxEntropy`. Its physical derivation from the fidelity
of displaced thermal states remains a precise proof plan in {ref "proof-plans"}[the
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