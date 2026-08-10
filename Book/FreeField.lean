import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Free Fields: the Gaussian and the Uniform Sphere" =>
%%%
tag := "free-field"
%%%

# The Problem: There Is No Infinite-Dimensional Lebesgue Measure

The finite-dimensional Born parametrization puts a uniform-looking measure on the
sphere and pushes it to the simplex. To pass to *field theory* — infinitely many
degrees of freedom — we would like a uniform (Lebesgue-like) measure on an
infinite-dimensional sphere. There is an immediate obstruction:

*There is no non-zero, translation-invariant measure that is finite on bounded sets in an infinite-dimensional normed space.*

The proof is a clean volume argument. In a translation-invariant measure, all balls
of a given radius have the same measure. In infinite dimension a ball of radius
$`r` contains *infinitely many* disjoint balls of radius $`r/2` (because there is
an infinite orthonormal set, and the small balls around well-separated points are
disjoint). If the small balls have measure $`m > 0`, the big ball has infinite
measure; if $`m = 0`, countable additivity is not even needed to see the big ball
has measure $`0` once it is covered by countably many null balls in the
finite-on-bounded case. Either way, no measure can be both translation-invariant and
finite and non-zero on bounded sets.

The verified statements (module `BookProof.ChapterNoLebesgue`):

```
#check @ChapterNoLebesgue.measure_ball_eq_measure_ball_zero
#check @ChapterNoLebesgue.not_exists_nonzero_isAddLeftInvariant_finite_on_bounded
```

This is the rigorous content of the manuscript's claim that "there is no
non-informative prior" on a continuous infinite-dimensional space, and it forces the
free-field construction to build its uniform measure *out of the Gaussian* rather
than out of a nonexistent Lebesgue measure.

# The Substitute: the Rotation-Invariant Gaussian

The standard Gaussian on $`\mathbb{R}^n`,

$$`\gamma_n(dx) = (2\pi)^{-n/2} e^{-\|x\|^2/2}\, dx,`

depends only on the radius $`\|x\|`. Consequently it is *rotation-invariant*:
pushing it forward by any orthogonal map $`L` leaves it unchanged. Its
characteristic function $`t \mapsto e^{-\|t\|^2/2}` likewise depends only on
$`\|t\|`, which pins down the measure and makes the invariance manifest.

The verified statements (module `BookProof.ChapterFreeFieldGaussian`):

```
#check @ChapterFreeFieldGaussian.instIsProbabilityMeasure_stdGaussian
#check @ChapterFreeFieldGaussian.charFun_stdGaussian
#check @ChapterFreeFieldGaussian.stdGaussian_map_linearIsometryEquiv
```

The last is the headline: $`(\gamma_n).\mathrm{map}(L) = \gamma_n` for every
orthogonal $`L`. The Gaussian is the canonical *rotation-invariant probability
prior*, the finite-dimensional stand-in for the uniform measure that does not exist
in infinite dimension.

# Pushing the Gaussian to the Sphere

Because the Gaussian has no atom at the origin (in dimension $`n \ge 1`), radial
normalization $`x \mapsto x/\|x\|` is defined almost everywhere and pushes
$`\gamma_n` to a probability measure *on the unit sphere*. By rotation-invariance
of the Gaussian, this induced sphere measure is itself rotation-invariant — it is
the *uniform measure on the sphere*, constructed without ever invoking a
Lebesgue measure on the infinite-dimensional ambient space. This is the
manuscript's free-field prior: "a uniform measure of an infinite-dimensional sphere
defined using the Gaussian measure and the Fock space."

This uniform sphere measure is the *Mehler measure*, and it is the exception to the
slogan this chapter opened with. There is no _Lebesgue_ uniform probability measure
on an infinite-dimensional space, but the Gaussian-built sphere measure is a genuine
uniform prior on the infinite-dimensional hypersphere. It is genuinely
non-informative — invariant under every symmetry the language can express — in the
{ref "solovay-tensor"}[Solovay–Kopperman space], where the restricted decidable
language forbids the reparametrizations that would otherwise turn a uniform prior
into an informative one ({ref "sequential-bayes"}[non-informativeness is
coordinate-dependent]). The free-field construction is the finite-dimensional shadow
of that infinite-dimensional exception.

# Born Pushes the Sphere to the Simplex

Composing the two maps — normalize the Gaussian to the sphere, then apply the Born
rule $`\psi \mapsto |\psi|^2` — parametrizes the probability simplex by the
Gaussian-built sphere measure. The finite-dimensional Born map is continuous and
surjective ({ref "born-reproduces"}[The Born rule reproduces every distribution]),
and its fibers are the phase/sign gauge of
{ref "born-fiber"}[the gauge ambiguity]. The simplex is thus realized as a
*quotient* of the Gaussian-built sphere by the gauge group, with a canonical
rotation-invariant measure on top.

# A Countability Sanity Check

One last measure-theoretic fact keeps the countable Euler-angle parametrization of
{ref "born-reproduces"}[the Born-rule chapter] honest. The manuscript asserts that
"any partition of the phase-space (where each part has a non-null Lebesgue measure)
is countable." This is a general fact about s-finite measures: a pairwise-disjoint
family of measurable sets, *every* one of positive measure, must be countable —
because in each measure band $`[1/(k+1), 1/k]` there can be only finitely many
disjoint sets, and a countable union of finite sets is countable.

The verified statements (module `BookProof.ChapterCountablePartition`):

```
#check @ChapterCountablePartition.countable_of_partition_pos
#check @ChapterCountablePartition.prob_partition_countable
```

So when the book indexes the parts of a phase-space partition by a countable
orthonormal basis (the setting of the countable stick-breaking chain), it is not
making an extra assumption: positivity of the part measures *forces* the index set
to be countable.

# Dimensional Reduction: the Krylov Shortcut and the Compiled Sketch

:::paragraph
The same Gaussian/Fock substrate is what makes the *computational* side of the
free-field thread tractable. Two reductions do the work. The first is the
inversion-free Krylov shortcut: the Krylov subspace
$`\mathrm{Kry}_m(\bar H, v_0) = \mathrm{span}\{v_0, \bar H v_0, \dots, \bar H^{m-1}v_0\}`
is unchanged when the generator is shifted by a multiple of the identity, because
the shift only adds lower-order terms. So the sequence $`w_k = (\bar H - \gamma I)w_{k-1}`,
which never solves a linear system, spans exactly the same subspace as the
rational construction that would; and pre-conditioning the seed makes the
resolvent merely lower the polynomial degree. The generator itself is bounded —
the Mehler projector is rank-one, the number operators diagonal.
:::

```
#check @BookProof.ChapterH5.krylovSpan
#check @BookProof.ChapterH5.krylov_subspace_span
#check @BookProof.ChapterH5.shift_pow_sub_pow_mem
#check @BookProof.ChapterH5.krylovSpan_shift_eq
#check @BookProof.ChapterH5.inversion_free_seed
#check @BookProof.ChapterH5.generator_bounded_of_rankOneProjector
#check @BookProof.ChapterH5.krylov_no_inversion_eq_standard
```

:::paragraph
The second reduction reads the Krylov projection as a *spectral low-pass filter*.
The compression $`\bar H_{\text{reduced}} = V^{\mathsf H}\bar H V` has the
restricted quadratic form, so each of its eigenvalues is a Rayleigh quotient of
the full generator and can never exceed its norm: the projection keeps
frequencies, it does not invent them. What it discards costs only the $`e^{-hm}`
term already carried by the SIRK error bound, which decays to zero as the
retained dimension grows. And generation is then a *single* matrix exponential
of an explicitly $`m \times m` object.
:::

```
#check @BookProof.ChapterH6.sirk_error_decay_exponential
#check @BookProof.ChapterH6.sirk_error_bound_antitone
#check @BookProof.ChapterH6.krylov_rayleigh_transfer
#check @BookProof.ChapterH6.krylovRetainsDominantSpectrum
#check @BookProof.ChapterH6.reduce_generator_mul_m
#check @BookProof.ChapterH6.generation_single_exponential
```

:::paragraph
Finally, the offline stage: a two-level sketch hashes raw coordinates into $`k`
features and places the features on distinct modes of a $`K_2`-mode Fock space,
producing a genuine single-excitation state from which the features can be read
back; and all observables of the reduced space are pre-projected into a complete
basis of $`m^2` matrix units. The corpus size enters only there — the online
cost carries no such term.
:::

```
#check @BookProof.ChapterF8.singleExcitation
#check @BookProof.ChapterF8.twoLevelHash_total
#check @BookProof.ChapterF8.featureHash_decodes
#check @BookProof.ChapterF8.offline_operatorBasis
#check @BookProof.ChapterF8.online_cost_independent_of_M
#check @BookProof.ChapterF8.tsr_offline_compiles
```

:::paragraph
Two properties make the reduction safe to *run*. First, when the full generator
is self-adjoint the compression is self-adjoint too, so every eigenvalue of the
reduced generator is real and is pinned between any bounds satisfied by the
quadratic form of the full generator: the reduced dynamics can neither go
complex nor leave the frequency band of the physics it came from. Second, the
reduced propagator $`e^{-\mathrm{i}t\bar H}` of a Hermitian generator is
unitary, hence generation conserves the $`\ell^2` mass exactly — the generated
state is a state, at every step and for every horizon $`t`.
:::

```
#check @BookProof.ChapterH7.compress_isSelfAdjoint
#check @BookProof.ChapterH7.compression_rayleigh_real
#check @BookProof.ChapterH7.compression_eigenvalue_mem_numericalRange
#check @BookProof.ChapterH7.reduceGenerator_isHermitian
#check @BookProof.ChapterH7.generationOperator_mem_unitaryGroup
#check @BookProof.ChapterH7.generation_preserves_l2
```

# Summary

The free-field thread replaces the nonexistent infinite-dimensional Lebesgue measure
with the rotation-invariant Gaussian, pushes it to a uniform measure on the sphere,
and then applies the Born rule to parametrize the simplex — all the while the gauge
fibers keep track of the invisible phase. The two negative results (no Lebesgue
measure; positive-measure partitions are countable) are not obstacles but the precise
statements that make the construction both necessary and well-defined.
