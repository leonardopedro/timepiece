import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Free Fields: the Gaussian and the Uniform Sphere" =>
%%%
tag := "free-field"
%%%

# The Problem: There Is No Infinite-Dimensional Lebesgue Measure

The finite-dimensional Born parametrization puts a uniform-looking measure on the
sphere and pushes it to the simplex. To pass to **field theory** — infinitely many
degrees of freedom — we would like a uniform (Lebesgue-like) measure on an
infinite-dimensional sphere. There is an immediate obstruction:

**There is no non-zero, translation-invariant measure that is finite on bounded sets in an infinite-dimensional normed space.**

The proof is a clean volume argument. In a translation-invariant measure, all balls
of a given radius have the same measure. In infinite dimension a ball of radius
$`r` contains **infinitely many** disjoint balls of radius $`r/2` (because there is
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
free-field construction to build its uniform measure **out of the Gaussian** rather
than out of a nonexistent Lebesgue measure.

# The Substitute: the Rotation-Invariant Gaussian

The standard Gaussian on $`\mathbb{R}^n`,

$$`\gamma_n(dx) = (2\pi)^{-n/2} e^{-\|x\|^2/2}\, dx,`

depends only on the radius $`\|x\|`. Consequently it is **rotation-invariant**:
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
orthogonal $`L`. The Gaussian is the canonical **rotation-invariant probability
prior**, the finite-dimensional stand-in for the uniform measure that does not exist
in infinite dimension.

# Pushing the Gaussian to the Sphere

Because the Gaussian has no atom at the origin (in dimension $`n \ge 1`), radial
normalization $`x \mapsto x/\|x\|` is defined almost everywhere and pushes
$`\gamma_n` to a probability measure **on the unit sphere**. By rotation-invariance
of the Gaussian, this induced sphere measure is itself rotation-invariant — it is
the **uniform measure on the sphere**, constructed without ever invoking a
Lebesgue measure on the infinite-dimensional ambient space. This is the
manuscript's free-field prior: "a uniform measure of an infinite-dimensional sphere
defined using the Gaussian measure and the Fock space."

This uniform sphere measure is the **Mehler measure**, and it is the exception to the
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
**quotient** of the Gaussian-built sphere by the gauge group, with a canonical
rotation-invariant measure on top.

# A Countability Sanity Check

One last measure-theoretic fact keeps the countable Euler-angle parametrization of
{ref "born-reproduces"}[the Born-rule chapter] honest. The manuscript asserts that
"any partition of the phase-space (where each part has a non-null Lebesgue measure)
is countable." This is a general fact about s-finite measures: a pairwise-disjoint
family of measurable sets, **every** one of positive measure, must be countable —
because in each measure band $`[1/(k+1), 1/k]` there can be only finitely many
disjoint sets, and a countable union of finite sets is countable.

The verified statements (module `BookProof.ChapterCountablePartition`):

```
#check @ChapterCountablePartition.countable_of_partition_pos
#check @ChapterCountablePartition.prob_partition_countable
```

So when the book indexes the parts of a phase-space partition by a countable
orthonormal basis (the setting of the countable stick-breaking chain), it is not
making an extra assumption: positivity of the part measures **forces** the index set
to be countable.

# Summary

The free-field thread replaces the nonexistent infinite-dimensional Lebesgue measure
with the rotation-invariant Gaussian, pushes it to a uniform measure on the sphere,
and then applies the Born rule to parametrize the simplex — all the while the gauge
fibers keep track of the invisible phase. The two negative results (no Lebesgue
measure; positive-measure partitions are countable) are not obstacles but the precise
statements that make the construction both necessary and well-defined.
