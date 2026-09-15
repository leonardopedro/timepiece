import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean


#doc (Manual) "Bayesian Updating Is Associative" =>
%%%
tag := "sequential-bayes"
%%%

# Updating One Piece of Evidence at a Time

:::paragraph
Bayesian inference updates a *prior* distribution into a *posterior* by
multiplying by a likelihood and renormalizing. On a finite hypothesis space
$`X`, with prior $`\pi : X \to \mathbb{R}` and likelihood weight
$`\ell : X \to \mathbb{R}`, the update is
:::

$$`\mathrm{bayesUpdate}(\pi, \ell)(x) = \frac{\pi(x)\,\ell(x)}{\sum_{x'} \pi(x')\,\ell(x')}.`

:::paragraph
The denominator is the *evidence* — the total probability of the observation —
and it is what makes the posterior sum to one.
:::

:::paragraph
Now suppose two observations arrive. There are two ways to use them:

 * *Sequentially.* Update on the first observation, take the resulting posterior
   as the new prior, and update again on the second.
 * *In a batch.* Multiply the prior by the product likelihood
   $`\ell_1(x)\,\ell_2(x)` and renormalize once.
:::

:::paragraph
The fundamental coherence property of Bayesian inference is that *these two
procedures give exactly the same posterior*. The order in which evidence is
processed, and whether it is processed one item at a time or all at once, is
irrelevant. This is the associativity of Bayesian updating.
:::

# Sketch Proof

:::paragraph
Write the evidence of the first update as
$`Z_1 = \sum_x \pi(x)\ell_1(x)`. After the first update the prior is
$`\pi_1(x) = \pi(x)\ell_1(x)/Z_1`. Updating $`\pi_1` on $`\ell_2` gives
:::

$$`\pi_2(x) = \frac{\pi_1(x)\,\ell_2(x)}{\sum_{x'} \pi_1(x')\,\ell_2(x')} = \frac{\dfrac{\pi(x)\ell_1(x)}{Z_1}\,\ell_2(x)}{\sum_{x'} \dfrac{\pi(x')\ell_1(x')}{Z_1}\,\ell_2(x')}.`

:::paragraph
The factor $`1/Z_1` appears in every term of both numerator and denominator, so it
*cancels*:
:::

$$`\pi_2(x) = \frac{\pi(x)\,\ell_1(x)\,\ell_2(x)}{\sum_{x'} \pi(x')\,\ell_1(x')\,\ell_2(x')} = \mathrm{bayesUpdate}(\pi,\,\ell_1\ell_2)(x).`

:::paragraph
The intermediate normalization is exactly what disappears. This is why a Bayesian
agent never needs to remember _how_ it accumulated its evidence — only the current
posterior matters, and it is the same as if all the evidence had been weighed at
once.
:::

# The Verified Statement

:::paragraph
The associativity, and the bookkeeping that the second-step evidence factorizes
correctly, are proved in `BookProof.ChapterSequentialBayes`:
:::

```
#check @ChapterSequentialBayes.sequential_eq_batch
#check @ChapterSequentialBayes.bayesUpdate_evidence
```

:::paragraph
The same module also confirms the basic sanity of the update — the posterior is
non-negative and, given positive evidence, sums to one:
:::

```
#check @ChapterSequentialBayes.bayesUpdate_nonneg
#check @ChapterSequentialBayes.bayesUpdate_sum_one
```

# Every Prior Is a Posterior From the Uniform Prior

:::paragraph
A fact the source manuscript uses repeatedly is that *no finite prior is
primitive*. Any finite prior can be obtained by starting from the uniform prior
and conditioning on suitable data.
:::

:::paragraph
Given a target distribution $`q` on $`X`, define a binary likelihood
:::

$$`L(x, \mathsf{true}) = q(x), \qquad L(x, \mathsf{false}) = 1 - q(x).`

:::paragraph
Starting from any positive constant prior and conditioning on the outcome
$`\mathsf{true}`, the posterior is exactly $`q`. So the choice of a prior can always
be re-expressed as the choice of a likelihood acting on the uniform prior.
:::

```
#check @ChapterUniformPriorPosterior.exists_likelihood_uniform_prior_posterior
```

:::paragraph
This is sometimes misread as saying that the uniform prior is the natural,
non-informative starting point. It says no such thing. The information has not
vanished; it has only *moved from the prior into the likelihood*. The uniform
prior is not privileged here — it is merely a convenient origin from which every
other prior is reachable. The next sections make precise both why the uniform prior
is _not_ intrinsically special, and what is actually true in the slogan "there are
no non-informative priors."
:::

# The Real Sense: Non-Informativeness Is Coordinate-Dependent

:::paragraph
The slogan refers to a different and deeper fact:
*non-informativeness is not invariant under a change of coordinates.* A density
that is flat — and therefore apparently non-informative — in one parametrization is
generally _not_ flat in another. Under a smooth reparametrization $`y = f(x)` the
density picks up the Jacobian factor $`|dx/dy|`, so a constant $`p_x` becomes a
non-constant $`p_y`. The prior that "assumed nothing" in the $`x`-coordinates quietly
assumes something in the $`y`-coordinates.
:::

:::paragraph
The converse is just as important, and it is what removes any special status the
uniform prior might seem to have: *any prior that is non-null on a finite set of
events can be made uniform on that same set by a reparametrization.* Given a
distribution $`p` on $`\{0, \dots, n-1\}` with $`p_k > 0`, form its cumulative sum
$`\mathrm{cdf}(k) = \sum_{i<k} p_i` and partition the unit interval into the seed
intervals $`[\mathrm{cdf}(k), \mathrm{cdf}(k+1))`, whose lengths are exactly the
$`p_k`. A _uniform_ seed on $`[0,1)`, decoded by which interval it falls in,
reproduces $`p`; read the other way, the cumulative-sum map sends $`p` back to the
uniform measure. The two distributions are the _same_ prior written in different
coordinates:
:::

```
#check @InverseTransform.seedSet_measure
#check @InverseTransform.seedSet_cover
#check @InverseTransform.seedSet_total_measure
```

:::paragraph
So uniformity is not an intrinsic property of a prior at all. It is a property of a
prior _relative to a chosen parametrization_. On a finite set every non-null prior
is "uniform in disguise," and which disguise counts as the neutral one is itself an
informative choice. _This_ is the precise sense of "there are no non-informative
priors": an apparently non-informative prior becomes apparently informative the
moment the coordinates are changed — and an apparently informative one can be made
to look non-informative just as easily. The measure-theoretic obstructions behind
the same slogan are taken up in
{ref "null-measure"}[null-measure sets need not be small] and
{ref "free-field"}[the free-field chapter].
:::

# The Uniform Prior Is Special Only Within a Parametrization

:::paragraph
None of this means the standard characterizations of the uniform prior are false.
They are true — and worth proving — but each of them is a statement _relative to a
fixed parametrization_, and that caveat is essential.
:::

:::paragraph
Within a fixed labeling of the hypotheses, the uniform prior is the *unique* prior
that treats all labels symmetrically: a prior unchanged under every permutation of
the labels must be constant, and a constant probability distribution on a finite
non-empty space is the uniform one, $`1/|X|`.
:::

```
#check @ChapterUniformPrior.isRelabelingInvariant_iff_constant
#check @ChapterUniformPrior.normalized_isRelabelingInvariant_eq_uniform
```

:::paragraph
But "relabeling-invariant" privileges one particular labeling of the hypotheses.
The previous section showed that any non-null prior can be reparametrized into the
uniform one; in those new coordinates it is the reparametrized prior, not the old
uniform one, that is "the invariant" prior. Symmetry under relabeling is a property
of the _coordinate system_, not an intrinsic property that singles out one prior
across all parametrizations. The same caveat attaches to the maximum-entropy
characterization ({ref "max-entropy"}[the maximum-entropy chapter]): entropy is
computed with respect to a chosen base measure, and changing coordinates changes
which distribution maximizes it.
:::

:::paragraph
A useful corollary connects two estimators that are often confused. The
*maximum a posteriori* (MAP) estimate maximizes the posterior
$`\pi(x)\,\ell(x)`; the *maximum-likelihood* (MLE) estimate maximizes
$`\ell(x)` alone. Under a positive uniform prior the factor $`\pi(x)` is constant,
so the two coincide:
:::

```
#check @ChapterUniformPrior.uniform_prior_isMAP_iff_isMLE
```

:::paragraph
This is the rigorous content of the common advice that "maximum likelihood is
Bayesian inference with a flat prior" — always understood as "flat _in the chosen
coordinates_."
:::

# The Exception: Infinite-Dimensional Spaces Need the Mehler Formalism

:::paragraph
On a *finite* set of events, then, uniform priors are cheap: any non-null prior
can be reparametrized into one. But that uniformity is parametrization-dependent,
hence not genuinely non-informative. The genuinely new case is not a merely
_countably_ infinite set of events but an *infinite-dimensional space* of events —
infinitely many degrees of freedom. There is no Lebesgue probability measure on such
a space ({ref "free-field"}[no translation-invariant finite measure]), and the
reparametrization trick that worked in finite dimension is exactly what destroys
uniformity there. To have a uniform prior on an infinite-dimensional space at all,
one needs the *Mehler formalism*.
:::

:::paragraph
A countably infinite set of events is a different, and worse, case still: there the
uniform prior is not merely parametrization-dependent but *impossible outright*.
There is no uniform probability measure on a countable space — assigning every
outcome the same positive mass gives an infinite total, while mass zero gives total
zero:
:::

```
#check @ChapterNoUniformCountable.no_uniform_countable_measure
```

:::paragraph
This is the measure-theoretic reason the construction below lives on a genuine
continuum ({ref "epr-complete"}[the rationals are not enough]) rather than on a
countable set of events.
:::

:::paragraph
This is the one setting in the manuscript where the slogan "there are no
non-informative priors" does not bite, and it is the setting this book is built
around. In the {ref "solovay-tensor"}[Solovay–Kopperman inner-product space] the
infinite tail is not a completed Hilbert space on which arbitrary unitary transforms
act. The admissible language is *cylindrical*: it may query only finitely many
coordinates, so it cannot name or distinguish individual elements of the
infinite-dimensional space. Because of that restriction the space is
*not necessarily metrically complete*, and arbitrary unitary transforms are simply
*not defined* within the language. The reparametrizations that would turn a uniform
prior into an informative one are not available.
:::

:::paragraph
The symmetries that survive are precisely the *admissible finite-orthogonal
symmetries* of the tail — the measure-preserving maps the language can express —
and the Mehler prior is invariant under every one of them. It is a probability
measure, it is atomless, and it concentrates on the infinite-dimensional unit
sphere:
:::

```
#check @only_mehler_on_tail
#check @mehler_invariant_under_finite_orthogonal
#check @mehler_concentrates_on_unit_sphere
```

:::paragraph
So within the restricted decidable language the Mehler uniform prior on the
infinite-dimensional hypersphere *is* genuinely uniform: every symmetry the
language can express leaves it unchanged, and there is no admissible change of
coordinates that could make it informative. Finite sets admit uniform priors only by
a parametrization-dependent trick; a countable infinity of events admits none at
all; the infinite-dimensional space admits one only through the Mehler formalism,
and there it is intrinsic. Probability on the infinite-dimensional part is not a
choice; it is the forced Mehler measure
({ref "solovay-tensor"}[The Solovay–Kopperman Tensor Product]).
:::
