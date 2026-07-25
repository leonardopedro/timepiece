import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean


#doc (Manual) "Bayesian Updating Is Associative" =>
%%%
tag := "sequential-bayes"
%%%

# Updating One Piece of Evidence at a Time

:::paragraph
Bayesian inference updates a **prior** distribution into a **posterior** by
multiplying by a likelihood and renormalizing. On a finite hypothesis space
$`X`, with prior $`\pi : X \to \mathbb{R}` and likelihood weight
$`\ell : X \to \mathbb{R}`, the update is
:::

$$`\mathrm{bayesUpdate}(\pi, \ell)(x) = \frac{\pi(x)\,\ell(x)}{\sum_{x'} \pi(x')\,\ell(x')}.`

:::paragraph
The denominator is the **evidence** — the total probability of the observation —
and it is what makes the posterior sum to one.
:::

:::paragraph
Now suppose two observations arrive. There are two ways to use them:

 * **Sequentially.** Update on the first observation, take the resulting posterior
   as the new prior, and update again on the second.
 * **In a batch.** Multiply the prior by the product likelihood
   $`\ell_1(x)\,\ell_2(x)` and renormalize once.
:::

:::paragraph
The fundamental coherence property of Bayesian inference is that **these two
procedures give exactly the same posterior**. The order in which evidence is
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
**cancels**:
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
A consequence that the source manuscript uses repeatedly is that **no prior is
truly primitive**. Any finite prior can be obtained by starting from the
_maximally uninformative_ (uniform) prior and conditioning on suitable data.
:::

:::paragraph
Given a target distribution $`q` on $`X`, define a binary likelihood
:::

$$`L(x, \mathsf{true}) = q(x), \qquad L(x, \mathsf{false}) = 1 - q(x).`

:::paragraph
Starting from any positive constant prior and conditioning on the outcome
$`\mathsf{true}`, the posterior is exactly $`q`. So the choice of a prior can always
be re-expressed as the choice of a likelihood acting on the uniform prior. This is
the formal sense in which "there are no non-informative priors": even the uniform
prior, once you condition on data, becomes an arbitrary one.
:::

```
#check @ChapterUniformPriorPosterior.exists_likelihood_uniform_prior_posterior
```

# The Uniform Prior Is the Relabeling-Invariant One

:::paragraph
There is, however, a precise sense in which the uniform prior is distinguished: it
is the **unique** prior that treats all hypotheses symmetrically. If a prior is
unchanged under every permutation of the hypothesis labels, then it must be
constant; and a constant probability distribution on a finite non-empty space is
the uniform one, $`1/|X|`.
:::

```
#check @ChapterUniformPrior.isRelabelingInvariant_iff_constant
#check @ChapterUniformPrior.normalized_isRelabelingInvariant_eq_uniform
```

:::paragraph
A useful corollary connects two estimators that are often confused. The
**maximum a posteriori** (MAP) estimate maximizes the posterior
$`\pi(x)\,\ell(x)`; the **maximum-likelihood** (MLE) estimate maximizes
$`\ell(x)` alone. Under a positive uniform prior the factor $`\pi(x)` is constant,
so the two coincide:
:::

```
#check @ChapterUniformPrior.uniform_prior_isMAP_iff_isMLE
```

:::paragraph
This is the rigorous content of the common advice that "maximum likelihood is
Bayesian inference with a flat prior."
:::
