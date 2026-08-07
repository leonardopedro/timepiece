import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Consciousness as a Representation of a Bayesian Prior" =>
%%%
tag := "consciousness-bayesian-prior"
%%%

# The Question

:::paragraph
The manuscript's chapter on consciousness begins from a basic fact of Bayesian
inference: there is always a prior probability distribution, and there is no prior
which is better for all cases — we always have to make assumptions. It draws
implications for consciousness, extraterrestrial intelligence, and artificial
general intelligence. Its central thesis is that a "conscious" system is one
running a symbolic manipulation of a Bayesian prior, and that a point of null
measure is not automatically special. The verified content here is the
measure-theoretic and Bayesian facts that the manuscript's argument rests on.
:::

# No Prior Is Special, and No Point Is Special

:::paragraph
Two claims underpin the manuscript's argument. First, *no point of null measure
is special*: every singleton of the real line has Lebesgue measure zero, so no
single value of a continuous random variable carries probability mass; and there
exist *uncountable* null sets (the Cantor set), so a set being null does not mean
it is small. Singling out one null point as a "conscious" observer is therefore
not justified by the measure:
:::

```
#check @BookProof.ConsciousnessNullMeasure.singleton_volume_zero
#check @BookProof.ConsciousnessNullMeasure.countable_volume_zero
#check @BookProof.ConsciousnessNullMeasure.cantorSet_uncountable
#check @BookProof.ConsciousnessNullMeasure.cantorSet_volume_zero
#check @BookProof.ConsciousnessNullMeasure.exists_uncountable_null_subset
```

:::paragraph
Second, *no prior is better for all cases*: for any two distinct finite priors
there is a decision problem (utility) preferring one and another preferring the
other — a no-free-lunch statement. Prior choice is unavoidable and subjective:
:::

```
#check @BookProof.ChapterNoBestPrior.expectedUtility
#check @BookProof.ChapterNoBestPrior.not_uniformly_better
#check @BookProof.ChapterNoBestPrior.distinct_priors_each_preferred
```

:::paragraph
And on a countably infinite space there is no uniform probability measure on
singletons at all — "the rationals are not enough", so a genuinely continuous
prior must be used:
:::

```
#check @BookProof.ChapterNoUniformCountable.no_uniform_countable_measure
#check @BookProof.ChapterNoUniformCountable.no_uniform_measure_nat
```

# A Deterministic Prior Is Still Subjective

:::paragraph
The manuscript argues that a deterministic (frequentist) prior is still
subjective. A Dirac prior concentrated at a single hypothesis is a genuine
probability distribution, Bayesian updating preserves it (a positive-likelihood
update keeps it deterministic), and two distinct deterministic priors yield
distinct posteriors for the same data — so the prior is doing real work and is
not eliminated by being "objective":
:::

```
#check @BookProof.ChapterPriorDependence.diracPrior
#check @BookProof.ChapterPriorDependence.diracPrior_sum_one
#check @BookProof.ChapterPriorDependence.posterior_dirac
#check @BookProof.ChapterPriorDependence.distinct_priors_distinct_posteriors
```

:::paragraph
The prior-odds form makes the subjectivity quantitative: posterior odds equal
prior odds times the likelihood ratio, and equal likelihoods preserve prior odds:
:::

```
#check @BookProof.ChapterPriorOdds.posterior_odds
#check @BookProof.ChapterPriorOdds.equal_likelihood_preserves_odds
```

# The Uniform Prior as a Point of Reference

:::paragraph
The uniform prior is the unique relabeling-invariant prior, and it serves as a
neutral reference: under a positive uniform prior, MAP estimation coincides with
maximum likelihood. This gives the manuscript's "no prior is better for all
cases" a positive counterpart — the uniform prior is the canonical prior-free
starting point from which any departure is an explicit assumption:
:::

```
#check @BookProof.ChapterUniformPrior.normalized_isRelabelingInvariant_eq_uniform
#check @BookProof.ChapterUniformPrior.uniform_prior_isMAP_iff_isMLE
#check @BookProof.ChapterUniformPriorPosterior.exists_likelihood_uniform_prior_posterior
```

# Bayesian Inference Is a Representation

:::paragraph
The manuscript's thesis that consciousness is a *representation* of a Bayesian
prior is captured abstractly by the fact that Bayesian inference is a unitary
(Born-rule) operation: the Bayes posterior equals the Born-rule conditional of the
wave-function $`\Psi = \sqrt{p}`, and a unitary matrix reproduces the posterior —
"unitary inference" is Bayesian inference. The uniform-prior posterior is likewise
a genuine probability distribution:
:::

```
#check @BookProof.ChapterBayesInference.posterior_eq_born_conditional
#check @BookProof.ChapterBayesInference.exists_unitary_reproduces_posterior
```

:::paragraph
Bayesian updating is irreversible in the information sense: entropy increases
under a doubly-stochastic Markov map (the discrete $`H`-theorem), so inference
generally destroys information. This is the mathematical counterpart of the
manuscript's point that a conscious system's internal model is not a literal
replay of the world:
:::

```
#check @BookProof.ChapterMarkovEntropy.entropy_applyMarkov_ge
#check @BookProof.ChapterMarkovEntropy.entropy_applyMarkov_permMatrix
```

# Summary

The verified content of the manuscript's consciousness chapter:

 * no point of null measure is special, and null sets need not be small (Cantor);
 * no finite prior is better for all cases (no-free-lunch), and no uniform prior exists on a countably infinite space;
 * a deterministic prior is still subjective (distinct Dirac priors give distinct posteriors);
 * the uniform prior is the unique relabeling-invariant reference (MAP = MLE);
 * Bayesian inference is a unitary/Born-rule representation, and updating is entropy-increasing.