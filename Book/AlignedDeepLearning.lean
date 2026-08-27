import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Aligned Deep Learning as a Random Sampling Method" =>
%%%
tag := "aligned-deep-learning"
%%%

# Orientation and Status

This chapter documents the finite Bayesian content of the manuscript's learning
proposal. Induced priors, posterior identities, and MAP algebra are formalized;
claims about generalization, overfitting, alignment, and real training systems need
separate statistical or empirical hypotheses and are listed as specialist proof
targets only when they have a precise mathematical formulation.

# The Question

:::paragraph
The manuscript's chapter on aligned deep learning separates the alignment problem
into two parts: estimating systematic uncertainties as in engineering, and — new
due to Big Data — how to randomly sample *computable* models from a set of
Bayesian models, almost all of which are uncomputable. It argues that deep neural
nets solve the second part, and that because no sufficiently simple metric is
reliable, the (dis)alignment is a *feature*: if the sampling were not random it
would not generalize well. The verified content here is the finite, Bayesian core
of that thesis: randomized training induces a prior, and the resulting posterior
and MAP estimates are exactly the Bayesian ones.
:::

# Randomized Training Induces a Prior

:::paragraph
The manuscript's central model is that training is a *random* procedure: a
distribution on training seeds is pushed forward through a training map to a
distribution on models — the *induced prior*. The verified facts are that this
induced distribution is a genuine probability distribution, that the mass of an
event equals the mass of its preimage, and that if every seed trains to an
admissible model then inadmissible models have zero mass:
:::

```
#check @BookProof.ChapterDeepLearningSampling.inducedPrior
#check @BookProof.ChapterDeepLearningSampling.inducedPrior_isProbability
#check @BookProof.ChapterDeepLearningSampling.sum_inducedPrior_event
#check @BookProof.ChapterDeepLearningSampling.inducedPrior_supported
```

:::paragraph
Expectations and evidence under the induced prior reduce to averages over
training seeds, and posterior expectations are ratios of seed-level weighted
averages:
:::

```
#check @BookProof.ChapterDeepLearningEnsemble.inducedPrior_expectation
#check @BookProof.ChapterDeepLearningEnsemble.evidence_eq_seed_average
#check @BookProof.ChapterDeepLearningEnsemble.posterior_expectation_eq_seed_ratio
```

:::paragraph
This is the precise sense in which "deep learning is a random sampling method":
the model distribution is the induced prior, and every Bayesian quantity is
computable as an expectation over the random seeds.
:::

# Deep Learning as MAP Estimation

:::paragraph
The manuscript connects randomized training to Bayesian MAP estimation. The
logarithmic objective $`\log(\text{prior}) + \log(\text{likelihood})` is ordered
exactly as the unnormalized posterior weight, so maximizing the log-objective is
maximizing the posterior (the normalization is irrelevant to the choice):
:::

```
#check @BookProof.ChapterDeepLearningMAP.logObjective
#check @BookProof.ChapterDeepLearningMAP.exp_logObjective
#check @BookProof.ChapterDeepLearningMAP.isMAP_iff_maximizes_logObjective
#check @BookProof.ChapterDeepLearningMAP.posterior_le_iff_weight
```

# The Induced Posterior Is Bayesian

:::paragraph
Conditioning the induced prior on observed data yields a genuine posterior
distribution, and models outside the image of training have zero posterior mass —
the finite version of "sampling computable models": only computable models are
reachable, and the posterior respects that constraint:
:::

```
#check @BookProof.ChapterDeepLearningSampling.evidence
#check @BookProof.ChapterDeepLearningSampling.posterior
#check @BookProof.ChapterDeepLearningSampling.posterior_sum_one
#check @BookProof.ChapterDeepLearningSampling.posterior_eq_zero_of_not_mem_range
```

# MAP Points Are Null Under an Atomless Posterior

:::paragraph
The manuscript's point that no single model is "the answer" is captured by the
fact that a selected MAP point has posterior mass zero under an atomless
posterior: a sample almost surely does not equal any fixed maximizer, and any
countable collection of maximizers is null. The "alignment" is a distributional
feature, not a single point:
:::

```
#check @BookProof.ChapterMAPNull.map_point_measure_zero
#check @BookProof.ChapterMAPNull.ae_ne_map_point
#check @BookProof.ChapterMAPNull.countable_map_set_measure_zero
```

# Hierarchical and Subjective Structure

:::paragraph
Real alignment problems are hierarchical. The verified facts are that a
two-level (or arbitrary finite) Bayesian hierarchy collapses to a single
kernel — arbitrarily deep marginalization equals one marginalization through the
collapsed kernel — and that the outer posterior is an ordinary Bayes update:
:::

```
#check @BookProof.ChapterHierarchicalBayes.outerPosterior_eq_bayesUpdate
#check @BookProof.ChapterHierarchicalBayes.outerPosterior_eq_sum_flat
#check @BookProof.ChapterHierarchicalBayesComposition.compKernel_assoc
#check @BookProof.ChapterFiniteBayesHierarchy.nestedMarginal_eq_terminalMarginal
```

:::paragraph
And because the prior is subjective (two distinct priors give distinct
posteriors; no prior is best for all cases), alignment is inherently a choice —
the sampling prior encodes the alignment target:
:::

```
#check @BookProof.ChapterNoBestPrior.distinct_priors_each_preferred
#check @BookProof.ChapterPriorDependence.distinct_priors_distinct_posteriors
```

# Previous Knowledge and Finite Arithmetic

:::paragraph
The manuscript's "previous knowledge as step-by-step learning" and the
"digital-first mathematics" themes have a finite, Bayesian rendering: a finite
exact arithmetic table admits a Bayesian extension by a finite hypothesis space,
and the extension preserves every result in the table. Known results are
represented exactly; the unknown is a genuine probability distribution:
:::

```
#check @BookProof.ChapterFiniteArithmeticPrior.BoundedArithmetic
#check @BookProof.ChapterFiniteArithmeticPrior.BayesianArithmeticExtension
#check @BookProof.ChapterFiniteArithmeticPrior.prior_is_probability
#check @BookProof.ChapterFiniteArithmeticPrior.certainExtension_known
```

# Probability as a Universal Language

Underlying the whole chapter is the manuscript's claim that probability is a
*universal language*: any mechanism that turns a state $`x` into a distribution
over answers — a Markov (conditional-probability) kernel $`\kappa : X \to
\mathrm{Pr}(Y)` — *transports* a prior on $`X` into a genuine predictive
distribution on $`Y`, and nothing is lost or created in the process: the total
mass stays $`1`:

```
#check @BookProof.ChapterKernelTransport.kernel_transport_isProbability
#check @BookProof.ChapterKernelTransport.kernel_transport_apply
#check @BookProof.ChapterKernelTransport.kernel_transport_lintegral
```

:::paragraph
The transported measure of a set is the $`\mu`-average of the kernel values (the
law of total probability), and expectations under the transported law are averages
of the conditional expectations. Deterministic transport is the special case where
the kernel is a measurable map $`f`:
:::

```
#check @BookProof.ChapterKernelTransport.map_transport_isProbability
#check @BookProof.ChapterKernelTransport.kernel_transport_deterministic
```

:::paragraph
This is the precise sense in which a model in this book is a genuine probability
space: whatever the internal mechanism (a training map, a neural net, a unitary
rotation), its output over a random input is a bona fide distribution, and every
Bayesian quantity is expressible as an expectation over it.
:::

# Summary

The finite, Bayesian core of the manuscript's deep-learning chapter:

 * randomized training induces a prior distribution on models;
 * the induced posterior is genuinely Bayesian, and models outside the image of training have zero mass;
 * deep learning is MAP estimation (maximizing the log-objective);
 * MAP points are null under an atomless posterior — alignment is distributional;
 * hierarchies collapse to a single kernel, and the outer posterior is an ordinary Bayes update;
 * previous knowledge is represented exactly and the unknown is a probability distribution.