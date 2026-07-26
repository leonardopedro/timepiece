import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "EPR-Completeness, Causality, and a Deterministic Theory" =>
%%%
tag := "epr-complete"
%%%

# Two Kinds of Incompleteness

The manuscript distinguishes **two** kinds of incompleteness that a stochastic
process can have, and argues that conflating them is the source of the EPR paradox.

: Stochastic incompleteness

  The root of probability is **absence of information**. A deterministic process can
  be turned into a stochastic one unambiguously (using trivial, delta-function
  distributions), but a stochastic process cannot be turned back into a
  deterministic one without **new information**. This kind of incompleteness is
  intrinsic to any statistical theory.

: Non-Markov incompleteness

  Any **non-Markov** stochastic process can be described as a **Markov** process in
  which some variables defining the state are hidden (unknown). Conversely, hiding
  variables from an irreducible Markov process produces a non-Markov process.
  Brownian motion is the textbook example: the underlying molecular dynamics is
  deterministic and Markov, but the observed motion is non-Markov because the full
  state cannot be measured.

# Quantum Mechanics Has Only the First Kind

In quantum mechanics, any sequence of measurements **is** a Markov stochastic
process: the outcome of each measurement, together with the state update, depends
only on the present state. So quantum mechanics has the **stochastic** kind of
incompleteness — as every statistical theory must. But it does **not** have the
non-Markov kind: there are no hidden variables whose revelation would restore a
deterministic Markov description.

The EPR argument tries to infer the non-Markov kind from the stochastic kind — to
argue that because position and momentum cannot be simultaneously measured, they
must be simultaneous "elements of reality" in some deeper description. The
manuscript's response is that this inference has no mathematical basis: the
stochastic kind of incompleteness is **harmless**, and the wave-function
parametrization shows that no deterministic model is more fundamental than quantum
mechanics. In this precise sense, **quantum mechanics is a complete statistical
theory** as EPR defined completeness.

The structural reason, again, is
{ref "time-translation-stochastic"}[the stochastic-process theorem]: the EPR setup
assumes a probability distribution for the state of the separated system _between_
preparation and measurement, but a non-deterministic time-evolution defines no such
distribution.

# Relativistic Causality

Now restrict to a **free** system, where relativistic quantum mechanics is
well-defined (the free Dirac equation). Relativistic causality holds there: the
propagator vanishes for space-like separation, so the probability that the system
moves faster than light is **null**.

A deterministic theory **compatible** with relativistic quantum mechanics is one
that, applied to an ensemble of free systems, reproduces quantum mechanics'
statistical predictions. Since in relativistic quantum mechanics the probability of
superluminal motion is null, **no** system in the ensemble moves faster than light;
hence any such deterministic theory necessarily respects relativistic causality. The
verified measure-theoretic statement (module `BookProof.ChapterCausality`):

```
#check @Causality.seedSet_biUnion_measure
#check @Causality.causality
#check @Causality.causality_ae
```

Reading them: the seed sets (the regions of the random seed that produce each
outcome) have a controlled union measure; `causality` bounds the measure of the
"superluminal" set; and `causality_ae` states that this set is **almost everywhere
empty** — the probability of violating causality is zero.

# A Deterministic Theory Exists: Inverse-Transform Sampling

Does such a deterministic theory actually exist? Yes, and the construction is the
classical **inverse-transform sampling** method. An experiment always yields a
discrete set of outcomes, so quantum mechanics predicts a cumulative distribution
function. Partition the unit interval into **seed sets** whose lengths are exactly
the predicted probabilities:

$$`\mathrm{seedSet}(k) = [\,\mathrm{cdf}(k),\; \mathrm{cdf}(k+1)\,).`

The verified partition (module `BookProof.ChapterInverseTransform`):

```
#check @InverseTransform.cdf_monotone
#check @InverseTransform.seedSet_measure
#check @InverseTransform.seedSet_disjoint
#check @InverseTransform.seedSet_cover
#check @InverseTransform.seedSet_total_measure
```

Reading them: the CDF is monotone; the $`k`-th seed set has measure exactly
$`p_k`; the seed sets are pairwise disjoint; they cover the whole unit interval; and
their total measure is $`1`. The deterministic theory is then: pick a seed (a point
of $`[0,1]`), find which seed set it lies in, and set the outcome accordingly. Each
run uses a different seed, so the procedure reproduces the quantum probabilities
exactly — and is therefore **experimentally indistinguishable** from quantum
mechanics.

The manuscript is candid that this theory is metaphysically unappealing (it relies
on pseudo-random number generation — one would have to "program" each particle), and
that it is **not** super-deterministic: the experimenter remains free to choose which
measurements to perform. Its purpose is logical, not persuasive: it exhibits a
complete, deterministic, causality-respecting theory compatible with quantum
mechanics, which is enough to show that the EPR and Bell arguments rest on an extra
assumption rather than on a theorem.

# Why No Uniform Countable Measure

One subtlety underlies the whole construction: there is **no** uniform probability
measure on a countable space. The verified statement (module
`BookProof.ChapterNoUniformCountable`):

```
#check @ChapterNoUniformCountable.no_uniform_countable_measure
```

This is why the seed space must be the **continuum** $`[0,1]` (a standard measure
space) rather than a countable set of seeds, and it is the measure-theoretic reason
the deterministic theory uses a continuous random seed.

# Summary

 * A stochastic process can be incomplete in two ways: **stochastic** (missing
   information) and **non-Markov** (hidden variables).
 * Quantum mechanics has only the stochastic kind, so it is a **complete**
   statistical theory in EPR's sense; the EPR inference to the non-Markov kind has no
   mathematical basis.
 * Any deterministic theory compatible with relativistic quantum mechanics respects
   causality, because the superluminal set has measure zero.
 * Such a theory exists, by inverse-transform sampling on $`[0,1]`; it reproduces the
   quantum probabilities exactly and is not super-deterministic.
 * The construction needs a continuous seed because there is no uniform measure on a
   countable space.
