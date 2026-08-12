import VersoManual

import Book.Introduction
import Book.DutchBook
import Book.SequentialBayes
import Book.MaxEntropy
import Book.TotalVariance
import Book.ProbabilityClock
import Book.BornReproduces
import Book.BornFiber
import Book.GaugeSymmetry
import Book.SternGerlach
import Book.RealRepresentations
import Book.YangMillsQuantization
import Book.GribovAmbiguity
import Book.PhysicalParity
import Book.DiffeomorphismsGravity
import Book.ConsciousnessBayesianPrior
import Book.AlignedDeepLearning
import Book.CoherentState
import Book.FreeField
import Book.Irreversibility
import Book.BijectionProbability
import Book.NullMeasure
import Book.BaryonAsymmetry
import Book.MeasurementLLN
import Book.OdeSingularity
import Book.PaFreeHilbert
import Book.DeterministicTransformations
import Book.CollapseKeepsKolmogorov
import Book.DoubleSlit
import Book.BellInequalities
import Book.EPRComplete
import Book.ProofPlans
import Book.SpinStatistics
import Book.SolovayTensor
import Book.ConditionalUnitary

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Timepiece: A Verified Mathematical Tour" =>
%%%
authors := ["The Timepiece Project"]
shortTitle := "Timepiece"
%%%

{index}[Timepiece]

This book is a pedagogical, machine-verified tour of the mathematical ideas behind
the _Timepiece_ programme: the observation that an ordinary probability measure can
be *parametrized by a wave-function*, and that this single change of variables
naturally reproduces the structural backbone of quantum mechanics — Born's rule,
unitary time-evolution, gauge symmetry, quantization, and the classical limit — as
theorems of probability theory rather than as physical postulates.

Every mathematical claim that can be made precise here is backed by a formal proof
in the Lean 4 proof assistant, checked against the Mathlib library. The companion
library `BookProof` contains these proofs; this book presents them.

# Preface: How to Read This Book
%%%
tag := "preface"
number := false
%%%

The book is written to be read in two layers at once.

: The mathematical layer

  Each chapter develops a self-contained mathematical idea in ordinary prose and
  notation, with a complete *sketch proof*. These sketches are meant to be
  readable: they explain _why_ a statement is true, not merely _that_ it is true.

: The verified layer

  Each section ends with one or more Lean 4 code blocks naming the theorem that
  formalizes the claim, identified by its exact Lean name (for example
  `ChapterTotalVariance.total_variance`). The full proof lives in the `BookProof`
  library. Where a claim is not yet proved, we say so and give a proof plan in
  {ref "proof-plans"}[the appendix].

*Verifying everything for yourself.* Two commands reproduce the whole
verification. From the repository root:

```
lake build BookProof
```

compiles the entire library of formal proofs. It is `sorry`-free, and every theorem
cited in this book relies only on Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`. The only `sorry`s in the repository are the two intentional,
quarantined ones in `UnusedRoute/SchoenfeldPRA.lean` (a historical PRA spine this
edition does not import); the claims they leave open are stated and planned in
{ref "proof-plans"}[the appendix]. And

```
lake build book && lake exe book
```

rebuilds this book and renders the HTML you are reading as a single page at
`_out/html-single/index.html`. (The Lean statements are currently shown as plain code
blocks; upgrading them to elaborated, hover-enabled blocks, and migrating to
`verso-blueprint`, are planned — see {ref "proof-plans"}[the appendix].)

*Scope of this edition.* This is a curated edition. It follows the structure of
the source manuscript `book.tex`, but it selects the threads whose mathematics is
both self-contained and already formalized. Two chapters of the manuscript are
deliberately replaced here:

 * the chapter on the ordinary differential equation $`x' = x^2` is presented in
   its expanded, operator-theoretic form ({ref "ode-chapter"}[Resolution of the
   singularity of an ODE]);
 * the chapters on _P versus NP_ and on the _Riemann Hypothesis_ are replaced by a
   single, self-contained metamathematical chapter
   ({ref "pa-free-chapter"}[Completeness without Peano Arithmetic]) that captures
   the precise point those chapters were making: a completed Hilbert space can be a
   complete, decidable extension that does not leak undecidable arithmetic, provided
   its infinite elements are kept _internally unselectable_.

*A note on what remains open.* Where a statement is mathematically relevant to the
narrative but is not yet proved in `BookProof`, we say so explicitly and give a
detailed proof plan in {ref "proof-plans"}[Appendix: Proof Plans]. Nothing in the
verified layer is asserted without a proof; the open items are quarantined there.

{include 0 Book.Introduction}

# Probability as Coherent Belief
%%%
tag := "part-probability"
%%%

The first part builds the probabilistic foundation on which the rest of the book
rests. We begin from the most primitive question — _what does it mean for a system
of degrees of belief to be consistent?_ — and recover the probability axioms as the
answer (the Dutch-book theorem). We then establish the three working tools used
throughout: the associativity of Bayesian updating, the maximum-entropy
justification of the uniform prior, and the decomposition of variance into
_within-group_ and _between-group_ parts.

{include 0 Book.DutchBook}

{include 0 Book.SequentialBayes}

{include 0 Book.MaxEntropy}

{include 0 Book.TotalVariance}

# Wave-functions, Euler's Formula, and the Born Rule
%%%
tag := "part-born"
%%%

The heart of the book. We make precise the parametrization of a probability
distribution by a wave-function: the probability clock and Euler's formula in two
dimensions, the fact that the Born rule reproduces _every_ distribution in any finite
(or countable) dimension, the gauge ambiguity (the invisible phase) of the
parametrization, the parametrization of any joint or conditional probability by a
unitary operator (the finite-dimensional core of the book's commutative Wigner
theorem), information erasure in the Stern–Gerlach experiment, the
free-field construction of a uniform measure on a sphere out of the Gaussian, and the
spin–statistics dichotomy that distinguishes bosonic commutation from fermionic
anticommutation in a finite tensor product of sample spaces.

{include 0 Book.ProbabilityClock}

{include 0 Book.BornReproduces}

{include 0 Book.BornFiber}

{include 0 Book.ConditionalUnitary}

{include 0 Book.GaugeSymmetry}

{include 0 Book.SternGerlach}

{include 0 Book.FreeField}

{include 0 Book.SpinStatistics}

# Relativity, Gauge Theory, and Gravity
%%%
tag := "part-relativity"
%%%

The manuscript's relativistic and field-theoretic programme. We develop the
Lorentz group and its real representations, the CPT theorem and the relativistic
position operator; quantization arising from time-evolution (Yang–Mills, the
Weyl/CCR relations, the nilpotent BRST charge); the Gribov ambiguity and the
abelian (electromagnetic) case; the physical parity transformation and
antiparticles; and the diffeomorphism/`3+1` structure of gravity.

{include 0 Book.RealRepresentations}

{include 0 Book.YangMillsQuantization}

{include 0 Book.GribovAmbiguity}

{include 0 Book.PhysicalParity}

{include 0 Book.DiffeomorphismsGravity}

# Consciousness, Deep Learning, and the Bayesian Prior
%%%
tag := "part-consciousness"
%%%

The manuscript's Bayesian foundations of agency. We show that no point of null
measure is special and no prior is best for all cases, that a deterministic prior
is still subjective, and that Bayesian inference is a unitary representation; and
that randomized (deep) learning is a random sampling method inducing a Bayesian
posterior over models. We close with the coherent-state reading of Softmax
attention, where the Born rule on coherent states is shown to be the same equation
as the attention mechanism.

{include 0 Book.ConsciousnessBayesianPrior}

{include 0 Book.AlignedDeepLearning}

{include 0 Book.CoherentState}

# Entropy, Irreversibility, and the Arrow of Time
%%%
tag := "part-entropy"
%%%

How an irreversible, entropy-increasing dynamics coexists with deterministic
evolution. We characterize irreversibility as injective-but-not-surjective dynamics,
show that a random map is almost surely non-invertible, exhibit uncountable
null-measure sets, quantify the cosmological amplification of the matter/radiation
ratio, and close with the law of large numbers that gives the probabilities their
empirical meaning.

{include 0 Book.Irreversibility}

{include 0 Book.BijectionProbability}

{include 0 Book.NullMeasure}

{include 0 Book.BaryonAsymmetry}

{include 0 Book.MeasurementLLN}

# The ODE Singularity
%%%
tag := "part-ode"
%%%

An operator-theoretic resolution of the finite-time blow-up of $`x' = x^2`, replacing
the ODE chapter of the manuscript.

{include 0 Book.OdeSingularity}

# A Decidable, Complete Foundation
%%%
tag := "part-pa-free"
%%%

A metamathematical chapter replacing the manuscript's chapters on _P versus NP_ and
the _Riemann Hypothesis_: the completed Hilbert space is complete and decidable
because its infinite elements are kept internally unselectable. The second chapter
builds the Solovay–Kopperman tensor product on this foundation: a finite-dimensional
factor carrying an arbitrary probability law, tensored with a separable
infinite-dimensional factor whose law is forced to be the Mehler measure precisely
because the language cannot distinguish its elements.

{include 0 Book.PaFreeHilbert}

{include 0 Book.SolovayTensor}

# Determinism, Complementarity, and Collapse
%%%
tag := "part-foundations"
%%%

The conceptual core of the manuscript's quantum-foundations chapters. We begin with
the group-theoretic fact that a symmetry group of canonical transformations is a
unitary representation, taking the one-parameter time-translation group as the
prototype; characterize deterministic versus non-deterministic symmetry
transformations and locate the origin of complementarity; show why wave-function
collapse keeps quantum mechanics an ordinary Kolmogorov probability theory, and how
this differs from Gleason's theorem; prove that time-translation
is a stochastic process _if and only if_ it is deterministic; reconstruct a quantum
trajectory at intermediate times by post-selection; work the double-slit
and Bell/CHSH experiments; and close with EPR-completeness, relativistic causality,
a concrete deterministic theory, and the classical limit.

{include 1 Book.DeterministicTransformations}

{include 1 Book.CollapseKeepsKolmogorov}

{include 1 Book.DoubleSlit}

{include 1 Book.BellInequalities}

{include 1 Book.EPRComplete}

{include 0 Book.ProofPlans}

# Index
%%%
tag := "index"
number := false
%%%

{theIndex}
