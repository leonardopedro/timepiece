import VersoManual

import Book.Introduction
import Book.DutchBook
import Book.SequentialBayes
import Book.MaxEntropy
import Book.TotalVariance
import Book.ProbabilityClock
import Book.BornReproduces
import Book.BornFiber
import Book.SternGerlach
import Book.FreeField
import Book.Irreversibility
import Book.BijectionProbability
import Book.NullMeasure
import Book.BaryonAsymmetry
import Book.MeasurementLLN
import Book.OdeSingularity
import Book.PaFreeHilbert
import Book.ProofPlans

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
be **parametrized by a wave-function**, and that this single change of variables
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
  notation, with a complete **sketch proof**. These sketches are meant to be
  readable: they explain _why_ a statement is true, not merely _that_ it is true.

: The verified layer

  Each section ends with one or more Lean 4 code blocks naming the theorem that
  formalizes the claim, identified by its exact Lean name (for example
  `ChapterTotalVariance.total_variance`). The full proof lives in the `BookProof`
  library. Where a claim is not yet proved, we say so and give a proof plan in
  {ref "proof-plans"}[the appendix].

**Verifying everything for yourself.** Two commands reproduce the whole
verification. From the repository root:

```
lake build BookProof
```

compiles the entire library of formal proofs (it is `sorry`-free and `axiom`-free,
relying only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound`).
And

```
lake build book && lake exe book
```

rebuilds this book and renders the HTML you are reading into the directory
`_out/html-multi/`. (The Lean statements are currently shown as plain code blocks;
upgrading them to elaborated, hover-enabled blocks, and migrating to
`verso-blueprint`, are planned — see {ref "proof-plans"}[the appendix].)

**Scope of this edition.** This is a curated edition. It follows the structure of
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

**A note on what remains open.** Where a statement is mathematically relevant to the
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
parametrization, information erasure in the Stern–Gerlach experiment, and the
free-field construction of a uniform measure on a sphere out of the Gaussian.

{include 0 Book.ProbabilityClock}

{include 0 Book.BornReproduces}

{include 0 Book.BornFiber}

{include 0 Book.SternGerlach}

{include 0 Book.FreeField}

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

# Resolution of the Singularity of an ODE
%%%
tag := "part-ode"
%%%

An operator-theoretic resolution of the finite-time blow-up of $`x' = x^2`, replacing
the ODE chapter of the manuscript.

{include 0 Book.OdeSingularity}

# Completeness without Peano Arithmetic
%%%
tag := "part-pa-free"
%%%

A metamathematical chapter replacing the manuscript's chapters on _P versus NP_ and
the _Riemann Hypothesis_: the completed Hilbert space is complete and decidable
because its infinite elements are kept internally unselectable.

{include 0 Book.PaFreeHilbert}

{include 0 Book.ProofPlans}

# Index
%%%
tag := "index"
number := false
%%%

{theIndex}
