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
import Book.Starobinsky
import Book.NavierStokesHashimoto
import Book.CarlemanFlux
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

*How to read this part.* Read {ref "pa-free-chapter"}[Completeness without Peano
Arithmetic] first: its one verified engine is the Riesz–Fischer characterization of
completeness by absolutely convergent series, and its one discipline is the refusal
to name infinite elements as constants. Everything else in the part — the
head–tail decomposition, the Mehler measure on the tail, the decidability of tensor
products — is the same discipline applied to two factors instead of one. When the
later physics chapters speak of a "free field" or of the "infinite tail" of a
state space, this is the precise object they mean; the {ref "free-field"}[free-field
chapter] in Part Relativity is the direct descendant of these two chapters and
repays re-reading them.

{include 0 Book.PaFreeHilbert}

{include 0 Book.SolovayTensor}

# Probability as Coherent Belief
%%%
tag := "part-probability"
%%%

The second part builds the probabilistic foundation on which the rest of the book
rests. We begin from the most primitive question — _what does it mean for a system
of degrees of belief to be consistent?_ — and recover the probability axioms as the
answer (the Dutch-book theorem). We then establish the three working tools used
throughout: the associativity of Bayesian updating, the maximum-entropy
justification of the uniform prior, and the decomposition of variance into
_within-group_ and _between-group_ parts.

*How to read this part.* The four chapters are a single toolkit, and they are
used constantly in the rest of the book. {ref "dutch-book"}[The Dutch-book theorem]
fixes the *target* of every later construction: whatever the wave-function
parametrization produces, it must land inside the coherent price systems, i.e.
inside the simplex. {ref "sequential-bayes"}[Bayesian updating is associative] is
the coherence property that makes the posterior a genuine state of knowledge, and
{ref "max-entropy"}[maximum entropy] and {ref "total-variance"}[the law of total
variance] are the two quantitative instruments — the former a principle for
*choosing* priors within a parametrization, the latter a bookkeeping identity for
*combining* sources of uncertainty. A reader who wants the conceptual core can read
just the Dutch-book chapter and the law of total variance; the other two are needed
by the consciousness and deep-learning parts later.

{include 0 Book.DutchBook}

{include 0 Book.SequentialBayes}

{include 0 Book.MaxEntropy}

{include 0 Book.TotalVariance}

# Determinism, Complementarity, and Collapse
%%%
tag := "part-foundations"
%%%

The third part is the conceptual core of the manuscript's quantum-foundations
chapters. We begin with the group-theoretic fact that a symmetry group of canonical
transformations is a unitary representation, taking the one-parameter time-translation
group as the prototype; characterize deterministic versus non-deterministic symmetry
transformations and locate the origin of complementarity; show why wave-function
collapse keeps quantum mechanics an ordinary Kolmogorov probability theory, and how
this differs from Gleason's theorem; prove that time-translation
is a stochastic process _if and only if_ it is deterministic; reconstruct a quantum
trajectory at intermediate times by post-selection; work the double-slit
and Bell/CHSH experiments; and close with EPR-completeness, relativistic causality,
a concrete deterministic theory, and the classical limit.

*How to read this part.* {ref "deterministic-transformations"}[Symmetries,
determinism, and complementarity] is the load-bearing chapter: everything else in
the part is an application of its one theorem — time-translation is a stochastic
process iff it is deterministic. {ref "collapse-kolmogorov"}[Collapse keeps quantum
mechanics a probability theory] answers the standard objection, and
{ref "double-slit"}[the double-slit experiment] and {ref "bell-inequalities"}[the
Bell inequalities] are the two laboratory situations the manuscript reads through
that lens; {ref "epr-complete"}[EPR-completeness] closes the logical circle. These
four form a single argument and are best read in sequence; the double-slit chapter
additionally introduces the post-selection and weak-value machinery that the
Solovay–Kopperman tensor product chapter later generalizes.

{include 1 Book.DeterministicTransformations}

{include 1 Book.CollapseKeepsKolmogorov}

{include 1 Book.DoubleSlit}

{include 1 Book.BellInequalities}

{include 1 Book.EPRComplete}

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
theorem), and information erasure in the Stern–Gerlach experiment.

*How to read this part.* {ref "probability-clock"}[The probability clock] is the
smallest possible instance of the whole book — read it first even if you read
nothing else in this part, since it introduces the generator $`J^2 = -1`$, Euler's
formula, and the singular collapse matrix in two dimensions. {ref "born-reproduces"}[The
Born rule reproduces every distribution] lifts the construction to $`n` outcomes,
countable chains, and the complex and quaternionic cases; {ref "born-fiber"}[the
gauge ambiguity] explains what is *invisible* in the parametrization. The remaining
two chapters are the bridge to physics: {ref "conditional-unitary"}[a joint
probability is a wave-function] is the finite-dimensional core of the commutative
Wigner theorem, and {ref "stern-gerlach"}[the Stern–Gerlach experiment] is the
first laboratory application. This part is the prerequisite for the field-theory
and relativity part that follows.

{include 0 Book.ProbabilityClock}

{include 0 Book.BornReproduces}

{include 0 Book.BornFiber}

{include 0 Book.ConditionalUnitary}

{include 0 Book.SternGerlach}

# Relativity, Gauge Theory, and Gravity
%%%
tag := "part-relativity"
%%%

The manuscript's relativistic and field-theoretic programme. We develop the
Lorentz group and its real representations, the CPT theorem and the relativistic
position operator; quantization arising from time-evolution (Yang–Mills, the
Weyl/CCR relations, the nilpotent BRST charge); the Gribov ambiguity and the
abelian (electromagnetic) case; the physical parity transformation and
antiparticles; and the diffeomorphism/`3+1` structure of gravity. We also develop
the field-theoretic foundations: gauge symmetry and dissipative dynamics, the
free-field construction of a uniform measure on a sphere out of the Gaussian, and
the spin–statistics dichotomy that distinguishes bosonic commutation from
fermionic anticommutation.

*How to read this part.* This is the longest part and the one with the most
independent threads. The two foundation chapters — {ref "gauge-symmetry"}[Gauge
symmetry and dissipative dynamics] and {ref "free-field"}[the free-field
construction] — set the vocabulary (gauge as parametrization redundancy, the
Gaussian as the rotation-invariant prior) that the rest assume. The middle block
({ref "real-representations"}[Real representations], {ref "quantization-time-evolution"}[Quantization
due to time-evolution], {ref "gribov-ambiguity"}[the Gribov ambiguity],
{ref "physical-parity"}[the physical parity transformation]) is the Standard-Model
thread, and can be read largely independently of the free-field thread. The final
chapters — {ref "diffeomorphisms-gravity"}[Diffeomorphisms and gravity], the
Starobinsky scalaron, and the Navier–Stokes and Carleman threads — apply the same
parametrization to the systems whose numerical validation is carried out in the
companion solver work: the 3D gauge-fixed gravity Hamiltonian, the Yang–Mills
Hamiltonian, and the Eulerian Navier–Stokes fiber. The {ref "spin-statistics"}[spin–
statistics] chapter belongs with the free-field thread (it is the finite-degree
instance of the tensor products of sample spaces).

{include 0 Book.GaugeSymmetry}

{include 0 Book.FreeField}

{include 0 Book.SpinStatistics}

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

*How to read this part.* The three chapters share one thesis — a system is a
Bayesian prior in action — but they use it in three different registers.
{ref "consciousness-bayesian-prior"}[Consciousness as a representation of a
Bayesian prior] is the philosophical application and needs only the probability
part behind it. {ref "aligned-deep-learning"}[Aligned deep learning as a random
sampling method] is the engineering application and re-uses the induced-prior
machinery of the Bayesian chapters. {ref "coherent-state-attention"}[Softmax is the Born rule
on coherent states] is the closest to physics: it re-uses the Gaussian of the
free-field chapter and the Born rule of Part II, and it is the one chapter here
that connects directly to the harmonic-oscillator machinery of the field-theory
part.

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

*How to read this part.* {ref "irreversibility"}[Irreversibility: injective but not
surjective] and {ref "bijection-probability"}[a random map is almost surely
non-invertible] form one argument (irreversibility is generic), while
{ref "null-measure"}[null-measure sets need not be small] is the measure-theoretic
caution that keeps the argument honest. {ref "baryon-asymmetry"}[the baryon
asymmetry] is the cosmological application — the one place the part connects to
the gravity thread, via the Friedmann–Robertson–Walker scaling that the companion
numerical validation checks — and {ref "measurement-lln"}[the law of large numbers]
closes the part by giving the probabilities their empirical content. Read the first
two chapters and the LLN chapter for the core; the baryon-asymmetry chapter needs
the FLRW terminology of the gravity part.

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

*How to read this part.* A single self-contained chapter, followed by the proof-plan
appendix. It is the book's most explicit exercise in *honesty about verification*:
read the section "What Is Verified, and What Is Open" carefully — the repository's
`Singularity` library is `sorry`-free, but it splits into genuine theorems (the
complexification resolution, the spectral energy bound) and algebraic certificates
(the flow-completeness flags) that must not be read as analytic results. The
chapter is also the conceptual bridge to the numerical SIRK solver work: the
detection pipeline and the change-of-variables strategy it describes are the same
ideas the companion solver implements when it evolves singular-looking systems.

{include 0 Book.OdeSingularity}

{include 0 Book.ProofPlans}

# Index
%%%
tag := "index"
number := false
%%%

{theIndex}
