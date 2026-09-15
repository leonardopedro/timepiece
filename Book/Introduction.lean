import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean


#doc (Manual) "Introduction" =>
%%%
tag := "introduction"
%%%

# What Probability Does: Relating the Complex to the Intuitive

:::paragraph
We begin not with a definition of probability, but with a description of what a
probability *does*. The point of view of this book is that a probability is a
_map from complex random events to standard, intuitive random events_. It does not
tell us what randomness _is_; it tells us how an event we do not understand lines
up with one we do.
:::

:::paragraph
Here is the picture from the source manuscript. Suppose someone tells you that a
certain event has probability $`0.32`. The number is a shorthand for the following
sentence:
:::

:::paragraph
_This event is as likely as finding a small object — say, a lost ring — that we
know is buried somewhere in the sand of a one-kilometre beach, if we search for it
with a metal detector over a $`320`-metre interval._
:::

:::paragraph
The treasure hunt is itself ambiguous: we do not know whether there are clues to
the ring's location, how it was lost, or who else has walked the beach. But that
ambiguity has been *moved* by the map. Whatever is mysterious about our original
event has been transferred onto a standard random event — _a point chosen on an
interval_ — that everyone already understands intuitively. The map from the complex
event to the treasure hunt is unambiguous, even though the treasure hunt is not.
:::

:::paragraph
This is the whole game. We do not need to settle what probability _means_. We need
only a disciplined way of *relating* an arbitrary, possibly very complicated
random event to a standard one — a point on a line, a draw from an urn, a spin of a
wheel — whose behaviour is transparent. Kolmogorov's axioms are precisely the rules
that make this relating consistent: a probability space is a sample space (the set
of possible states), a Boolean algebra of events (subsets of states), and a measure
assigning each event a number in $`[0,1]`, with the whole space carrying measure
$`1`.
:::

:::paragraph
Most probability spaces that arise in applications are *standard* measure spaces:
up to sets of measure zero they are the unit interval with Lebesgue measure, a
finite or countable discrete space, or a mixture of the two. On a standard measure
space one can always form regular conditional probabilities, and — this is the
technical fact the whole book rests on — one can always parametrize the resulting
probability distributions by a wave-function on a sphere.
:::

# The Central Idea

:::paragraph
A *probability distribution* on a finite set of outcomes $`\{1, \dots, n\}` is a
list of non-negative numbers that sum to one:
:::

$$`p_1, \dots, p_n \ge 0, \qquad \sum_{k=1}^{n} p_k = 1.`

:::paragraph
The set of all such lists is the *probability simplex*. It is a convex body: a
mixture $`\lambda p + (1-\lambda) q` of two distributions is again a distribution.
This convexity is the mathematical expression of the fact that one can be
_uncertain about which of two models is correct_.
:::

:::paragraph
Now observe a curious fact. Every point of the simplex can be written as the
coordinate-wise square of a point on the unit sphere. If
:::

$$`\psi = (\psi_1, \dots, \psi_n), \qquad \sum_{k=1}^{n} \psi_k^2 = 1,`

:::paragraph
then setting $`p_k = \psi_k^2` automatically gives a probability distribution:
each $`p_k \ge 0` and $`\sum_k p_k = 1`. The vector $`\psi` is a
*wave-function*, and the rule $`p_k = \psi_k^2` (more generally
$`p_k = |\psi_k|^2` over the complex numbers) is *Born's rule*.
:::

:::paragraph
This change of variables — from a distribution $`p` on the simplex to a
wave-function $`\psi` on the sphere — is the seed from which the whole book grows.
It is a _parametrization_: it does not change the probabilities, only the
coordinates we use to describe them. The source manuscript is emphatic that this is
all it is — a "mere (but very useful) parametrization" of probability. The
wave-function is "nothing else than one possible parametrization of any probability
distribution"; the "coherence," "interference," and "collapse" that appear in these
coordinates are features of the parametrization, not new physical phenomena. The
whole quantum formalism is read this way here, against the "exotic" view that
quantum mechanics is a new physics that "shook our sense of reality."
:::

# One Answer Among Many: Coherent Belief

:::paragraph
Because a probability is a _relation_ between events rather than a substance, one
can ask what constraints this relation must obey. Different answers give different
foundations of the same calculus.
:::

:::paragraph
One influential answer treats probabilities as *degrees of belief* and asks: when
is a system of beliefs internally consistent? The *Dutch-book* argument shows
that a bettor whose degrees of belief violate the probability axioms can be offered
a combination of bets that loses money no matter what happens — a _sure loss_.
Avoiding such a sure loss forces the degrees of belief to obey exactly the
probability axioms. We develop this in {ref "dutch-book"}[Part I]. It is a beautiful
and useful answer, and it is _one_ example of what probability can be.
:::

:::paragraph
But it is not the answer this book is built around. The Dutch-book view explains
what coherence _demands_ of a single agent's beliefs. The view we take here is
broader and, we think, closer to how probability is actually used in physics and
engineering: probability is the *bridge* that lets us reason about a complex
random event by relating it to an intuitive one. The wave-function parametrization
is a construction _on that bridge_. Everything else in the book — Born's rule,
unitary evolution, gauge symmetry, the classical limit — is read off from the
geometry of the bridge, not from any single philosophical account of what
probability _is_.
:::

# Why a Simple Solution Exists

:::paragraph
The source manuscript opens with a diagnosis. Real-world engineering is impossible
without managing uncertainty, yet the mathematical tools of engineering
(differential geometry, the calculus of variations) are built on deterministic
logic. The difficulty is sharpest in infinite-dimensional spaces: there is no
Lebesgue measure on an infinite-dimensional Euclidean-like space, and once
probabilities are placed on a space of functions one typically leaves the separable
world in which computation is possible. The result is a zoo of _ad hoc_ methods.
:::

:::paragraph
The manuscript's claim is that the obstruction is narrower than it looks.
Infinite dimensions are not themselves the problem. A *uniform, Lebesgue-like
measure on an infinite-dimensional sphere* _can_ be defined, using the Gaussian
measure and the *Fock space* (the separable Hilbert space used in the second
quantization of free fields). Such a sphere parametrizes the probability
distribution of another probability distribution — a _free-field parametrization_.
We make the finite-dimensional version of this construction precise in
{ref "free-field"}[the free-field chapter].
:::

:::paragraph
The real problem, then, is not infinity but *constraints*: how to impose an exact
constraint inside a separable probability space _without_ giving the constrained set
measure zero. The manuscript's thesis is that *quantum constraints* — which,
unlike classical ones, need not commute with the variables that define the sample
space — solve precisely this. This is the thread that connects the foundations of
probability to the foundations of quantum field theory, and it is the reason a
"simple solution" is even plausible.
:::

# Why "Timepiece"

:::paragraph
The name of the programme refers to a piece of structure that the manuscript insists
on. A *dynamical system* has two parts: a _state_, which is a point of a state
space and involves no time (it is the _present_ state); and an _evolution rule_,
which says how a future state is produced from the present one. The notion of
"time" is determined by the evolution rule itself; it is not a pre-existing
concept, and it may be measured by integers, by real or complex numbers, or by a
more general algebraic object.
:::

:::paragraph
In a Hamiltonian formalism with *time-dependent* transformations, the symplectic
form of conservative classical mechanics is not invariant. The cleanest way to make
non-relativistic mechanics consistent with that fact is to formulate it as a field
theory whose phase space is a fibred manifold over an extra "time" axis. The name
_Timepiece_ refers to this extra axis — defined by the phase space — which is
complementary to the ordinary time defined by the time-evolution operator. The
distinction between these two notions of time recurs throughout the book, and it is
what makes the wave-function parametrization compatible with both classical
Hamiltonian mechanics and quantum mechanics.
:::

# Aim, and What Quantization Is Not

:::paragraph
The aim is a simple, mathematically meaningful account of *quantization* that
applies uniformly to quantum mechanics and to (classical and quantum) statistical
field theory, and that shows the "mystery" of quantum mechanics to be a feature of
the parametrization rather than of nature. To clear the ground, the manuscript is
explicit about what quantization is *not*:
:::

 * It is not *prequantization* — the mechanical replacement of Poisson brackets by
   commutators — which can always be done for analytic functions but does not by
   itself yield useful results.
 * It is not *second quantization* (the Fock-space passage from one particle to
   many), which can only be applied to a theory that is already quantum — hence
   "second".
 * It is not the *Feynman path integral*, which lacks the $`\sigma`-additivity
   that would make it an integral in the first place.
 * It is not a *perturbative expansion* or a *lattice regularization*: both are
   well-defined approximations, but they are complementary, so neither can serve as
   the _definition_.

:::paragraph
The positive proposal is that quantization is a consequence of *time-evolution*:
the wave-function is one parametrization of an arbitrary probability distribution,
the parametrization is a surjective map from a hypersphere to the set of all
probability distributions, and two wave-functions are always related by a rotation
of that hypersphere. The non-commutativity of operators is then intrinsic to _any_
statistical theory, not a deformation imposed on a classical algebra.
:::

# Why Parametrize a Probability by a Wave-function?

:::paragraph
The parametrization $`p_k = \psi_k^2` is many-to-one. Both $`\psi` and
$`-\psi` give the same distribution, and over the complex numbers the whole
*phase* $`e^{i\theta}` is invisible to $`p_k = |\psi_k|^2`. The wave-function
therefore carries _more_ information than the distribution: it remembers a phase
that the probabilities have forgotten.
:::

:::paragraph
This redundancy is not a defect; it is the origin of *interference*. On the
simplex, probabilities only ever add. On the sphere, wave-functions add _first_ and
are squared _afterwards_, so two alternatives $`\psi` and $`\phi` combine as
:::

$$`|\psi + \phi|^2 = |\psi|^2 + |\phi|^2 + 2\,\mathrm{Re}(\overline{\psi}\,\phi),`

:::paragraph
and the final *cross term* is precisely the interference that has no analogue on
the simplex. The double-slit experiment, the Stern–Gerlach experiment, and the rest
of the phenomenology of quantum mechanics are, in this view, consequences of doing
linear algebra on $`\psi` before applying Born's rule.
:::

:::paragraph
The programme of this book is to make this precise and to prove it. The slogan is:
*quantum mechanics is what probability theory looks like when you parametrize the
simplex by the sphere.*
:::

:::paragraph
The slogan is rhetoric, and it should be read with the manuscript's own caveat
attached: quantum mechanics is a generalization of *classical statistical
mechanics*, *not* of probability theory itself. The parametrization by a
wave-function is available for any probability distribution and changes none of
the Kolmogorov axioms; what quantum mechanics adds is the freedom to act on the
parametrized distribution *non-deterministically*. That distinction is stated
precisely in the chapter on deterministic transformations, and again in the
chapter on collapse and the Kolmogorov axioms.
:::

:::paragraph
The unitary time-evolution of quantum mechanics becomes a rotation of the sphere;
the quantization of energy becomes a statement about periodic rotations; gauge
symmetry becomes the invisibility of the phase; and the *classical limit* becomes
the question of when the interference cross terms become negligible.
:::

# Euler's Formula as the Parametrization

:::paragraph
There is an even more explicit form of the same parametrization, and it is the one
that gives the book its name. Any probability distribution on $`n` outcomes can be
written using *Euler angles* $`\theta_1, \dots, \theta_{n-1}` as a telescoping
product of sines and cosines:
:::

$$`p_1 = \cos^2\theta_1, \quad p_2 = \sin^2\theta_1\cos^2\theta_2, \quad p_3 = \sin^2\theta_1\sin^2\theta_2\cos^2\theta_3, \quad \dots`

:::paragraph
with the last outcome carrying the remaining product of sines. Because every
number in $`[0,1]` is a $`\cos^2` of some angle, this parametrization reaches
_every_ distribution; and because the sines and cosines telescope, the
probabilities sum to one *identically*, for every choice of angles. We prove this
in {ref "born-reproduces"}[The Born rule reproduces every distribution].
:::

:::paragraph
For a single two-outcome system the parametrization is the *probability clock*
$`\Psi(t) = (\cos t, \sin t)`. As $`t` advances, the point travels around the unit
circle and the probabilities $`(\cos^2 t, \sin^2 t)` oscillate. The infinitesimal
generator of this motion is the matrix
:::

$$`J = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}, \qquad J^2 = -\mathbf{1},`

:::paragraph
which squares to minus the identity — it is a real incarnation of the imaginary
unit, and *Euler's formula* $`e^{tJ} = \cos t\,\mathbf{1} + \sin t\, J` is the
statement that the rotation of the probability clock is the exponential of this
generator. This is the bridge from probability to the complex numbers, and we make
it explicit in {ref "probability-clock"}[The probability clock and Euler's formula].
:::

# What Is Verified, and How

:::paragraph
The formal counterpart of this book is the Lean 4 library `BookProof`. It currently
contains well over one hundred modules, each formalizing one self-contained
mathematical claim from the source manuscript. The whole library is
*`sorry`-free* (no proof is omitted) and *`axiom`-free* in substance: it relies
only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. (The only
`axiom` declarations are two `axiom … : True` placeholders in the P-versus-NP module,
which this edition does not cite; since `True` is already provable, they add no
logical strength.) The statements quoted in this book are
drawn from that library; each is identified by its Lean name so that you can find
its full proof.
:::

:::paragraph
As a first example, here is the verified statement that the Born-rule/Euler-angle
parametrization really does sum to one for any choice of angles — the formal
counterpart of the telescoping identity previewed above. It lives in the module
`BookProof.ChapterEulerNState`:
:::

```
#check @ChapterEulerNState.euler_sum_one
```

:::paragraph
Reading the type: for any sequence of angles $`\theta` and any number of outcomes
$`n \ge 1`, the sum of the Born probabilities $`\sum_{k<n} \mathrm{bornProb}\,\theta\,n\,k`
equals $`1`. The symbol `#check` asks Lean to print the precise statement of
an existing theorem; the fact that this block elaborates at all is the kernel
confirming that the theorem exists and has exactly this type.
:::

# Roadmap

:::paragraph
The book is organized into six parts.
:::

: Part I — Probability as Coherent Belief

  The probabilistic foundations: the Dutch-book derivation of the probability
  axioms, the associativity of Bayesian updating, the maximum-entropy
  characterization of the uniform prior (and why it holds only relative to a chosen
  parametrization), and the law of total variance.

: Part II — Wave-functions, Euler's Formula, and the Born Rule

  The heart of the book: the probability clock and Euler's formula, the fact that
  the Born rule reproduces every distribution, the gauge ambiguity (phase) of the
  parametrization, information erasure in the Stern–Gerlach experiment, and the
  free-field construction of a uniform measure on a sphere.

: Part III — Entropy, Irreversibility, and the Arrow of Time

  How an irreversible, entropy-increasing dynamics coexists with deterministic
  evolution: injective-but-not-surjective maps, the vanishing probability that a
  random map is invertible, uncountable null-measure sets, cosmological
  amplification of the matter/radiation ratio, and the law of large numbers.

: Part IV — Resolution of the Singularity of an ODE

  An operator-theoretic resolution of the blow-up of $`x' = x^2`, via
  Koopman–von Neumann theory, Weyl quantization, Nelson's essential
  self-adjointness theorem, and the complexification argument
  (`ae_no_real_singular_time`). All results are `sorry`-free.

: Part V — Completeness without Peano Arithmetic

  A metamathematical chapter: the completed Hilbert space is a complete, decidable,
  conservative extension that does not leak undecidable arithmetic, because its
  infinite elements are kept internally unselectable.

: Part VI — Determinism, Complementarity, and Collapse

  The conceptual core of the manuscript's quantum-foundations chapters: deterministic
  versus non-deterministic transformations and the origin of complementarity; why
  wave-function collapse keeps quantum mechanics an ordinary (Kolmogorov)
  probability theory, and how this differs from Gleason's theorem; the Euler-angle
  parametrization in arbitrary, countable, complex, and quaternionic dimension; the
  theorem that time-translation is a stochastic process _if and only if_ it is
  deterministic; the double-slit and Bell/CHSH experiments; EPR-completeness and
  relativistic causality; and the classical limit.
