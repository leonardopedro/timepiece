import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean


#doc (Manual) "The Dutch-book Theorem: Probability Is Coherence" =>
%%%
tag := "dutch-book"
%%%

# Orientation and Status

The Dutch-book result is a finite sample-space theorem. It establishes the precise
coherence/probability equivalence used by the manuscript, while continuous-space
and decision-theoretic extensions require separate measure and utility hypotheses.

# The Question

:::paragraph
Before we can parametrize probability distributions by wave-functions, we should
ask what a probability distribution _is_, and why its rules are the rules they are.
The cleanest answer is due to de Finetti and Ramsey, and it is operational:
probabilities are *coherent betting prices*.
:::

:::paragraph
Imagine a bookmaker who posts a price $`\mathrm{Pr}(A)` for each event
$`A` in a finite sample space $`\Omega`. A bettor may buy, for a stake
$`s`, a ticket on $`A` that pays $`s` if $`A` happens and returns the price
$`s\cdot\mathrm{Pr}(A)` regardless. The bookmaker's *net payoff* in a state
$`\omega` from a finite family of such bets is
:::

$$`\mathrm{payoff}(\omega) = \sum_i s_i\big(\mathbf{1}_{A_i}(\omega) - \mathrm{Pr}(A_i)\big).`

:::paragraph
The posted prices are *incoherent* if the bettor can choose stakes so that the
bookmaker loses money in _every_ state — that is, $`\mathrm{payoff}(\omega) < 0`
for all $`\omega`. Such a guaranteed-loss portfolio is called a *Dutch book*.
The prices are *coherent* if no Dutch book exists.
:::

:::paragraph
The theorem, made precise below, is the striking fact:
:::

:::paragraph
*The coherent price systems are exactly the probability distributions.*
:::

:::paragraph
In other words, the Kolmogorov axioms — non-negativity, normalization, and finite
additivity — are not arbitrary conventions. They are precisely the condition under
which a bookmaker cannot be forced into a sure loss. Probability is _consistency of
partial belief_.
:::

# The Formal Setup

:::paragraph
We work on a finite sample space $`\Omega`. A price system is a function
$`\mathrm{Pr} : \mathrm{Finset}\,\Omega \to \mathbb{R}` assigning a real number to
each event. The two central definitions are:
:::

```
#check @ChapterDutchBook.HasDutchBook
#check @ChapterDutchBook.Coherent
```

:::paragraph
Thus `HasDutchBook Pr` says there is a finite family of bets whose payoff is
strictly negative in every state, and `Coherent Pr` is its negation. A
genuine probability distribution is recorded by:
:::

```
#check @ChapterDutchBook.IsProb
#check @ChapterDutchBook.Represents
```

:::paragraph
Here `Represents Pr p` means that the price of every event is the
$`p`-measure of that event, $`\mathrm{Pr}(A) = \sum_{\omega \in A} p(\omega)`.
:::

# Sketch Proof

:::paragraph
*Easy direction — a probability is coherent.* Suppose $`\mathrm{Pr}(A) =
\sum_{\omega \in A} p(\omega)` for a genuine distribution $`p`. Take the
$`p`-expectation of the payoff:
:::

$$`\sum_{\omega} p(\omega)\,\mathrm{payoff}(\omega) = \sum_i s_i\Big(\sum_\omega p(\omega)\mathbf{1}_{A_i}(\omega) - \mathrm{Pr}(A_i)\Big) = \sum_i s_i\big(\mathrm{Pr}(A_i) - \mathrm{Pr}(A_i)\big) = 0.`

:::paragraph
A quantity whose $`p`-average is $`0` cannot be strictly negative at every state
(since $`p` is a probability and at least one state has positive weight). So no
Dutch book exists.
:::

:::paragraph
*Hard direction — coherence forces the axioms.* Assume $`\mathrm{Pr}` is
coherent. Each axiom is forced by an explicit Dutch book that would otherwise be
available to the bettor:

 * $`\mathrm{Pr}(\varnothing) = 0`: if the price of the empty event were positive,
   buy a ticket on it — it never pays, so the bookmaker loses the price in every
   state.
 * $`\mathrm{Pr}(\Omega) = 1`: if the price of the certain event were not $`1`, a
   single ticket on $`\Omega` (which always pays its stake) yields a sure gain or
   loss.
 * $`0 \le \mathrm{Pr}(A) \le 1`: a negative price, or a price above $`1`, is
   exploited by a single ticket on $`A`.
 * *Finite additivity on disjoint events*: if $`A \cap B = \varnothing` but
   $`\mathrm{Pr}(A \cup B) \ne \mathrm{Pr}(A) + \mathrm{Pr}(B)`, a three-ticket
   portfolio — long $`A \cup B` and short $`A` and $`B` (or the reverse) — locks in
   the discrepancy as a sure profit.
:::

:::paragraph
Once additivity holds, the price of any event is the sum of the prices of its
singletons, $`\mathrm{Pr}(A) = \sum_{\omega \in A} \mathrm{Pr}(\{\omega\})`. So the
distribution $`p(\omega) := \mathrm{Pr}(\{\omega\})` *represents* $`\mathrm{Pr}`,
and the axioms above make $`p` a genuine probability. This is the converse
direction.
:::

# The Verified Statement

:::paragraph
The full equivalence is the headline theorem of `BookProof.ChapterDutchBook`:
:::

```
#check @ChapterDutchBook.coherent_iff_exists_prob
```

:::paragraph
The two directions are also available separately. That a represented probability is
coherent:
:::

```
#check @ChapterDutchBook.represents_isProb_coherent
```

:::paragraph
and that coherence yields a representing distribution, built from the singleton
prices:
:::

```
#check @ChapterDutchBook.coherent_exists_prob
#check @ChapterDutchBook.Coherent.additive
```

:::paragraph
The last of these is the finite-additivity step, the only part of the argument that
needs a genuinely new idea (the three-ticket book); the rest are one-ticket
constructions.
:::

# Why This Matters Here

:::paragraph
The Dutch-book theorem fixes the stage on which the rest of the book is played.
Whatever parametrization we choose for a probability distribution — and we will
choose a wave-function — it must land inside the coherent price systems, i.e. inside
the simplex. The parametrizations of Part II will be maps _into_ this simplex, and
the theorem above tells us exactly what it means for the image to be a legitimate
probability.
:::

# The Rules Are Objective; The Priors Are Not

:::paragraph
There is a misreading the theorem invites, and the source manuscript is explicit in
resisting it. The Dutch-book argument makes the *rules* of probability objective:
coherence forces non-negativity, normalization, and finite additivity, and there is
no choice in the matter. It does *not* make the *priors* objective. Coherence
constrains the _form_ a probability must take — it must be a point of the simplex —
but it is silent on _which_ point of the simplex is the right one. The prior is a
free, unavoidable act of theoretical prejudice.
:::

:::paragraph
The manuscript leans on this repeatedly, citing the result of Eaton and Freedman
(_Dutch book against some 'objective' priors_, Bernoulli 10(5), 2004, 861–872): "in
Bayesian inference there is always a prior probability distribution, and there is no
prior which is better for all cases." Priors that are marketed as "objective" —
symmetry priors, reference priors, and the uniform prior among them — can themselves
be Dutch-booked; no single prior is good for every problem. The same source draws
the sharper conclusion that "there are no non-informative priors in Bayesian
inference, therefore theoretical prejudice is unavoidable."
:::

:::paragraph
This is the betting-theoretic complement to the coordinate argument of
{ref "sequential-bayes"}[the previous chapter]. There the point was that the uniform
prior's distinguishing properties — relabeling-invariance, maximum entropy — hold
only _within a fixed parametrization_, and that any non-null finite prior can be
reparametrized into the uniform one. Here the point is that coherence cannot certify
any prior as the correct one, because against any proposed "objective" prior an
adversary can construct a Dutch book in some problem. The uniform prior is
appropriate "in many cases, not in all cases": a useful default, not an objective
truth.
:::

:::paragraph
So the Dutch-book theorem fixes the *objective* part of probability — the
calculus, the simplex, the rules any coherent belief must obey — and leaves the
*subjective* part exactly where it belongs, in the choice of prior. The
parametrizations of Part II map into this objectively fixed simplex; the point they
land on is never forced by coherence alone. The one place a prior _is_ forced is the
infinite-dimensional tail of the {ref "solovay-tensor"}[Solovay–Kopperman
construction], and there it is forced not by Dutch-book objectivity but by the
blindness of the decidable language: the Mehler measure is the only law the language
can express, not the only law a rational agent may hold.
:::
