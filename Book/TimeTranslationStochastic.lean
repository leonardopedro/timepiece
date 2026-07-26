import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Time-Translation Is a Stochastic Process If and Only If It Is Deterministic" =>
%%%
tag := "time-translation-stochastic"
%%%

# The Question

A **stochastic process** is a family of random events indexed by time: there is a
probability distribution for _each_ time, and the times are glued together by
conditional probabilities. Does the time-evolution of quantum mechanics define such
a process? The manuscript's answer is a precise and surprising one:

:::paragraph
There is a group action of a symmetry group on the **probability distribution** if
and only if the symmetry transforms **deterministic** distributions into
deterministic distributions. In particular, **time-translation in quantum mechanics
is a stochastic process if and only if it is deterministic.**
:::

This single fact is, the manuscript argues, overlooked by the assumptions of both
Bell's theorem and the EPR paradox.

# Setting Up the Equality

Start with a probability distribution $`\mathrm{diag}(\rho_1)`. Acting on the
wave-function with a group element $`g` and then collapsing gives a new distribution
$`\mathrm{diag}(\rho_g)`. The composition of two group elements $`g, h`, applied to
an event $`A`, would be the succession of two random experiments:

$$`P(A) = \mathrm{tr}\bigl(\mathrm{diag}(\rho_g)\, U_h P_A U_h^\dagger\bigr).`

But **Wigner's theorem** says the action of a symmetry on the wave-function is
linear and unitary, which would instead give

$$`P(A) = \mathrm{tr}\bigl(\rho_g\, U_h P_A U_h^\dagger\bigr).`

For the symmetry to act on the **probability distribution** (and hence for a
stochastic process to exist), these two expressions must agree for every pure
$`\rho_g`, every event $`A`, and every group element $`h`:

$$`\mathrm{tr}\bigl(\mathrm{diag}(\rho_g)\, U_h P_A U_h^\dagger\bigr) = \mathrm{tr}\bigl(\rho_g\, U_h P_A U_h^\dagger\bigr).`

# The Difference Is the Off-Diagonal Part

The two traces differ exactly by the off-diagonal part of $`\rho_g`. The verified
accounting (module `BookProof.ChapterTimeTranslation`):

```
#check @ChapterTimeTranslation.trace_rho_measOp
#check @ChapterTimeTranslation.trace_diagPart_measOp
#check @ChapterTimeTranslation.trace_diff
```

The first two compute the two traces; the third isolates their difference. The
headline equivalence then falls out:

```
#check @ChapterTimeTranslation.trace_eq_iff_isDeterministic
#check @ChapterTimeTranslation.trace_eq_iff_isDeterministic_pure
```

Reading them: the two traces agree for every state and every event **if and only
if** $`U` is deterministic (the second states the same for pure states only).

The mechanism is concrete. If $`U` is deterministic, then
$`\overline{U_{ja}}\, U_{jl} = 0` whenever $`a \neq l`, so the off-diagonal
contribution vanishes. If $`U` is **not** deterministic, then for some column
$`a` and some $`l \neq m` one has $`\overline{U_{ma}}\, U_{la} \neq 0`; choosing the
superposition $`\Psi = (\delta_m + \delta_l)/\sqrt 2` makes the difference of traces
equal to $`\overline{U_{ma}}\, U_{la} \neq 0`. The same content, phrased through the
off-diagonal part (module `BookProof.ChapterReconstruct`):

```
#check @ChapterReconstruct.offDiag_eq_zero_iff_isDeterministic
```

# Why It Matters

If the time-evolution is non-deterministic, then there is **no** probability
distribution attached to each intermediate time — the symmetry does not descend to
the distributions, so no stochastic process is defined. One applies a single
non-deterministic transformation; the parameter one calls "time" merely labels which
transformation, it does not index a family of random events.

This is the mathematical core behind several of the manuscript's most provocative
claims:

 * **EPR.** After the entangled particles separate and before the measurement
   transformation, there is no probability distribution for the state — because the
   (non-deterministic) time-evolution is not a stochastic process.
 * **Bell.** The Bell assumptions implicitly treat the time-evolution as a stochastic
   process; the theorem above shows that this is legitimate only in the
   deterministic case.
 * **The double-slit.** The product of two non-deterministic transformations is not
   the same as a stochastic process in which they are applied in sequence — which is
   exactly why the interference pattern appears (see
   {ref "double-slit"}[the double-slit chapter]).

# Summary

 * A symmetry acts on the probability distribution iff the "collapsed" and
   "uncollapsed" traces agree for every state and event.
 * They agree **iff** the symmetry is deterministic — the difference is precisely the
   off-diagonal coherence.
 * Hence time-translation in quantum mechanics is a stochastic process **if and only
   if** it is deterministic.
 * Non-deterministic evolutions do not define a probability distribution at each
   time; this is the structural fact behind the EPR, Bell, and double-slit
   discussions.
