import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Collapse Keeps Quantum Mechanics a Probability Theory" =>
%%%
tag := "collapse-kolmogorov"
%%%

# The Apparent Non-Commutativity

It is often said that quantum mechanics is a *non-commutative generalization of
probability theory*. The evidence seems clear: the projection $`P_X` onto a region
of space and the projection $`U P_p U^\dagger` onto a region of momentum are
diagonal in different bases (related by a Fourier transform $`U`), so they do not
commute. Since we may choose to measure position _or_ momentum, the algebra of
"events" looks non-commutative.

The manuscript's claim is that this appearance is created by *forgetting the
collapse*. Once the collapse is taken seriously, quantum mechanics remains an
ordinary Kolmogorov probability theory, even when complementary observables are
considered.

# The State of an Ensemble Is Diagonal

The state of a statistical ensemble is a linear functional $`E(A) = \mathrm{tr}(\rho A)`
on operators, where $`\rho` is a self-adjoint operator with $`\mathrm{tr}\,\rho = 1`.
After a measurement, the wave-function has collapsed, so $`\rho` is *diagonal* in
the measurement basis. The defining property of a diagonal state is:

$$`E(O) = \mathrm{tr}(\rho\, O) = 0 \qquad \text{for every operator } O \text{ with null diagonal.}`

The verified statement (module `BookProof.ChapterCollapseDiagonal`):

```
#check @ChapterCollapseDiagonal.trace_diag_nullDiag_zero
#check @ChapterCollapseDiagonal.trace_diagonal_mul_diag
```

The first is exactly the property above: a diagonal $`\rho` pairs to zero with any
null-diagonal operator. The second says that, for diagonal $`\rho`, the expectation
of any operator depends only on that operator's diagonal part. *The off-diagonal
(coherence) part is invisible to a collapsed ensemble.*

# Measuring Momentum Changes the Ensemble

Now suppose we want the probability that the system lies in a region of momentum
$`p`. We cannot read this off the same ensemble $`E`; we must first apply the
physical transformation $`U` that relates the position and momentum bases, and then
collapse. The result is a *new* ensemble $`E_U`, diagonal in the momentum basis,
defined on diagonal operators $`D` by

$$`E_U(D) = \mathrm{tr}(\rho_U D) = \mathrm{tr}(\rho\, U D\, U^\dagger) = E(U D\, U^\dagger).`

For a null-diagonal operator $`O`, the collapse gives $`E_U(O) = 0`. Hence

$$`E_U(P_p) = E(U P_p U^\dagger)`

is a perfectly good probability — but it is a probability for the _new_ ensemble
$`E_U`, not for $`E`. The ensembles $`E` and $`E_U` are different; a physical
transformation relates them.

*Without* the collapse we would instead have $`E_U(O) = E(U O U^\dagger) \neq 0`
for null-diagonal $`O`, and we could speak of a single common state assigning
probabilities to a non-commutative algebra. *The collapse is what prevents this.*
It keeps quantum mechanics a Kolmogorov probability theory: every actual measurement
sees a single commutative (diagonal) algebra.

# The Collapse Is a Recursion of Two-Dimensional Maps

The collapse that makes the ensemble diagonal has a description in wave-function
coordinates that is worth making explicit, because it links the abstract argument
above to the concrete two-dimensional maps of the manuscript. In
{ref "probability-clock"}[the probability clock] the collapse of a two-state
wave-function $`\Psi(t) = (\cos t, \sin t)` is exactly the map that takes the
rank-one projector

$$`\rho(t) = \Psi(t)\Psi(t)^\top = \tfrac12\,\mathbf 1 + Z\,(\cos 2t\,\mathbf 1 + \sin 2t\, J)`

to its diagonal by setting to zero the term proportional to $`J` — the imaginary
unit of the plane, $`J^2 = -\mathbf 1`. This is "taking the real part" of the
"complex number" $`\cos(2t) + J\sin(2t)`. The verified statements (module
`BookProof.ChapterEulerDensityMatrix`):

```
#check @ChapterEulerDensityMatrix.density_euler
#check @ChapterEulerDensityMatrix.density_collapse
#check @ChapterEulerDensityMatrix.Jdens_sq
```

The manuscript lifts this from two states to $`n` and to a countable partition by
constructing the wave-function *recursively* from two-dimensional angles — *Euler
angles* $`v_k = \cos\theta_k\, l_k + \sin\theta_k\, v_{k+1}`. The recursion step
is formalized by `eulerVec`; the expanded density matrix is given by
`outer_eulerVec`. At each level the same two-dimensional identity holds, with a
generator $`J_k` in the plane spanned by $`\{l_k, v_{k+1}\}`:

$$`v_k v_k^\dagger = \tfrac12\,\mathbf 1 + \tfrac12\,\big(l_k l_k^\dagger - v_{k+1} v_{k+1}^\dagger\big)\,(\cos 2\theta_k + J_k\sin 2\theta_k).`

Collapse at level $`k` deletes the $`J_k`-proportional term, leaving the diagonal
operator whose entries are the *conditional* probabilities
$`P(k \mid k \text{ or above}) = \cos^2(\theta_k)`. Iterating over all levels gives
a probability on a single commutative algebra:

$$`P(n) = P((n \text{ or above}))\, P(n \mid n \text{ or above})
  = \Big(\prod_{k=1}^{n-1} P\big((k{+}1 \text{ or above})\mid (k \text{ or above})\big)\Big)
     P(n \mid n \text{ or above}).`

This is the manuscript's statement that *the collapse of the wave-function for a
generic phase space is a recursion of collapses of two-dimensional real
wave-functions* — the probability clock, nested. The verified statements (module
`BookProof.ChapterEulerGenericDensity`):

```
#check @ChapterEulerGenericDensity.eulerVec
#check @ChapterEulerGenericDensity.outer_eulerVec
#check @ChapterEulerGenericDensity.Jgen_sq
#check @ChapterEulerGenericDensity.density_euler_generic
#check @ChapterEulerGenericDensity.density_collapse_generic
#check @ChapterEulerGenericDensity.density_idempotent
#check @ChapterEulerGenericDensity.conditional_probability_at
#check @ChapterEulerGenericDensity.product_probability
```

Here $`J_k^2 = -\mathbf 1`, so each recursion step is again the two-dimensional
map of {ref "probability-clock"}[the probability clock]. This doubly confirms the
message of the previous sections. First, the collapse seen ensemble by ensemble
($`E_U(O) = 0` for null-diagonal $`O`) is the same operation as this level-by-level
deletion of the $`J_k`-coherence. Second, and more important, what a measurement
observes is only the sequence of *conditional* probabilities — a family of real
numbers in $`[0,1]` — that is, an ordinary commutative algebra. Every
non-commutativity lives in the invisible phases $`J_k` that the collapse discards,
exactly as in {ref "probability-clock"}[the probability clock]. The recursion
shows that no dimensional escape from this conclusion exists: quantum mechanics is
Kolmogorov at every level, and the "non-commutative" structure is the same
two-dimensional bookkeeping of the parametrization at each stage.

# Contrast with Gleason's Theorem

This result resembles Gleason's theorem but differs from it in exactly the place
that matters. Gleason's theorem says that any probability measure on *all the
non-commuting projections* of a Hilbert space of dimension $`\ge 3` is given by a
*density matrix* — which includes mixed states. Our result parametrizes
*commuting* projections by a *wave-function* — a pure state.

The difference is visible in the smallest non-trivial real example, two dimensions.
Take the two non-commuting projections

$$`P_1 = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}, \qquad Q = \frac12 \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}.`

The verified facts (module `BookProof.ChapterGleason2D`):

```
#check @ChapterGleason2D.P1_Q_noncomm
#check @ChapterGleason2D.pure_realizes_P1
#check @ChapterGleason2D.pure_realizes_Q
#check @ChapterGleason2D.no_pure_state_both
#check @ChapterGleason2D.mixed_state_both
```

Reading them: $`P_1` and $`Q` do not commute; there is a pure state realizing
$`\mathrm{tr}(\rho P_1) = \tfrac12`, and a (different) pure state realizing
$`\mathrm{tr}(\rho Q) = \tfrac12`; but there is *no* pure state realizing _both_
simultaneously. By contrast, the *mixed* state $`\rho = \tfrac12 \mathbf 1`
realizes both at once. The same contrast, stated as a single theorem (module
`BookProof.ChapterGleasonPureMixed`):

```
#check @ChapterGleasonPureMixed.pure_vs_mixed_gleason_contrast
#check @ChapterGleasonPureMixed.exists_mixed_state_both
```

The lesson: a single *wave-function* (pure state) can reproduce the probabilities
of any _one_ commuting family of events — which is all a single measurement ever
sees, because of collapse. A *density matrix* (mixed state) is needed only if one
insists on attaching probabilities to several non-commuting families at once — which
is precisely what the collapse forbids. Gleason's theorem is relevant only when the
collapse is neglected.

# Summary

 * A collapsed ensemble is diagonal: it assigns zero to every null-diagonal
   operator, so it sees only one commutative algebra of events.
 * Measuring a complementary observable applies a physical transformation *and* a
   collapse, producing a _new_ diagonal ensemble — not a single non-commutative
   state.
 * Therefore quantum mechanics is *not* a non-commutative generalization of
   probability theory; the collapse keeps it Kolmogorov.
 * In wave-function coordinates the same collapse is a *recursion of collapses of
   two-dimensional real wave-functions* — the probability clock nested — deleting
   the $`J_k`-coherence at every level.
 * The wave-function parametrizes *commuting* projections (pure states); Gleason's
   density matrix parametrizes *non-commuting* projections (mixed states). The two
   differ exactly where the collapse is or is not used.

In the manuscript's phrasing, quantum mechanics is "a generalization of classical
statistical mechanics (but not of probability theory)." The non-commutativity and the
off-diagonal coherence are artifacts of the wave-function parametrization; once the
collapse is taken seriously they dissolve, and what remains is an ordinary Kolmogorov
probability theory.
