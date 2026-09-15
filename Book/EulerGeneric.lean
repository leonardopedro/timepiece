import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Euler's Formula in Arbitrary, Countable, Complex, and Quaternionic Dimension" =>
%%%
tag := "euler-generic"
%%%

# From the Clock to the Hypersphere

The probability clock parametrizes a two-outcome distribution by a point on the
circle. This chapter lifts the construction to an arbitrary number of outcomes, to
countably infinite outcome spaces, and finally to complex and quaternionic
wave-functions. The mechanism is the same throughout: a recursive sequence of
two-dimensional rotations — *Euler angles* — whose telescoping guarantees that the
probabilities sum to one.

# Euler Angles for Finitely Many States

Let $`l_1, \dots, l_n` be an orthonormal basis. A normalized vector is built
recursively from angles $`\theta_1, \dots, \theta_{n-1}` by

$$`v_k = \cos\theta_k\, l_k + \sin\theta_k\, v_{k+1}, \qquad v_n = l_n.`

Unwinding the recursion gives the Born probabilities as a telescoping product:

$$`P(1) = c_1^2, \quad P(2) = s_1^2 c_2^2, \quad P(3) = s_1^2 s_2^2 c_3^2, \quad \dots, \quad P(n) = s_1^2 \cdots s_{n-1}^2,`

where $`c_k = \cos\theta_k` and $`s_k = \sin\theta_k`. The verified statements
(module `BookProof.ChapterEulerNState`):

```
#check @ChapterEulerNState.euler_sum_one
#check @ChapterEulerNState.euler_wave_unit
#check @ChapterEulerNState.euler_reproduces
```

The first two say that for any angles the Born probabilities sum to $`1` and the
wave-function has unit norm — the telescoping identity, made formal. The third is
the *surjectivity*: every probability distribution $`p` with $`p_k \ge 0` arises
from some choice of angles. The ingredient that makes surjectivity work is that
every number in $`[0,1]` is a $`\cos^2`:

```
#check @ChapterEulerNState.exists_cos_sq
```

# The Density Matrix and Collapse, Generically

At each step the rank-one projector $`v_k v_k^\dagger` has an Euler form. Writing
$`J_k = l_k v_{k+1}^\dagger - v_{k+1} l_k^\dagger` for the generator in the plane
spanned by $`\{l_k, v_{k+1}\}`, one has $`J_k^2 = -\mathbf 1` on that plane, and

$$`v_k v_k^\dagger = \tfrac12(\cdots) + \tfrac12(l_k l_k^\dagger - v_{k+1}v_{k+1}^\dagger)\,(\cos 2\theta_k + J_k \sin 2\theta_k).`

The term proportional to $`J_k` is the off-diagonal coherence — a feature of the
wave-function parametrization, not a physical quantity (as in
{ref "probability-clock"}[the probability clock]). *Collapse* is, once again,
taking the "real part" — deleting the $`J_k` term — leaving a diagonal
operator whose entries are the conditional probabilities
$`P(k \mid k \text{ or above}) = c_k^2`. The verified statements (module
`BookProof.ChapterEulerGenericDensity`):

```
#check @ChapterEulerGenericDensity.Jgen_sq
#check @ChapterEulerGenericDensity.density_euler_generic
#check @ChapterEulerGenericDensity.density_collapse_generic
#check @ChapterEulerGenericDensity.density_idempotent
```

Thus the collapse for a generic phase space is just a *recursion of collapses of
two-dimensional real wave-functions* — the probability clock, nested.

# Countably Infinite Outcome Spaces

The recursion does not need to stop. For a countable (possibly infinite) partition
of the phase space, the same construction gives a *stick-breaking* process: at
step $`n` one breaks off a fraction $`c_n` of the remaining stick. The verified
statements (module `BookProof.ChapterEulerCountableChain`):

```
#check @ChapterEulerCountableChain.stick_tsum_one
#check @ChapterEulerCountableChain.stickProb_euler
#check @ChapterEulerCountableChain.euler_tsum_one
```

The first says the stick-breaking probabilities sum (as an infinite series) to
$`1`; the second identifies each stick-breaking probability with a $`\cos^2` of an
angle; the third is the resulting statement that the Euler-angle parametrization of
a countable distribution sums to $`1`. The parametrization that reached every
finite distribution now reaches every countable one.

# Complex and Quaternionic Wave-functions

The real parametrization is always possible, but it need not be the most natural
one. The manuscript's argument for the complex and quaternionic cases runs through
the *real Schur's lemma*: if a set of normal operators (the projections together
with a unitary representation of a symmetry group) leaves no non-trivial closed
subspace invariant, then the algebra of operators commuting with all of them is a
*real associative division algebra* — and such an algebra is isomorphic to exactly
one of the real numbers, the complex numbers, or the quaternions.

When the commuting algebra is the complex (respectively quaternionic) numbers, one
may equivalently use complex (respectively quaternionic) wave-functions. The Born
rule then uses the squared norm. The verified statements (module
`BookProof.ChapterEulerComplexQuat`):

```
#check @ChapterEulerComplexQuat.cbornProb_nonneg
#check @ChapterEulerComplexQuat.complex_realification_norm
#check @ChapterEulerComplexQuat.complex_reproduces
#check @ChapterEulerComplexQuat.quat_reproduces
```

Reading them: the complex Born probability $`|v_k|^2` is non-negative; the norm of
a complex wave-function equals the norm of its *realification* (a complex
Hilbert space is a real one of twice the dimension, with the same norm); and the
Born rule reproduces every distribution in the complex case and in the quaternionic
case, exactly as in the real case.

The upshot: the field over which the wave-function lives — real, complex, or
quaternionic — is *not* an extra physical postulate. It is read off from the
commuting algebra of the symmetry representation, and the parametrization of
probability by a wave-function works uniformly over all three.

# Summary

 * For $`n` outcomes, Euler angles parametrize every distribution by a telescoping
   product of sines and cosines; the probabilities sum to one identically.
 * The generic density matrix is a recursion of probability-clock Euler forms;
   collapse deletes the $`J_k`-coherence at every level.
 * The construction extends to countably infinite outcome spaces via stick-breaking,
   with the infinite sum still equal to one.
 * Complex and quaternionic wave-functions arise from the real Schur's lemma; the
   Born rule (squared norm) reproduces every distribution over all three fields.
