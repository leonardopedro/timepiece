import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Stern-Gerlach Experiment" =>
%%%
tag := "stern-gerlach"
%%%

# A Stronger Case for Non-Deterministic Symmetry

In {ref "probability-clock"}[the probability clock] the symmetry transformations
used so far are *deterministic*: they send a point of the phase space to a point
of the phase space. The manuscript argues that the Stern-Gerlach experiment makes
a strong case for *generalizing* the symmetry transformations to be
*non-deterministic*, and that its theoretical predictions only require a phase
space with two states like the one already discussed in the previous chapter. It
is a concrete setting in which the wave-function parametrization — and the fact
that a symmetry of the wave-function can be non-deterministic on the
probabilities — is put to work.

# The Experiment

A beam of silver atoms is sent through a magnetic field with a gradient along
the $`z`-axis or the $`x`-axis and the deflection is observed. The result is
that the silver atoms possess an *intrinsic angular momentum* (spin) that takes
only one of two possible values, represented by the symbols $`+` and $`-`.
Moreover, in *sequential* Stern-Gerlach experiments, the measurement of the spin
along the $`z`-axis destroys the information about the spin of an atom along the
$`x`-axis, and vice versa.

# A Two-State Phase Space

We take as the phase space not only the spin of an atom of the beam but also the
*angle of orientation of a macroscopic reference object*, for pedagogical
purposes. A rotation of the phase space is then a *non-deterministic* transformation
of the spin of the atom and a *deterministic* transformation of the macroscopic
object. To keep track of the part of the wave-function corresponding to the
orientation angle we only need its *central value*, which we call simply "the
angle," and we then consider only the part of the wave-function corresponding to
the spin.

With $`\cos^2(t)` the probability that the spin is in the state $`+`, and
$`\sin^2(t)` the probability that it is in the state $`-`, the
non-deterministic symmetry transformation given by a rotation of the spin in the
$`x-z` plane is parametrized by the parameter $`t`, and its linear representation
on the wave-function is exactly the probability clock of
{ref "probability-clock"}[that chapter]. The Euler identity for the 2-state
density matrix (module `BookProof.ChapterEulerDensityMatrix`):

```
#check @ChapterEulerDensityMatrix.density_euler
#check @ChapterEulerDensityMatrix.density_collapse
```

We only make measurements along the
$`z` and $`x`-axis; if we also measured along the $`y`-axis, the phase space would
require *four* states, or equivalently, a parametrization with a complex
wave-function.

# Sequential Measurements Give 50/50

In the first measurement the reference angle is $`0` with respect to the
$`z`-axis, and we know for sure that the spin is in the state $`+` because we
measure the spin along the $`z`-axis of atoms previously filtered to be in the
state $`+`.

A second, sequential measurement along the $`x`-axis means that we rotate the
reference object by $`90` degrees, so the new angle is $`90` degrees; and we
rotate the spin of the atom by $`45` degrees in the $`x-z` plane, that is
$`t = \pi/4`, because the spin group is a double cover of the orthogonal group,
for which the angle would be $`90` degrees. We then determine whether the spin is
in the $`+` or $`-` state — the wave-function collapses. The probability of each
outcome is now $`50\%/50\%`:

```
#check @ChapterSternGerlach.sg_cos_sq_quarter
#check @ChapterSternGerlach.sg_sin_sq_quarter
```

since $`\cos^2(\pi/4) = \sin^2(\pi/4) = 1/2`.

A third, sequential measurement along the $`z`-axis means that we rotate the
reference object by $`-90` degrees (so the new angle is again $`0`) and apply a
$`-\pi/4` rotation to the atoms with spin $`+`; we then determine the spin one
more time, and the wave-function collapses again. Although in the first measurement
the spin was in the state $`+`, the probability is still $`50\%/50\%` — because the
same non-deterministic rotation was applied in the second and third steps to switch
from the $`z` to the $`x`-axis and back.

Generalizing the symmetry transformations to be non-deterministic therefore
suffices to account for all the experimental results described by quantum
mechanics, with the Stern-Gerlach experiment being one example. The question
remaining is whether the Euler's formula applies for phase-spaces with more than
two states — which would imply that the collapse of the wave-function is merely a
mathematical artifact of the wave-function parametrization. That is the subject of
{ref "euler-generic"}[the Euler chapters].

# Information Erasure by a Unitary

The manuscript draws a second, sharper conclusion from this experiment, now about
the *reversibility* of the erasure. Consider a quantum theory whose phase space is
an orthogonal basis of a Hilbert space of finite dimension $`n`. There is *always a
unitary transformation* $`U` such that the corresponding probability distribution
is necessarily the *constant* distribution, for all initial states in the same
orthogonal basis. Under Born's rule, feeding any basis state $`e_j` into such a
unitary and measuring in the same basis gives the uniform output
$`i \mapsto |U_{ij}|^2 = 1/n`. A unitary time evolution can therefore turn any
incoming basis state into a maximally mixed, *information-erased* distribution
while remaining perfectly reversible — erasure is not in tension with unitary.

One such unitary for every $`n` is the *normalized discrete Fourier transform* (a
complex Hadamard matrix):

$$`U_{ij} = \frac{1}{\sqrt n}\, e^{2\pi i\, i j / n}.`

Every entry has the same squared modulus $`|U_{ij}|^2 = 1/n`, and the matrix is
unitary because the columns are orthonormal, which follows from the vanishing of
the geometric sum over one full period. For $`n = 2` this is the Hadamard gate,
the case of the two-state Stern-Gerlach model. The construction and its properties
are in `BookProof.ChapterSternGerlach`:

```
#check @ChapterSternGerlach.dft_normSq
#check @ChapterSternGerlach.dft_unitary
#check @ChapterSternGerlach.exists_uniform_unitary
```

The headline `exists_uniform_unitary` is exactly the manuscript's assertion: for
every $`n \ge 1` there is a unitary sending every basis state to the constant law
$`i \mapsto 1/n`. The subtlety — and the resolution of the apparent paradox with
{ref "probability-clock"}[the singular collapse matrix] — is that this erasure is
*unitary*, hence reversible at the level of the wave-function: the information is
not destroyed but delocalized into the relative phases between the
$`1/\sqrt n` amplitudes. What is irreversible is only the subsequent restriction
to the probabilities $`|U_{ij}|^2 = 1/n`$, which discards those phases. The unitary
mixes the state perfectly; Born's rule then forgets how. This is the cleanest
finite illustration of the manuscript's distinction between reversible wave-function
dynamics and the irreversible appearance of measurement statistics.

# Summary

 * The Stern-Gerlach experiment requires as a phase space only two states, and
   motivates generalizing the symmetry transformations to be *non-deterministic*.
 * Sequential measurements along the $`z` and $`x`-axis then give only $`50/50`
   outcomes, the spin being rotated by $`\pi/4` on a double-cover of the
   orthogonal group; each measurement collapses the wave-function and destroys the
   orthogonal information. Yet the same non-deterministic rotation is why the
   third measurement still yields $`50/50`.
 * A unitary transformation always exists sending every basis state of any finite
   dimension to the uniform distribution, so this erasure is reversible at the
   level of the wave-function.