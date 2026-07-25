import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Information Erasure: the Stern–Gerlach Experiment" =>
%%%
tag := "stern-gerlach"
%%%

# A Unitary That Forgets Everything

In {ref "probability-clock"}[the probability clock] we saw that collapse — sending a
superposition to a definite outcome — is **irreversible** on the simplex: the
required stochastic matrix is singular. There is, however, a perfectly reversible
operation on the wave-function that has the _statistical_ effect of erasing
information: a **unitary** that sends _every_ basis state to the **uniform**
distribution.

The manuscript asserts that "there is always a unitary transformation such that the
corresponding probability distribution is necessarily the constant distribution, for
all initial states in the same orthogonal basis." Under Born's rule this means: for
any finite dimension $`n`, there is a unitary matrix whose every entry has squared
modulus $`1/n`. Feeding any basis state into such a matrix produces the uniform
(maximally mixed, information-erased) output $`i \mapsto 1/n`.

# The Construction: the Fourier Matrix

The required unitary is the **normalized discrete Fourier transform** (a complex
Hadamard matrix):

$$`U_{ij} = \frac{1}{\sqrt n}\, e^{2\pi i \, i j / n}, \qquad i,j \in \{0,\dots,n-1\}.`

Every entry has the same squared modulus:

$$`|U_{ij}|^2 = \frac{1}{n}.`

So each column — the image of a basis state under $`U` — is the constant
distribution $`i \mapsto 1/n`. The matrix is unitary because the columns are
orthonormal, which follows from the vanishing of the geometric sum over a full
period:

$$`\sum_{j=0}^{n-1} e^{2\pi i\, j\, m/n} = 0 \qquad (m \not\equiv 0 \pmod n).`

# The Verified Statement

The construction and its properties are in `BookProof.ChapterSternGerlach`:

```
#check @ChapterSternGerlach.dft_normSq
#check @ChapterSternGerlach.dft_unitary
#check @ChapterSternGerlach.exists_uniform_unitary
```

The headline `exists_uniform_unitary` is exactly the manuscript's assertion: for
every $`n \ge 1` there exists a unitary sending every basis state to the constant
law $`i \mapsto 1/n`.

# The Two-State Case: Stern–Gerlach

For $`n = 2` the Fourier matrix is the **Hadamard gate**
$`\frac{1}{\sqrt 2}\begin{pmatrix}1 & 1 \\ 1 & -1\end{pmatrix}` of the two-state
Stern–Gerlach model. A spin prepared in any basis state and passed through a
$`\pi/4` rotation gives outcomes with probability $`1/2` each:

```
#check @ChapterSternGerlach.sg_cos_sq_quarter
#check @ChapterSternGerlach.sg_sin_sq_quarter
```

since $`\cos^2(\pi/4) = \sin^2(\pi/4) = 1/2`. This is the iconic "50/50" split of a
Stern–Gerlach apparatus oriented perpendicular to the prepared spin: the device
**erases** the information about which basis state went in, replacing it with the
uniform distribution.

# Reversible Dynamics, Irreversible-Looking Statistics

The subtle point — and the resolution of the apparent paradox with
{ref "probability-clock"}[the singular collapse matrix] — is that this erasure is
**unitary**, hence reversible at the level of the wave-function. The information is
not destroyed; it is delocalized into the relative phases between the
$`1/\sqrt n` amplitudes. What is irreversible is the subsequent restriction to the
probabilities $`|U_{ij}|^2 = 1/n`, which discards those phases. The unitary mixes
the state perfectly; Born's rule then forgets how. This is the cleanest finite
illustration of the book's distinction between reversible wave-function dynamics and
the irreversible appearance of measurement statistics.
