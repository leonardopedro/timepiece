import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Probability Clock and Euler's Formula" =>
%%%
tag := "probability-clock"
%%%

# A Two-State System

The smallest non-trivial probability space has two outcomes. A distribution on it is
a pair $`(p, 1-p)`, a single number $`p \in [0,1]`. The source manuscript calls the
wave-function parametrization of this space the **probability clock**:

$$`\Psi(t) = (\cos t,\; \sin t), \qquad p = \cos^2 t, \quad 1-p = \sin^2 t.`

As the parameter $`t` advances, the point $`\Psi(t)` travels around the unit circle
and the probabilities oscillate between the two outcomes. This is the real,
two-dimensional incarnation of a quantum two-level system (a _qubit_).

# The Generator Squares to Minus One

What moves the clock? The infinitesimal generator of the rotation
$`\Psi(t) \mapsto \Psi(t+a)` is the matrix

$$`J = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}.`

A direct multiplication shows the single most important fact about this matrix:

$$`J^2 = \begin{pmatrix} -1 & 0 \\ 0 & -1 \end{pmatrix} = -\mathbf{1}.`

The generator squares to **minus the identity**. This is exactly the defining
property of the imaginary unit $`i`, and it is the reason the complex numbers
appear in quantum mechanics: the real rotation generator behaves algebraically like
$`i`.

# Euler's Formula, as a Matrix Identity

Because $`J^2 = -\mathbf{1}`, the exponential of $`a J` collapses, by the power
series of the exponential, into sines and cosines:

$$`e^{aJ} = \cos a \,\mathbf{1} + \sin a \, J = \begin{pmatrix} \cos a & -\sin a \\ \sin a & \cos a \end{pmatrix} =: R(a).`

This is **Euler's formula**, lifted from complex numbers to the rotation matrix.
The matrix $`R(a)` is a genuine rotation: its determinant is $`1`, so it is
invertible, and it acts on the clock by advancing the parameter:

$$`\Psi(t+a) = R(a)\,\Psi(t).`

The verified statements (module `BookProof.ChapterProbabilityClockStochastic`):

```
#check @ChapterProbabilityClockStochastic.Jgen_sq
#check @ChapterProbabilityClockStochastic.rotMat_eq_exp
#check @ChapterProbabilityClockStochastic.rotMat_det
#check @ChapterProbabilityClockStochastic.rotMat_mulVec_clockPsi
#check @ChapterProbabilityClockStochastic.clockPsi_eq_exp
```

# Why Act on the Wave-function and Not on the Probability?

Here is the crux of the whole book, in the smallest possible setting. We could try
to act **directly** on the probability vector $`(p, 1-p)` instead of on the
wave-function. Which linear maps preserve the space of probability vectors?

A linear map preserves probability vectors **exactly when it is column-stochastic**:
each column is itself a probability vector. The most general such $`2\times 2` map
is parametrized by two angles:

$$`M(a,b) = \begin{pmatrix} \cos^2 a & \cos^2 b \\ \sin^2 a & \sin^2 b \end{pmatrix}.`

The verified classification (module `BookProof.ChapterEulerStochastic`):

```
#check @ChapterEulerStochastic.preservesProb_iff_exists_angles
#check @ChapterProbabilityClockStochastic.isColumnStochastic_eq_Mab
```

Now ask: is there such a map that sends the **uniform** distribution
$`\tfrac12(1,1)` to a **vertex** $`(1,0)` (a deterministic outcome)? There is — but
any such map has determinant **zero**:

```
#check @ChapterEulerStochastic.uniform_to_vertex_singular
#check @ChapterProbabilityClockStochastic.stochastic_uniform_to_deterministic_singular
```

A singular matrix is **not invertible**, so it cannot represent a symmetry (a
symmetry must be reversible). This is the precise obstruction the manuscript
identifies: on the probability simplex, the only linear "symmetries" are stochastic
matrices, and the operation that turns a superposition into a definite outcome —
**collapse** — is necessarily irreversible.

By contrast, the rotation $`R(a)` acting on the wave-function has determinant
$`1`: it is invertible, hence a genuine symmetry. **Reversible dynamics lives on the
wave-function; irreversible collapse lives on the probabilities.** This is the
mathematical origin of the contrast between unitary evolution and measurement.

# The Density Matrix and Collapse

It is illuminating to write the **density matrix** of the clock, the rank-one
projector $`\rho(t) = \Psi(t)\,\Psi(t)^\top`:

$$`\rho(t) = \begin{pmatrix} \cos^2 t & \cos t \sin t \\ \cos t \sin t & \sin^2 t \end{pmatrix}.`

Using $`J` and the diagonal generator $`Z = \tfrac12\operatorname{diag}(1,-1)`, this
projector can be rewritten in Euler form:

$$`\rho(t) = \tfrac12\,\mathbf{1} + Z\,(\cos 2t \,\mathbf{1} + \sin 2t \, J).`

The term proportional to $`J` is the **off-diagonal** (coherence) part. The
manuscript's model of **wave-function collapse** is simply: set the
$`J`-proportional part to zero. What remains is the diagonal, classical
distribution:

$$`\rho(t) \;\longrightarrow\; \begin{pmatrix} \cos^2 t & 0 \\ 0 & \sin^2 t \end{pmatrix}.`

The verified statements (module `BookProof.ChapterEulerDensityMatrix`):

```
#check @ChapterEulerDensityMatrix.density_euler
#check @ChapterEulerDensityMatrix.density_collapse
#check @ChapterEulerDensityMatrix.Jdens_sq
#check @ChapterEulerDensityMatrix.densityMatrix_trace
#check @ChapterEulerDensityMatrix.densityMatrix_idempotent
```

The last of these, $`\rho^2 = \rho`, says the clock is in a **pure** state; the
trace $`\operatorname{tr}\rho = 1` says it is normalized. Collapse destroys the
idempotent purity by deleting the coherence term, leaving a genuine classical
probability on the diagonal.

# Summary

In two dimensions we have already seen the entire mechanism of the book:

 * parametrizing the probability by a wave-function $`\Psi = (\cos t, \sin t)`;
 * a rotation generator $`J` with $`J^2 = -1`, i.e. an emergent imaginary unit;
 * Euler's formula $`e^{aJ} = R(a)` giving reversible, unitary dynamics;
 * the obstruction that direct linear action on probabilities is stochastic and
   singular at collapse, hence irreversible;
 * collapse as deletion of the $`J`-proportional coherence in the density matrix.

The rest of Part II lifts each of these facts from two dimensions to arbitrary
finite dimension, and then to the countable and continuous settings.
