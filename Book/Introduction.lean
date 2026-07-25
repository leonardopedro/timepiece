import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean


#doc (Manual) "Introduction" =>
%%%
tag := "introduction"
%%%

# The Central Idea

:::paragraph
A **probability distribution** on a finite set of outcomes $`\{1, \dots, n\}` is a
list of non-negative numbers that sum to one:
:::

$$`p_1, \dots, p_n \ge 0, \qquad \sum_{k=1}^{n} p_k = 1.`

:::paragraph
The set of all such lists is the **probability simplex**. It is a convex body: a
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
**wave-function**, and the rule $`p_k = \psi_k^2` (more generally
$`p_k = |\psi_k|^2` over the complex numbers) is **Born's rule**.
:::

:::paragraph
This change of variables — from a distribution $`p` on the simplex to a
wave-function $`\psi` on the sphere — is the seed from which the whole book grows.
It is a _parametrization_: it does not change the probabilities, only the
coordinates we use to describe them. And yet, as we will see, the new coordinates
make visible a structure that was invisible on the simplex.
:::

# Why Parametrize a Probability by a Wave-function?

:::paragraph
The parametrization $`p_k = \psi_k^2` is many-to-one. Both $`\psi` and
$`-\psi` give the same distribution, and over the complex numbers the whole
**phase** $`e^{i\theta}` is invisible to $`p_k = |\psi_k|^2`. The wave-function
therefore carries _more_ information than the distribution: it remembers a phase
that the probabilities have forgotten.
:::

:::paragraph
This redundancy is not a defect; it is the origin of **interference**. On the
simplex, probabilities only ever add. On the sphere, wave-functions add _first_ and
are squared _afterwards_, so two alternatives $`\psi` and $`\phi` combine as
:::

$$`|\psi + \phi|^2 = |\psi|^2 + |\phi|^2 + 2\,\mathrm{Re}(\overline{\psi}\,\phi),`

:::paragraph
and the final **cross term** is precisely the interference that has no analogue on
the simplex. The double-slit experiment, the Stern–Gerlach experiment, and the rest
of the phenomenology of quantum mechanics are, in this view, consequences of doing
linear algebra on $`\psi` before applying Born's rule.
:::

:::paragraph
The programme of this book is to make this precise and to prove it. The slogan is:
**quantum mechanics is what probability theory looks like when you parametrize the
simplex by the sphere.**
:::

:::paragraph
The unitary time-evolution of quantum mechanics becomes a rotation of the sphere;
the quantization of energy becomes a statement about periodic rotations; gauge
symmetry becomes the invisibility of the phase; and the **classical limit** becomes
the question of when the interference cross terms become negligible.
:::

# Euler's Formula as the Parametrization

:::paragraph
There is an even more explicit form of the same parametrization, and it is the one
that gives the book its name. Any probability distribution on $`n` outcomes can be
written using **Euler angles** $`\theta_1, \dots, \theta_{n-1}` as a telescoping
product of sines and cosines:
:::

$$`p_1 = \cos^2\theta_1, \quad p_2 = \sin^2\theta_1\cos^2\theta_2, \quad p_3 = \sin^2\theta_1\sin^2\theta_2\cos^2\theta_3, \quad \dots`

:::paragraph
with the last outcome carrying the remaining product of sines. Because every
number in $`[0,1]` is a $`\cos^2` of some angle, this parametrization reaches
_every_ distribution; and because the sines and cosines telescope, the
probabilities sum to one **identically**, for every choice of angles. We prove this
in {ref "born-reproduces"}[The Born rule reproduces every distribution].
:::

:::paragraph
For a single two-outcome system the parametrization is the **probability clock**
$`\Psi(t) = (\cos t, \sin t)`. As $`t` advances, the point travels around the unit
circle and the probabilities $`(\cos^2 t, \sin^2 t)` oscillate. The infinitesimal
generator of this motion is the matrix
:::

$$`J = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}, \qquad J^2 = -\mathbf{1},`

:::paragraph
which squares to minus the identity — it is a real incarnation of the imaginary
unit, and **Euler's formula** $`e^{tJ} = \cos t\,\mathbf{1} + \sin t\, J` is the
statement that the rotation of the probability clock is the exponential of this
generator. This is the bridge from probability to the complex numbers, and we make
it explicit in {ref "probability-clock"}[The probability clock and Euler's formula].
:::

# What Is Verified, and How

:::paragraph
The formal counterpart of this book is the Lean 4 library `BookProof`. It currently
contains well over one hundred modules, each formalizing one self-contained
mathematical claim from the source manuscript. The whole library is
**`sorry`-free** (no proof is omitted) and **`axiom`-free** (it adds no axioms
beyond Lean's standard logical foundations). The statements quoted in this book are
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
The book is organized into five parts.
:::

: Part I — Probability as Coherent Belief

  The probabilistic foundations: the Dutch-book derivation of the probability
  axioms, the associativity of Bayesian updating, the maximum-entropy origin of the
  uniform prior, and the law of total variance.

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
  Koopman–von Neumann theory, Weyl quantization, and Nelson's essential
  self-adjointness theorem.

: Part V — Completeness without Peano Arithmetic

  A metamathematical chapter: the completed Hilbert space is a complete, decidable,
  conservative extension that does not leak undecidable arithmetic, because its
  infinite elements are kept internally unselectable.
