import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Starobinsky Scalaron: from Potential to Fock Space" =>
%%%
tag := "starobinsky-scalaron"
%%%

# Why R + αR²

:::paragraph
The simplest modification of Einstein–Hilbert gravity that is both ghost-free and
capable of inflation is the Starobinsky action
$`f(R) = \tfrac{M^2}{2} R + \alpha R^2` with $`\alpha > 0`. The point of the
quadratic term is *regularization of the conformal mode*: pure general relativity,
whose conformal-mode gradient energy carries a negative sign, is unbounded below,
and the positive $`\alpha R^2` turns that unstable direction into a parabola
bounded below by $`-M^4/(16\alpha)`. This is the same conformal-mode stabilization
that the $`3+1` split of the diffeomorphism chapter (`Book/DiffeomorphismsGravity.lean`)
meets at the level of the spatial metric.
:::

:::paragraph
The verified content here is the full chain: the classical scalar–tensor
equivalence, the Einstein-frame scalaron potential and its shape, the
regularization of the conformal mode, essential self-adjointness of the
gauge-fixed Hamiltonian on a continuum core (exponential wall included), and the
quantization to the nested Fock space. The modules are `BookProof/ChapterStarobinskyPotential.lean`,
`BookProof/ChapterScalaronCoreEsa.lean` and `BookProof/ChapterScalaronFockEsa.lean`
(plan item A5 of `CONSOLIDATED_PLAN.md`), all registered in `BookProof.lean`
and certified axiom-free in `BookProof/ChapterRoadmapAudit.lean`.
:::

# The Ghost-Free Scalar–Tensor Form

:::paragraph
With the auxiliary field $`\psi = 1 + 4\alpha R/M^2` and the potential
$`U(\psi) = \frac{M^4}{16\alpha}(\psi - 1)^2`, the identity
$`f(R) = \frac{M^2}{2}\psi R - U(\psi)` recasts $`R + \alpha R^2` gravity as a
*second-order* scalar–tensor theory: the would-be fourth-order mode is traded for
a genuine scalar, the scalaron, with a standard quadratic potential. There is no
Ostrogradsky ghost — the theory has exactly two propagating degrees of freedom
plus the scalar.
:::

```
#check @BookProof.Starobinsky.fR_eq_scalarTensor
```

# The Einstein-Frame Potential: a Square

:::paragraph
In the Einstein frame the scalaron moves in the potential
$`V(\varphi) = \frac{M^4}{16\alpha}\bigl(1 - e^{-\sqrt{2/3}\,\varphi/M}\bigr)^2`.
Because it is *manifestly a square*, it is non-negative — the strongest form of the
correct (elliptic) sign — vanishes at $`\varphi = 0` (the flat Minkowski vacuum),
tends to the plateau $`M^4/(16\alpha)` at large field (the inflationary slow-roll
regime), and rises exponentially as $`\varphi \to -\infty` (the wall that keeps the
field on the plateau side).
:::

```
#check @BookProof.Starobinsky.starobinskyV_nonneg
#check @BookProof.Starobinsky.starobinskyV_zero
#check @BookProof.Starobinsky.starobinskyV_tendsto_plateau
#check @BookProof.Starobinsky.starobinskyV_tendsto_atBot_atTop
```

# The Conformal Mode and What α Buys

:::paragraph
In the densitized variables the spatial potential is the parabola
$`V_3(R_c) = \alpha\bigl(R_c - \frac{M^2}{4\alpha}\bigr)^2 - \frac{M^4}{16\alpha}`,
bounded below by $`-M^4/(16\alpha)` for $`\alpha > 0`. The contrast with
$`\alpha = 0` is the whole story: the linear theory is *not* bounded below, which is
exactly the conformal-mode instability. The completed-square identity exhibits the
regularization, and the mode-level operator inherits it uniformly: the gravity
fibre symbol $`(1/16)a_k^2 - (1/24)b_k^2 + V_k` with the Starobinsky potential
$`V_k = V_3(R_c k)` is essentially self-adjoint on its maximal domain.
:::

```
#check @BookProof.Starobinsky.confV_completed_square
#check @BookProof.Starobinsky.confV_ge
#check @BookProof.Starobinsky.confV_bddBelow
#check @BookProof.Starobinsky.confV_zero_alpha_tendsto_atBot
#check @BookProof.Starobinsky.qgR2Mode_potential_ge
#check @BookProof.Starobinsky.qgR2Mode_esa
```

# Essential Self-Adjointness on the Continuum

:::paragraph
The scalaron potential is *not* of temperate growth: it grows exponentially as
$`\varphi \to -\infty`, so the standard multiplication-operator theorem for
potentials of temperate growth on the Schwartz core does not apply. The resolution
is to move to the smaller — still dense — core of smooth compactly supported
functions, where no growth hypothesis is needed at all: multiplication by any
smooth real function preserves the core, and the deficiency argument (divide a test
bump by the nowhere-vanishing smooth function $`W - \bar z` at a non-real $`z`) stays
inside it. What survives is only the analytic content the physics needs: a dense
core, and — for the combination with the kinetic term — the potential bounded
below, which the Starobinsky potential is in the strongest way (it is a square).
:::

```
#check @BookProof.ScalaronEsa.ccDomain_dense
#check @BookProof.ScalaronEsa.smoothPotential_symmetric
#check @BookProof.ScalaronEsa.smoothPotential_deficiencyTrivial
#check @BookProof.ScalaronEsa.smoothPotential_essentiallySelfAdjoint
#check @BookProof.ScalaronEsa.contDiff_starobinskyV
#check @BookProof.ScalaronEsa.starobinskyV_not_hasTemperateGrowth
```

# The Fock-Space Statement

:::paragraph
Quantization of a continuum field theory lives on the *nested Fock space*
$`\bigoplus_n L^2(E_n)`: the $`n`-particle sector carries the $`n`-fold
configuration space, and the Hamiltonian acts sector by sector with the many-body
potential the sum of the one-particle potentials of the individual quanta. Essential
self-adjointness is *fibrewise* — a deficiency vector of an orthogonal direct sum,
tested against single-fibre states, has vanishing coordinates — so the one-particle
theorems glue to the whole Fock space. Applied to the gauge-fixed $`R + \alpha R^2`
potential $`\sum_j \bigl(V_3(R_c{}_j) + V(\varphi_j)\bigr)` — smooth, bounded below
by $`-n M^4/(16\alpha)`, and at $`n = 1` exactly the one-particle potential — this
yields essential self-adjointness and the complete unitary group $`e^{-itH}` of the
scalaron Hamiltonian, in both the continuum and the mode realisation.
:::

```
#check @BookProof.ScalaronFock.nestedCore_dense
#check @BookProof.ScalaronFock.fockSmoothPotential_esa
#check @BookProof.ScalaronFock.fockSmoothPotential_stone_flow
#check @BookProof.ScalaronFock.contDiff_qgManyPotential
#check @BookProof.ScalaronFock.qgManyPotential_ge
#check @BookProof.ScalaronFock.qgManyPotential_esa
#check @BookProof.ScalaronFock.qgManyPotential_one
#check @BookProof.ScalaronFock.qgScalaronFock_esa
#check @BookProof.ScalaronFock.qgScalaronFock_stone_flow
```

:::paragraph
This closes plan item A5: the Starobinsky sector of the gauge-fixed
Hamiltonian is a well-defined self-adjoint operator whose unitary flow is the
quantized dynamics — the formal counterpart of the Fock realization
$`\sum_i m \, N_i` with $`m^2 = M^2/(12\alpha)` used in the numerical
validation of the model.
:::
