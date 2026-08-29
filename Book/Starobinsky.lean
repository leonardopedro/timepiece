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
The 3D gauge fixing of the Cadabra2 derivation is done entirely in metric
variables — no vielbein is needed here. The steps are the synchronous gauge
$`N = 1, N^i = 0`; the $`3+1` split $`R = R_3 + (K^2 - K_{ij}K^{ij})`; the
conformal decomposition of the spatial metric
$`R_c = \Omega^{-4}\bar R_c - 8\Omega^{-5}\bar\nabla^2\Omega`; the
Navier–Stokes-style fixing of the spatial derivative variables
($`(\partial_i\varphi)(\partial^i\varphi) \to \text{grad}^2`); and the
Hamiltonian constraint solved for the conformal-mode curvature $`R_c`. The
vielbein is only *required* for the teleparallel (torsion) formulation — the
torsion scalar $`T` and the Weitzenböck connection are built from the vielbein
and its local Lorentz freedom must be gauge-fixed, which is the TEGR module's
job. Starobinsky is $`f(R)`, a function of the *Ricci scalar* — a metric
object — so the ADM split and the conformal-mode stabilization are
self-contained in the metric.
:::

:::paragraph
Since the base theory is teleparallel-equivalent to GR
($`eR = e\cdot T + \text{divergence}`, the TEGR identity verified in
`Book/BaryonAsymmetry.lean`), this construction *could* equally be carried out
in the vielbein variables of the TEGR module, with the *same* teleparallel
restrictions on the frame (Weitzenböck connection: metric-compatible,
curvature-free, torsion-carrying). Writing $`R = T + B` with the boundary term
$`B = 2\nabla_\mu T^\mu`, the $`R^2` action would read $`\int e\, f(T+B)` — a
functional of the torsion scalar *and* its boundary term. It is therefore
not a pure $`f(T)` (teleparallel) action: $`f(T+B) \neq f(T)` generically,
and pure $`f(T)` gravity is a different theory. Everything below depends only
on $`R = T + B`, so the scalar–tensor reduction, the conformal-mode parabola,
and $`H_{\rm final}` are unchanged by the choice of variables.
:::

:::paragraph
The verified content here is the full chain: the classical scalar–tensor
equivalence, the Einstein-frame scalaron potential and its shape, the
regularization of the conformal mode, essential self-adjointness of the
gauge-fixed Hamiltonian on a continuum core (exponential wall included), and the
quantization to the nested Fock space. The modules are `BookProof/ChapterStarobinskyPotential.lean`,
`BookProof/ChapterScalaronCoreEsa.lean`, `BookProof/ChapterScalaronFockEsa.lean` and —
for the exponential wall of the *sum* $`-d^2/d\varphi^2 + V` —
`BookProof/ChapterWeakSecondDerivative.lean` with `BookProof/ChapterScalaronWallEsa.lean`
(plan item *A5* of `CONSOLIDATED_PLAN.md`), all registered in `BookProof.lean`
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
functions, where *no growth hypothesis is needed at all*: multiplication by any
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
This closes plan item *A5*: the Starobinsky sector of the gauge-fixed
Hamiltonian is a well-defined self-adjoint operator whose unitary flow is the
quantized dynamics — the formal counterpart of the Fock realization
$`\sum_i m \, N_i` with $`m^2 = M^2/(12\alpha)` used in the numerical
validation of the model.
:::

:::paragraph
The final Hamiltonian is the one-particle Hamiltonian enclosed in creation
(on the left) and annihilation (on the right) operators on the nested Fock
space — the same doctrine as QYM, QED, and NS: $`H = \sum_{ij} h_{ij}
C^\dagger(e_i) A(e_j)` with $`h = h_{\rm TEGR} \oplus (m)` for the vielbein
(teleparallel) form, i.e. $`H = \sum_i :(1/16)\mathcal S_i^2: + m\,N_\psi`.
The nested Fock space has two levels: the outer Fock space (whose ladders are
the $`C^\dagger/A` of the enclosure) and the inner one-particle Hilbert space
on which $`h` acts. The outer Hamiltonian is a *quadratic (free-particle-like)
form in the outer ladders for any* $`h` — so the FULL Einstein-frame scalaron
potential $`V(\varphi) = \frac{M^4}{16\alpha}(1-e^{-\sqrt{2/3}\,\varphi/M})^2`,
*exponential included*, may live inside $`h` (in the one-particle matrix
elements $`\langle e_i, h\, e_j\rangle`), with no 3-/4-particle vertices at
the outer level. That is the realization `qg_starobinsky_vielbein_
hamiltonian_full` in `../unfer` (the truncated-Hermite enclosure of
$`h = \tfrac12\pi^2 + V(\hat\varphi)`, whose one-particle spectrum is exactly
the Schrödinger spectrum proved essentially self-adjoint above,
`starobinskyWall_esa`); the quadratic $`m\,N_\psi` realization is its
small-field limit. Either way $`\langle 0|H|0\rangle = 0` and the outer vacuum
is the exact ground — the R² content never creates higher vertices at the outer
level.
:::

:::paragraph
The scalaron sector's outer-Fock gap is now a theorem, not a hypothesis.
`BookProof/ChapterScalaronFockGapChain.lean` runs the abstract gap chain (the
one instantiated conditionally for gauge-fixed QYM in
`ChapterYangMillsFockGapChain`) for the sector whose one-particle operator is
the *positive constant* $`m = 1/\sqrt{12\alpha}` — precisely the
$`m\,N_\psi` realization above. For the constant operator the one-particle
form gap that the Yang–Mills chain must assume is an identity
(`constOnePart_quadForm`: the form is exactly $`m\|x\|^2`), so every
conclusion follows unconditionally: `const_fock_gap` proves
$`d\Gamma(m \cdot 1)\Omega = 0` and the bound $`\mathrm{Re}\langle u, d\Gamma(m \cdot 1) u\rangle \ge m\|u\|^2`
on vacuum-orthogonal finite states, `const_fock_mass_gap` adds the positive
self-adjoint (Friedrichs) extension with strictly positive non-vacuum energy,
`const_fock_gap_of_field_perturbation` keeps the surviving gap
$`(m - 2\|f\|)\|u\|^2` under the unbounded, number-changing coupling
$`\Phi(f)` whenever $`2\|f\| < m`, and — via the companion module
`ChapterFockCubicQuarticStability`, which stabilizes the bare cubic term of
`ChapterFockCubicUnbounded` by its normal-ordered quartic partner on all
finite states (not just the trial family) —
`const_fock_cubic_quartic_bounded_below` keeps the energy bounded below when
cubic/quartic mode couplings
are added. The scalaron instantiations are `scalaron_fock_mass_gap` and its
two siblings at `scalaronMass α = 1/\sqrt{12\alpha}`.
:::

:::paragraph
The honest boundary is the modelling input, and it is worth stating plainly
because it is exactly where the two realizations above meet. What the chain
takes as given is that the sector's one-particle energy is the constant
$`1/\sqrt{12\alpha}` — true for the quadratic $`m\,N_\psi` realization by
definition. For the full-exponential realization
$`h_\psi = \tfrac12\pi^2 + V(\hat\varphi)` — the exponential used as-is, no
Taylor expansion — a precision is owed about *which* formalized Hamiltonian
the proved QG theorems address, and what transfers. The wall theory
(`starobinskyWall_esa` in `ChapterScalaronWallEsa`: every smooth
non-negative potential, no growth restriction, on the compactly supported
smooth core, plus `wallHamBddBelow_semibounded` for the form) is stated for
$`-d^2/dx^2 + W`; the model's kinetic normalization is
$`\tfrac12\pi^2 = -\tfrac12\,d^2/d\varphi^2`, the same class after the
unitary rescaling $`\varphi = \sqrt2\,x` — so the scalaron *fiber*'s
essential self-adjointness, Stone flow and lower bound carry over with the
potential needing no caveat at all (the model's $`V` is exactly the
formalized `starobinskyV`). Separately, `ChapterScalaronFockEsa`
(`qgScalaronFock_esa`, `qgScalaronFock_stone_flow`) and the densitized
route (`ChapterQuantumGravityDensitized`, `ChapterScalaronDensitizedTransfer`)
formalize the **metric-route** 3+1 gauge fixing — conformal mode
$`V_3(R_c)` plus the scalaron on the densitized conformal variables — that
is, the previous module `docs/qg_starobinsky_hamiltonian.cdb`, **not** the
vielbein/TEGR Hamiltonian derived above. For the vielbein/TEGR Hamiltonian
(`docs/qg_starobinsky_vielbein_hamiltonian.cdb`) the proved layer applies
fiber by fiber: the scalaron fiber via the wall class (same $`V`, rescaled
kinetic), the TEGR shear fibers via the constant/diagonal one-particle
chains (per-mode energy a positive constant), and the fibrewise
direct-sum instrument (`ChapterDirectSumEsa`, the generic
`fockSmoothPotential_esa`) reassembles the nested Fock space once each
fiber's essential self-adjointness is in place. What the metric-route
theorems do *not* provide is a statement about the TEGR gravity sector
itself. With the fibers covered, the single remaining input for a *strict*
gap is the positivity of the one-particle edge: an explicit $`E_0 > 0`
with $`\langle\psi, h_\psi\,\psi\rangle \ge E_0\|\psi\|^2`
(numerically $`E_0 \approx 0.689` at $`\alpha = 1/12` in `../unfer`,
`qg_starobinsky_vielbein_hamiltonian_full`). That is an elementary
confinement estimate, not an existence problem: for any $`0 < c <
M^4/(16\alpha)` the superlevel set $`\{V < c\}` is a bounded interval
(exponential wall on one side, potential shelf $`M^4/(16\alpha)` on the
other), the kinetic energy inside it and the outside cost $`c` bound the
form away from zero — or the certified Ritz bands of the numerical model
feed the existing `BandEnclosure` route. The TEGR kinetic sector is not
covered by the constant-model chain, and no Yang–Mills claim is made.
:::

# The Hermite Core: Where the Hamiltonian Is Defined

:::paragraph
The numerics work in the Hermite basis, so the honest domain question is whether
the Hamiltonian is defined on the *Gauss–polynomial core* — the functions
$`p(x) e^{-x^2/4}` with $`p` a polynomial. It is, and the reason is a single
inequality: the Gaussian tail dominates every exponential,
$`e^{c|x|} \le e^{2c^2} e^{x^2/8}` for all real $`c` and $`x`, so that
$`e^{c|x|} e^{-x^2/4} \le e^{2c^2} e^{-x^2/8} \to 0`. Every function in the
*exponential growth class* $`|W(x)| \le C e^{c\|x\|}` — which contains every
polynomial, and contains the scalaron potential, whose exponential wall puts it
outside the temperate class — therefore multiplies a core element back into
$`L^2`. The core is also invariant under differentiation, since
$`(p e^{-x^2/4})' = (p' - x p/2) e^{-x^2/4}`, so the second derivative of a core
element is again a core element and
$`H\psi = -\psi'' + W\psi` lands in $`L^2` for every core element $`\psi`.
:::

```
#check @BookProof.QgHermiteCore.exp_abs_le_const_mul_exp_sq
#check @BookProof.QgHermiteCore.exp_abs_mul_gaussH_le
#check @BookProof.QgHermiteCore.tendsto_exp_abs_mul_gaussH_atTop
#check @BookProof.QgHermiteCore.expBounded_poly
#check @BookProof.QgHermiteCore.expBounded_starobinskyV
#check @BookProof.QgHermiteCore.memLp_mul_gaussPoly_of_expBounded
#check @BookProof.QgHermiteCore.hasDerivAt_gaussPoly
#check @BookProof.QgHermiteCore.memLp_hamiltonian_gaussPoly
#check @BookProof.QgHermiteCore.memLp_scalaronHamiltonian_gaussPoly
```

:::paragraph
The same argument runs in every dimension on the product Gauss–polynomial core of
$`L^2(\mathbb{R}^d)`, since a polynomial in the coordinates is itself dominated by
an exponential of the norm and an exponentially bounded function of one coordinate
is exponentially bounded on $`\mathbb{R}^d`. In particular the full potential of
the reduced two-variable sector, $`V_3(R_c) + V(\varphi)`, maps the core of
$`L^2(\mathbb{R}^2)` into $`L^2(\mathbb{R}^2)`.
:::

```
#check @BookProof.QgHermiteCore.integral_gaussPoly_mul
#check @BookProof.QgHermiteCore.gint_gaussPolyDeriv_antisymm
#check @BookProof.QgHermiteCore.gint_gaussPolyDeriv_two_symm
#check @BookProof.QgHermiteCore.integral_kinetic_symm
#check @BookProof.QgHermiteCore.integral_hamiltonian_symm
#check @BookProof.QgHermiteCore.integral_scalaronHamiltonian_symm
```

:::paragraph
On this core the Hamiltonian is moreover *symmetric*. Differentiation is antisymmetric
against the Gaussian weight — the boundary terms of the integration by parts vanish —
so the second derivative is symmetric, and multiplication by a real potential is
symmetric for free; the two combine into
$`\int \psi\,(H\varphi) = \int (H\psi)\,\varphi` for all core elements. Together with
the density of the core this is the symmetric-operator half of the essential
self-adjointness question; the deficiency half is not proved here.
:::

```
#check @BookProof.QgHermiteCore.exists_exp_bound_mvPolyEval
#check @BookProof.QgHermiteCore.memLp_mul_pgFun_of_expBounded
#check @BookProof.QgHermiteCore.expBounded_scalaronSectorPotential
#check @BookProof.QgHermiteCore.memLp_scalaronSectorPotential_mul_pgFun
```

:::paragraph
This is the well-definedness half of the Hermite-core programme. It fixes the
domain in the basis the algorithm uses; it does *not* by itself give essential
self-adjointness on that core. For the *potential term* the next section closes
that gap even for the exponential wall; for the full operator $`-\Delta + V` it
remains open, as does the hyperbolic (Strichartz / direct-integral) residue for the
conformal-mode kinetic term.
:::

# The Exponential Wall Is Not an Obstruction on the Hermite Core

:::paragraph
Multiplication by the scalaron potential is *essentially* self-adjoint on the
Gauss–polynomial core — no temperate growth, no boundedness, no semiboundedness
hypothesis. The obstruction one expects is that a deficiency vector $`w` at a
non-real $`z` gives the function $`u = (W - z)w`, which is *not* square
integrable when $`W` grows exponentially, so the usual moment argument (vanishing
of all $`\int p\,e^{-\|x\|^2/4}u`) cannot be quoted. What replaces square
integrability is *Gaussian exponential decay*: $`e^{c\|x\|}e^{-\|x\|^2/4}u` is
integrable for *every* $`c`, because $`|u| \le C e^{c\|x\|}|w|` with
$`w \in L^2` and the Gaussian beats every exponential. That is all the Fourier
argument ever used: the transform of $`e^{-\|x\|^2/4}u` is an everywhere
convergent power series in the moments, hence identically zero, hence $`u = 0`
almost everywhere; and $`W - z` never vanishes because $`W` is real. So $`w = 0`,
both deficiency spaces are trivial, and the core is a genuine core.
:::

```
#check @BookProof.ScalaronHermiteEsa.gaussExpDecay_potential_sub
#check @BookProof.ScalaronHermiteEsa.ae_eq_zero_of_moments_of_gaussExpDecay
#check @BookProof.ScalaronHermiteEsa.potCore_deficiencyTrivialAt
#check @BookProof.ScalaronHermiteEsa.potCore_essentiallySelfAdjoint
#check @BookProof.ScalaronHermiteEsa.scalaronPot_essentiallySelfAdjoint
#check @BookProof.ScalaronHermiteEsa.scalaronSector_essentiallySelfAdjoint
#check @BookProof.ScalaronHermiteEsa.scalaronPot_stone_flow
#check @BookProof.ScalaronHermiteEsa.scalaronSector_stone_flow
```

:::paragraph
The statement holds in every dimension for every continuous exponentially bounded
real potential, so both the one-variable scalaron potential and the full reduced
sector potential $`V_3(R_c) + V(\varphi)` are covered, and the essential
self-adjointness — rather than a choice of extension — is what produces the
self-adjoint realization and its unitary group. What is *not* claimed is the sum
$`-\Delta + V` on the Hermite core with the exponential potential; there the
Friedrichs realization of the next section is still what is available.
:::

# Why Kato–Rellich Cannot Be Used for the Sum

:::paragraph
The natural first attempt at $`-\Delta + V` on the Hermite core is Kato–Rellich:
show that $`V` is relatively bounded with respect to the kinetic term with
relative bound less than one. For the exponential wall that attempt cannot
succeed, and the reason is quantitative. Test the two sides against the monomial
core family $`\psi_N(x) = x^N e^{-x^2/4}`. The reference operators map this family
into itself by polynomial maps of fixed degree increment,
$`(-d^2/dx^2 + x^2/4)\psi_N = ((N + \tfrac12)x^N - N(N-1)x^{N-2})e^{-x^2/4}`, and
the monomial moment recursion turns that into $`\|H_0\psi_N\| \le (N^2+1)\|\psi_N\|`
and $`\|\psi_N''\| \le (N^2+1)\|\psi_N\|`: cubic growth at worst. The wall, by
contrast, is an exponentially tilted Gaussian moment; keeping the eighth-order term
of the tilt gives $`\int e^{-2sx}x^{2N}e^{-x^2/2} \ge (2s^8/315)M_{2N+8}` and
$`M_{2N+8} = (2N+7)(2N+5)(2N+3)(2N+1)M_{2N}`, so the quadratic form of $`V` along
the family grows like $`N^4`. A quartic cannot be dominated by a cubic, and the
conclusion is not merely that the relative bound fails to be small — no pair of
constants $`(a,b)` works at all, for the kinetic term and for the conformal-mode
oscillator alike.
:::

```
#check @BookProof.HermiteExpWall.quadForm_scalaron_ge
#check @BookProof.HermiteExpWall.l2_scalaron_ge
#check @BookProof.HermiteExpWall.l2_kin_le
#check @BookProof.HermiteExpWall.l2_osc_le
#check @BookProof.HermiteExpWall.not_relatively_bounded_of_cubic
#check @BookProof.HermiteExpWall.scalaronV_not_kinetic_relativelyBounded
#check @BookProof.HermiteExpWall.scalaronV_not_oscillator_relativelyBounded
```

:::paragraph
This is a genuine obstruction rather than a gap in the bookkeeping, and it explains
the shape of the two preceding sections: the oscillator chapter can only absorb
*bounded* perturbations by Kato–Rellich, and the exponential case had to be handled
by the Fourier/moment route instead. For the sum $`-\Delta + V` with the exponential
wall what remains is the Friedrichs realization.
:::

# What Kato–Rellich *Can* Reach: Quadratically Dominated Potentials

:::paragraph
The obstruction of the previous section is about the exponential wall specifically,
not about the method, and it is worth recording exactly how far the method does
reach. The reference operator to perturb is not the bare kinetic term but the
harmonic Hamiltonian $`H_0 = -\Delta + W` with $`W(x) = \|x\|^2/4`, the one for
which the Gauss–polynomial core is already a core. Against *that* operator the
harmonic potential itself is relatively bounded, with relative constant exactly one:
$`\|W\psi\|^2 \le \|H_0\psi\|^2 + \tfrac{d}{2}\|\psi\|^2` for every $`\psi` in the
core. The proof is the anticommutator identity $`\{-\Delta, W\} = -\Delta W +
2\sum_j(-\partial_j)W\partial_j`, which on the core is a finite algebraic
computation with the twisted derivative $`D_j` and Gaussian integration by parts:
since $`W \ge 0` and $`\Delta W = d/2`, the cross term
$`2\operatorname{Re}\langle -\Delta\psi, W\psi\rangle` is bounded below by
$`-\tfrac{d}{2}\|\psi\|^2`, and expanding $`\|H_0\psi\|^2` gives the bound.
:::

:::paragraph
Kato–Rellich then absorbs any continuous potential $`V` dominated pointwise by
$`a\|x\|^2/4 + b` with $`a < 1`: the Gauss–polynomial core stays a core for
$`-\Delta + \|x\|^2/4 + V`, and $`V` is allowed to be unbounded. In growth form the
criterion reads: a continuous potential $`U` with
$`|U(x) - \|x\|^2/4| \le A\|x\|^2 + C\|x\| + B` and $`4A < 1` — the linear and
constant coefficients arbitrary — is essentially self-adjoint on the core. Two
corollaries are worth naming: every perturbation of at most linear growth is
admissible, and the scaled oscillator $`-\Delta + \lambda\|x\|^2/4` is essentially
self-adjoint on the *fixed*, width-one Gauss core for every $`\lambda \in (0,2)`.
:::

```
#check @BookProof.HermiteQuadraticEsa.gaussInt_anticommutator
#check @BookProof.HermiteQuadraticEsa.norm_sq_harmPoly_mul_le
#check @BookProof.HermiteQuadraticEsa.norm_harmPoly_mul_le
#check @BookProof.HermiteQuadraticEsa.harmonic_add_subquadratic_essentiallySelfAdjoint
#check @BookProof.HermiteQuadraticEsa.harmonic_add_subquadratic_stone_flow
#check @BookProof.HermiteQuadraticEsa.quadraticGrowth_essentiallySelfAdjoint
#check @BookProof.HermiteQuadraticEsa.harmonic_add_linearGrowth_essentiallySelfAdjoint
#check @BookProof.HermiteQuadraticEsa.scaledHarmonic_essentiallySelfAdjoint
```

:::paragraph
The instance this chapter was after is the regularized conformal mode itself. The
potential $`V_3(R_c) = -\tfrac{M^2}{2}R_c + \alpha R_c^2` differs from $`R_c^2/4` by
$`(\alpha - \tfrac14)R_c^2 - \tfrac{M^2}{2}R_c`, so the criterion applies as soon as
$`|\alpha - \tfrac14| < \tfrac14`, that is for $`0 < \alpha < \tfrac12`, with the
mass term absorbed for free at any $`M`. The conclusion is unconditional — no
finite-speed and no unique-continuation hypothesis — and it yields the unitary group
directly, without a choice of extension.
:::

```
#check @BookProof.HermiteQuadraticEsa.confW
#check @BookProof.HermiteQuadraticEsa.confV_essentiallySelfAdjoint
#check @BookProof.HermiteQuadraticEsa.confV_stone_flow
```

:::paragraph
The two-variable reduced sector is reached the same way. Its potential is
$`V_3(R_c) + V(\varphi)`, and while the exponential wall $`V(\varphi)` is out of
reach, its harmonic approximation at the minimum is not: $`V` vanishes to second
order at $`\varphi = 0` with $`V(\varphi)/\varphi^2 \to M^2/(24\alpha)`, so the
quadratic sector potential is $`V_3(R_c) + \mu\varphi^2`. Both variables now have to
sit inside the window of the core, which is $`0 < \alpha < \tfrac12` for the
conformal mode and $`0 < \mu < \tfrac12` for the scalaron mass; at the physically
natural $`\mu = M^2/(24\alpha)` the second condition reads $`M^2 < 12\alpha`.
:::

```
#check @BookProof.HermiteQuadraticEsa.sectorQuadW
#check @BookProof.HermiteQuadraticEsa.sectorQuad_essentiallySelfAdjoint
#check @BookProof.HermiteQuadraticEsa.sectorQuad_stone_flow
#check @BookProof.HermiteQuadraticEsa.tendsto_starobinskyV_div_sq
#check @BookProof.HermiteQuadraticEsa.sectorHarmonicApprox_essentiallySelfAdjoint
```

:::paragraph
The window $`a < 1` is the honest edge of the method rather than an artifact: the
relative bound of $`W` against $`H_0` is exactly one, so a strictly larger relative
bound cannot be absorbed. On a Gauss core of a different width the same argument
relocates the window in $`\alpha`; what no width reaches is the exponential wall,
by the refutation of the previous section.
:::

# The Friedrichs Realization on the Hermite Core

:::paragraph
Fixing the domain is not yet fixing the operator. On the Gauss–polynomial core the
Hamiltonian $`H = -\Delta + W` is a densely defined *symmetric* operator, and the
question the numerics ultimately need answered is which self-adjoint operator it is
that the algorithm propagates. The first half of that answer is unconditional: in
every dimension, and for every continuous potential of exponential growth class,
$`H` is symmetric on the core and its quadratic form is bounded below by the lower
bound of the potential,
$`\operatorname{Re}\langle \psi, H\psi\rangle \ge c\,\|\psi\|^2` whenever
$`W \ge c`. The kinetic half of that inequality is an identity: integrating by parts
against the Gaussian weight turns $`\langle \psi, -\Delta\psi\rangle` into
$`\sum_j \|D_j\psi\|^2 \ge 0`, where $`D_j p = \partial_j p - x_j p/2` is the
twisted derivative that differentiation induces on the polynomial factor.
:::

```
#check @BookProof.QgHermiteFriedrichs.coreD
#check @BookProof.QgHermiteFriedrichs.kinPoly
#check @BookProof.QgHermiteFriedrichs.gaussInt_coreD
#check @BookProof.QgHermiteFriedrichs.gaussInt_kinPoly
#check @BookProof.QgHermiteFriedrichs.hamCore
#check @BookProof.QgHermiteFriedrichs.hamCore_symmetricOn
#check @BookProof.QgHermiteFriedrichs.re_gaussInt_kinPoly_self
#check @BookProof.QgHermiteFriedrichs.hamCore_quadForm_ge
#check @BookProof.QgHermiteFriedrichs.hasDerivAt_pgFun_coord
```

:::paragraph
Density of the core plus symmetry plus semiboundedness is exactly the input of the
Friedrichs extension theorem, so the Hamiltonian on the Hermite core has a canonical
semibounded self-adjoint realization — positive when the potential is. For the
scalaron this is unconditional, because $`V(\varphi) = \frac{M^4}{16\alpha}
\left(1 - e^{-\sqrt{2/3}\,\varphi/M}\right)^2 \ge 0`: the one-particle scalaron
Hamiltonian on the Gauss–polynomial core of $`L^2(\mathbb{R})` has a *positive*
self-adjoint extension. On the reduced two-variable sector $`(R_c, \varphi)` the
conformal-mode parabola contributes its own lower bound $`-M^4/(16\alpha)`, and the
realization is semibounded with that constant.
:::

```
#check @BookProof.QgHermiteFriedrichs.hermiteCore_friedrichs_extension
#check @BookProof.QgHermiteFriedrichs.hermiteCore_friedrichs_extension_of_nonneg
#check @BookProof.QgHermiteFriedrichs.qgOneParticleHermite_friedrichs
#check @BookProof.QgHermiteFriedrichs.qgOneParticleSector_friedrichs
```

:::paragraph
The honest boundary is the difference between *a* self-adjoint realization and *the*
one. What is proved is existence together with a canonical choice; what is not proved
is that the choice is forced, i.e. essential self-adjointness of $`H` on the
Gauss–polynomial core. Uniqueness would remove the last piece of arbitrariness from
the one-particle sector; the hyperbolic (Strichartz / direct-integral) residue for the
conformal-mode kinetic term is a separate open question, unaffected by this section.
:::

# When the Core Is a Core: Essential Self-Adjointness for the Parabolic Potential

:::paragraph
For one potential the arbitrariness disappears entirely. The Gauss–polynomial core is
spanned by the product Hermite functions
$`\psi_\alpha(x) = \prod_i He_{\alpha_i}(x_i)\, e^{-\|x\|^2/4}`, and those are
*eigenvectors* of $`-\Delta + \|x\|^2/4`: on the polynomial side the Hamiltonian is the
number operator plus $`d/2`, because
$`-D_j^2 + x_j^2/4 = a_j^\dagger a_j + 1/2` and $`a_j^\dagger a_j He_\alpha = \alpha_j
He_\alpha`. Hence $`H\psi_\alpha = (|\alpha| + d/2)\,\psi_\alpha`. A symmetric operator
whose domain contains an orthonormal basis of eigenvectors with real eigenvalues has no
deficiency vector at any non-real point — if $`\langle Hv, w\rangle = z\langle v,
w\rangle` for all $`v` in the domain, then $`(\lambda_\alpha - z)\langle \psi_\alpha,
w\rangle = 0` for every $`\alpha`, and $`z` non-real forces $`w = 0`. So the harmonic
Hamiltonian is *essentially* self-adjoint on the Gauss–polynomial core, in every
dimension, with no auxiliary hypothesis; Stone's theorem then supplies the unitary flow.
:::

```
#check @BookProof.QgHermiteOscillator.deficiencyTrivialAt_of_eigenbasis
#check @BookProof.QgHermiteOscillator.essentiallySelfAdjointOn_of_eigenbasis
#check @BookProof.QgHermiteOscillator.kinPoly_add_harmPoly
#check @BookProof.QgHermiteOscillator.crePoly_annPoly_hermiteMv
#check @BookProof.QgHermiteOscillator.harmCore_hermiteMvLp
#check @BookProof.QgHermiteOscillator.harmonicCore_essentiallySelfAdjoint
#check @BookProof.QgHermiteOscillator.harmonicCore_stone_flow
```

:::paragraph
Kato–Rellich extends the conclusion past the exact parabola: multiplication by a bounded
continuous real function is symmetric on the core and satisfies $`\|B\psi\| \le M\|\psi\|`,
a relative bound of $`0`, so $`-\Delta + \|x\|^2/4 + B` is essentially self-adjoint on the
same core. What is still missing is the exponential wall — the scalaron potential is not
dominated by the parabola, and for it only the Friedrichs realization of the previous
section is available.
:::

```
#check @BookProof.QgHermiteOscillator.potCore_symmetricOn
#check @BookProof.QgHermiteOscillator.norm_potLp_le
#check @BookProof.QgHermiteOscillator.hamCore_add_potential
#check @BookProof.QgHermiteOscillator.harmonic_add_bounded_essentiallySelfAdjoint
```

# In What Sense the Realization Is Canonical

:::paragraph
"Friedrichs extension" names a construction, not yet a characterization: a densely
defined symmetric operator generally admits many self-adjoint extensions, and the
construction only produces one of them. What singles this one out is its *form
domain*. The domain of $`H` carries the form inner product
$`\langle x, y\rangle_1 = \langle x, y\rangle + \langle x, Hy\rangle`; positivity and
symmetry make it an inner product dominating the ambient one, its completion embeds
injectively back into the Hilbert space, and that image $`Q(H)` is the form domain.
The Friedrichs domain — the range of the resolvent $`S = (H+1)^{-1}` built by Riesz
representation in the form space — lies inside $`Q(H)`, as does the domain of $`H`
itself.
:::

```
#check @BookProof.FriedrichsCanonical.formDomain
#check @BookProof.FriedrichsCanonical.friedrichsDomain
#check @BookProof.FriedrichsCanonical.friedrichsOp
#check @BookProof.FriedrichsCanonical.dom_le_formDomain
#check @BookProof.FriedrichsCanonical.friedrichsDomain_le_formDomain
#check @BookProof.FriedrichsCanonical.friedrichsOp_isPositiveSelfAdjointExtension
```

:::paragraph
The characterization is that nothing else fits inside $`Q(H)`. Let $`A'` be any
symmetric extension of $`H` with $`\operatorname{dom} A' \subseteq Q(H)`, and let
$`x \in \operatorname{dom} A'`. Put $`u = A'x + x` and $`y = Su`. Both $`x` and $`y`
lie in the form domain, so their difference is the image of some vector $`k` of the
form completion, and for every $`v` in the domain of $`H` the form pairing computes
as $`\langle v, k\rangle_1 = \langle v + Hv, x - y\rangle`. Symmetry of $`A'` turns
the first half into $`\langle v, u\rangle`, and self-adjointness of $`S` together with
$`S(v + Hv) = v` turns the second half into the same thing, so the pairing vanishes.
The domain is dense in the completion, hence $`k = 0`, hence $`x = y` — every such
$`A'` is a restriction of the Friedrichs operator. If $`A'` is in addition
self-adjoint, its own self-adjointness criterion forces the reverse inclusion, and
the two operators coincide, domain and action alike.
:::

```
#check @BookProof.FriedrichsCanonical.friedrichs_canonical
#check @BookProof.FriedrichsCanonical.friedrichs_unique_selfAdjoint
```

:::paragraph
Applied to the scalaron this says: on the Gauss–polynomial core of $`L^2(\mathbb{R})`
the Hamiltonian $`-\Delta + V(\varphi)` has one and only one positive self-adjoint
realization whose domain stays inside the form domain, and it is the constructed one.
This is weaker than essential self-adjointness and does not pretend otherwise — an
operator that is not essentially self-adjoint still has other self-adjoint extensions,
but each of them must leave $`Q(H)`. Within the energy-form class the quantum-gravity
one-particle Hamiltonian is therefore unambiguous.
:::

```
#check @BookProof.FriedrichsCanonical.qgOneParticleHermite_friedrichs_canonical
#check @BookProof.FriedrichsCanonical.qgOneParticleHermite_friedrichs_unique
```

:::paragraph
The same account covers the merely semibounded case, which is what the reduced
two-variable sector needs: if $`\langle x, Hx\rangle \ge -c\|x\|^2` then $`H + c` is
positive, its Friedrichs extension exists by the above, and subtracting $`c` again
returns a self-adjoint extension of $`H` with the same lower bound — unique, once
more, among those whose domain lies in the form domain of the shift. For the sector
$`(R_c, \varphi)` the constant is the one the conformal-mode parabola supplies.
:::

```
#check @BookProof.FriedrichsCanonical.semiboundedFriedrichsOp
#check @BookProof.FriedrichsCanonical.semiboundedFriedrichsOp_isSemiboundedSelfAdjointExtension
#check @BookProof.FriedrichsCanonical.semibounded_friedrichs_unique
#check @BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_canonical
#check @BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_unique
```

:::paragraph
None of this is vacuous: applied to the diagonal operator $`Ae_n = n e_n` on the
finite-mode domain of $`\ell^2(\mathbb{N})` — genuinely unbounded — the construction
produces a positive self-adjoint extension, and the uniqueness statement pins it down
among the extensions whose domain lies in the form domain.
:::

```
#check @BookProof.FriedrichsCanonical.unbounded_friedrichs_canonical_example
```

# The Compactly Supported Core

:::paragraph
The Gauss–polynomial core is convenient but not canonical. The core a physicist
actually writes down is $`C_c^\infty(\mathbb{R}^d)`, the smooth functions of compact
support: it is where test wave packets live, it is stable under localization, and it
is the building block of the finite-particle Fock core. Essential self-adjointness on
it is the stronger statement, because a smaller core means fewer test vectors are
available to kill a deficiency vector — and it implies the same conclusion on every
larger core, the Gauss core included.
:::

:::paragraph
Neither core sits inside the other: a Gauss polynomial $`p(x)e^{-\|x\|^2/4}` is never
compactly supported, and a bump function is never a Gauss polynomial. So the transfer
cannot be a restriction argument. What replaces it is approximation in the graph norm:
if every vector of $`D_1` is approximated, together with its image under the operator,
by vectors of $`D_2`, then a deficiency vector for the operator on $`D_2` is one for
the operator on $`D_1`, and triviality of the deficiency spaces passes from $`D_1` to
$`D_2` even though the domains are unrelated.
:::

```
#check @BookProof.QgOneParticleCc.deficiencyTrivialAt_of_graphApprox
#check @BookProof.QgOneParticleCc.essentiallySelfAdjointOn_of_graphApprox
#check @BookProof.QgOneParticleCc.ccHam
#check @BookProof.QgOneParticleCc.ccHam_symmetricOn
```

:::paragraph
The analytic input is a cut-off estimate. With $`\chi` a fixed bump equal to one on the
unit ball and $`\chi_R(x) = \chi(x/R)`, the Leibniz rule gives
$$`(-\Delta + W)(\chi_R\psi) - (-\Delta + W)\psi
 = (\chi_R - 1)(-\Delta\psi + W\psi) - 2\sum_j \partial_j\chi_R\,\partial_j\psi
   - (\Delta\chi_R)\psi.`
Each of the three terms is $`o(1)` in $`L^2`: the first by dominated convergence, since
$`\chi_R - 1` vanishes on the ball of radius $`R` and is bounded; the second and third
because the scaling gives $`|\partial\chi_R| \le C/R` and $`|\Delta\chi_R| \le C/R^2`
while $`\partial_j\psi` and $`\psi` are square integrable. Hence every Gauss-core vector
is a graph-norm limit of compactly supported smooth ones, and essential self-adjointness
descends.
:::

```
#check @BookProof.QgOneParticleCc.exists_cut_derivative_bounds
#check @BookProof.QgOneParticleCc.exists_cc_graph_approx
#check @BookProof.QgOneParticleCc.ccHam_essentiallySelfAdjoint_of_core
```

:::paragraph
The payoff is the one-particle theorem in the form the applications want: for every
smooth $`V` with $`|V| \le a\|x\|^2/4 + b` and $`a < 1`, the gauge-fixed Hamiltonian
$`-\Delta + \|x\|^2/4 + V` is essentially self-adjoint on $`C_c^\infty(\mathbb{R}^d)`,
and Stone's theorem then supplies the unitary group. The conformal mode in one variable
and the reduced two-variable sector $`(R_c,\varphi)` of $`R + \alpha R^2` are instances,
under the same $`0 < \alpha < 1/2` window that made the parabola subquadratic.
:::

```
#check @BookProof.QgOneParticleCc.qgOneParticleCc_esa
#check @BookProof.QgOneParticleCc.qgOneParticleCc_stone_flow
#check @BookProof.QgOneParticleCc.confVCc_esa
#check @BookProof.QgOneParticleCc.sectorQuadCc_esa
```

:::paragraph
Second quantization is then free. The $`n`-particle potential
$`\sum_k (\|x_k\|^2/4 + V(x_k))` on $`(\mathbb{R}^d)^n \cong \mathbb{R}^{nd}` obeys the
same quadratic bound with the same $`a` and $`n` times the constant, so each sector
Hamiltonian is essentially self-adjoint on its own compactly supported smooth core; the
direct-sum criterion assembles the sectors into the finite-particle Fock space, whose
core is the algebraic direct sum of the one-particle cores. The second-quantized
$`R + \alpha R^2` Hamiltonian is essentially self-adjoint there, with a unitary
time evolution.
:::

```
#check @BookProof.QgOneParticleCc.qgNParticleCc_esa
#check @BookProof.QgOneParticleCc.qgFock
#check @BookProof.QgOneParticleCc.qgFockCore
#check @BookProof.QgOneParticleCc.qgFockHam
#check @BookProof.QgOneParticleCc.qgFockCc_esa
#check @BookProof.QgOneParticleCc.qgFockCc_stone_flow
```

:::paragraph
The boundary is the same one as on the Gauss core, and is stated rather than hidden: the
potential class transported here is the quadratic one. The exponentially growing scalaron
wall $`e^{\beta\varphi}` is not covered — on the Gauss core it is refuted outright, because
the wall does not even map that core into $`L^2`. Localizing the core does not repair that;
it only strengthens the conclusion within the class where the conclusion holds. The wall is
reached instead by the entirely different argument of the next section.
:::

# The Exponential Wall, Closed by Convexity

:::paragraph
The transfer of the previous section moves a *quadratic-class* theorem, so it leaves the
wall itself untouched, and every perturbative route to the wall is refuted: it is not a
relatively bounded perturbation of $`-\Delta` or of $`-\Delta + x^2/4` on the Gauss core
with any pair of constants, and the Carleman flux criterion fails because the Hermite
amplitudes grow like $`e^{c\sqrt{N}}`, so $`\sum 1/A` converges. What closes the wall is
not a perturbation argument at all, but the classical convexity argument for a
*non-negative* potential — and the Starobinsky potential is non-negative, being a square.
:::

:::paragraph
The argument runs on the compactly supported smooth core of $`L^2(\mathbb{R})`, the
scalaron direction alone. A deficiency vector $`u` at $`z = \pm i` satisfies
$`u'' = (V - z)u` in the sense of distributions. That is an $`L^2` statement about an
equation between distributions, so the first step is regularity: du Bois-Reymond's lemma
in its second-order form says that a locally integrable function orthogonal to the second
derivative of every test function is almost everywhere affine, and iterating it against
the double antiderivative of the right-hand side identifies $`u`, almost everywhere, with
a genuine twice differentiable solution $`W` of $`W'' = (V - z)W`.
:::

```
#check @BookProof.WeakSecondDeriv.ae_eq_affine_of_integral_deriv2_smul_eq_zero
#check @BookProof.WeakSecondDeriv.exists_ae_eq_doubleAntideriv_add_affine
#check @BookProof.WeakSecondDeriv.exists_deriv2_of_weak_eq
```

:::paragraph
With a classical solution in hand the geometry takes over. Since $`\operatorname{Re} z = 0`,
$$`(|W|^2)'' = 2\operatorname{Re}(\bar W W'') + 2|W'|^2 = 2\bigl(V|W|^2 + |W'|^2\bigr) \ge 0,`
so $`|W|^2` is convex. It is also non-negative and — because $`u \in L^2` — integrable.
A convex function on the whole line satisfies $`F(a-s) + F(a+s) \ge 2F(a)`; integrating
over $`s \in [0,R]` bounds $`2F(a)R` by the total integral for *every* $`R`, which forces
$`F \equiv 0`. Hence $`u = 0`: both deficiency spaces are trivial, and the operator is
essentially self-adjoint. No growth hypothesis on $`V` is used anywhere.
:::

```
#check @BookProof.ScalaronWallEsa.eq_zero_of_convexOn_nonneg_integrable
#check @BookProof.ScalaronWallEsa.ode_solution_eq_zero
#check @BookProof.ScalaronWallEsa.wallHam
#check @BookProof.ScalaronWallEsa.wallHam_symmetricOn
#check @BookProof.ScalaronWallEsa.wallHam_essentiallySelfAdjoint
```

:::paragraph
Applied to the scalaron this says: $`-d^2/d\varphi^2 + V(\varphi)` with the exponentially
growing Einstein-frame wall is essentially self-adjoint on $`C_c^\infty(\mathbb{R})`, and
Stone's theorem turns the unique self-adjoint extension into the unitary group
$`e^{-itH}` solving the Schrödinger equation globally in time. The honest boundary that
remains is dimensional rather than about growth: the statement is one-dimensional and the
hypothesis is $`V \ge 0`.
:::

```
#check @BookProof.ScalaronWallEsa.starobinskyWall_esa
#check @BookProof.ScalaronWallEsa.starobinskyWall_stone_flow
```

# Bounded Below, Not Just Non-Negative

:::paragraph
The convexity argument just given needs the potential to be non-negative. That
hypothesis is a restriction on the *argument*, not on the physics, and
`BookProof/ChapterWallEsaBddBelow.lean` removes it with the cheapest possible
move: a constant shift. Multiplication by a real constant `c` is a bounded
symmetric operator (`constOp`, `constOp_symmetric`), and shifting the potential by
`c` shifts the whole operator by exactly that constant (`wallHam_add_const`);
adding a bounded symmetric perturbation preserves essential self-adjointness —
this is Kato–Rellich with relative bound zero
(`BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded`) — so `-d²/dx² + V`
is essentially self-adjoint on the compactly supported smooth core of `L²(ℝ)` for
*every* smooth potential `V` that is merely bounded below, still with no growth
restriction above (`wallHam_essentiallySelfAdjoint_of_bddBelow`), and Stone's
theorem turns the unique extension into the unitary group
(`wallHam_stone_flow_of_bddBelow`).
:::

```
#check @BookProof.WallEsaBddBelow.constOp
#check @BookProof.WallEsaBddBelow.constOp_symmetric
#check @BookProof.WallEsaBddBelow.wallHam_add_const
#check @BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded
#check @BookProof.WallEsaBddBelow.wallHam_essentiallySelfAdjoint_of_bddBelow
#check @BookProof.WallEsaBddBelow.wallHam_stone_flow_of_bddBelow
```

:::paragraph
Two instances put the shift to work. `scalaronPlus_esa` is the scalaron wall plus
an arbitrary smooth, bounded-below addition — and the conformal-mode parabola,
bounded below by `-M⁴/(16α)`, is exactly such an addition, so the full
one-variable gauge-fixed operator `-d²/dφ² + V(φ) + V₃(R_c)` is essentially
self-adjoint on the compactly supported smooth core. `oscillatorPlus_esa` is the
harmonic oscillator `-d²/dx² + x²/4 + V` with `V` merely bounded below: *no*
relative bound between `V` and the oscillator is required — which is precisely
what fails for the exponential wall on the Gauss–polynomial core, where the wall
is not a relatively bounded perturbation of the oscillator with any pair of
constants (the `HermiteExpWall` refutation above). The two routes are
complementary rather than redundant: the Hermite route reaches the quadratically
dominated class on the Gauss core, and the wall route reaches every
bounded-below potential on the compactly supported core.
:::

```
#check @BookProof.WallEsaBddBelow.scalaronPlus_esa
#check @BookProof.WallEsaBddBelow.oscillatorPlus_esa
```

# The Exponential Wall Itself, and the Energy Form

:::paragraph
The clause "every smooth potential bounded below" contains the motivating example
of the whole discussion, so it is worth writing it down as its own theorem. The
potential $`V(x) = e^{x} + e^{-x} = 2\cosh x` is smooth and bounded below by `2`,
so `-d²/dx² + (eˣ + e⁻ˣ)` is essentially self-adjoint on the compactly supported
smooth core of $`L^2(\mathbb{R})` (`expPotential_esa`), with unitary group
$`e^{-itH}` (`expPotential_stone_flow`); `coshPotential_esa` below is the same
statement written with `cosh`. This potential grows faster than any polynomial,
so no relative-boundedness (Kato–Rellich) criterion reaches it.
:::

```
#check @BookProof.ExpPotentialEsa.contDiff_Vexp
#check @BookProof.ExpPotentialEsa.expPotential_esa
#check @BookProof.ExpPotentialEsa.expPotential_stone_flow
#check @BookProof.ExpPotentialEsa.coshPotential_esa
```

:::paragraph
The shift-invert schemes need one more thing from the operator: that its
*quadratic form* be bounded below, not merely that the operator be essentially
self-adjoint. On the compactly supported smooth core this is one integration by
parts. The Green identity
$`\langle (-d^2/dx^2 + V) f, f\rangle = \int |f'|^2 + \int V|f|^2`
splits the pairing into a Dirichlet term (`kinCcR_quadratic_form`) and a potential
term (`opCc_quadratic_form`); the first is non-negative and the second is at least
$`-c\|f\|^2` when $`V \geq -c`, which is `wallHamBddBelow_semibounded`. For the
exponential wall the constant is `0` (`expPotential_semibounded`).
:::

```
#check @BookProof.WallEsaSemibounded.SemiboundedBelowOn
#check @BookProof.WallEsaSemibounded.integral_conj_neg_deriv2_mul
#check @BookProof.WallEsaSemibounded.kinCcR_quadratic_form
#check @BookProof.WallEsaSemibounded.opCc_quadratic_form
#check @BookProof.WallEsaSemibounded.wallHamBddBelow_semibounded
#check @BookProof.ExpPotentialEsa.expPotential_semibounded
```

:::paragraph
There is also a second, entirely elementary route to the same physics, which does
not go through the convexity argument or the constant shift at all:
`BookProof/ChapterSchrodingerCutoffEsa.lean` runs the Simader–Faris–Lavine
cutoff/commutator energy estimate directly. Testing $`-u'' + Vu = zu` against
$`\chi_R^2 \bar u` and integrating by parts once gives
$`\int_{[-R,R]} (V - \operatorname{Re} z)|u|^2 \leq (2C^2/R^2)\|u\|^2_{L^2}`
together with the companion Dirichlet bound (`cutoff_energy_core`), where `C`
bounds $`|\chi'|`; letting $`R \to \infty` forces `u = 0`
(`l2_classical_solution_eq_zero`). Applied to $`z = \pm i` this says that
$`-d^2/dx^2 + (e^x + e^{-x})` has no nonzero square-integrable *classical*
solution of $`Hu = \pm i u`. Setting $`V = 0` gives the same statement for the
free Laplacian (`laplacian_deficiency_trivial`). The honest boundary of this
second route is that it speaks about classical (twice-differentiable) solutions:
passing from a general $`L^2` deficiency vector to a classical solution is
elliptic regularity, which the first route supplies and this one does not.
:::

```
#check @BookProof.SchrodingerCutoff.exists_scaled_cutoff
#check @BookProof.SchrodingerCutoff.schrodingerOp_symmetric
#check @BookProof.SchrodingerCutoff.cutoff_energy_core
#check @BookProof.SchrodingerCutoff.cutoff_energy_estimate
#check @BookProof.SchrodingerCutoff.l2_classical_solution_eq_zero
#check @BookProof.SchrodingerCutoff.schrodinger_exp_deficiency_trivial_I
#check @BookProof.SchrodingerCutoff.laplacian_deficiency_trivial
```
