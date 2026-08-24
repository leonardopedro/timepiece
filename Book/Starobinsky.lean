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
self-adjointness on that core, which remains open, as does the hyperbolic
(Strichartz / direct-integral) residue for the conformal-mode kinetic term.
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
