import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Fourier Elimination of the Derivative Variables" =>
%%%
tag := "fourier-elimination"
%%%

# The Idea: Eliminate the Jets, Do Not Gauge-Fix Them

:::paragraph
Navier–Stokes is a first-order system in the fields $`u_i` *and* their spatial
derivatives $`u_{i,j} = \partial_j u_i`. When the field space is built out of
coordinates, the derivatives have to be represented by something, and the
preceding chapters represented them by *independent* coordinates
($`u_{i,j}`, the viscous combination $`w_i`, and the auxiliary expansion
coordinates $`y_j`) which were then *fixed* by a gauge symmetry — a BRST charge
with ghosts, whose nilpotency made the gauge-invariant algebra well-defined but
did not remove the redundancy: the constrained sector still had to be built and
the gauge forms appeared inside the Hamiltonian.

This chapter records the alternative followed by the current plan of record:
*eliminate* the derivative coordinates instead of fixing them. The
elimination is applied *inside the squares* that make up the Hamiltonian — each
constraint form is substituted and *both* of its real-coefficient parts are
squared, so the nonlinear advection is kept, squared, rather than dropped — so
the jet coordinates never appear as dynamical variables at all, no ghost sector
is introduced, and the derivative content is carried by the momentum of a spatial
Fourier transform — $`\partial_j \mapsto i k_j` at momentum $`k`. The
substitution is

$`u_{i,j} \mapsto i k_j u_i, \qquad w_i \mapsto -|k|^2 u_i, \qquad y_j \mapsto 0,
\qquad u_i \mapsto u_i, \qquad q_i \mapsto q_i,`

reducing each parcel from twenty-one field-space coordinates to the
*six* physical ones $`(u_i, q_i)`. The algebraic content of the chapter — that
the substitution is a ring map, that the residual and the incompressibility
become *quadratic* and *linear* symbols, and that the reduced Hamiltonian is
again a sum of squares — both real parts of every reduced form, the advection
among them — on which the Friedrichs extension and Faris–Lavine run as
before — is verified in this repository; the displayed algebra of the
substitution is engine-checked in the companion symbolic module
`../unfer/docs/ns_qg_fourier_elimination.cdb`, which is *reference only* and is
never part of a Lean build.
:::

# The Substitution as a Ring Map

:::paragraph
The elimination is defined parcelwise on the polynomial coordinate ring. On one
parcel, `nsElimCoord` maps the twenty-one coordinates $(`u_i`, the nine
`u_{i,j}`, the three `w_i`, the three `q_i`, the three `y_j`) to polynomials in
the six reduced coordinates, and `nsElimHom` applies it to every parcel at once:
:::

```
#check @BookProof.NsFullEuler.nsElimCoord
#check @BookProof.NsFullEuler.liftParcel
#check @BookProof.NsFullEuler.nsElimHom
#check @BookProof.NsFullEuler.nsElimHom_X_d
#check @BookProof.NsFullEuler.nsElimHom_X_w
#check @BookProof.NsFullEuler.nsElimHom_X_y
```

:::paragraph
The last three state that the substitution really is what the display above
claims: the derivative coordinate $`u_{i,j}` goes to $`i k_j u_i`, the viscous
coordinate $`w_i` to $`-|k|^2 u_i`, and the auxiliary coordinate $`y_j` to
$`0`. Because `nsElimHom` is a *ring* homomorphism (an `eval₂Hom`), it
commutes with every sum and product, which is what makes the next step a
computation rather than an argument.
:::

# The Residual Becomes Quadratic

:::paragraph
With the substitution in hand, the two constraint polynomials of the Eulerian
chapter — the residual $`R_i = \sum_j u_j u_{i,j} + q_i - \nu w_i` and the
incompressibility $`\sum_j u_{j,j}` — can be pushed through it. The advection,
the pressure gradient and the viscous term are computed one at a time:
:::

```
#check @BookProof.NsFullEuler.nsElimSubst_advect
#check @BookProof.NsFullEuler.nsElimSubst_pressure
#check @BookProof.NsFullEuler.nsElimSubst_viscous
```

:::paragraph
and assembling them gives the two identities that the elimination rests on:
:::

```
#check @BookProof.NsFullEuler.nsElimSubst_resPoly
#check @BookProof.NsFullEuler.nsElimSubst_divPoly
```

:::paragraph
Written out, the first is

$`\sigma(R_i) = i\,(k \cdot u)\, u_i + q_i + \nu |k|^2 u_i,
\qquad (k \cdot u) = \sum_j k_j u_j,`

and the second is $`\sigma(\sum_j u_{j,j}) = i\,(k \cdot u)`. This is the whole
point of the elimination. In the original coordinates the residual is *cubic*
as a symbol — a product of the field with the field's derivative — which is
exactly what defeats a quadratic comparison operator; after the elimination the
only nonlinearity is the product of two reduced velocities, so the residual is
a *quadratic* form in six variables and the incompressibility is linear. The
symbols themselves are named in the library as `fourierMomentum` (the scalar
$`k \cdot u`), `fourierAdvect` ($`(k \cdot u) u_i`), `fourierDiv`
($`i (k \cdot u)`) and `fourierVisc` ($`q_i + \nu |k|^2 u_i`).
:::

# The Reduced Hamiltonian: Both Real Parts Are Squares

:::paragraph
A multiplication operator on $`L^2` with respect to the real coordinates is
symmetric exactly when its symbol has *real* coefficients. The residual splits
as $`\sigma(R_i) = i\,(k \cdot u) u_i + \big(q_i + \nu |k|^2 u_i\big)`, and *both*
brackets have real coefficients — the first is a real polynomial times $`i`.
Multiplication by that imaginary part is indeed *skew-adjoint* and its operator
square is *negative*, but that square is the operator of the *equation*, not a
summand of the Hamiltonian; the squares in the Hamiltonian are the two
real-coefficient parts, $`\tfrac12\big((k\cdot u)u_i\big)^2` and
$`\tfrac12\big(q_i + \nu|k|^2u_i\big)^2` (equivalently the modulus square of the
multiplication operator of the complex form, whose skew cross term is invisible on
the quadratic form). The reduced Hamiltonian is a Weyl-ordered sum of squares of
those two parts — `fourierVisc` and `fourierAdvect` (the line above lifts the
real part as `redVisc`) — hence nonnegative:
:::

```
#check @BookProof.NsFullEuler.fourierVisc
#check @BookProof.NsFullEuler.redVisc
#check @BookProof.NsFullEuler.realCoeff_redVisc
#check @BookProof.NsFullEuler.redHam
#check @BookProof.NsFullEuler.redHam_symmetricOn
#check @BookProof.NsFullEuler.redHam_quadForm_nonneg
#check @BookProof.NsFullEuler.redHam_friedrichs_extension
```

:::paragraph
This is the honest form of the strategy: the *squares* are the two
real-coefficient parts of each substituted form, so the genuine nonlinearity —
the advection $`(k\cdot u)u_i` — is *inside* the Hamiltonian as one of the
squares, and no perturbation, no commutator estimate and no ghost sector is owed.
Positivity of the sum of squares is what makes the Friedrichs extension
unconditional, exactly as for the full Eulerian sector. The field family
`redFieldN` is the honest one — seven real-coefficient forms per parcel
(`redFormPoly`): the three real residual parts, the three advection parts and the
eliminated incompressibility — so `redHam` is the full modulus-square Hamiltonian
and `redFieldN_advect` exhibits the advection as one of its squares.
:::

# The Nested Fock Lift and Faris–Lavine

:::paragraph
The outer Fock space of the reduced model is the nested space
$`\bigoplus_n L^2(\mathbb{R}^{6n})`, and `nsRedFullFockHam` is the
*particle-number-conserving second quantization* $`d\Gamma(H_1)` of the reduced
one-particle Hamiltonian `redHam` at $`n = 1` — a direct sum over parcel number,
taking no new square. The comparison operator the route needs is the lifted
Friedrichs realization of the reduced one-body operators on that space.
Positivity, symmetry and surjectivity of $`N + 1` are all fibrewise, so they lift
verbatim from the fibre:
:::

```
#check @BookProof.NsFullEuler.nsRedFockSpace
#check @BookProof.NsFullEuler.nsRedFockCore
#check @BookProof.NsFullEuler.nsRedFullFockHam
#check @BookProof.NsFullEuler.nsRedFullFockHam_symmetricOn
#check @BookProof.NsFullEuler.nsRedFullFockHam_quadForm_nonneg
#check @BookProof.NsFullEuler.nsRedFullFock_friedrichs_extension
#check @BookProof.NsFullEuler.nsRedFullFockHam_number_conserving
```

:::paragraph
and Faris–Lavine then gives essential self-adjointness of the reduced generator
on the domain of the lifted comparison operator — the `H = N`, `c = 0` case of
the criterion, in which the committed operator *is* its own comparison, so the
commutator form vanishes — together with the extension statement that discharges
the plan's definition of done for the reduced sector:
:::

```
#check @BookProof.NsFullEuler.nsRedOuterComparison
#check @BookProof.NsFullEuler.nsRedOuterN_apply
#check @BookProof.NsFullEuler.nsRedFockCore_le_friedDom
#check @BookProof.NsFullEuler.nsRedFullOuterN_esa
#check @BookProof.NsFullEuler.nsRedFullOuterN_isPositiveSelfAdjointExtension
```

# The Lagrangian Sector: the Volume Constraint Collapses

:::paragraph
Navier–Stokes is equally often written in **Lagrangian** variables, where the field is the placement
and the derivative content is the deformation gradient $`F = \partial x/\partial X` — so the
elimination has a second, independent instance, and there the elimination degenerates in a way that
is itself the mathematical content.

Everything is done parcelwise on the twelve coordinates of one parcel (`lRedIdx`), with the
substitution defined by `lagElimCoord` and applied by the ring homomorphism `lagElimHom`; the
coordinate values (`lagElimHom_X_xiIdx`, `_vIdx`, `_accIdx`, `_qIdx`, `_fIdx`, `_vgIdx`, `_sIdx`,
`_yIdx`) name what each Lagrangian coordinate becomes. Two index lemmas — `lagElimCoord_fIdx` and
`lagElimCoord_vgIdx` — are the bookkeeping that the earlier state of this chapter left open at a
`whnf` heartbeat timeout; they are proved by rewriting the index arithmetic *before* touching the
dependent `Fin` constructors.
:::

```
#check @BookProof.NsLagFourier.lRedIdx
#check @BookProof.NsLagFourier.lagElimCoord_fIdx
#check @BookProof.NsLagFourier.lagElimCoord_vgIdx
#check @BookProof.NsLagFourier.lagElimHom_X_fIdx
#check @BookProof.NsLagFourier.lagElimHom_X_vgIdx
```

:::paragraph
The degenerate part is the **rank-one** structure of the eliminated kinematics. The cofactor matrix
of the eliminated deformation gradient vanishes identically (`rankOne_cof_zero`), and with it the Piola
coupling that would carry the deformation-gradient square:

 * `lagElimSubst_cofPoly` — the cofactor polynomial is the constant `0`;
 * `lagElimSubst_piola` — the Piola stress that multiplies it is annihilated;
 * `lagElimSubst_detPoly` — hence $`\det F = 0`;
 * `lagElimSubst_volumePoly` and `lagElimSubst_volumePoly_sq` — so the volume constraint
   $`\det F = 1` collapses to the constant $`-1`, whose square is `1`: it carries no field content
   and cannot couple to the field;
 * `lagElimSubst_lagResPoly` — the surviving form is the momentum equation, a *quadratic* symbol in
   the reduced velocities rather than a cubic one in the deformation gradient.

This is the Lagrangian face of the same claim the Eulerian chapter makes: after the elimination the
only squares that carry field content are the momentum/viscous and advection forms — for both real
parts of each substituted form — and any deformation-gradient square is vacuous rather than merely
absent.  The consequence for the plan is a *removal* obligation, not a proof obligation: no
invariance under the deformation gradient, and no determinant identity inside the Hamiltonian, has to
be established, because the determinant is constant there.
:::

```
#check @BookProof.NsLagFourier.rankOne_cof_zero
#check @BookProof.NsLagFourier.lagElimSubst_cofPoly
#check @BookProof.NsLagFourier.lagElimSubst_piola
#check @BookProof.NsLagFourier.lagElimSubst_detPoly
#check @BookProof.NsLagFourier.lagElimSubst_volumePoly
#check @BookProof.NsLagFourier.lagElimSubst_volumePoly_sq
#check @BookProof.NsLagFourier.lagElimSubst_lagResPoly
```

# Where the Two New Operator Chapters Sit

The elimination above produces the *reduced* forms; the operator questions they raise are answered in
two chapters of this book:

 * {ref "ns-one-particle-hamiltonian"}[the Navier–Stokes one-particle Hamiltonian and its Fock
   enclosure] takes the reduced one-parcel family, exhibits the one-body generator
   $`H_{\rm sp} = H_{\rm visc} + H_{\rm advect}` as its single-parcel member, proves the two
   Faris–Lavine inequalities for the exact nonlinearity, and identifies the outer Hamiltonian as its
   second quantization $`d\Gamma(H_{\rm sp})` — creation on the left, annihilation on the right;
 * {ref "qg-elimination"}[eliminating the derivative variables in quantum gravity] does the same
   service for the vielbein sector of the $`R^2` model, where the elimination removes twenty-seven
derivative components per momentum and still reproduces the vielbein self-interaction and the
   scalaron coupling verbatim.

# Summary

The Fourier-elimination route, as verified here:

 * the derivative coordinates are *eliminated* by a ring homomorphism (`nsElimHom`) that sends $`u_{i,j}` to $`i k_j u_i`, $`w_i` to $`-|k|^2 u_i` and $`y_j` to $`0`, cutting each parcel from twenty-one coordinates to six;
 * the residual and the incompressibility are pushed through it, `nsElimSubst_resPoly` and `nsElimSubst_divPoly`, becoming a *quadratic* symbol $`i (k \cdot u) u_i + q_i + \nu |k|^2 u_i` and a *linear* one $`i (k \cdot u)` — the cubic symbol of the gauge-fixed presentation is gone, so no ghost sector is needed for the definition;
 * the reduced Hamiltonian on $`L^2(\mathbb{R}^{6n})` is built with the same Weyl-ordered sum of squares (`redHam`), squaring *both* real-coefficient parts of each substituted form (the *definition* is the one-particle case $`n = 1`; `redHam` at general $`n` is that one-particle operator summed over the parcels, and the Fock operator `nsRedFullFockHam` is its particle-number-conserving lift $`d\Gamma(H_1)` — no further square is taken) — so the real pressure–viscous symbol $`q_i + \nu|k|^2 u_i` *and* the advection $`(k\cdot u)u_i` both sit inside squares, and the Hamiltonian keeps the Navier–Stokes nonlinearity in full; it is symmetric and bounded below (`redHam_symmetricOn`, `redHam_quadForm_nonneg`) and therefore has an unconditional positive self-adjoint Friedrichs extension;
 * the comparison operator of the Faris–Lavine criterion is free, and the convenient choice is this same lifted Friedrichs realization, on which the reduced Hamiltonian is essentially self-adjoint with `c = 0` (`nsRedFullOuterN_esa`, `nsRedFullOuterN_isPositiveSelfAdjointExtension`) — the advection is inside it rather than measured against it by a commutator estimate;
 * the reduced field family `redFieldN` is the honest one: `redFormPoly` collects, for each parcel, the real and imaginary parts of every surviving substituted form — the three real residual parts $`q_i + \nu|k|^2 u_i`, the three advection parts $`(k\cdot u)u_i` and the eliminated incompressibility $`k\cdot u` — and `redFieldN_advect` exhibits the advection as one of the squares of the Hamiltonian.
