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
elimination is applied *inside the squares* that make up the Hamiltonian, so the
jet coordinates never appear as dynamical variables at all, no ghost sector is
introduced, and the derivative content is carried by the momentum of a spatial
Fourier transform — $`\partial_j \mapsto i k_j` at momentum $`k`. The
substitution is

$`u_{i,j} \mapsto i k_j u_i, \qquad w_i \mapsto -|k|^2 u_i, \qquad y_j \mapsto 0,
\qquad u_i \mapsto u_i, \qquad q_i \mapsto q_i,`

reducing each parcel from twenty-one field-space coordinates to the
*six* physical ones $`(u_i, q_i)`. The algebraic content of the chapter — that
the substitution is a ring map, that the residual and the incompressibility
become *quadratic* and *linear* symbols, and that the reduced Hamiltonian is
again a sum of squares on which the Friedrichs extension and Faris–Lavine run as
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

# The Reduced Hamiltonian, and Which Part Is a Square

:::paragraph
A multiplication operator on $`L^2` with respect to the real coordinates is
symmetric exactly when its symbol has *real* coefficients. The residual splits
as $`\sigma(R_i) = i\,(k \cdot u) u_i + \big(q_i + \nu |k|^2 u_i\big)`: the
first term is purely imaginary, so multiplication by it is *skew-adjoint* and
its square is *negative*, while the second term is real. The reduced Hamiltonian
is therefore built from the real symbol — `fourierVisc` and its lifted form
`redVisc` — and its quadratic form is a sum of Weyl-ordered squares, hence
nonnegative:
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
This is the honest form of the strategy: the *squares* are the real
(pressure–viscous) part, and the skew-adjoint advection — the genuine
nonlinearity — is not smuggled into them but is carried by the momentum
convolution of the plan and bounded against this comparison operator by the
Faris–Lavine commutator estimate. Positivity of the square part is what makes
the Friedrichs extension unconditional, exactly as for the full Eulerian sector.
:::

# The Nested Fock Lift and Faris–Lavine

:::paragraph
The comparison operator the route needs is the lifted Friedrichs realization of
the reduced one-body operators, on the nested Fock space
$`\bigoplus_n L^2(\mathbb{R}^{6n})`. Positivity, symmetry and surjectivity of
$`N + 1` are all fibrewise, so they lift verbatim from the fibre:
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

# Summary

The Fourier-elimination route, as verified here:

 * the derivative coordinates are *eliminated* by a ring homomorphism (`nsElimHom`) that sends $`u_{i,j}` to $`i k_j u_i`, $`w_i` to $`-|k|^2 u_i` and $`y_j` to $`0`, cutting each parcel from twenty-one coordinates to six;
 * the residual and the incompressibility are pushed through it, `nsElimSubst_resPoly` and `nsElimSubst_divPoly`, becoming a *quadratic* symbol $`i (k \cdot u) u_i + q_i + \nu |k|^2 u_i` and a *linear* one $`i (k \cdot u)` — the cubic symbol of the gauge-fixed presentation is gone, so no ghost sector is needed for the definition;
 * the reduced Hamiltonian on $`L^2(\mathbb{R}^{6n})` is built with the same Weyl-ordered sum of squares (`redHam`), with the real pressure–viscous symbol inside the squares and the skew-adjoint advection kept out of them; it is symmetric and bounded below (`redHam_symmetricOn`, `redHam_quadForm_nonneg`) and therefore has an unconditional positive self-adjoint Friedrichs extension;
 * the lift to the nested Fock space preserves all three comparison-operator properties, and the lifted Friedrichs realization is a positive self-adjoint extension of the reduced Hamiltonian on which the latter is essentially self-adjoint (`nsRedFullOuterN_esa`, `nsRedFullOuterN_isPositiveSelfAdjointExtension`);
 * the remaining analytic obligation of the route is external to this chapter: the advection as a momentum convolution, bounded against the reduced comparison operator — the same shape as the full Eulerian sector's commutator estimate, and the reason the elimination was performed in the first place.
