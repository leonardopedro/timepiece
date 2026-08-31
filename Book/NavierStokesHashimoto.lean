import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Shift-Invert Selection for the Navier–Stokes Generator" =>
%%%
tag := "navier-stokes-hashimoto"
%%%

# Why a Selection Theorem

:::paragraph
The inverse-free rational-Krylov (Hashimoto/SIRK) method never forms the
resolvent $`(H - z)^{-1}`: it works with the *forward* sequence
$`w_k = (H - z_k I) w_{k-1}` and reconstructs spectral information from the Gram
matrix of the Krylov subspace. The method is trustworthy exactly when the
shift-inverted resolvents $`X_j = (\\gamma_j - G)^{-1}` of the generator $`G` are
well-behaved — bounded, commuting, satisfying the resolvent identity and the
Hashimoto–Nodera SIRK relation, and recovered by Galerkin truncation. Proving
those properties for a *concrete* Hamiltonian is a selection theorem: it selects
the operator the Krylov iteration is actually computing.
:::

:::paragraph
For the Navier–Stokes fiber generator the selection was proved in the abstract
sequence-space realization: the Hermite matrix `velCore` on $`\\ell^2(Vel)` with
$`Vel = \\operatorname{Fin} 3 \\to \\mathbb N`$. The *differential* realization —
the same Hamiltonian written with $`\\pi_i = -i\\,\\partial/\\partial u_i` and $`u_i`
a genuine multiplication operator on the Gauss–polynomial (product Hermite) core
of $`L^2(du_1 du_2 du_3)` — was known to be essentially self-adjoint but carried
no selection theorem. The module `BookProof/ChapterNavierStokesDiffHashimoto.lean`
supplies it (namespace `BookProof.NavierStokesFlow`).
:::

# What the Forward Sequence Is Doing, Intuitively

:::paragraph
Before the formal statements, it helps to see why the resolvents
$`X_j = (\\gamma_j - G)^{-1}` are the right object at all. The SIRK method shifts
by a complex number $`\\gamma_j` — *not* an eigenvalue — purely to make the
inversion well-behaved: $`\\gamma_j - G` is invertible because $`\\gamma_j` has a
non-zero imaginary part, so no point of the (real) spectrum can coincide with the
shift. The inverse then exists as a bounded operator, and the forward sequence
$`w_k = (H - z_k I) w_{k-1}` accumulates information about it. If the resolvents
were *not* bounded, or did *not* commute, or were *not* recovered by Galerkin
truncation, then the Krylov subspace would silently compute something else — a
different operator, or an artifact of the finite-dimensional cut. The selection
theorem rules all of that out for the Navier–Stokes generator.
:::

:::paragraph
A concrete miniature makes the mechanism visible. Take a single velocity mode
with the fiber Hamiltonian
$`G = \\tfrac12(\\pi V + V\\pi)` where $`V = \\kappa u + c` (an affine drift), and
shift by $`\\gamma = i` (imaginary part $`1`). The resolvent bound in the theorem
says $`\\|(i - G)^{-1}\\| \\le 1/|\\operatorname{Im} i| = 1`: the inverted operator
shrinks every vector, which is precisely what makes the Krylov recurrence stable
and the Gram matrix well-conditioned. The same bound holds for *every* non-real
shift, uniformly, and it is exactly the estimate that the SIRK implementations in
the companion numerical validation (`fock_sirk/tests/ns_numerical_validation.rs`,
S35) rely on when they evolve the laminar decay $`du/dt = -\\nu k^2 u` and measure
the decay rate $`\\nu k^2` to high precision.
:::

# The Differential Generator is the Transport of a Polynomial

:::paragraph
The Weyl-ordered Hamiltonian — the sum of the symmetrized products
$`\\tfrac12(\\pi_i V_i + V_i \\pi_i)` of the momentum with the affine fiber field —
is, on the Hermite core, the transport of a polynomial-level operator: `nsDiffPoly`
is the polynomial whose core realization is exactly `nsDiffH`. Gauss symmetry of
the polynomial is what makes the operator symmetric on the Hermite core of
$`L^2(\\mathbb R^3)`.
:::

```
#check @BookProof.NavierStokesFlow.nsDiffPoly
#check @BookProof.NavierStokesFlow.nsDiffH_eq_coreOp
#check @BookProof.NavierStokesFlow.nsDiffPoly_polySym
#check @BookProof.NavierStokesFlow.nsDiffH_symmetricOn
```

:::paragraph
The route through the polynomial is not a detour: it is how the symmetry is
*seen*. On the Hermite core the momentum is $`\\pi_i = -i\\partial_i` and the field
is multiplication by the *affine-linear* polynomial
$`V_i(u) = \\sum_k A_{ik} u_k + c_i` — a general velocity-gradient matrix $`A`
(the strain and vorticity content of $`u_{i,j}`) plus the constant term $`c_i`.
The
symmetrized product is then the *symmetrization of a polynomial operator* — the
statement `nsDiffPoly_polySym` — and Gauss symmetry of that polynomial is
checked purely algebraically, with no analysis. All the analytic work (domains,
deficiency spaces, closures) is then done once, on the polynomial transport.
:::

# A Unique Self-Adjoint Extension

:::paragraph
Symmetry alone is not enough: a symmetric operator may have many self-adjoint
extensions. Here there is exactly one — the closure. Note that this is *not* a
positivity argument: the strain, vorticity and constant hoppings carry arbitrary
signs, so the Hamiltonian is genuinely indefinite; the uniqueness comes from the
analysis of the deficiency spaces on the core.
:::

```
#check @BookProof.NavierStokesFlow.nsDiffH_selfAdjoint_extension
#check @BookProof.NavierStokesFlow.nsDiffH_selfAdjoint_extension_unique
```

:::paragraph
Why uniqueness matters for the numerics: a symmetric operator with several
self-adjoint extensions is a Hamiltonian with several *different* time evolutions
— the Stone theorem would not know which unitary group to use. The SIRK solver
can only compute one of them, so a multiplicity of extensions would mean the
numerical flow is computing an arbitrary choice. The theorem that the closure is
the *unique* self-adjoint extension removes the ambiguity: there is only one
candidate, and the Krylov iteration, if it converges at all, converges to it.
:::

# The Hashimoto Selection

:::paragraph
The headline: for an arbitrary sequence of non-real shifts $`\\gamma_j`, the
shift-inverted resolvents $`X_j = (\\gamma_j - G)^{-1}` of the differential
Navier–Stokes generator exist, are bounded by $`1/|\\operatorname{Im} \\gamma_j|`,
share the domain of $`G`, satisfy the resolvent identity, commute, satisfy the
Hashimoto–Nodera SIRK relation, have strongly convergent Galerkin truncations,
and each one alone determines $`G` completely. The single-shift form is the
version used in practice, and the explicit coefficients $`(\\nu, u_{i,j}, u_{i,jj})`
spell the same statement out in the physical variables.
:::

```
#check @BookProof.NavierStokesFlow.nsDiffH_hashimoto_selects
#check @BookProof.NavierStokesFlow.nsDiffH_shiftInvert_selects
#check @BookProof.NavierStokesFlow.nsQuadraticDiffH_hashimoto_selects
#check @BookProof.NavierStokesFlow.exists_l2dHilbertBasisNat
```

:::paragraph
Reading the single-shift statement `nsDiffH_shiftInvert_selects`: fix one shift
$`\\gamma` with $`\\operatorname{Im}\\gamma \\neq 0`. The theorem says the single
resolvent $`X = (\\gamma - G)^{-1}` *determines* $`G` — because the resolvent
identity lets you recover the spectrum and the spectral projections from one
resolvent value. In practice this means the SIRK method needs only the forward
sequence at the chosen shifts; it does not need to *approximate* the resolvent by
anything else. And `nsQuadraticDiffH_hashimoto_selects` gives the same guarantee
in the notation a fluid dynamicist writes down: the viscosity $`\\nu`, the
velocity-gradient matrix $`u_{i,j}` and the second derivatives $`u_{i,jj}` appear
explicitly in the statement.
:::

:::paragraph
Non-vacuity is part of the statement: $`L^2(\\mathbb R^3)` carries an
$`\\mathbb N`-indexed Hilbert basis — the product Hermite functions, enumerated —
so the Galerkin truncations in the theorem are honest finite-dimensional
projections of a concrete Hilbert space. Together with the Carleman flux criteria
(`Book/CarlemanFlux.lean`) that underpin the core analysis, this is what makes the
inverse-free SIRK numerics of the Navier–Stokes validation a computation of *this*
operator rather than of an artefact of the discretization.
:::

# How This Connects to the Numerical Validation

:::paragraph
The selection theorem is the *raison d'être* of the SIRK tests in the companion
repository. Two features of those tests are direct consequences of what is proved
here:

* *The Ehrenfest identity is exact on probes.* The test
  `ns_sirk_laminar_decay_rate` verifies
  $`i\\langle[H, u]\\rangle = 4\\kappa\\langle u\\rangle + 4c` exactly on
  occupation/coherent probes. This is a statement about the *operator* $`H` — the
  one the selection theorem pins down — not about any finite-dimensional
  truncation. The identity holds because the Weyl-ordered symmetrization
  $`\\{V, \\pi\\}` carries the factor two, which is precisely the polynomial
  transport `nsDiffH_eq_coreOp` records.
* The decay rate $`\nu k^2` is reproduced to < 1e-2 (with the viscosity in the analytic window). With
  $`\\kappa = -\\nu k^2/4`, the Ehrenfest identity reduces to the classical
  Navier–Stokes decay $`du/dt = -\\nu k^2 u`, and the SIRK-restarted evolution
  measures it. That the measured rate agrees with the analytic one is the
  numerical shadow of `nsDiffH_hashimoto_selects`: the Krylov iteration is
  computing the resolvent of *the* differential generator, whose spectrum
  contains exactly the expected decay rates.
:::

:::paragraph
The companion tests `ns_derivative_variable_fixing.rs` (and the higher-Hermite
extension) verify the promoted derivative variables $`g_m = 2(m+1)u_{m+1}`$
against the field derivatives, and check that the bare and BRST-projected SIRK
flows give identical observables. These are statements *about the physical
subspace* of the same operator — the one selected here. The selection theorem is
what guarantees that the whole edifice (Ehrenfest identities, gauge-fixed
derivative variables, energy conservation) is a computation about the
Navier–Stokes generator in $`L^2` rather than about some discretization artifact.
:::

# What the Eulerian Fiber Can Certify: the Absence of a Form Gap, and the Comparison Operator

:::paragraph
The shift-invert selection theorems above identify *which operator* the Krylov
iteration computes. A separate question — the one the gap programme asks of
every sector — is whether that operator has a positive spectral gap above its
ground state. For the Navier–Stokes Eulerian fiber the answer is *negative and
provable*: `BookProof/ChapterNavierStokesFiberGap.lean` (namespace
`BookProof.NavierStokesFlow`) shows that the fiber Hamiltonian has *no
one-particle form gap at any positive level*, and explains why none of the gap
instruments that other sectors enjoy applies here.
:::

```
#check @BookProof.NavierStokesFlow.nsFiber_quadForm_coreState
#check @BookProof.NavierStokesFlow.nsFiber_no_form_gap
#check @BookProof.NavierStokesFlow.nsComparison_friedrichs_gap
```

:::paragraph
The mechanism is elementary and structural. The Eulerian fiber Hamiltonian on
the Hermite core is a sum of symmetrized products of the ladder pairs — the
velocity creation and annihilation operators — and its quadratic form vanishes
on *every* Hermite basis state (`nsFiber_quadForm_coreState`, via the ladder
normal form and the vanishing of the diagonal coefficients
$`c_{\mathrm{Fun}}(A,i,i) = c_{\mathrm{Rot}}(A,i,i) = 0`). A form that vanishes
on the basis vectors of a dense core cannot bound any positive multiple of the
norm from below: `nsFiber_no_form_gap` rules out
$`\mu\|x\|^2 \le \langle x, H_{\rm fiber} x\rangle` for every $`\mu > 0`.
Physically this is the expected structure — the strain and vorticity hoppings
are off-diagonal and sign-indefinite, so there is no confining potential in the
fiber variables to push the Rayleigh quotient away from zero.
:::

:::paragraph
Consequences: the *constant* and *diagonal* gap chains
(`ChapterScalaronFockGapChain`, `ChapterFockDiagonalGapChain` — the instruments
that make the scalaron and free massive sectors unconditional) do *not* apply
to this fiber. What the fiber *can* certify is a weaker but still
self-adjointness-relevant statement: `nsComparison_friedrichs_gap` shows that
the Faris–Lavine comparison operator $`N_\mu` has a positive self-adjoint
(Friedrichs) extension — the one the Hashimoto shift-invert selects at
$`\gamma = 1` — with the bound $`\langle y, N y\rangle \ge \|y\|^2` on its
whole domain. That is exactly the regularity the SIRK implementation needs to
run at all: the comparison operator is well defined, positive, and
self-adjoint even though the fiber itself carries no spectral gap. The honest
summary: the Eulerian fiber certifies *positivity and self-adjointness of the
comparison problem*, and certifies the *absence* of a one-particle form gap —
neither a mass gap nor a continuum-gap claim is made for this sector.
:::
