import BookProof.ChapterNsOuterFockFarisLavine.Part1
import BookProof.ChapterNsOuterFockFarisLavine.Part2

/-!
# The gauge-fixed Navier–Stokes Hamiltonian on the outer Fock space, by Faris–Lavine

This module carries out for Navier–Stokes what
`BookProof.ChapterQgOuterFockFullFL` and `BookProof.ChapterQgOuterFockInteractionFL` do for
quantum gravity: it exhibits the gauge-fixed Hamiltonian as a *uniform* kinetic-plus-squares
family on the sectors of an outer Fock space and runs the Faris–Lavine theorem there, with
the **same comparison operator** — the lifted Friedrichs extension `dΓ(N₁)` of the positive
one-particle operator `N₁ = −Δ + ‖x‖²/4`.

## The variables

The parcel (excitation) of the Navier–Stokes thread carries the gauge-fixed field variables
of `BookProof.ChapterNavierStokesGaugeY`, *without* the space coordinate `x_j`, on which the
Hamiltonian symbol does not depend (`genX_nsSymbol`): the three velocity modes `u_i`, the
nine first-derivative modes `u_{i,j}`, the three Laplacian modes `u_{i,jj}` and the three
auxiliary coordinates `y_j` in which the field is expanded, `u_i(y) = u_i + u_{i,j} y_j`.
That is `18` coordinates per parcel (`NsLoc`), so the `n`-parcel sector is `L²(ℝ^{18n})` and
the state space is the outer Fock space `⊕ₙ L²(ℝ^{18n})`.

## The Hamiltonian

For a background advection velocity `bv`, viscosity `nu`, derivative-gauge strengths `lam`,
`mu` and `y`-gauge strength `gg`, the `n`-parcel Hamiltonian is

`H_n = ½ Σ_I π_I² + ½ Σ_r L_r²`

with, for every parcel `p`, the following four families of linear forms `L_r` (`sameVec`
gives their coefficients on the coordinates of `p`, `nextVec` those on the coordinates of
the cyclic neighbour `nextPart p`):

* **the Navier–Stokes constraint** `A_i = Σ_j bv_j u_{i,j} − nu·u_{i,jj}` — the advection
  (with background velocity `bv`) and viscous terms of the Navier–Stokes symbol, imposed as
  a squared constraint exactly as the torsion constraints are in the gravity sector;
* **the derivative gauge-fixing** `lam·(u_{i,j} + u_i − u_i^{next})` — the statement that
  the variable `u_{i,j}`, which represents a *spatial derivative of the field*, is the
  finite difference of the velocity between neighbouring parcels.  This form mixes the
  coordinates of two different parcels, so it is genuinely an **interaction term**;
* **the Laplacian gauge-fixing** `mu·(u_{i,jj} + Σ_j u_{i,j} − Σ_j u_{i,j}^{next})` — the
  same for the second-derivative variables;
* **the `y`-gauge fixing** `gg·y_j` — the gauge condition `y = 0` of the auxiliary
  expansion coordinate, whose generator `G_j = ∂/∂y_j − u_{i,j}∂/∂u_i` annihilates the
  Navier–Stokes symbol.

## What is proved

* `NsLoc`, `locU`, `locD`, `locL`, `locY`, `coordOf`, `parcelOf`, `locOf`,
  `sum_reindex_parcels` — the `18` field coordinates of a parcel and the bookkeeping of the
  `18n` coordinates of a sector;
* `sameVec`, `nextVec`, `nsVec` — the coefficient vectors of the four families of forms,
  with `nsVec_advection`, `nsVec_viscous`, `nsVec_tie_self`, `nsVec_tie_velocity`,
  `nsVec_lap_self`, `nsVec_gaugeY` reading off the individual coefficients, and
  `linForm_nsVec`, `linForm_nsConstraint`, `linForm_nsTie`, `linForm_nsLap`,
  `linForm_nsGaugeY` writing the four families out as polynomials in the field variables;
* `sum_abs_sameVec_row`, `sum_abs_nextVec_row`, `sum_abs_sameVec_col`,
  `sum_abs_nextVec_col`, `nsVec_row_le`, `nsVec_col_le` — the Schur data: every form has
  `ℓ¹` norm at most `7B` and every coordinate is touched by forms of total `ℓ¹` weight at
  most `6B`, where `B` bounds all the coefficients.  **Both bounds are independent of the
  parcel number `n`** — the locality of the gauge-fixing couplings — which is exactly the
  uniformity the `ℓ²`-direct-sum Faris–Lavine theorem needs;
* `nsFamily` — the family, as a `BookProof.SqSumOuterFamily.SqFamily`;
* `nsSectorHam`, `nsOuterHam` — the sector Hamiltonians and the full Hamiltonian on the
  finite-particle core of the outer Fock space, `nsOuterHam_symmetricOn`,
  `nsOuterHam_esa_core`;
* **`nsOuterFock_esa_farisLavine`** — the headline: the full gauge-fixed Navier–Stokes
  Hamiltonian, with its interaction (inter-parcel) terms and all its gauge-fixing terms, is
  essentially self-adjoint on the domain of the lifted Friedrichs extension of `N₁`, and
  the operator so realized extends `nsOuterHam` on the finite-particle core;
* `nsVec_coupling`, `ns_interaction_nontrivial` — the derivative gauge-fixing forms really
  do couple two different parcels, so for `lam ≠ 0` the Hamiltonian is *not* a sum of
  one-parcel operators.

## Honest boundary

*Added 2026‑09‑12:* the **full**, non-linearised Navier–Stokes Hamiltonians — with the exact
advection `u·∇u` in Eulerian variables and the exact Piola pressure term together with the
exact `det F = 1` volume constraint in Lagrangian variables — are carried by
`BookProof/ChapterNavierStokesFullEulerianFock.lean` and
`BookProof/ChapterNavierStokesFullLagrangianFock.lean`.  They are bounded below, so there the
route is the direct Friedrichs extension, lifted fibrewise to the outer Fock space, with the
Faris–Lavine criterion run there with that lift as comparison operator; *essential*
self-adjointness on the finite-parcel core is what this module — the quadratic model — adds,
and it is claimed for the quadratic model only.

The Hamiltonian of *this* module is quadratic: the advection is taken with a **background velocity field
`bv`** (the Oseen linearisation), the nonlinear self-advection `u_j u_{i,j}` — a cubic term
in the canonical variables — is *not* included, and nothing here bears on global regularity
of the classical Navier–Stokes equations.  This is the same class of Hamiltonian as in the
gravity sector, and the restriction is essential: for a genuinely nonlinear transport
symbol the classical flow can leave every ball in finite time and no comparison operator
can help — the `ẋ = x²` warning of the Navier–Stokes thread, formalized in
`BookProof.ChapterNavierStokesFullEsa.exists_nsFullData_not_hasZeroDeficiencyOn`.  The Fock
space is the `ℓ²`-direct sum of the sectors (distinguishable parcels, no symmetrization),
and no spectral information is claimed.

Everything is `sorry`-free and `axiom`-free.
-/
