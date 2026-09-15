import BookProof.ChapterNavierStokesFockLagrangian.Part1
import BookProof.ChapterNavierStokesFockLagrangian.Part2

/-!
# The transformed Navier–Stokes Hamiltonian in the Lagrangian momentum
representation: essential self-adjointness with continuous spectrum

`BookProof.ChapterNavierStokesLagrangianEsa` sets up the untruncated Lagrangian
data `LagrangianFullData` — the parcel momenta `Pᵢ`, the viscous gradients `Qᵢ`,
the force drift generators `Dᵢ` and the volume-preservation constraint `C` — and
proves that the transformed Hamiltonian

`ĥ_full = ½∑ᵢPᵢ² + ν∑ᵢQᵢ² + ∑ᵢfᵢDᵢ + C`

is symmetric with positive second-order part, essentially self-adjoint whenever
the constituents admit a *total family of common eigenvectors*.

That criterion is a discrete-spectrum criterion: it needs eigenvectors.  The
Lagrangian momentum representation of a *continuum* fluid has none — the
constituents are multiplication operators by the momentum coordinates, whose
spectrum is purely continuous.  This module closes that gap.

## What is proved here

* `DominatedOn` and the multiplication operator `mulD` — multiplication by a
  real measurable symbol `h` on the bounded-energy core of a *scale* function
  `g`, available whenever `h` is bounded on the level sets of `g`, with its
  algebra (`mulD_comp`, `mulD_add`, `mulD_sum`, `mulD_real_smul`).
* `mulD_hasZeroDeficiencyOn` — **multiplication by any symbol dominated by the
  scale is essentially self-adjoint on the bounded-energy core of the scale.**
  This generalizes `FockContinuum.multOp_hasZeroDeficiencyOn`, where symbol and
  scale had to coincide, and it is what allows *all four* constituents of the
  transformed Hamiltonian to live on one common core.
* `LagSymbols` — the Lagrangian momentum representation itself: arbitrary
  measurable real symbols `Pᵢ, Qᵢ, Dᵢ, C` on a measure space of momentum
  configurations, with no boundedness assumption whatsoever, and the common
  core `boundedEnergyCore μ S.scale`.
* `LagSymbols.data` — the resulting `LagrangianFullData`, so everything proved
  about the abstract transformed operator (symmetry, positivity of the advective
  and viscous terms, transfer along the change of variables) applies verbatim.
* `LagSymbols.hFull_eq_mulD` — **the transformed Hamiltonian is multiplication
  by the total Lagrangian symbol** `½∑pᵢ² + ν∑qᵢ² + ∑fᵢdᵢ + c`.
* `LagSymbols.hFull_hasZeroDeficiencyOn` — **the headline: the untruncated
  transformed Navier–Stokes Hamiltonian is essentially self-adjoint in the
  Lagrangian momentum representation**, for arbitrary measurable symbols, with
  in general purely continuous spectrum and no eigenvectors at all.
* `norm_mulD_ge`, `mulD_not_bounded` — the lower bound that makes such an
  operator genuinely unbounded whenever its symbol is.

The second-quantized realization on the continuum Fock space of all
parcel-number sectors — where this criterion is applied to the transformed
Navier–Stokes Hamiltonian itself — is in
`BookProof.ChapterNavierStokesFockParcels`.

## Scope

Nothing here claims global existence for Navier–Stokes, and nothing here claims
essential self-adjointness of the *Eulerian* continuum generator: what is proved
is essential self-adjointness of the transformed operator in the Lagrangian
momentum representation, which by
`NavierStokesFlow.NSFullData.hasZeroDeficiencyOn_of_lagrangian` transports back
along a unitary change of variables only when such a change of variables is
supplied.
-/
