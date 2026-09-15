import BookProof.ChapterNavierStokesFockParcels.Part1
import BookProof.ChapterNavierStokesFockParcels.Part2

/-!
# The continuum Fock space over a parcel domain

`BookProof.ChapterNavierStokesFockLagrangian` proves that the untruncated
transformed Navier–Stokes Hamiltonian is essentially self-adjoint in the
Lagrangian momentum representation, for arbitrary measurable symbols
(`LagSymbols.hFull_hasZeroDeficiencyOn`).  This module supplies the
second-quantized realization of that theorem.

* `ParcelConf`, `fockMeasure`, `fockMeasure_sector` — the measure space of *all*
  finite parcel configurations: the continuum Fock space `⨁ₙ L²(Ωⁿ)` realized as
  a single `L²` space, with the `n`-parcel sector carrying the `n`-fold product
  measure.
* `secondQuant` — the second quantization `dΓ(s)(ξ) = ∑ₖ s(ξₖ)` of a one-parcel
  symbol.
* `fockLagSymbols`, `fockLagrangian_hasZeroDeficiencyOn` — **the transformed
  Navier–Stokes Hamiltonian, second-quantized on the whole continuum Fock space
  (all parcel-number sectors at once), is essentially self-adjoint** on a dense
  domain; the one-parcel symbols are arbitrary measurable real functions.
* `momFock`, `momFock_not_bounded`, `momFock_hasZeroDeficiencyOn` — the physical
  choice of symbols, where the advective term is the total kinetic energy: the
  resulting operator is genuinely unbounded, and essentially self-adjoint all the
  same.
* `momFock_core_ne_top` — the domain is a *proper* dense subspace: the state
  `tailState`, supported on unboundedly large momenta of finite total measure,
  lies in the Fock space but outside the domain.
* `momFock_no_eigenvector`, `momFock_vacuum_eigenvector` — the spectrum is
  purely continuous above the vacuum: no nonzero energy is an eigenvalue, while
  the vacuum is an honest unit eigenvector of energy zero.

## Scope

As in the parent module, nothing here claims global existence for Navier–Stokes,
and nothing is claimed for the Eulerian continuum generator except through the
unitary change of variables of
`BookProof.ChapterNavierStokesLagrangianEsa`.
-/
