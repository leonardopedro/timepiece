import BookProof.ChapterNavierStokesFullEsa.Part1
import BookProof.ChapterNavierStokesFullEsa.Part2

/-!
# The **full** (untruncated) Navier–Stokes Hamiltonian and its essential
self-adjointness

`BookProof.ChapterNavierStokesFlow` builds the Navier–Stokes Hamiltonian
`H = ∑_i (π_i A_i + A_i π_i)`, `A_i = ∑_j u_j u_{i,j} − ν u_{i,jj}`, for a
**finite truncation**: the fifteen field modes and the three momenta are
matrices on a finite-dimensional state space.  This module removes the
truncation: the modes and momenta are now (possibly unbounded) operators on a
dense domain `D` of an arbitrary complex inner-product space, and `H` is the
same polynomial expression in them.

## What is proved here

* `NSFullData` — the untruncated data: a dense domain `D`, fifteen symmetric,
  pairwise commuting field modes and three symmetric momenta, all of them
  mapping `D` into `D`, and a viscosity `ν`.  Nothing is finite-dimensional and
  nothing is bounded.
* `NSFullData.hamiltonian_isSymmetricDom` — **the full Hamiltonian is symmetric
  on its domain**, unconditionally.
* `NSFullData.hasZeroDeficiencyOn_of_completeUnitaryFlow` — **essential
  self-adjointness of the full Hamiltonian from a complete unitary flow**
  (Nelson's route), and `NSFullData.hasZeroDeficiencyOn_of_total_eigenvectors`,
  the eigenvector route.
* `NSFullData.hasZeroDeficiencyOn_of_boundedRealization` — if the full
  Hamiltonian is the restriction of a bounded symmetric operator, it is
  essentially self-adjoint on `D`.
* **A genuinely infinite-dimensional, untruncated instance**: on `ℓ²(ℤ)`, with
  all fifteen modes realized as multiplication by bounded real velocity fields
  and the momenta as the lattice (symmetric-difference) momentum, the full
  Navier–Stokes Hamiltonian is essentially self-adjoint on the **proper** dense
  domain of finitely supported modes: `latticeFull_hasZeroDeficiencyOn`.  The
  operator is not the zero operator (`latticeFullHamiltonianCLM_ne_zero`).
* **An unbounded instance**: on `ℓ²(ℕ)`, with all modes and momenta diagonal
  with (possibly unbounded) real symbols, the full Hamiltonian is essentially
  self-adjoint on the finite-mode domain (`diagFull_hasZeroDeficiencyOn`), and
  for a suitable choice of data it is genuinely unbounded
  (`diagFull_not_bounded`).  So essential self-adjointness of the *full*
  Hamiltonian is not a boundedness phenomenon.
* **Sharpness.** `exists_nsFullData_not_hasZeroDeficiencyOn`: there is
  untruncated Navier–Stokes data on `ℓ²(ℕ)` — dense domain, symmetric pairwise
  commuting modes, symmetric momenta, positive viscosity — whose full
  Hamiltonian is **not** essentially self-adjoint.  Hence the structural
  hypotheses alone (Hermitian modes and momenta, degree ≤ 3) can never yield
  essential self-adjointness of the full operator: an analytic input such as
  completeness of the flow is indispensable.  This is the formal counterpart of
  the `ẋ = x²` warning of the ODE chapter.

## Scope

Essential self-adjointness of the *continuum* Navier–Stokes generator, and with
it global existence for Navier–Stokes, is **not** claimed: the positive results
above are unconditional for the realizations described (bounded lattice modes,
diagonal modes), and conditional — on a complete unitary flow, resp. a total
family of eigenvectors — in general, which by
`exists_nsFullData_not_hasZeroDeficiencyOn` is the best possible shape for a
statement about the abstract data.
-/
