import BookProof.ChapterNavierStokesCarleman.Part1
import BookProof.ChapterNavierStokesCarleman.Part2

/-!
# Carleman's criterion, and an **unbounded, non-commuting** full Navier–Stokes
Hamiltonian that is essentially self-adjoint

`BookProof.ChapterNavierStokesFullEsa` proves essential self-adjointness of the
full (untruncated) Navier–Stokes Hamiltonian in two infinite-dimensional
realizations: a *bounded* one on `ℓ²(ℤ)`, and an *unbounded but diagonal* one on
`ℓ²(ℕ)`, where the momenta commute with the field modes.  Neither carries the
genuine difficulty of the continuum problem, in which the momentum does **not**
commute with the (possibly unbounded) velocity field.

This module supplies that case.  On the half-line lattice `ℓ²(ℕ)` the momentum
is the symmetric-difference operator `(p f)_n = -(i/2)(f_{n+1} - f_{n-1})`, the
field modes are multiplication by arbitrary real sequences — bounded or not —
and the Weyl-symmetrized Navier–Stokes Hamiltonian
`H = ∑_i (π_i A_i + A_i π_i)` is then a **tridiagonal (Jacobi) operator** whose
off-diagonal couplings are `c_n = -(i/2)(α_n + α_{n+1})`, `α` the total
Navier–Stokes symbol `∑_i (∑_j u_j u_{i,j} − ν u_{i,jj})`.

* `tridiagOp` — the tridiagonal operator with complex couplings `c`, on the
  finite-mode domain of `ℓ²(ℕ)`; `tridiagOp_isSymmetricDom` its symmetry.
* `tridiag_hasZeroDeficiencyOn_of_carleman` — **Carleman's criterion**: if
  `∑ 1/|c_n| = ∞` then the tridiagonal operator is essentially self-adjoint.
  The proof is the classical Wronskian argument: a deficiency vector `w`
  satisfies `c_n w_{n+1} + \bar c_{n-1} w_{n-1} = ± i w_n`, whose Wronskian
  telescopes to `2i ∑_{m ≤ n} |w_m|²`, forcing
  `|w_n| |w_{n+1}| ≥ (∑_{m ≤ n₀} |w_m|²)/|c_n|`; summing contradicts
  `∑ 1/|c_n| = ∞` because `∑ |w_n| |w_{n+1}| ≤ ‖w‖²`.
* `halfLineFullData` — the untruncated Navier–Stokes data on `ℓ²(ℕ)` with the
  symmetric-difference momentum and arbitrary real field modes, and
  `halfLineFullData_hamiltonian`, the identification of its full Hamiltonian
  with a tridiagonal operator.
* `halfLineFull_hasZeroDeficiencyOn` — **the headline**: the full Navier–Stokes
  Hamiltonian of this realization is essentially self-adjoint whenever the
  Navier–Stokes symbol satisfies Carleman's growth condition.
* `linearFull_hasZeroDeficiencyOn` together with `linearFull_not_bounded` — a
  concrete instance: a velocity/viscous field growing **linearly** gives an
  unbounded full Navier–Stokes Hamiltonian, with non-commuting momentum and
  field modes, which is essentially self-adjoint.

*The dichotomy.*  Carleman's condition is a growth restriction: `α_n ∼ n`
diverges (`∑ 1/n = ∞`) and gives essential self-adjointness, while for a field
growing fast enough the sum converges and the criterion is silent — as it must
be, since `BookProof.ChapterNavierStokesDeficiency` exhibits a tridiagonal
operator with geometrically growing couplings that is *not* essentially
self-adjoint, and `BookProof.ChapterNavierStokesFullEsa` realizes it as a full
Navier–Stokes Hamiltonian.  This is the lattice form of the ODE chapter's
`ẋ = x²` warning: quadratic (and faster) growth of the field can destroy
essential self-adjointness, subquadratic growth cannot.
-/
