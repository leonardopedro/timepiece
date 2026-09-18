import BookProof.ChapterNsKoopman.Part1
import BookProof.ChapterNsKoopman.Part2

/-!
# The mainstream Navier–Stokes Hamiltonian, its indefiniteness, and its Faris–Lavine comparison

This chapter treats the Hamiltonian of the **mainstream** incompressible Navier–Stokes
equations — the Koopman–von Neumann (Liouville) generator of the flow
`u̇ = −νAu + B(u,u)` in the functional form in which the equations are always written, with the
exact quadratic advection and with the two structural identities of incompressibility (Leray's
energy identity and the phase-space Liouville identity).

* `BookProof.ChapterNsKoopman.Part1` — the system, the Hamiltonian `H_NS`, its symmetry on the
  Gauss–polynomial core, the conjugation antisymmetry `C H_NS C = −H_NS`, the exact one-mode
  matrix element, and the headline `nsKoopmanOp_not_bounded_below`: the form of `H_NS` is
  unbounded below.  In particular `H_NS` is not positive, so it cannot be the comparison
  operator `N` of the Faris–Lavine criterion — the `H = N`, `c = 0` shortcut used elsewhere in
  this project applies to the auxiliary positive sum-of-squares operator, never to `H_NS`.
* `BookProof.ChapterNsKoopman.Part2` — the replacement comparison operator: the Leray energy
  `N_E = 1 + ‖u‖²`, the exact commutator `i[H_NS, N_E] = F·∇E = −2ν Σ_i λ_i u_i²`, and the
  Faris–Lavine commutator inequality `|⟪x, i[H_NS,N_E] x⟫| ≤ 2νΛ ⟪x, N_E x⟫` for the exact
  nonlinear Hamiltonian, the advection dropping out by Leray's identity.
-/
