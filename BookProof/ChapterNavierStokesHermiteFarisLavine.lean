import BookProof.ChapterNavierStokesHermiteFarisLavine.Part1
import BookProof.ChapterNavierStokesHermiteFarisLavine.Part2

/-!
# The two Faris–Lavine inequalities, verified for the Navier–Stokes generator

Everywhere else on this route the two Faris–Lavine inequalities

* the relative bound `‖H x‖² ≤ a‖N x‖² + b‖x‖²`, and
* the form-commutator bound `± i[H, N] ≤ c N`,

are *hypotheses* on the Hamiltonian.  Here they are **proved**, for a concrete
Hamiltonian in a representation in which the momentum and the fiber coordinate
genuinely do **not** commute — so that the commutator `[H, N]` is genuinely
non-zero (`commForm_ne_zero_of_pos`), and the Faris–Lavine mechanism (the
non-commuting cross terms `π · V` are dominated by the sum of the squares
`π² + V²`) is what makes the argument work.

## The model

On the fiber, the one-particle Navier–Stokes transport operator is the symmetric
first-order operator
`h = ½ (πᵢ Vᵢ + Vᵢ πᵢ)`,
with `πᵢ = -i ∂/∂uᵢ` and with the *linear* advection field `Vᵢ(u) = Mᵢⱼuⱼ + Cᵢ`.
The comparison operator is built, as Faris–Lavine requires, from the squares of
the individual non-commuting pieces:
`N = πᵢπᵢ + Vᵢ(u)Vᵢ(u) + I ≥ I`.

Take one fiber degree of freedom and the linear field `V(u) = κ u` (`κ ≥ 0` the
strain rate).  In the Hermite (harmonic-oscillator) basis `eₙ` of `L²(du)`,
normalised so that
`u = (a + a†)/√(2κ)`, `π = i√(κ/2)(a† - a)` — hence `[π, u] = -i`, `nsComm_pu` —
one has

* `N = π² + V² + I = κ(2n̂ + 1) + I`: **diagonal**, multiplication by the symbol
  `oscSymbol κ n = κ(2n+1) + 1 ≥ 1` (`nsN_core_eq`);
* `H = ½(πV + Vπ) = (iκ/2)(a†² - a²)`: the **±2-shift** operator
  `(Hx)ₘ = i(w(m-2) x(m-2) - w(m) x(m+2))`, `w(n) = (κ/2)√((n+1)(n+2))`
  (`nsH`, `nsH_core_eq`).

`H` is *not* diagonal, and `[H, N] = -2iκ²(a² + a†²) ≠ 0`.

## What is proved

* `nsH_symmetricOn` — `H` is symmetric on the maximal domain of `N`;
* `nsH_relative_bound` — **the first Faris–Lavine inequality**
  `‖Hx‖² ≤ ½‖Nx‖² + 2κ²‖x‖²`;
* `nsH_commForm_bound` — **the second Faris–Lavine inequality**
  `|⟪x, i[H,N]x⟫| ≤ (2κ + 4κ²) ⟪x, Nx⟫`, proved exactly by the mechanism of the
  theorem: the commutator is the cross term `∝ κ² (a² + a†²)`, and
  `2ab ≤ a² + b²` dominates it by `π² + V² + I = N`;
* `commForm_ne_zero_of_pos` — the commutator form is genuinely non-zero, so the
  bound is not vacuous;
* `nsH_essentiallySelfAdjointOn_core` — consequently, by the Faris–Lavine theorem
  of `BookProof.ChapterFarisLavine` together with the Ikebe–Kato input of
  `BookProof.ChapterNavierStokesIkebeKato`, **the Navier–Stokes fiber Hamiltonian
  is essentially self-adjoint on the finite-mode core**, with no hypothesis left.

Nothing here claims global regularity for the Navier–Stokes equation.
-/
