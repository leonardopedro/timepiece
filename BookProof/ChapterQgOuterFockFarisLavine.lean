import BookProof.ChapterQgOuterFockFarisLavine.Part1
import BookProof.ChapterQgOuterFockFarisLavine.Part2

/-!
# Faris–Lavine on the outer Fock space: the lifted Friedrichs comparison operator

`BookProof.ChapterQgOuterFockEsa` proves that the full gauge-fixed gravity Hamiltonian is
essentially self-adjoint on the finite-particle core of the outer Fock space
`𝔉 = ⊕ₙ L²(ℝ^{84n})`, by the Carleman route sector by sector.  This module builds the
**Faris–Lavine apparatus on the outer Fock space itself**, with the comparison operator
that the strategy calls for: the Friedrichs extension of the positive one-particle
operator `N₁ = −Δ + ‖x‖²/4`, lifted to `𝔉`.

Theorem 1 of Faris–Lavine (`BookProof.ChapterFarisLavine`) needs exactly three things of
its comparison operator `N`: symmetry, positivity, and that `N + 1` maps the domain
**onto** the space — the one consequence of self-adjointness the argument uses.  The point
of this module is that all three survive the two constructions the strategy chains
together:

* **Friedrichs.**  `friedrichsComparison` packages the Friedrichs extension of
  `BookProof.ChapterFriedrichsExtension` as such a comparison operator: the extension is
  built there as `S⁻¹ − 1` for the resolvent `S = (P+1)⁻¹`, so `N + 1` is onto by
  construction.  `Comparison.selfAdjoint` shows conversely that these three properties
  *are* self-adjointness, so `Comparison.isPositiveSelfAdjointExtension` produces the
  project's `IsPositiveSelfAdjointExtension` predicate.
* **Lifting.**  `dsComparison` lifts a family of fibre comparison operators to the
  `ℓ²`-direct sum, on the maximal domain `dsDom`.  Symmetry and positivity are fibrewise
  (`dsCompOp_hasSum_quadForm`), and surjectivity of `N + 1` lifts because the fibre
  solutions obey `‖xᵢ‖ ≤ ‖(Nᵢ+1)xᵢ‖ = ‖fᵢ‖` (`norm_le_norm_shift`), so they are
  automatically square-summable (`dsCompOp_surj`).  This is the precise sense in which
  "the Friedrichs extension of the positive one-particle operator lifts to an operator on
  the outer Fock space".

## What is proved

* `Comparison`, `Comparison.selfAdjoint`, `Comparison.isPositiveSelfAdjointExtension`,
  `Comparison.essentiallySelfAdjointOn`, `Comparison.esa_self` — comparison operators and
  the Faris–Lavine criterion packaged with one; a comparison operator is essentially
  self-adjoint on its own domain (the case `H = N`, `c = 0`).
* `friedrichsComparison`, `friedrichsComparison_extends` — every densely defined positive
  symmetric operator has one, namely its Friedrichs extension.
* `dsDom`, `dsCompOp`, `dsComparison`, `dsCompOp_surj` — the lift to an `ℓ²`-direct sum.
* `dsFibOp`, `dsFibOp_symmetricOn`, `dsFibOp_hasSum_commForm`, `dsFibOp_commForm_le` — a
  fibrewise symmetric operator on the lifted domain, under a relative bound
  `‖Hᵢu‖ ≤ K‖(Nᵢ+1)u‖` uniform in the fibre; **the commutator form of the lift is the sum
  of the fibre commutator forms**, so the Faris–Lavine bound `±i[H,N] ≤ cN` lifts with the
  *same* constant `c`.
* `dsFibOp_essentiallySelfAdjointOn` — **Faris–Lavine on an `ℓ²`-direct sum**: uniform
  fibre data gives essential self-adjointness of the direct-sum operator on the lifted
  domain.
* `harmPosSym`, `harmFried`, `harmFried_isPositiveSelfAdjointExtension` — the positive
  one-particle gravity operator `N₁ = −Δ + ‖x‖²/4` and its Friedrichs extension.
* `qgOuterComparison`, `qgOuterFriedDom`, `qgOuterFriedN`, `qgOuterFriedN_surj`,
  `qgOuterCore_le_friedDom`, `qgOuterFriedN_isPositiveSelfAdjointExtension`,
  `qgOuterFriedN_esa` — **the lifted comparison operator on the outer Fock space**: it is
  a positive self-adjoint extension of the finite-particle-core operator `dΓ(N₁)`
  (`qgOuterN`), `𝑁 + 1` is onto `𝔉`, and it is essentially self-adjoint on its domain.
* `qgOuterFock_esa_farisLavine` — **the Faris–Lavine theorem for the gravity Hamiltonian
  on the outer Fock space**: given sector realizations of the `n`-particle Hamiltonians on
  the domain of the sector comparison operator that are symmetric, relatively bounded by
  `N + 1` and satisfy `±i[H,N] ≤ cN`, all with constants uniform in the particle number,
  the lifted Hamiltonian is essentially self-adjoint on the lifted domain and extends the
  outer Fock Hamiltonian `qgOuterHam` on the finite-particle core.

## Honest boundary

The sector data of `qgOuterFock_esa_farisLavine` are hypotheses, not theorems of this
module: extending the `n`-particle quadratic Hamiltonian from the Gauss–polynomial core to
the *whole* domain of the sector oscillator, with a relative bound and a commutator bound
whose constants do not degrade as the particle number grows, is a separate analytic step
(the Hermite matrix elements of `BookProof.FullQuadratic.fqOp_hermiteCore` are the natural
route to it) and is not carried out here.  What is unconditional here is everything about
the comparison operator — the Friedrichs extension, its lift, and the fact that
Faris–Lavine applies on the outer Fock space once the sector data are supplied, with the
same constant `c` — together with the observation that uniformity in the particle number
is the only thing the lift asks for.  The *unconditional* essential self-adjointness of
the gravity Hamiltonian on the finite-particle core is proved, by the independent Carleman
route, in `BookProof.ChapterQgOuterFockEsa` (`qgOuterFock_esa`).

Everything in this module is `sorry`-free and `axiom`-free.
-/
