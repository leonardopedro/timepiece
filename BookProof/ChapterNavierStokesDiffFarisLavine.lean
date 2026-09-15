import BookProof.ChapterNavierStokesDiffFarisLavine.Part1
import BookProof.ChapterNavierStokesDiffFarisLavine.Part2

/-!
# The two Faris–Lavine inequalities for the *differential* Navier–Stokes symbol

`BookProof.ChapterNavierStokesHermiteFarisLavine` and
`BookProof.ChapterNavierStokesFockManyMode` prove the two Faris–Lavine inequalities — the
relative bound `‖Hx‖² ≤ a‖Nx‖² + b‖x‖²` and the form-commutator bound
`±i[H, N] ≤ c N` — in the *sequence* (occupation-number) realization, and
`BookProof.ChapterNavierStokesDifferentialL2` proves essential self-adjointness of the
Navier–Stokes quadratic symbol written as an honest differential operator on
`L²(du₁du₂du₃)`, but by transporting the sequence-space theorem along the Hermite basis.
This module supplies the missing layer: the two Faris–Lavine inequalities **for the
differential operator itself**, against a differential comparison operator, and the
resulting Faris–Lavine proof of essential self-adjointness in `L²(ℝ³)`.

## The two operators

On the Gauss–polynomial (Hermite) core `polyGaussCore` of `L²(ℝ³)`, with `πᵢ = −i ∂/∂uᵢ`
(`momOp`) and `uᵢ` multiplication by the coordinate (`posOp`):

* the Hamiltonian is the Weyl quantization `nsDiffH A c = ∑ᵢ ½(πᵢVᵢ + Vᵢπᵢ)` of the
  Navier–Stokes quadratic symbol `A_i(u) = u_j u_{i,j} − ν u_{i,jj}`, `Vᵢ = ∑ₖA_{iₖ}uₖ + cᵢ`
  (`BookProof.ChapterNavierStokesDifferentialL2`);
* the comparison operator is the *differential* harmonic-oscillator operator
  `nsDiffN μ = 2μ ∑ᵢ (πᵢ² + uᵢ²/4) + 1`, whose one-mode blocks are the honest
  second-order operators `−∂²/∂uᵢ² + uᵢ²/4`.

`oscOp_eq_number` is the algebraic heart of the identification: on the Gauss–polynomial
core, `πᵢ² + uᵢ²/4 = aᵢ†aᵢ + ½`, proved as a polynomial identity (`oscPoly_eq`) from the
Leibniz rule `∂ᵢ(uᵢp) = p + uᵢ∂ᵢp`.  Hence `nsDiffN μ` is the transport of multiplication
by the comparison symbol `velSym μ β = μ(2|β| + 3) + 1` (`intertwined_nsDiffN`,
`velNcore_eq_diagMax`), and `embedCore_surjective` says the Gauss–polynomial core *is* the
transported finite-mode core, so every statement about core states is a statement about
all of `polyGaussCore`.

## What is proved

* `nsDiffN_symmetricOn`, `nsDiffN_quadForm_ge_norm_sq` — the differential comparison
  operator is symmetric and dominates the identity (`⟪f, Nf⟫ ≥ ‖f‖²`);
* `nsDiffH_relative_bound` — **the first Faris–Lavine inequality** for the differential
  operator: `‖H f‖² ≤ a‖N f‖² + b‖f‖²` on the Hermite core, for every real velocity
  gradient `A` and constant part `c`;
* `nsDiffH_commForm_bound` — **the second Faris–Lavine inequality**:
  `|⟪f, i[H, N] f⟫| ≤ c ⟪f, N f⟫`;
* `diffMaxDom`, `diffMaxH`, `diffMaxN` — the same pair on the maximal domain of the
  comparison operator in `L²(ℝ³)`, with the Faris–Lavine package there
  (`diffMaxH_symmetricOn`, `diffMaxN_quadForm_nonneg`, `diffMaxN_add_one_surjective`,
  `diffMaxN_core_approx`, `diffMaxH_relative_bound`, `diffMaxH_commForm_bound`) and
  `diffMaxH_restrict`, which identifies its restriction to the Hermite core with
  `nsDiffH`;
* `nsDiffH_esa_of_farisLavine` — **the payoff**: essential self-adjointness of the
  differentially written Navier–Stokes symbol on the Hermite core of `L²(du₁du₂du₃)`,
  obtained from the Faris–Lavine criterion of `BookProof.ChapterFarisLavine` applied in
  `L²(ℝ³)` itself — the alternative route to
  `BookProof.ChapterNavierStokesDifferentialL2.nsDiffH_essentiallySelfAdjointOn_core`,
  which transported essential self-adjointness instead of the estimates.

## Honest boundary

The estimates are the transported sequence-space ones: the mathematics unifying the two
pictures is the identification `πᵢ² + uᵢ²/4 = aᵢ†aᵢ + ½` and the fact that the
Gauss–polynomial core is the transported finite-mode core, not a new analytic input.  The
non-vacuity of the mechanism (a genuinely non-zero commutator `[H, N]`, and an unbounded
`H`) is recorded in `BookProof.ChapterNavierStokesHermiteFarisLavine.commForm_ne_zero_of_pos`,
`BookProof.ChapterNavierStokesFockManyMode.fock_commForm_ne_zero` and
`BookProof.ChapterNavierStokesDifferentialL2.nsDiffH_not_bounded`.  As everywhere on this
route, nothing here claims global regularity of the classical Navier–Stokes equation
(Contention D5): the statement is about the Hilbert-space operator at one Eulerian fiber,
where the derivative fields `u_{i,j}`, `u_{i,jj}` are independent canonical coordinates.
-/
