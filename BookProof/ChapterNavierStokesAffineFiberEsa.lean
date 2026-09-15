import BookProof.ChapterNavierStokesAffineFiberEsa.Part1
import BookProof.ChapterNavierStokesAffineFiberEsa.Part2

/-!
# The **affine** Navier–Stokes fiber field: a `±1`-shift on top of the `±2`-shift

`BookProof.ChapterNavierStokesHermiteFarisLavine` proves the two Faris–Lavine
inequalities, and hence essential self-adjointness on the finite-mode core, for
the Navier–Stokes fiber Hamiltonian `H = ½(π V + V π)` with a **linear**
advection field `V(u) = κ u`.  `BookProof.ChapterNavierStokesBilinearEsa` lifts
that to the genuinely bilinear (quadratic-symbol) advection term by decomposing
`ℓ²(ℕ × J)` into blocks, one for each eigenvalue `κ_j` of the derivative field.

The boundary recorded there was the **affine** fiber field

`V(u) = κ u + c`,

which is what the viscous term `−ν u_{i,jj}` and the cross terms `u_j u_{i,j}`
with `j ≠ i` produce: they contribute a term that is *constant* in the velocity
mode `u_i` being differentiated.  In the Hermite basis of the fiber,
`½(π V + V π) = κ · ½(π u + u π) + c · π`, and while `½(π u + u π) =
(i/2)(a†² − a²)` is a `±2`-shift (the operator of `ChapterNavierStokes‐
HermiteFarisLavine`), the extra term `c · π = (i c/√2)(a† − a)` is a **`±1`
shift**.  This module removes that boundary.

## The instrument: sums of shift Hamiltonians

The Faris–Lavine hypotheses used in this project
(`BookProof.FarisLavine.essentiallySelfAdjointOn_core_of_farisLavine`) are

* `H` symmetric, `N ≥ 0` with `N + 1` surjective,
* a **relative bound** `‖Hx‖² ≤ a‖Nx‖² + b‖x‖²` — with *no* smallness
  requirement on `a`, and
* a **commutator bound** `|⟪x, i[H, N]x⟫| ≤ c ⟪x, Nx⟫`.

All three are stable under sums: `‖(H₁+H₂)x‖² ≤ 2‖H₁x‖² + 2‖H₂x‖²` and the
commutator form is additive in `H`.  So two shift Hamiltonians sharing one
comparison operator may simply be added.  That is the content of `PairShift`
below: a single symbol `σ` carrying two shifts at once.

## What is proved

* `PairShift.pairH` — the sum of two shift Hamiltonians with a common comparison
  symbol, on the maximal domain of that symbol;
* `PairShift.pairH_symmetricOn`, `PairShift.pairH_relative_bound`,
  `PairShift.pairH_commForm_bound` — the two Faris–Lavine inequalities for the
  sum, with explicit constants;
* `PairShift.pairH_essentiallySelfAdjointOn_core` — the sum is essentially
  self-adjoint on the finite-mode core;
* `affH` — the affine Navier–Stokes fiber Hamiltonian `½(π V + V π)` for
  `V(u) = κ u + c`, in the Hermite basis of `ℓ²(ℕ)`;
* `affH_symmetricOn`, `affH_essentiallySelfAdjointOn_core` — **the headline**:
  the affine fiber Hamiltonian is symmetric and essentially self-adjoint on the
  finite-mode core, for all `κ ≥ 0` and `c ≥ 0`;
* `affH_coord_succ` and `affH_coord_succ_succ` — the two matrix entries of `H`
  on a Hermite basis vector: the `±1`-hopping `(c/√2)√(n+1)` of the constant
  part and the `±2`-hopping `(κ/2)√((n+1)(n+2))` of the linear part;
* `affH_ne_zero_of_pos_shear` and `affH_not_bounded` — the `±1`-hopping really
  is present when `c > 0`, and the operator is genuinely unbounded when
  `κ > 0`.

## Honest boundary

`c ≥ 0` is assumed, only because a `ShiftData` amplitude is required to be
non-negative; the case `c < 0` is the conjugate of the case `|c|` by the
sign-flip unitary `x_n ↦ (−1)ⁿ x_n`, which reverses the sign of a `±1`-hopping
and preserves a `±2`-hopping — that unitary equivalence is *not* formalized
here, so nothing below is claimed for `c < 0`.  The comparison operator used is
`N = μ(2n+1) + 1` with `μ = κ + c + 1`, i.e. the harmonic-oscillator number
operator rescaled so as to dominate both amplitudes.  As in the modules quoted
above, everything is stated on the abstract sequence space `ℓ²(ℕ)` with the
operator given by its matrix in the Hermite basis; the differential realization
on `L²(du)` is not built here.  Only one velocity component is carried, and
nothing here claims global regularity for the classical Navier–Stokes equation.
-/
