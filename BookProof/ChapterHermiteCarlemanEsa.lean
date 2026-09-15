import BookProof.ChapterHermiteCarlemanEsa.Part1
import BookProof.ChapterHermiteCarlemanEsa.Part2

/-!
# A Carleman criterion on the product Hermite basis, and the full diagonal quadratic
family with an arbitrary first-order term

`BookProof.ChapterHermiteRelativeBound` proves that the inhomogeneous quadratic
Hamiltonian

`H = ∑ᵢ cᵢ(πᵢ² + xᵢ²/4) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`

is essentially self-adjoint on the Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`
when the quadratic part is **elliptic** (`cᵢ ≥ c₀ > 0`), by a relative bound; the
shifted-core modules (`ChapterShiftedQuadraticEsa`,
`ChapterShiftedQuadraticMatrixEsa`, `ChapterShiftedQuadraticDegenerate`) remove the sign
and the invertibility conditions by completing the square, but need a *classical
equilibrium* — which does not exist in a direction where the quadratic part vanishes and
both `bᵢ` and `b'ᵢ` are present — and they pay for it by moving to a translated,
modulated core.  `ChapterQuadratureEsa` settles the opposite extreme, `c = 0`, on the
plain core.

This module removes **all** of those restrictions at once, by a different route: a
*Carleman-type criterion* for the coefficient recursion on the multi-index lattice.

## What is proved

* `LadderRec`, `ladder_eq_zero` — **the instrument.**  Let `u : (Fin d →₀ ℕ) → ℂ` be a
  square-summable family (only Bessel's inequality `∑_{a ∈ F} ‖u a‖² ≤ B` on finite sets
  is used) satisfying, for every multi-index `α`, the nearest-neighbour recursion

  `lam α u_α + ∑ᵢ (conj(wᵢ)√(αᵢ+1) u_{α+eᵢ} + wᵢ√αᵢ u_{α−eᵢ}) = z u_α`

  with a **real** diagonal `lam` and constant amplitudes `w`, at a point `z` off the real
  axis.  Then `u = 0`.  The proof is the classical Wronskian/flux argument of Carleman,
  run on cubes `{α : ∀ i, αᵢ ≤ N}` instead of intervals: the interior contributions are
  pairwise conjugate, so the imaginary part of the recursion telescopes to the flux
  through the boundary faces (`flux_identity`), which is bounded by `√(N+1)` times the
  `ℓ²`-mass carried by those faces (`flux_bound`).  The faces are disjoint, so that mass
  is summable, while `∑ 1/√(N+1) = ∞` — a contradiction unless the mass vanishes.

* `mixOp_hermiteCore` — the ladder form of `H` on the product Hermite basis: the
  quadratic part is diagonal with the real symbol `∑ᵢ cᵢ(αᵢ + ½)`, and the first-order
  part raises the `i`-th excitation number with amplitude `wᵢ = bᵢ + ib'ᵢ/2` and lowers
  it with `conj wᵢ`.

* `mixOp_deficiencyTrivialAt`, `mixOp_essentiallySelfAdjoint` — **the headline.**  For
  **arbitrary** real weights `c` (any signs, zeros allowed) and **arbitrary** real
  coefficients `b, b'`, the operator `H_c + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` is essentially
  self-adjoint on the plain Gauss–polynomial core of `L²(ℝᵈ)`.  No ellipticity, no sign
  condition, no classical equilibrium, and no change of core.

* `mixOp_stone_flow` — the resulting complete unitary Schrödinger flow, by Stone's
  theorem.

* `wave_indefiniteQuadratic_firstOrder_essentiallySelfAdjoint` — the Minkowski corollary:
  `□ + V` with `V(t,x) = (t² − ‖x‖²)/4` plus an arbitrary constant external field and an
  arbitrary constant boost, on the plain core.

Everything is `sorry`-free and `axiom`-free.
-/
