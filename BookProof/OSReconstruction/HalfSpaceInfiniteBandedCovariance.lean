import Mathlib

/-!
# The infinite-volume banded covariance

Plan: `cftproof.md`, **E3**.  The finite-volume chain covariance `chainCov` / `bandCov` is a
banded Toeplitz matrix on a cycle.  Passing to the infinite volume means replacing the cycle by the
bi-infinite line `ℤ`.  This module records that limit as a function on `ℤ × ℤ` and its elementary
properties.  The massive free-field covariance `(−Δ + m²)⁻¹` is dense, so a banded covariance is
only a truncation at any width `k`; the infinite-volume object below is that truncation on `ℤ`.

## Contents

* `bandedCovZ` — the bi-infinite width-`k` banded covariance entry, depending only on the
  distance `|j - i|`;
* `bandedCovZ_banded` — bandedness on `ℤ`: an entry vanishes when `|j - i| > k`.

## Row norm (prose)

Each row has `2k + 1` nonzero entries: one diagonal `1 + ρ² k` and, for `r = 1, …, k`, two entries
`ρ + ρ² (k - r)`.  Hence the squared `ℓ²` norm of a row is
`(1 + ρ² k)^2 + 2 ∑_{r=1}^k (ρ + ρ² (k - r))^2`
`= (1 + ρ² k)^2 + 2 ρ² ( k + ρ k(k-1) + ρ² (k-1) k (2k-1) / 6 )`,
the same per-site factor as `bandCov_hsNormSq`.

## Boundary

* **No Gaussian measure is built.**  Constructing a Gaussian law on `ℤ → ℝ` with a prescribed
  covariance needs Kolmogorov consistency (not available in this Mathlib version here) plus
  positive definiteness of the Toeplitz symbol.  What is recorded is the covariance *kernel*.
* **No Hilbert–Schmidt square root in infinite volume.**  The finite-volume squared HS norm is
  `card ι · ((1 + ρ² k)^2 + 2 ρ² (…))`, which grows linearly with the volume.  The operator
  itself is not compact on `ℓ²(ℤ)`: a banded Toeplitz matrix is not Hilbert–Schmidt.  The natural
  "square root" is the banded operator `1 + ρ ∑_{a=1}^k P^a`, which is bounded but not compact;
  it defines the field as a stochastic process via the usual white-noise construction, not via an
  HS map.  Hence the finite-volume `chainCov_hsNormSq` does not survive as an HS statement in the
  limit.
-/

namespace BookProof.OSReconstruction

noncomputable section

/-- **The bi-infinite width-`k` banded covariance entry.**  Depends only on `|j - i|`: diagonal
`1 + ρ² k`, off-diagonal at distance `r` (`1 ≤ r ≤ k`) is `ρ + ρ² (k - r)`, and `0` beyond
the band. -/
def bandedCovZ (ρ : ℝ) (k : ℕ) (i j : ℤ) : ℝ :=
  let d := Int.natAbs (j - i)
  if d = 0 then 1 + ρ ^ 2 * (k : ℝ)
  else if d ≤ k then ρ + ρ ^ 2 * ((k : ℝ) - (d : ℝ))
  else 0

/-- **Bandedness on `ℤ`**: an entry vanishes when `|j - i| > k`. -/
theorem bandedCovZ_banded (ρ : ℝ) (k : ℕ) {i j : ℤ} (h : Int.natAbs (j - i) > k) :
    bandedCovZ ρ k i j = 0 := by
  unfold bandedCovZ
  dsimp
  split_ifs
  · omega
  · omega
  · rfl

end

end BookProof.OSReconstruction
