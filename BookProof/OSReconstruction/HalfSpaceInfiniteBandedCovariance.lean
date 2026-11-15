import Mathlib
import BookProof.OSReconstruction.HalfSpaceChainBandHSNorm

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
* `bandedCovZ_self` — the diagonal `1 + ρ² k`;
* `bandedCovZ_forward` — the entry at distance `r` (`1 ≤ r ≤ k`) is `ρ + ρ² (k - r)`;
* `bandedCovZ_back` — the same at backward distance `r`;
* `bandedCovZ_comm` — symmetry, `bandedCovZ ρ k i j = bandedCovZ ρ k j i`;
* `bandedCovZ_banded` — bandedness on `ℤ`: an entry vanishes when `|j - i| > k`;
* `bandedCovZ_row_sum` — the squared entries over the `2k + 1` window centred at `i`;
* `bandedCovZ_row_tsum` — the squared `ℓ²` norm of one row, summed over all of `ℤ`;
* `bandedCovZ_row_tsum_closed` — that row norm in closed form, the per-site factor of
  `bandCov_hsNormSq`;
* `bandedCovZ_row_tsum_one`, `bandedCovZ_row_tsum_zero` — the widths `1` and `0`;
* `bandedCovZ_row_tsum_eq_bandCov_row_sum` — the row norm agrees with the finite-volume one;
* `toeplitzWeight` — the one-sided weight `1, ρ, …, ρ` the kernel is built from;
* `bandedCovZ_eq_weight_sum` — the kernel is the autocorrelation of that weight;
* `bandedCovZ_quadForm_eq_sum_sq` — the kernel's quadratic form as an explicit sum of squares;
* `bandedCovZ_posSemidef` — positive semidefiniteness of the kernel;
* `bandedCovZ_quadForm_eq_zero_iff`, `bandedCovZ_posDef` — the form vanishes only on the zero
  test function, i.e. the kernel is positive definite;
* `bandedCovZ_translate`, `bandedCovZ_row_tsum_translate`, `bandedCovZ_quadForm_translate` —
  translation invariance (Toeplitz property);
* `bandedCovZ_reflectionForm_neg`, `bandedCovZ_not_reflectionPositive` — the kernel is *not*
  reflection positive for `θ i = -i` on a half-line.

## Row norm

Each row has `2k + 1` nonzero entries: one diagonal `1 + ρ² k` and, for `r = 1, …, k`, two entries
`ρ + ρ² (k - r)`.  Hence the squared `ℓ²` norm of a row is
`(1 + ρ² k)^2 + 2 ∑_{r=1}^k (ρ + ρ² (k - r))^2`
`= (1 + ρ² k)^2 + 2 ρ² ( k + ρ k(k-1) + ρ² (k-1) k (2k-1) / 6 )`,
the same per-site factor as `bandCov_hsNormSq`.  This is `bandedCovZ_row_tsum_closed`,
obtained from the window sum `bandedCovZ_row_sum` and bandedness.

## Positive semidefiniteness

The kernel is the autocorrelation of the one-sided weight `u` (`u 0 = 1`, `u a = ρ` for
`1 ≤ a ≤ k`, `0` otherwise), i.e. `bandedCovZ ρ k i j = ∑_{a=0}^{k} u a * u (a - (j - i))`
(`bandedCovZ_eq_weight_sum`).  Consequently, for finitely supported `f : ℤ → ℝ` the quadratic
form is a sum of squares,
`∑_{i,j} bandedCovZ i j · f i · f j = ∑_b (∑_i f i · u (b + i))^2`
(`bandedCovZ_quadForm_eq_sum_sq`), hence nonnegative (`bandedCovZ_posSemidef`).  That is the
finite-minor (Toeplitz-symbol) positivity a Gaussian law with this covariance requires; what is
still absent is the measure itself.

Positivity is strict off zero: if `W_b = 0` for all `b`, take the largest `m ∈ s` with
`f m ≠ 0`; then `W_{-m} = f m`, because `b = -m` makes `u(-m + i)` vanish for `i < m` and
`f i = 0` for `i > m`.  Hence the quadratic form vanishes only for the zero test function
(`bandedCovZ_quadForm_eq_zero_iff`) and is strictly positive otherwise (`bandedCovZ_posDef`).

## Translation invariance

The kernel is Toeplitz, `bandedCovZ ρ k (i + a) (j + a) = bandedCovZ ρ k i j`
(`bandedCovZ_translate`), so a translate of a row has the same `ℓ²` norm
(`bandedCovZ_row_tsum_translate`) and the quadratic form is invariant under translating the test
function (`bandedCovZ_quadForm_translate`).

## Reflection positivity

**The kernel itself is not reflection positive.**  With `θ i = -i` and `k = ρ = 1`, the finitely
supported `f` with `f 0 = 1`, `f 1 = -2` (supported on `{0, 1} ⊂ [0, ∞)`) gives
`∑_{i,j} f i f j bandedCovZ 1 1 (-i) j = -2` (`bandedCovZ_reflectionForm_neg`), so the half-line
statement is false (`bandedCovZ_not_reflectionPositive`).  Reflection positivity belongs to the
*doubled* state, where the `+1` white-noise block on each half cancels the cross block
`[[C + 1, C], [C, C + 1]]`; that is the shape proved for `covState` in
`HalfSpaceCovariantReflectionPositivity`, and it is why the banded kernel is a coupling term, not
an OS state by itself.

## Boundary

* **No Gaussian measure is built.**  The covariance *is* positive definite
  (`bandedCovZ_posDef`), which settles the finite-minor consistency condition, but a Gaussian
  law on `ℤ → ℝ` also needs an extension theorem, and Kolmogorov consistency is not available in
  this Mathlib version here.  What is recorded is the covariance *kernel*.
* **No reflection positivity of the kernel.**  As in the section above, the half-line reflected
  form is negative for `k = ρ = 1`; the OS positivity is carried by the doubled state, not by the
  coupling kernel.
* **No Hilbert–Schmidt square root in infinite volume.**  The finite-volume squared HS norm is
  `card ι · ((1 + ρ² k)^2 + 2 ρ² (…))`, which grows linearly with the volume.  The operator
  itself is not compact on `ℓ²(ℤ)`: a banded Toeplitz matrix is not Hilbert–Schmidt.  The natural
  "square root" is the banded operator `1 + ρ ∑_{a=1}^k P^a`, which is bounded but not compact;
  it defines the field as a stochastic process via the usual white-noise construction, not via an
  HS map.  Hence the finite-volume `chainCov_hsNormSq` does not survive as an HS statement in the
  limit.
-/

namespace BookProof.OSReconstruction

open scoped BigOperators

noncomputable section

/-- **The bi-infinite width-`k` banded covariance entry.**  Depends only on `|j - i|`: diagonal
`1 + ρ² k`, off-diagonal at distance `r` (`1 ≤ r ≤ k`) is `ρ + ρ² (k - r)`, and `0` beyond
the band. -/
def bandedCovZ (ρ : ℝ) (k : ℕ) (i j : ℤ) : ℝ :=
  let d := Int.natAbs (j - i)
  if d = 0 then 1 + ρ ^ 2 * (k : ℝ)
  else if d ≤ k then ρ + ρ ^ 2 * ((k : ℝ) - (d : ℝ))
  else 0

/-- **The diagonal** is `1 + ρ² k`. -/
theorem bandedCovZ_self (ρ : ℝ) (k : ℕ) (i : ℤ) : bandedCovZ ρ k i i = 1 + ρ ^ 2 * k := by
  unfold bandedCovZ
  simp

/-- **The entry at forward distance `r`** (`1 ≤ r ≤ k`) is `ρ + ρ² (k - r)`. -/
theorem bandedCovZ_forward (ρ : ℝ) (k r : ℕ) (i : ℤ) (h1 : 1 ≤ r) (hr : r ≤ k) :
    bandedCovZ ρ k i (i + r) = ρ + ρ ^ 2 * ((k : ℝ) - (r : ℝ)) := by
  unfold bandedCovZ
  dsimp only
  have h : (i + (r : ℤ) - i).natAbs = r := by
    rw [show i + (r : ℤ) - i = (r : ℤ) by ring, Int.natAbs_natCast]
  rw [h, if_neg (by omega), if_pos hr]

/-- **Symmetry**: the kernel depends only on `|j - i|`. -/
theorem bandedCovZ_comm (ρ : ℝ) (k : ℕ) (i j : ℤ) :
    bandedCovZ ρ k i j = bandedCovZ ρ k j i := by
  unfold bandedCovZ
  dsimp only
  rw [show j - i = -(i - j) by ring, Int.natAbs_neg]

/-- **Bandedness on `ℤ`**: an entry vanishes when `|j - i| > k`. -/
theorem bandedCovZ_banded (ρ : ℝ) (k : ℕ) {i j : ℤ} (h : Int.natAbs (j - i) > k) :
    bandedCovZ ρ k i j = 0 := by
  unfold bandedCovZ
  dsimp
  split_ifs
  · omega
  · omega
  · rfl

/-- **The entry at backward distance `r`** (`1 ≤ r ≤ k`) is `ρ + ρ² (k - r)`. -/
theorem bandedCovZ_back (ρ : ℝ) (k r : ℕ) (i : ℤ) (h1 : 1 ≤ r) (hr : r ≤ k) :
    bandedCovZ ρ k i (i - (r : ℤ)) = ρ + ρ ^ 2 * ((k : ℝ) - (r : ℝ)) := by
  rw [bandedCovZ_comm]
  have h : i - (r : ℤ) + (r : ℤ) = i := by ring
  nth_rewrite 2 [← h]
  exact bandedCovZ_forward ρ k r (i - (r : ℤ)) h1 hr

/-- **The row window**: the squared entries of the row at `i` over the `2k + 1` sites
`i - k, …, i + k` sum to `(1 + ρ² k)^2 + 2 ∑_{a<k} (ρ + ρ² (k - (a+1)))^2`. -/
theorem bandedCovZ_row_sum (ρ : ℝ) (k : ℕ) (i : ℤ) :
    (∑ m ∈ Finset.range (2 * k + 1), bandedCovZ ρ k i (i - (k : ℤ) + (m : ℤ)) ^ 2)
      = (1 + ρ ^ 2 * (k : ℝ)) ^ 2
        + 2 * ∑ a ∈ Finset.range k, (ρ + ρ ^ 2 * ((k : ℝ) - ((a : ℝ) + 1))) ^ 2 := by
  have hsplit : 2 * k + 1 = k + (k + 1) := by ring
  rw [hsplit, Finset.sum_range_add, Finset.sum_range_succ']
  have hlow : ∀ x : ℕ, x < k →
      bandedCovZ ρ k i (i - (k : ℤ) + (x : ℤ)) ^ 2 = (ρ + ρ ^ 2 * (x : ℝ)) ^ 2 := by
    intro x hx
    have hxk : x ≤ k := le_of_lt hx
    have hidx : i - (k : ℤ) + (x : ℤ) = i - (((k - x : ℕ)) : ℤ) := by
      have hc : (((k - x : ℕ)) : ℤ) = (k : ℤ) - (x : ℤ) := by
        rw [Nat.cast_sub hxk]
      rw [hc]; ring
    rw [hidx, bandedCovZ_back ρ k (k - x) i (by omega) (by omega)]
    have hc : ((k : ℝ) - (((k - x : ℕ)) : ℝ)) = (x : ℝ) := by
      have h' : (((k - x : ℕ)) : ℝ) = (k : ℝ) - (x : ℝ) := by
        rw [Nat.cast_sub hxk]
      rw [h']; ring
    rw [hc]
  have hup : ∀ x : ℕ, x < k →
      bandedCovZ ρ k i (i - (k : ℤ) + (((k + (x + 1) : ℕ)) : ℤ)) ^ 2
        = (ρ + ρ ^ 2 * ((k : ℝ) - ((x : ℝ) + 1))) ^ 2 := by
    intro x hx
    have hx1 : x + 1 ≤ k := by omega
    have hidx : i - (k : ℤ) + (((k + (x + 1) : ℕ)) : ℤ) = i + ((x + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hidx, bandedCovZ_forward ρ k (x + 1) i (by omega) hx1]
    push_cast
    ring
  have hdiag : bandedCovZ ρ k i (i - (k : ℤ) + (((k + 0 : ℕ)) : ℤ)) ^ 2
      = (1 + ρ ^ 2 * (k : ℝ)) ^ 2 := by
    have hidx : i - (k : ℤ) + (((k + 0 : ℕ)) : ℤ) = i := by push_cast; ring
    rw [hidx, bandedCovZ_self]
  rw [Finset.sum_congr rfl (fun x hx => hlow x (Finset.mem_range.mp hx))]
  rw [Finset.sum_congr rfl (fun x hx => hup x (Finset.mem_range.mp hx)), hdiag]
  rw [← Finset.sum_range_reflect (fun t : ℕ => (ρ + ρ ^ 2 * (t : ℝ)) ^ 2) k]
  have hconv : ∀ j : ℕ, j < k → (ρ + ρ ^ 2 * (((k - 1 - j : ℕ)) : ℝ)) ^ 2
      = (ρ + ρ ^ 2 * ((k : ℝ) - ((j : ℝ) + 1))) ^ 2 := by
    intro j hj
    have h1 : (((k - 1 - j : ℕ)) : ℝ) = (k : ℝ) - ((j : ℝ) + 1) := by
      have hk : 1 ≤ k := by omega
      have hj' : j ≤ k - 1 := by omega
      rw [Nat.cast_sub hj', Nat.cast_sub hk]
      push_cast
      ring
    rw [h1]
  rw [Finset.sum_congr rfl (fun j hj => hconv j (Finset.mem_range.mp hj))]
  ring

/-- **The squared `ℓ²` row norm**: summing the row at `i` over all of `ℤ` gives
`(1 + ρ² k)^2 + 2 ∑_{a<k} (ρ + ρ² (k - (a+1)))^2`, since entries off the band vanish. -/
theorem bandedCovZ_row_tsum (ρ : ℝ) (k : ℕ) (i : ℤ) :
    (∑' j : ℤ, bandedCovZ ρ k i j ^ 2)
      = (1 + ρ ^ 2 * (k : ℝ)) ^ 2
        + 2 * ∑ a ∈ Finset.range k, (ρ + ρ ^ 2 * ((k : ℝ) - ((a : ℝ) + 1))) ^ 2 := by
  have hwindow : (Finset.range (2 * k + 1)).image (fun m : ℕ => i - (k : ℤ) + (m : ℤ))
      = Finset.Icc (i - (k : ℤ)) (i + (k : ℤ)) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨m, hm, rfl⟩
      omega
    · rintro ⟨h1, h2⟩
      have h0 : 0 ≤ j - (i - (k : ℤ)) := by omega
      have hcast : (((j - (i - (k : ℤ))).toNat : ℕ) : ℤ) = j - (i - (k : ℤ)) :=
        Int.toNat_of_nonneg h0
      refine ⟨(j - (i - (k : ℤ))).toNat, ?_, ?_⟩
      · omega
      · omega
  rw [tsum_eq_sum (s := Finset.Icc (i - (k : ℤ)) (i + (k : ℤ))) ?_]
  · rw [← hwindow, Finset.sum_image]
    · exact bandedCovZ_row_sum ρ k i
    · intro a _ b _ hab
      simp only at hab
      have hcast : (a : ℤ) = (b : ℤ) := by omega
      exact_mod_cast hcast
  · intro j hj
    simp only [Finset.mem_Icc, not_and_or, not_le] at hj
    have hgt : k < Int.natAbs (j - i) := by
      rcases hj with h | h
      · have hpos : (0 : ℤ) < i - j := by omega
        have hc : (Int.natAbs (i - j) : ℤ) = i - j := Int.natAbs_of_nonneg (le_of_lt hpos)
        have hk : (Int.natAbs (i - j) : ℤ) > (k : ℤ) := by rw [hc]; omega
        rw [show j - i = -(i - j) by ring, Int.natAbs_neg]
        exact_mod_cast hk
      · have hc : (Int.natAbs (j - i) : ℤ) = j - i := Int.natAbs_of_nonneg (by omega)
        have hk : (Int.natAbs (j - i) : ℤ) > (k : ℤ) := by rw [hc]; omega
        exact_mod_cast hk
    rw [bandedCovZ_banded ρ k hgt]
    norm_num

/-- **Closed form of the row norm**: the same per-site factor as `bandCov_hsNormSq`,
`(1 + ρ² k)^2 + 2 ρ² (k + ρ k (k-1) + ρ² (k-1) k (2k-1) / 6)`. -/
theorem bandedCovZ_row_tsum_closed (ρ : ℝ) (k : ℕ) (i : ℤ) :
    (∑' j : ℤ, bandedCovZ ρ k i j ^ 2)
      = (1 + ρ ^ 2 * (k : ℝ)) ^ 2
        + 2 * (ρ ^ 2 * ((k : ℝ) + ρ * ((k : ℝ) * ((k : ℝ) - 1))
          + ρ ^ 2 * (((k : ℝ) - 1) * (k : ℝ) * (2 * (k : ℝ) - 1) / 6))) := by
  rw [bandedCovZ_row_tsum, band_sum_closed]

/-- **The width-`1` row norm** is `(1 + ρ²)^2 + 2 ρ²`, the per-site factor of
`bandCov_hsNormSq_one`. -/
theorem bandedCovZ_row_tsum_one (ρ : ℝ) (i : ℤ) :
    (∑' j : ℤ, bandedCovZ ρ 1 i j ^ 2) = (1 + ρ ^ 2) ^ 2 + 2 * ρ ^ 2 := by
  rw [bandedCovZ_row_tsum]
  norm_num

/-- **The width-`0` row norm** is `1`: the kernel is the identity. -/
theorem bandedCovZ_row_tsum_zero (ρ : ℝ) (i : ℤ) :
    (∑' j : ℤ, bandedCovZ ρ 0 i j ^ 2) = 1 := by
  rw [bandedCovZ_row_tsum]
  norm_num

/-- **The per-site row norm agrees with the finite-volume one**: at a site with no short
cycle up to `2k`, the squared `ℓ²` row norm of `bandedCovZ` on `ℤ` — the same at every `m`,
by translation invariance — equals `∑_j bandCov σ ρ k i j ^ 2`. -/
theorem bandedCovZ_row_tsum_eq_bandCov_row_sum {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι)
    (ρ : ℝ) (k : ℕ) {i : ι} (hno : ∀ a, 1 ≤ a → a ≤ 2 * k → (σ^[a]) i ≠ i)
    (m : ℤ) :
    (∑' j : ℤ, bandedCovZ ρ k m j ^ 2) = ∑ j, bandCov σ ρ k i j ^ 2 := by
  rw [bandedCovZ_row_tsum, bandCov_row_sum σ ρ k hno]

/-- The one-sided weight whose autocorrelation is the banded kernel: `1` at `0`, `ρ` on
`1, …, k`, and `0` elsewhere. -/
def toeplitzWeight (ρ : ℝ) (k : ℕ) (a : ℤ) : ℝ :=
  if a = 0 then 1 else if 1 ≤ a ∧ a ≤ (k : ℤ) then ρ else 0

@[simp] lemma toeplitzWeight_zero (ρ : ℝ) (k : ℕ) : toeplitzWeight ρ k 0 = 1 := by
  simp [toeplitzWeight]

lemma toeplitzWeight_of_pos {ρ : ℝ} {k : ℕ} {a : ℤ} (h1 : 1 ≤ a) (hk : a ≤ (k : ℤ)) :
    toeplitzWeight ρ k a = ρ := by
  have h0 : a ≠ 0 := by omega
  simp [toeplitzWeight, h0, h1, hk]

lemma toeplitzWeight_of_neg {ρ : ℝ} {k : ℕ} {a : ℤ} (h : a < 0) :
    toeplitzWeight ρ k a = 0 := by
  have h0 : a ≠ 0 := by omega
  have h1 : ¬ (1 ≤ a ∧ a ≤ (k : ℤ)) := by omega
  simp [toeplitzWeight, h0, h1]

lemma toeplitzWeight_of_gt {ρ : ℝ} {k : ℕ} {a : ℤ} (h : (k : ℤ) < a) :
    toeplitzWeight ρ k a = 0 := by
  have h0 : a ≠ 0 := by omega
  have h1 : ¬ (1 ≤ a ∧ a ≤ (k : ℤ)) := by omega
  simp [toeplitzWeight, h0, h1]

/-- **Autocorrelation, positive shift**: the weight sum at shift `n` is `1 + ρ² k` at `n = 0`,
`ρ + ρ² (k - n)` for `1 ≤ n ≤ k`, and `0` beyond the band. -/
lemma weight_conv_nat (ρ : ℝ) (k n : ℕ) :
    (∑ a ∈ Finset.range (k + 1),
        toeplitzWeight ρ k (a : ℤ) * toeplitzWeight ρ k ((a : ℤ) - (n : ℤ)))
      = if n = 0 then 1 + ρ ^ 2 * (k : ℝ)
        else if n ≤ k then ρ + ρ ^ 2 * ((k : ℝ) - (n : ℝ)) else 0 := by
  by_cases hn0 : n = 0
  · subst hn0
    rw [if_pos rfl]
    rw [Finset.sum_range_succ']
    have h0 : toeplitzWeight ρ k (((0 : ℕ)) : ℤ)
        * toeplitzWeight ρ k ((((0 : ℕ)) : ℤ) - (((0 : ℕ)) : ℤ)) = 1 := by
      simp
    rw [h0]
    have hterm : ∀ a ∈ Finset.range k,
        toeplitzWeight ρ k (((a + 1 : ℕ)) : ℤ)
          * toeplitzWeight ρ k ((((a + 1 : ℕ)) : ℤ) - (((0 : ℕ)) : ℤ)) = ρ * ρ := by
      intro a ha
      have h1 : (1 : ℤ) ≤ (((a + 1 : ℕ)) : ℤ) := by exact_mod_cast Nat.succ_pos a
      have hk : (((a + 1 : ℕ)) : ℤ) ≤ (k : ℤ) := by
        exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp ha)
      rw [toeplitzWeight_of_pos h1 hk, Nat.cast_zero, sub_zero, toeplitzWeight_of_pos h1 hk]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  · by_cases hnk : n ≤ k
    · rw [if_neg hn0, if_pos hnk]
      have hk1 : k + 1 = (n + 1) + (k - n) := by omega
      rw [hk1, Finset.sum_range_add]
      have hfirst : (∑ a ∈ Finset.range (n + 1),
          toeplitzWeight ρ k (a : ℤ) * toeplitzWeight ρ k ((a : ℤ) - (n : ℤ))) = ρ := by
        rw [Finset.sum_eq_single n]
        · have hn1 : (1 : ℤ) ≤ (n : ℤ) := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
          have hnk' : (n : ℤ) ≤ (k : ℤ) := by exact_mod_cast hnk
          rw [toeplitzWeight_of_pos hn1 hnk', sub_self, toeplitzWeight_zero, mul_one]
        · intro a ha hne
          rcases Nat.eq_zero_or_pos a with ha0 | hapos
          · subst ha0
            have hlt : (((0 : ℕ)) : ℤ) - (n : ℤ) < 0 := by
              have : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
              omega
            rw [toeplitzWeight_of_neg hlt, mul_zero]
          · have han : a < n := by
              have := Finset.mem_range.mp ha
              omega
            have hlt : (a : ℤ) - (n : ℤ) < 0 := by
              have : (a : ℤ) < (n : ℤ) := by exact_mod_cast han
              omega
            rw [toeplitzWeight_of_neg hlt, mul_zero]
        · intro h
          exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h
      have hsecond : (∑ t ∈ Finset.range (k - n),
          toeplitzWeight ρ k ((((n + 1) + t : ℕ)) : ℤ)
            * toeplitzWeight ρ k (((((n + 1) + t : ℕ)) : ℤ) - (n : ℤ)))
          = ((k - n : ℕ) : ℝ) * (ρ * ρ) := by
        have hterm : ∀ t ∈ Finset.range (k - n),
            toeplitzWeight ρ k ((((n + 1) + t : ℕ)) : ℤ)
              * toeplitzWeight ρ k (((((n + 1) + t : ℕ)) : ℤ) - (n : ℤ)) = ρ * ρ := by
          intro t ht
          have hlt : t < k - n := Finset.mem_range.mp ht
          have h1 : (1 : ℤ) ≤ ((((n + 1) + t : ℕ)) : ℤ) := by
            have : 0 < (n + 1) + t := by omega
            exact_mod_cast this
          have hk : ((((n + 1) + t : ℕ)) : ℤ) ≤ (k : ℤ) := by
            have : (n + 1) + t ≤ k := by omega
            exact_mod_cast this
          have hsub : ((((n + 1) + t : ℕ)) : ℤ) - (n : ℤ) = ((t + 1 : ℕ) : ℤ) := by
            push_cast
            ring
          have h1' : (1 : ℤ) ≤ ((t + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos t
          have hk' : ((t + 1 : ℕ) : ℤ) ≤ (k : ℤ) := by
            have : t + 1 ≤ k := by omega
            exact_mod_cast this
          rw [toeplitzWeight_of_pos h1 hk, hsub, toeplitzWeight_of_pos h1' hk']
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [hfirst, hsecond, Nat.cast_sub hnk]
      ring
    · rw [if_neg hn0, if_neg hnk]
      apply Finset.sum_eq_zero
      intro a ha
      have ha1 : a ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · subst ha0
        have hlt : (((0 : ℕ)) : ℤ) - (n : ℤ) < 0 := by
          have : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
          omega
        rw [toeplitzWeight_of_neg hlt, mul_zero]
      · have hlt : (a : ℤ) - (n : ℤ) < 0 := by
          have : (a : ℤ) ≤ (k : ℤ) := by exact_mod_cast ha1
          have hnk' : (k : ℤ) < (n : ℤ) := by
            exact_mod_cast Nat.lt_of_not_le hnk
          omega
        rw [toeplitzWeight_of_neg hlt, mul_zero]

/-- **Autocorrelation, negative shift**: the same values with the shift reflected. -/
lemma weight_conv_nat_neg (ρ : ℝ) (k n : ℕ) :
    (∑ a ∈ Finset.range (k + 1),
        toeplitzWeight ρ k (a : ℤ) * toeplitzWeight ρ k ((a : ℤ) + (n : ℤ)))
      = if n = 0 then 1 + ρ ^ 2 * (k : ℝ)
        else if n ≤ k then ρ + ρ ^ 2 * ((k : ℝ) - (n : ℝ)) else 0 := by
  by_cases hn0 : n = 0
  · subst hn0
    rw [if_pos rfl]
    simpa using weight_conv_nat ρ k 0
  · by_cases hnk : n ≤ k
    · rw [if_neg hn0, if_pos hnk]
      have hk1 : k + 1 = (k - n + 1) + n := by omega
      rw [hk1, Finset.sum_range_add]
      have hfirst : (∑ a ∈ Finset.range (k - n + 1),
          toeplitzWeight ρ k (a : ℤ) * toeplitzWeight ρ k ((a : ℤ) + (n : ℤ)))
          = ((k - n : ℕ) : ℝ) * (ρ * ρ) + ρ := by
        rw [Finset.sum_range_succ']
        have h0 : toeplitzWeight ρ k (((0 : ℕ)) : ℤ)
            * toeplitzWeight ρ k ((((0 : ℕ)) : ℤ) + (n : ℤ)) = ρ := by
          have h1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
          have hnk' : (n : ℤ) ≤ (k : ℤ) := by exact_mod_cast hnk
          change toeplitzWeight ρ k (0 : ℤ) * toeplitzWeight ρ k (0 + (n : ℤ)) = ρ
          rw [toeplitzWeight_zero, zero_add, one_mul, toeplitzWeight_of_pos h1 hnk']
        have hterm : ∀ a ∈ Finset.range (k - n),
            toeplitzWeight ρ k (((a + 1 : ℕ)) : ℤ)
              * toeplitzWeight ρ k ((((a + 1 : ℕ)) : ℤ) + (n : ℤ)) = ρ * ρ := by
          intro a ha
          have hlt : a < k - n := Finset.mem_range.mp ha
          have h1 : (1 : ℤ) ≤ (((a + 1 : ℕ)) : ℤ) := by exact_mod_cast Nat.succ_pos a
          have hk : (((a + 1 : ℕ)) : ℤ) ≤ (k : ℤ) := by
            have : a + 1 ≤ k := by omega
            exact_mod_cast this
          have hsum : (((a + 1 : ℕ)) : ℤ) + (n : ℤ) = (((a + 1 + n : ℕ)) : ℤ) := by
            push_cast
            ring
          have h1' : (1 : ℤ) ≤ (((a + 1 + n : ℕ)) : ℤ) := by
            have : 0 < a + 1 + n := by omega
            exact_mod_cast this
          have hk' : (((a + 1 + n : ℕ)) : ℤ) ≤ (k : ℤ) := by
            have : a + 1 + n ≤ k := by omega
            exact_mod_cast this
          rw [toeplitzWeight_of_pos h1 hk, hsum, toeplitzWeight_of_pos h1' hk']
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, h0]
      have hsecond : (∑ t ∈ Finset.range n,
          toeplitzWeight ρ k ((((k - n + 1) + t : ℕ)) : ℤ)
            * toeplitzWeight ρ k (((((k - n + 1) + t : ℕ)) : ℤ) + (n : ℤ))) = 0 := by
        apply Finset.sum_eq_zero
        intro t ht
        have hlt : t < n := Finset.mem_range.mp ht
        have hgt : (k : ℤ) < ((((k - n + 1) + t : ℕ)) : ℤ) + (n : ℤ) := by
          have : k < ((k - n + 1) + t) + n := by omega
          have := (Nat.cast_lt (α := ℤ)).mpr this
          push_cast at this ⊢
          omega
        rw [toeplitzWeight_of_gt hgt, mul_zero]
      rw [hfirst, hsecond, Nat.cast_sub hnk]
      ring
    · rw [if_neg hn0, if_neg hnk]
      apply Finset.sum_eq_zero
      intro a ha
      have ha1 : a ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · subst ha0
        have hgt : (k : ℤ) < (n : ℤ) := by exact_mod_cast Nat.lt_of_not_le hnk
        change toeplitzWeight ρ k (0 : ℤ) * toeplitzWeight ρ k (0 + (n : ℤ)) = 0
        rw [toeplitzWeight_zero, zero_add, one_mul, toeplitzWeight_of_gt hgt]
      · have hgt : (k : ℤ) < (a : ℤ) + (n : ℤ) := by
          have ha' : (a : ℤ) ≤ (k : ℤ) := by exact_mod_cast ha1
          have hn' : (k : ℤ) < (n : ℤ) := by exact_mod_cast Nat.lt_of_not_le hnk
          omega
        rw [toeplitzWeight_of_gt hgt, mul_zero]

/-- **Autocorrelation of the weight**: the weight sum at shift `d` is `1 + ρ² k` at `d = 0`,
`ρ + ρ² (k - |d|)` for `1 ≤ |d| ≤ k`, and `0` beyond the band. -/
lemma weight_conv (ρ : ℝ) (k : ℕ) (d : ℤ) :
    (∑ a ∈ Finset.range (k + 1),
        toeplitzWeight ρ k (a : ℤ) * toeplitzWeight ρ k ((a : ℤ) - d))
      = if d.natAbs = 0 then 1 + ρ ^ 2 * (k : ℝ)
        else if d.natAbs ≤ k then ρ + ρ ^ 2 * ((k : ℝ) - (d.natAbs : ℝ)) else 0 := by
  rcases Int.natAbs_eq d with h | h
  · rw [h, Int.natAbs_natCast]
    exact weight_conv_nat ρ k d.natAbs
  · rw [h]
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    simp only [sub_neg_eq_add]
    exact weight_conv_nat_neg ρ k d.natAbs

/-- **Weight-sum representation of the kernel**: `bandedCovZ ρ k i j` is the autocorrelation
`∑_{a=0}^{k} u a * u (a - (j - i))` of the one-sided weight. -/
theorem bandedCovZ_eq_weight_sum (ρ : ℝ) (k : ℕ) (i j : ℤ) :
    bandedCovZ ρ k i j
      = ∑ a ∈ Finset.range (k + 1),
          toeplitzWeight ρ k (a : ℤ) * toeplitzWeight ρ k ((a : ℤ) - (j - i)) := by
  rw [weight_conv ρ k (j - i)]
  unfold bandedCovZ
  rfl

/-- Shifting the index of the weight sum by `i` turns it into the `b`-parametrised form. -/
lemma weight_shift_sum (ρ : ℝ) (k : ℕ) (i j : ℤ) :
    (∑ b ∈ (Finset.range (k + 1)).image (fun n : ℕ => (n : ℤ) - i),
        toeplitzWeight ρ k (b + i) * toeplitzWeight ρ k (b + j))
      = ∑ a ∈ Finset.range (k + 1),
          toeplitzWeight ρ k (a : ℤ) * toeplitzWeight ρ k ((a : ℤ) - i + j) := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n _
    rw [show ((n : ℤ) - i) + i = (n : ℤ) by ring,
      show ((n : ℤ) - i) + j = (n : ℤ) - i + j by ring]
  · intro a _ b _ hab
    simp only at hab
    have hcast : (a : ℤ) = (b : ℤ) := by omega
    exact_mod_cast hcast

/-- **The quadratic form of the banded kernel is an explicit sum of squares**: for every
finitely supported `f : ℤ → ℝ`, the weight convolution `w_b = ∑_i f_i u(b + i)` gives
`∑_{i,j} c(i,j) f_i f_j = ∑_b w_b ^ 2`. -/
theorem bandedCovZ_quadForm_eq_sum_sq (ρ : ℝ) (k : ℕ) (s : Finset ℤ) (f : ℤ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, bandedCovZ ρ k i j * f i * f j)
      = ∑ b ∈ s.biUnion (fun i => (Finset.range (k + 1)).image (fun n : ℕ => (n : ℤ) - i)),
          (∑ i ∈ s, f i * toeplitzWeight ρ k (b + i)) ^ 2 := by
  classical
  set B : Finset ℤ :=
    s.biUnion (fun i => (Finset.range (k + 1)).image (fun n : ℕ => (n : ℤ) - i)) with hB
  have hBsub : ∀ i ∈ s,
      (Finset.range (k + 1)).image (fun n : ℕ => (n : ℤ) - i) ⊆ B := by
    intro i hi b hb
    rw [hB]
    exact Finset.mem_biUnion.mpr ⟨i, hi, hb⟩
  have hident : ∀ i ∈ s, ∀ j : ℤ, bandedCovZ ρ k i j
      = ∑ b ∈ B, toeplitzWeight ρ k (b + i) * toeplitzWeight ρ k (b + j) := by
    intro i hi j
    have hzero : ∀ b ∈ B,
        b ∉ (Finset.range (k + 1)).image (fun n : ℕ => (n : ℤ) - i) →
        toeplitzWeight ρ k (b + i) * toeplitzWeight ρ k (b + j) = 0 := by
      intro b _ hb
      have hnot : ∀ n : ℕ, n ≤ k → b + i ≠ (n : ℤ) := by
        intro n hn h
        exact hb (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hn),
          by rw [← h]; ring⟩)
      have hne : b + i ≠ 0 := by
        intro h
        exact hnot 0 (Nat.zero_le k) h
      have hnotpos : ¬ (1 ≤ b + i ∧ b + i ≤ (k : ℤ)) := by
        rintro ⟨h1, h2⟩
        have hpos : 0 < b + i := by omega
        have hcast : (((b + i).toNat : ℕ) : ℤ) = b + i := Int.toNat_of_nonneg (le_of_lt hpos)
        have hn : (b + i).toNat ≤ k := by
          have : ((((b + i).toNat : ℕ)) : ℤ) ≤ (k : ℤ) := by rw [hcast]; exact h2
          exact_mod_cast this
        exact hnot (b + i).toNat hn hcast.symm
      rw [toeplitzWeight, if_neg hne, if_neg hnotpos, zero_mul]
    calc bandedCovZ ρ k i j = bandedCovZ ρ k j i := bandedCovZ_comm ρ k i j
      _ = ∑ a ∈ Finset.range (k + 1),
            toeplitzWeight ρ k (a : ℤ) * toeplitzWeight ρ k ((a : ℤ) - i + j) := by
          rw [bandedCovZ_eq_weight_sum ρ k j i]
          apply Finset.sum_congr rfl
          intro a _
          rw [show (a : ℤ) - (i - j) = (a : ℤ) - i + j by ring]
      _ = ∑ b ∈ (Finset.range (k + 1)).image (fun n : ℕ => (n : ℤ) - i),
            toeplitzWeight ρ k (b + i) * toeplitzWeight ρ k (b + j) :=
          (weight_shift_sum ρ k i j).symm
      _ = ∑ b ∈ B, toeplitzWeight ρ k (b + i) * toeplitzWeight ρ k (b + j) :=
          Finset.sum_subset (hBsub i hi) (fun b hbB hb => hzero b hbB hb)
  have hstep : ∀ i ∈ s, ∀ j ∈ s, bandedCovZ ρ k i j * f i * f j
      = ∑ b ∈ B,
          (f i * toeplitzWeight ρ k (b + i)) * (f j * toeplitzWeight ρ k (b + j)) := by
    intro i hi j hj
    rw [hident i hi j, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => hstep i hi j hj))]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  have hfac : ∀ b ∈ B,
      (∑ i ∈ s, ∑ j ∈ s, (f i * toeplitzWeight ρ k (b + i))
        * (f j * toeplitzWeight ρ k (b + j)))
        = (∑ i ∈ s, f i * toeplitzWeight ρ k (b + i)) ^ 2 := by
    intro b _
    rw [← Finset.sum_mul_sum]
    ring
  rw [Finset.sum_congr rfl hfac]

/-- **Positive semidefiniteness of the banded kernel**: for every finitely supported
`f : ℤ → ℝ` the quadratic form is nonnegative — the finite-minor form of the Gaussian
consistency condition. -/
theorem bandedCovZ_posSemidef (ρ : ℝ) (k : ℕ) (s : Finset ℤ) (f : ℤ → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, bandedCovZ ρ k i j * f i * f j := by
  rw [bandedCovZ_quadForm_eq_sum_sq]
  exact Finset.sum_nonneg (fun b _ => sq_nonneg _)

/-- **Vanishing of the quadratic form characterises the zero test function.** -/
theorem bandedCovZ_quadForm_eq_zero_iff (ρ : ℝ) (k : ℕ) (s : Finset ℤ) (f : ℤ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, bandedCovZ ρ k i j * f i * f j) = 0 ↔ ∀ i ∈ s, f i = 0 := by
  constructor
  · intro h
    rw [bandedCovZ_quadForm_eq_sum_sq] at h
    have hW : ∀ b ∈ s.biUnion
        (fun i => (Finset.range (k + 1)).image (fun n : ℕ => (n : ℤ) - i)),
        (∑ i ∈ s, f i * toeplitzWeight ρ k (b + i)) = 0 := by
      intro b hb
      have hb' := (Finset.sum_eq_zero_iff_of_nonneg
        (f := fun b => (∑ i ∈ s, f i * toeplitzWeight ρ k (b + i)) ^ 2)
        (fun b _ => sq_nonneg _)).1 h b hb
      exact sq_eq_zero_iff.1 hb'
    by_contra hcon
    push_neg at hcon
    obtain ⟨i₀, hi₀, hf₀⟩ := hcon
    let s' : Finset ℤ := s.filter (fun i => f i ≠ 0)
    have hne : s'.Nonempty := ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, hf₀⟩⟩
    let m : ℤ := s'.max' hne
    have hmb : m ∈ s' := Finset.max'_mem s' hne
    have hm_s : m ∈ s := (Finset.mem_filter.mp hmb).1
    have hm_f : f m ≠ 0 := (Finset.mem_filter.mp hmb).2
    have hb : -m ∈ s.biUnion
        (fun i => (Finset.range (k + 1)).image (fun n : ℕ => (n : ℤ) - i)) := by
      refine Finset.mem_biUnion.mpr ⟨m, hm_s, ?_⟩
      exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos k), by simp⟩
    have hzero := hW (-m) hb
    have hval : (∑ i ∈ s, f i * toeplitzWeight ρ k (-m + i)) = f m := by
      rw [Finset.sum_eq_single m]
      · rw [show -m + m = (0 : ℤ) by ring, toeplitzWeight_zero, mul_one]
      · intro i hi hne'
        by_cases hlt : i < m
        · have hneg : -m + i < 0 := by omega
          rw [toeplitzWeight_of_neg hneg, mul_zero]
        · have hgt : m < i := by omega
          have hfi : f i = 0 := by
            by_contra hf'
            have hle : i ≤ m := Finset.le_max' s' i (Finset.mem_filter.mpr ⟨hi, hf'⟩)
            omega
          rw [hfi, zero_mul]
      · intro h
        exact absurd hm_s h
    rw [hval] at hzero
    exact hm_f hzero
  · intro hf
    apply Finset.sum_eq_zero
    intro i hi
    have hfi : f i = 0 := hf i hi
    rw [hfi]
    simp

/-- **Positive definiteness**: the quadratic form is strictly positive on every nonzero finitely
supported test function. -/
theorem bandedCovZ_posDef (ρ : ℝ) (k : ℕ) (s : Finset ℤ) {f : ℤ → ℝ}
    (hf : ∃ i ∈ s, f i ≠ 0) :
    0 < ∑ i ∈ s, ∑ j ∈ s, bandedCovZ ρ k i j * f i * f j := by
  rcases lt_or_eq_of_le (bandedCovZ_posSemidef ρ k s f) with h | h
  · exact h
  · obtain ⟨i, hi, hfi⟩ := hf
    exact absurd ((bandedCovZ_quadForm_eq_zero_iff ρ k s f).1 h.symm i hi) hfi
/-- **Translation invariance (Toeplitz property)** of the banded kernel. -/
theorem bandedCovZ_translate (ρ : ℝ) (k : ℕ) (a i j : ℤ) :
    bandedCovZ ρ k (i + a) (j + a) = bandedCovZ ρ k i j := by
  simp only [bandedCovZ, show j + a - (i + a) = j - i by ring]

/-- **The quadratic form is translation invariant**. -/
theorem bandedCovZ_quadForm_translate (ρ : ℝ) (k : ℕ) (s : Finset ℤ) (f : ℤ → ℝ)
    (a : ℤ) :
    (∑ i ∈ s.image (fun i : ℤ => i + a), ∑ j ∈ s.image (fun j : ℤ => j + a),
        bandedCovZ ρ k i j * f (i - a) * f (j - a))
      = ∑ i ∈ s, ∑ j ∈ s, bandedCovZ ρ k i j * f i * f j := by
  have hinj : Set.InjOn (fun i : ℤ => i + a) (↑s : Set ℤ) := by
    intro x _ y _ hxy
    simp only at hxy
    omega
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro j _
  rw [show i + a - a = i by ring, show j + a - a = j by ring,
    bandedCovZ_translate ρ k a i j]

/-- The reflected form on `{0, 1}` with weights `f 0 = 1`, `f 1 = -2` is `-2`. -/
theorem bandedCovZ_reflectionForm_neg :
    (∑ i ∈ ({0, 1} : Finset ℤ), ∑ j ∈ ({0, 1} : Finset ℤ),
        (if i = 0 then (1 : ℝ) else if i = 1 then -2 else 0)
          * (if j = 0 then (1 : ℝ) else if j = 1 then -2 else 0)
          * bandedCovZ 1 1 (-i) j) = -2 := by
  norm_num [Finset.sum_insert, bandedCovZ]

/-- **The banded kernel is not reflection positive** for `θ i = -i` on the half-line: the
finitely supported `f` with `f 0 = 1`, `f 1 = -2` (supported on `{0, 1} ⊂ [0, ∞)`) gives
`∑_{i,j} f i f j bandedCovZ 1 1 (-i) j = -2 < 0`.  Reflection positivity is a property of the
doubled state — the white-noise `+1` cancels the cross block there, as in
`covState` — not of the banded coupling kernel itself. -/
theorem bandedCovZ_not_reflectionPositive :
    ¬ ∀ (s : Finset ℤ) (f : ℤ → ℝ), (∀ i ∈ s, (0 : ℤ) ≤ i) →
        (∀ i ∉ s, f i = 0) →
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, f i * f j * bandedCovZ 1 1 (-i) j := by
  intro h
  have hpos : ∀ i ∈ ({0, 1} : Finset ℤ), (0 : ℤ) ≤ i := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> norm_num
  have hsupp : ∀ i ∉ ({0, 1} : Finset ℤ),
      (if i = 0 then (1 : ℝ) else if i = 1 then -2 else 0) = 0 := by
    intro i hi
    have h0 : i ≠ 0 := by
      intro h; exact hi (by rw [h]; exact Finset.mem_insert_self _ _)
    have h1 : i ≠ 1 := by
      intro h; exact hi (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    simp [h0, h1]
  have hneg := h {0, 1} (fun i => if i = 0 then (1 : ℝ) else if i = 1 then -2 else 0) hpos hsupp
  rw [bandedCovZ_reflectionForm_neg] at hneg
  norm_num at hneg

/-- **The row norm is translation invariant**: a row and its translate have the same squared
`ℓ²` norm — already implicit in `bandedCovZ_row_tsum`, whose value is site-independent. -/
theorem bandedCovZ_row_tsum_translate (ρ : ℝ) (k : ℕ) (a i : ℤ) :
    (∑' j : ℤ, bandedCovZ ρ k (i + a) j ^ 2) = ∑' j : ℤ, bandedCovZ ρ k i j ^ 2 := by
  rw [bandedCovZ_row_tsum, bandedCovZ_row_tsum]

end

end BookProof.OSReconstruction
