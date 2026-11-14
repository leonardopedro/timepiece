import Mathlib
import BookProof.OSReconstruction.HalfSpaceCovStateCovariance

/-!
# A width-`k` banded covariance on an `n`-site chain

Plan: `cftproof.md`, **E3**, continuation of `HalfSpaceChainCovariance`, whose band matrix is the
one-step `Y i = X i + ρ X (σ i)`.  This module widens the band: for a permutation `σ` of the site
set, an integer `k`, and white noise `X`,

  `Y i = X i + ρ ∑_{a=1}^{k} X (σ^a i)`

i.e. the pushforward of `whiteNoise` along `1 + ρ ∑_{a=1}^{k} P_σ^a`.  Its covariance is

  `Cov(Y i, Y j) = δ_{ij} + ρ ∑_a (δ_{σ^a i, j} + δ_{i, σ^a j})
                     + ρ² ∑_{a,b} δ_{σ^a i, σ^b j}`,

which is supported on the **width-`k` band** `{σ^d i : |d| ≤ k}`: the linear terms reach distance
`k`, and the quadratic terms reach distance `k - 1`, so the union is the band of radius `k`
(`bandCov_eq_zero`).  On the diagonal of a site with no short cycle the double sum contributes `k`
times `ρ²` (`bandCov_diag`), which is the width-`k` counterpart of `chainCov_diag`.

`bandCov_one` checks that `k = 1` recovers `chainCov`, so this is a genuine extension of
`HalfSpaceChainCovariance`, not a parallel construction.

## Contents

* `bandMap`, `bandLaw`, `bandModel`, `memLp_bandModel` — the width-`k` band matrix and its state;
* `bandCov` — the explicit covariance, with `bandLaw_cov` (the state has exactly that covariance);
* **`bandCov_eq_zero`** — bandedness: the covariance vanishes off the width-`k` band;
* `iterate_inj_of_no_short_cycle` — on a site with no short cycle, the band nodes are distinct;
* **`bandCov_diag`** — the diagonal is `1 + ρ² k`;
* **`bandCov_one`** — the width-`1` case is `chainCov`.

## Boundary

* The construction is still a **finite** band around the diagonal, and still not `(−Δ+m²)⁻¹`: the
  inverse of a chain Laplacian is dense, so a banded covariance is a truncation at any width `k`.
* The width-`k` band contains overlapping terms (`(k - d)` paths of length `d`), so its off-diagonal
  coefficients are `ρ + ρ²(k - d)`, not the single `ρ` of the width-`1` case; the coefficient
  formula is `bandCov_forward` / `bandCov_backward` and the Hilbert-Schmidt norm is
  `bandCov_hsNormSq` (in `HalfSpaceChainBandHSNorm`).
* The width-`1` norm is `chainCov_hsNormSq`; the width-`k` norm is
  `card ι * ((1+ρ²k)^2 + 2 ρ² (k + ρ k(k-1) + ρ² (k-1)k(2k-1)/6))`.
-/

namespace BookProof.OSReconstruction

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-! ## The width-`k` band matrix -/

/-- **The width-`k` band matrix**: `p ↦ fun i => p i + ρ ∑_{a=1}^{k} p (σ^a i)`. -/
def bandMap {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ) : (ι → ℝ) → (ι → ℝ) :=
  fun p i => p i + ρ * ∑ a ∈ Finset.range k, p ((σ^[a + 1]) i)

theorem measurable_bandMap {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ) :
    Measurable (bandMap σ ρ k) := by
  refine measurable_pi_lambda _ fun i => ?_
  have h1 : Measurable fun p : ι → ℝ => p i := measurable_pi_apply i
  have h2 : Measurable fun p : ι → ℝ => ∑ a ∈ Finset.range k, p ((σ^[a + 1]) i) :=
    Finset.measurable_sum _ fun a _ => measurable_pi_apply _
  exact h1.add (h2.const_mul ρ)

/-- **The width-`k` band state**: white noise pushed forward by the band matrix. -/
def bandLaw {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ) : Measure (ι → ℝ) :=
  (whiteNoise ι).map (bandMap σ ρ k)

instance bandLaw_isProbability {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ) :
    IsProbabilityMeasure (bandLaw σ ρ k) := by
  unfold bandLaw
  exact Measure.isProbabilityMeasure_map (measurable_bandMap σ ρ k).aemeasurable

/-- The `i`-th coordinate of the band state, read on the white noise. -/
def bandModel {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ) (i : ι) : (ι → ℝ) → ℝ :=
  fun p => p i + ρ * ∑ a ∈ Finset.range k, p ((σ^[a + 1]) i)

theorem memLp_bandModel {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ) (i : ι) :
    MemLp (bandModel σ ρ k i) 2 (whiteNoise ι) :=
  (memLp_eval i).add ((memLp_finset_sum _
    fun a _ => memLp_eval ((σ^[a + 1]) i)).const_mul ρ)

/-! ## The covariance matrix -/

/-- **The width-`k` covariance**:
`δ_{ij} + ρ ∑_a (δ_{σ^a i, j} + δ_{i, σ^a j}) + ρ² ∑_{a,b} δ_{σ^a i, σ^b j}`, with `a`, `b`
running from `1` to `k`. -/
def bandCov {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ) (i j : ι) : ℝ := by
  classical
  exact (if i = j then 1 else 0)
    + ρ * (∑ a ∈ Finset.range k, ((if (σ^[a + 1]) i = j then 1 else 0)
        + (if i = (σ^[a + 1]) j then 1 else 0)))
    + ρ ^ 2 * (∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k,
        (if (σ^[a + 1]) i = (σ^[b + 1]) j then 1 else 0))

/-- **The band state has the explicit width-`k` covariance.** -/
theorem bandLaw_cov {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ) (i j : ι) :
    cov[fun z : ι → ℝ => z i, fun z : ι → ℝ => z j; bandLaw σ ρ k] = bandCov σ ρ k i j := by
  classical
  rw [bandLaw, covariance_map (Z := bandMap σ ρ k)
    (Measurable.aestronglyMeasurable (measurable_eval i))
    (Measurable.aestronglyMeasurable (measurable_eval j))
    (measurable_bandMap σ ρ k).aemeasurable]
  change cov[((fun p : ι → ℝ => p i) + fun p => ρ * ∑ a ∈ Finset.range k, p ((σ^[a + 1]) i)),
      ((fun p => p j) + fun p => ρ * ∑ a ∈ Finset.range k, p ((σ^[a + 1]) j)); whiteNoise ι]
    = bandCov σ ρ k i j
  rw [covariance_add_add_gen (whiteNoise ι) (fun p => p i) (fun p => p j)
    (fun p => ρ * ∑ a ∈ Finset.range k, p ((σ^[a + 1]) i))
    (fun p => ρ * ∑ a ∈ Finset.range k, p ((σ^[a + 1]) j))
    (memLp_eval i) (memLp_eval j)
    (((memLp_finset_sum _ fun a _ => memLp_eval ((σ^[a + 1]) i))).const_mul ρ)
    (((memLp_finset_sum _ fun a _ => memLp_eval ((σ^[a + 1]) j))).const_mul ρ)]
  rw [covariance_const_mul_right, covariance_const_mul_left, covariance_const_mul_left,
    covariance_const_mul_right]
  rw [covariance_fun_sum_right' (fun a _ => memLp_eval ((σ^[a + 1]) j)) (memLp_eval i)]
  rw [covariance_fun_sum_left' (fun a _ => memLp_eval ((σ^[a + 1]) i)) (memLp_eval j)]
  rw [covariance_fun_sum_fun_sum' (fun a _ => memLp_eval ((σ^[a + 1]) i))
    (fun b _ => memLp_eval ((σ^[b + 1]) j))]
  simp only [covariance_eval_eval]
  unfold bandCov
  rw [Finset.sum_add_distrib]
  ring

/-! ## Bandedness -/

/-- **Bandedness**: every entry off the width-`k` band `{σ^d i : |d| ≤ k}` vanishes.  Concretely, it
suffices that `j` is neither `σ^a`-forward nor `σ^a`-backward from `i` for any `a ≤ k`. -/
theorem bandCov_eq_zero {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ) {i j : ι}
    (hpos : ∀ a, a ≤ k → j ≠ (σ^[a]) i) (hneg : ∀ a, a ≤ k → i ≠ (σ^[a]) j) :
    bandCov σ ρ k i j = 0 := by
  classical
  have hdiag : i ≠ j := fun h => hpos 0 (by omega) h.symm
  have hfirst : ∀ a ∈ Finset.range k, (if (σ^[a + 1]) i = j then (1 : ℝ) else 0) = 0 := by
    intro a ha
    rw [if_neg]
    exact fun h => hpos (a + 1) (by simpa using Nat.succ_le_of_lt (Finset.mem_range.mp ha)) h.symm
  have hsecond : ∀ a ∈ Finset.range k, (if i = (σ^[a + 1]) j then (1 : ℝ) else 0) = 0 := by
    intro a ha
    rw [if_neg]
    exact hneg (a + 1) (by simpa using Nat.succ_le_of_lt (Finset.mem_range.mp ha))
  have hthird : ∀ a ∈ Finset.range k, ∀ b ∈ Finset.range k,
      (if (σ^[a + 1]) i = (σ^[b + 1]) j then (1 : ℝ) else 0) = 0 := by
    intro a ha b hb
    rw [if_neg]
    intro h
    have hak : a + 1 ≤ k := by simpa using Nat.succ_le_of_lt (Finset.mem_range.mp ha)
    have hbk : b + 1 ≤ k := by simpa using Nat.succ_le_of_lt (Finset.mem_range.mp hb)
    rcases le_total b a with hba | hab
    · have h1 : (σ^[b + 1]) ((σ^[a - b]) i) = (σ^[a + 1]) i := by
        rw [← Function.iterate_add_apply]
        congr 1
        omega
      have h2 : (σ^[a - b]) i = j := σ.injective.iterate (b + 1) (by rw [h1, h])
      exact hpos (a - b) (by omega) h2.symm
    · have h1 : (σ^[a + 1]) ((σ^[b - a]) j) = (σ^[b + 1]) j := by
        rw [← Function.iterate_add_apply]
        congr 1
        omega
      have h2 : (σ^[b - a]) j = i := σ.injective.iterate (a + 1) (by rw [h1, ← h])
      exact hneg (b - a) (by omega) h2.symm
  unfold bandCov
  rw [if_neg hdiag, Finset.sum_eq_zero (fun a ha => by rw [hfirst a ha, hsecond a ha, add_zero]),
    Finset.sum_eq_zero (fun a ha => Finset.sum_eq_zero (fun b hb => hthird a ha b hb))]
  ring

/-! ## Site with no short cycle: the band nodes are distinct -/

/-- **No short cycle means the band nodes are distinct**: if `σ^a i ≠ i` for `1 ≤ a ≤ 2k`, then the
`2k+1` sites `σ^d i`, `-k ≤ d ≤ k`, are pairwise distinct.  Stated for exponents up to `2k`. -/
theorem iterate_inj_of_no_short_cycle {ι : Type*} (σ : Equiv.Perm ι) (k : ℕ) {i : ι}
    (hno : ∀ a, 1 ≤ a → a ≤ 2 * k → (σ^[a]) i ≠ i) {m n : ℕ}
    (hm : m ≤ 2 * k) (hn : n ≤ 2 * k) (h : (σ^[m]) i = (σ^[n]) i) : m = n := by
  rcases le_total m n with hmn | hnm
  · have h1 : (σ^[m]) ((σ^[n - m]) i) = (σ^[n]) i := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    have h2 : (σ^[n - m]) i = i := σ.injective.iterate m (by rw [h1, h])
    by_contra hne
    exact hno (n - m) (by omega) (by omega) h2
  · have h1 : (σ^[n]) ((σ^[m - n]) i) = (σ^[m]) i := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    have h2 : (σ^[m - n]) i = i := σ.injective.iterate n (by rw [h1, h.symm])
    by_contra hne
    exact hno (m - n) (by omega) (by omega) h2

/-- **The diagonal of the width-`k` covariance** is `1 + ρ² k`. -/
theorem bandCov_diag {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ) {i : ι}
    (hno : ∀ a, 1 ≤ a → a ≤ 2 * k → (σ^[a]) i ≠ i) :
    bandCov σ ρ k i i = 1 + ρ ^ 2 * k := by
  classical
  have hfirst : ∀ a ∈ Finset.range k,
      ((if (σ^[a + 1]) i = i then (1 : ℝ) else 0) + (if i = (σ^[a + 1]) i then 1 else 0)) = 0 := by
    intro a ha
    have hak : a + 1 ≤ 2 * k := by
      have := Nat.succ_le_of_lt (Finset.mem_range.mp ha)
      omega
    have hne := hno (a + 1) (by omega) hak
    rw [if_neg hne, if_neg hne.symm, add_zero]
  have hinner : ∀ a ∈ Finset.range k,
      (∑ b ∈ Finset.range k, (if (σ^[a + 1]) i = (σ^[b + 1]) i then (1 : ℝ) else 0)) = 1 := by
    intro a ha
    have hterm : ∀ b ∈ Finset.range k, b ≠ a →
        (if (σ^[a + 1]) i = (σ^[b + 1]) i then (1 : ℝ) else 0) = 0 := by
      intro b hb hba
      rw [if_neg]
      intro h
      have hak : a + 1 ≤ 2 * k := by
        have := Nat.succ_le_of_lt (Finset.mem_range.mp ha)
        omega
      have hbk : b + 1 ≤ 2 * k := by
        have := Nat.succ_le_of_lt (Finset.mem_range.mp hb)
        omega
      exact hba (by have := iterate_inj_of_no_short_cycle σ k hno hak hbk h; omega)
    have hnot : a ∉ Finset.range k →
        (if (σ^[a + 1]) i = (σ^[a + 1]) i then (1 : ℝ) else 0) = 0 := fun h => absurd ha h
    rw [Finset.sum_eq_single a hterm hnot, if_pos rfl]
  unfold bandCov
  rw [if_pos rfl, Finset.sum_eq_zero (fun a ha => by rw [hfirst a ha]),
    Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  ring

/-! ## Consistency with the width-`1` band -/

/-- **The width-`1` band is the one-step chain covariance** of `HalfSpaceChainCovariance`. -/
theorem bandCov_one {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ) (i j : ι) :
    bandCov σ ρ 1 i j = chainCov σ ρ i j := by
  classical
  unfold bandCov chainCov
  simp only [Finset.sum_range_one, Nat.reduceAdd, Function.iterate_one]
  rw [σ.injective.eq_iff]

/-! ## Feeding the width-`k` band into the coupled state -/

/-- **The width-`k` band state has second moments.** -/
theorem memLp_eval_bandLaw {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ) (i : ι) :
    MemLp (fun z : ι → ℝ => z i) 2 (bandLaw σ ρ k) := by
  have h : MemLp (bandModel σ ρ k i) 2 (whiteNoise ι) := memLp_bandModel σ ρ k i
  unfold bandLaw
  rw [memLp_map_measure_iff (Measurable.aestronglyMeasurable (measurable_eval i))
    (measurable_bandMap σ ρ k).aemeasurable]
  exact h

/-- **The coupled state with a width-`k` banded shift** has off-diagonal block `bandCov`. -/
theorem covState_bandLaw_cov_fst_snd {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ)
    (i j : ι) :
    cov[fun z : (ι → ℝ) × (ι → ℝ) => z.1 i, fun z => z.2 j; covState (bandLaw σ ρ k)]
      = bandCov σ ρ k i j := by
  rw [covState_cov_fst_snd (bandLaw σ ρ k) (fun l => memLp_eval_bandLaw σ ρ k l) i j, shiftCov,
    bandLaw_cov σ ρ k i j]

/-- **The coupled state with a width-`k` shift is supported on the width-`k` band**: off the band
`{σ^d i : |d| ≤ k}` the cross-covariance of the two halves vanishes. -/
theorem covState_bandLaw_cov_fst_snd_eq_zero {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ)
    (k : ℕ) {i j : ι} (hpos : ∀ a, a ≤ k → j ≠ (σ^[a]) i)
    (hneg : ∀ a, a ≤ k → i ≠ (σ^[a]) j) :
    cov[fun z : (ι → ℝ) × (ι → ℝ) => z.1 i, fun z => z.2 j; covState (bandLaw σ ρ k)] = 0 := by
  rw [covState_bandLaw_cov_fst_snd σ ρ k i j]
  exact bandCov_eq_zero σ ρ k hpos hneg

end

end BookProof.OSReconstruction
