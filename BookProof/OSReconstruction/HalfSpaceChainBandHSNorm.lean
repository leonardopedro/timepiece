import Mathlib
import BookProof.OSReconstruction.HalfSpaceChainBandCovariance

/-!
# Width-`k` off-diagonal coefficients of the banded chain covariance

Plan: `cftproof.md`, **E3**.  `HalfSpaceChainBandCovariance` builds the width-`k` banded covariance
`bandCov σ ρ k` and proves its diagonal (`1 + ρ² k`), bandedness, and recovery of `chainCov` at
`k = 1`.  This module adds the off-diagonal coefficient formula.

At a site `i` with no short cycle up to `2k`, the entry at forward distance `d`
(`1 ≤ d ≤ k`, i.e. `j = σ^d i`) is

  `bandCov σ ρ k i j = ρ + ρ² (k - d)`.

The same value holds at backward distance `d` by symmetry of the band under
`σ ↔ σ⁻¹`.  The count behind it: the linear term contributes one (the single
`a = d - 1`), and the quadratic term counts the pairs `(a, b)` with `a = b + d`,
of which there are `k - d`.

## Hilbert–Schmidt norm (derivation)

With no short cycle up to `2k`, every row has the same `2k + 1` band entries:
one diagonal `1 + ρ² k` and, for each `r = 1, …, k`, two entries
`ρ + ρ² (k - r)` (forward and backward).  Hence

  `∑_j bandCov i j ^ 2 = (1 + ρ² k)^2 + 2 ∑_{r=1}^k (ρ + ρ² (k - r))^2`.

Writing `t = k - r` (so `t = 0, …, k-1`),

  `∑_{r=1}^k (ρ + ρ² (k - r))^2 = ∑_{t=0}^{k-1} (ρ + ρ² t)^2
     = ρ² [ k + ρ k(k-1) + ρ² (k-1) k (2k-1) / 6 ]`.

Therefore, when every cycle of `σ` has length `> 2k` (so every site has no short
cycle and all rows are equivalent),

  `∑_{i,j} bandCov σ ρ k i j ^ 2
     = card ι * ( (1 + ρ² k)^2
                  + 2 ρ² ( k + ρ k(k-1) + ρ² (k-1) k (2k-1) / 6 ) )`.

For `k = 1` this reduces to `card ι * ((1 + ρ²)^2 + 2 ρ²)`, which is
`chainCov_hsNormSq`.  For `k = 0` it gives `card ι`.  (Only the forward
coefficient is formalised below; the norm is this closed form.)
-/

namespace BookProof.OSReconstruction

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- **Forward off-diagonal coefficient**: if `j = σ^d i` with `1 ≤ d ≤ k` and `i` has no short
cycle up to `2k`, then `bandCov σ ρ k i j = ρ + ρ² (k - d)`. -/
theorem bandCov_forward {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ) {i j : ι} {d : ℕ}
    (hd : 1 ≤ d) (hdk : d ≤ k) (hj : j = (σ^[d]) i)
    (hno : ∀ a, 1 ≤ a → a ≤ 2 * k → (σ^[a]) i ≠ i) :
    bandCov σ ρ k i j = ρ + ρ ^ 2 * (k - d) := by
  classical
  have hdiag : i ≠ j := by
    intro h
    have : (σ^[d]) i = i := by rw [← hj, h]
    exact hno d hd (by omega) this
  have hfirst : (∑ a ∈ Finset.range k,
      (if (σ^[a + 1]) i = j then (1 : ℝ) else 0)) = 1 := by
    have hterm : ∀ a ∈ Finset.range k, a ≠ d - 1 →
        (if (σ^[a + 1]) i = j then (1 : ℝ) else 0) = 0 := by
      intro a ha hne
      rw [if_neg]
      intro h
      have ha1 : a + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp ha)
      have heq : a + 1 = d := by
        have := iterate_inj_of_no_short_cycle σ k hno
          (by omega : a + 1 ≤ 2 * k) (by omega : d ≤ 2 * k)
          (by
            have h1 : (σ^[a + 1]) i = j := h
            rw [h1, hj])
        omega
      exact hne (by omega)
    have hnot : d - 1 ∉ Finset.range k →
        (if (σ^[d - 1 + 1]) i = j then (1 : ℝ) else 0) = 0 :=
      fun h => absurd (Finset.mem_range.mpr (by omega : d - 1 < k)) h
    rw [Finset.sum_eq_single (d - 1) hterm hnot]
    rw [if_pos (by
      rw [show d - 1 + 1 = d by omega]
      exact hj.symm)]
  have hsecond : (∑ a ∈ Finset.range k,
      (if i = (σ^[a + 1]) j then (1 : ℝ) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [if_neg]
    intro h
    have ha1 : a + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp ha)
    have hexp : a + 1 + d ≤ 2 * k := by omega
    have hret : (σ^[a + 1 + d]) i = i := by
      have h' : i = (σ^[a + 1]) ((σ^[d]) i) := by rw [← hj]; exact h
      rw [← Function.iterate_add_apply σ (a + 1) d i] at h'
      exact h'.symm
    exact hno (a + 1 + d) (by omega) hexp hret
  have hthird : (∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k,
      (if (σ^[a + 1]) i = (σ^[b + 1]) j then (1 : ℝ) else 0)) = (k - d : ℝ) := by
    have hinner : ∀ b ∈ Finset.range k,
        (∑ a ∈ Finset.range k,
            (if (σ^[a + 1]) i = (σ^[b + 1]) j then (1 : ℝ) else 0))
          = if b + d < k then 1 else 0 := by
      intro b hb
      by_cases hbd : b + d < k
      · have ha : b + d ∈ Finset.range k := Finset.mem_range.mpr hbd
        have huniq : ∀ a ∈ Finset.range k, a ≠ b + d →
            (if (σ^[a + 1]) i = (σ^[b + 1]) j then (1 : ℝ) else 0) = 0 := by
          intro a ha hne
          rw [if_neg]
          intro h
          have ha1 : a + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp ha)
          have hb1 : b + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp hb)
          have hexp1 : a + 1 ≤ 2 * k := by omega
          have hexp2 : b + 1 + d ≤ 2 * k := by omega
          have heq : a + 1 = b + 1 + d := by
            have h1 : (σ^[a + 1]) i = (σ^[b + 1]) j := h
            have h2 : (σ^[b + 1]) j = (σ^[b + 1 + d]) i := by
              rw [hj]; rw [← Function.iterate_add_apply σ (b + 1) d i]
            have := iterate_inj_of_no_short_cycle σ k hno hexp1 hexp2 (by rw [h1, h2])
            omega
          exact hne (by omega)
        rw [Finset.sum_eq_single (b + d) huniq (fun h => absurd ha h)]
        have h1 : (σ^[b + d + 1]) i = (σ^[b + 1]) ((σ^[d]) i) := by
          rw [show b + d + 1 = b + 1 + d by omega]
          exact Function.iterate_add_apply σ (b + 1) d i
        rw [if_pos (by rw [h1, hj])]
        rw [if_pos hbd]
      · have hterm :
          ∀ a ∈ Finset.range k, (if (σ^[a + 1]) i = (σ^[b + 1]) j then (1 : ℝ) else 0) = 0 := by
          intro a ha
          rw [if_neg]
          intro h
          have ha1 : a + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp ha)
          have hb1 : b + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp hb)
          have hexp1 : a + 1 ≤ 2 * k := by omega
          have hexp2 : b + 1 + d ≤ 2 * k := by omega
          have heq : a + 1 = b + 1 + d := by
            have h1 : (σ^[a + 1]) i = (σ^[b + 1]) j := h
            have h2 : (σ^[b + 1]) j = (σ^[b + 1 + d]) i := by
              rw [hj]; rw [← Function.iterate_add_apply σ (b + 1) d i]
            have := iterate_inj_of_no_short_cycle σ k hno hexp1 hexp2 (by rw [h1, h2])
            omega
          have : b + d = a := by omega
          exact hbd (by omega : b + d < k)
        rw [Finset.sum_eq_zero hterm]
        rw [if_neg hbd]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun b hb => hinner b hb)]
    have : (Finset.range k).sum (fun b => if b + d < k then (1 : ℝ) else 0)
        = (k - d : ℝ) := by
      have hcount : (Finset.range k).filter (fun b => b + d < k) = Finset.range (k - d) := by
        ext b; simp [Finset.mem_range]; omega
      rw [Finset.sum_boole (fun b => b + d < k) (Finset.range k)]
      rw [hcount]
      rw [Finset.card_range]
      rw [Nat.cast_sub hdk]
    exact this
  unfold bandCov
  rw [if_neg hdiag]
  rw [Finset.sum_add_distrib]
  rw [hfirst, hsecond]
  rw [hthird]
  ring

end

end BookProof.OSReconstruction
