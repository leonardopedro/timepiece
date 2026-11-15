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
`chainCov_hsNormSq`.  For `k = 0` it gives `card ι`.

## Formalised results

* `bandCov_comm` — the covariance matrix is symmetric;
* `bandCov_forward` — the forward coefficient `ρ + ρ² (k - d)`;
* `bandCov_backward` — the backward coefficient `ρ + ρ² (k - d)`;
* `bandCov_row_sum` — one row of squared entries, bandedness reducing it to the
  `2k + 1` band sites;
* `band_sum_closed` — evaluation of the row sum as the polynomial above;
* `bandCov_hsNormSq` — the squared Hilbert–Schmidt norm `card ι * (row sum)`;
* `bandCov_hsNormSq_one` — at `k = 1` this is `chainCov_hsNormSq`.
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
          ∀ a ∈ Finset.range k,
            (if (σ^[a + 1]) i = (σ^[b + 1]) j then (1 : ℝ) else 0) = 0 := by
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

lemma bandCov_comm {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ) (i j : ι) :
    bandCov σ ρ k i j = bandCov σ ρ k j i := by
  classical
  unfold bandCov
  simp only [eq_comm]
  have hL : ∀ x ∈ Finset.range k,
      ((if j = (⇑σ)^[x + 1] i then (1 : ℝ) else 0) + (if i = (⇑σ)^[x + 1] j then 1 else 0))
      = ((if i = (⇑σ)^[x + 1] j then (1 : ℝ) else 0)
          + (if j = (⇑σ)^[x + 1] i then 1 else 0)) := by
    intro x _
    rw [add_comm]
  rw [Finset.sum_congr rfl hL]
  have hQ : (∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k,
        (if (⇑σ)^[a + 1] i = (⇑σ)^[b + 1] j then (1 : ℝ) else 0))
      = (∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k,
        (if (⇑σ)^[a + 1] j = (⇑σ)^[b + 1] i then (1 : ℝ) else 0)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : (⇑σ)^[a + 1] j = (⇑σ)^[b + 1] i
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  rw [hQ]

lemma perm_iterate_symm_iterate {ι : Type*} (σ : Equiv.Perm ι) (n : ℕ) (x : ι) :
    (σ^[n]) ((σ.symm^[n]) x) = x := by
  have hcoe : ((σ.symm ^ n : Equiv.Perm ι)) = (σ ^ n)⁻¹ := by
    rw [show σ.symm = σ⁻¹ from rfl, inv_pow]
  calc (σ^[n]) ((σ.symm^[n]) x)
      = (σ ^ n) ((σ.symm ^ n) x) := by
          rw [← Equiv.Perm.coe_pow, ← Equiv.Perm.coe_pow]
    _ = ((σ ^ n) * (σ.symm ^ n)) x := by rw [Equiv.Perm.mul_apply]
    _ = (1 : Equiv.Perm ι) x := by rw [hcoe, mul_inv_cancel]
    _ = x := by simp

lemma perm_symm_iterate_iterate {ι : Type*} (σ : Equiv.Perm ι) (n : ℕ) (x : ι) :
    (σ.symm^[n]) ((σ^[n]) x) = x := by
  have hcoe : ((σ.symm ^ n : Equiv.Perm ι)) = (σ ^ n)⁻¹ := by
    rw [show σ.symm = σ⁻¹ from rfl, inv_pow]
  calc (σ.symm^[n]) ((σ^[n]) x)
      = (σ.symm ^ n) ((σ ^ n) x) := by
          rw [← Equiv.Perm.coe_pow, ← Equiv.Perm.coe_pow]
    _ = ((σ.symm ^ n) * (σ ^ n)) x := by rw [Equiv.Perm.mul_apply]
    _ = (1 : Equiv.Perm ι) x := by rw [hcoe, inv_mul_cancel]
    _ = x := by simp

/-- Iterates of a permutation commute. -/
lemma iterate_comm_apply {ι : Type*} (σ : Equiv.Perm ι) (m n : ℕ) (x : ι) :
    (σ^[m]) ((σ^[n]) x) = (σ^[n]) ((σ^[m]) x) := by
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
  congr 1
  omega

theorem bandCov_row_sum {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ) {i : ι}
    (hno : ∀ a, 1 ≤ a → a ≤ 2 * k → (σ^[a]) i ≠ i) :
    (∑ j, bandCov σ ρ k i j ^ 2)
      = (1 + ρ ^ 2 * k) ^ 2
        + 2 * ∑ a ∈ Finset.range k, (ρ + ρ ^ 2 * (k - (a + 1))) ^ 2 := by
  classical
  set F : Finset ι := (Finset.range k).image (fun a => (σ^[a + 1]) i) with hF
  set G : Finset ι := (Finset.range k).image (fun a => (σ.symm^[a + 1]) i) with hG
  set B : Finset ι := insert i (F ∪ G) with hB
  have hno_symm : ∀ a, 1 ≤ a → a ≤ 2 * k → (σ.symm^[a]) i ≠ i := by
    intro a ha1 ha2 hcontra
    apply hno a ha1 ha2
    have h := congrArg (σ^[a]) hcontra
    rw [perm_iterate_symm_iterate] at h
    exact h.symm
  have hzero : ∀ j ∈ (Finset.univ : Finset ι), j ∉ B → bandCov σ ρ k i j ^ 2 = 0 := by
    intro j _ hj
    have hpos : ∀ a, a ≤ k → j ≠ (σ^[a]) i := by
      intro a ha heq
      apply hj
      rcases Nat.eq_zero_or_pos a with ha0 | ha1
      · subst ha0
        have hji : j = i := by simpa using heq
        rw [hB, hji]
        exact Finset.mem_insert_self i (F ∪ G)
      · have hmem : j ∈ F := by
          rw [hF]
          exact Finset.mem_image.mpr ⟨a - 1, Finset.mem_range.mpr (by omega),
            by rw [Nat.sub_add_cancel ha1]; exact heq.symm⟩
        rw [hB]
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hmem)
    have hneg : ∀ a, a ≤ k → i ≠ (σ^[a]) j := by
      intro a ha heq
      apply hj
      have h1 : j = (σ.symm^[a]) i := by
        have h2 := congrArg (σ.symm^[a]) heq
        simp only [perm_symm_iterate_iterate] at h2
        exact h2.symm
      rcases Nat.eq_zero_or_pos a with ha0 | ha1
      · subst ha0
        rw [hB, h1]
        exact Finset.mem_insert_self i (F ∪ G)
      · have hmem : j ∈ G := by
          rw [hG]
          exact Finset.mem_image.mpr ⟨a - 1, Finset.mem_range.mpr (by omega),
            by rw [Nat.sub_add_cancel ha1]; exact h1.symm⟩
        rw [hB]
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hmem)
    rw [bandCov_eq_zero σ ρ k hpos hneg]
    ring
  rw [← Finset.sum_subset (Finset.subset_univ B) hzero]
  have hi_notin : i ∉ F ∪ G := by
    intro hi
    rcases Finset.mem_union.mp hi with h | h
    · rw [hF, Finset.mem_image] at h
      obtain ⟨a, ha, hja⟩ := h
      exact hno (a + 1) (by omega)
        (by have := Finset.mem_range.mp ha; omega) hja
    · rw [hG, Finset.mem_image] at h
      obtain ⟨a, ha, hja⟩ := h
      have hcontra : (σ^[a + 1]) i = i := by
        have h := congrArg (σ^[a + 1]) hja
        rw [perm_iterate_symm_iterate] at h
        exact h.symm
      exact hno (a + 1) (by omega)
        (by have := Finset.mem_range.mp ha; omega) hcontra
  have hdisj : Disjoint F G := by
    rw [Finset.disjoint_left]
    intro j hjF hjG
    rw [hF, Finset.mem_image] at hjF
    rw [hG, Finset.mem_image] at hjG
    obtain ⟨a, ha, hja⟩ := hjF
    obtain ⟨b, hb, hjb⟩ := hjG
    have hab : (σ^[b + 1]) ((σ^[a + 1]) i) = i := by
      rw [hja, ← hjb]
      exact perm_iterate_symm_iterate σ (b + 1) i
    have hab' : (σ^[(b + 1) + (a + 1)]) i = i := by
      rw [Function.iterate_add_apply]
      exact hab
    exact hno ((b + 1) + (a + 1)) (by omega)
      (by have := Finset.mem_range.mp ha; have := Finset.mem_range.mp hb; omega) hab'
  rw [hB, Finset.sum_insert hi_notin, Finset.sum_union hdisj]
  have hFsum : ∑ j ∈ F, bandCov σ ρ k i j ^ 2
      = ∑ a ∈ Finset.range k, (ρ + ρ ^ 2 * (k - (a + 1))) ^ 2 := by
    rw [hF, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      rw [bandCov_forward σ ρ k (i := i) (j := (σ^[a + 1]) i) (d := a + 1)
        (show 1 ≤ a + 1 by omega) (Nat.succ_le_of_lt (Finset.mem_range.mp ha)) rfl hno]
      push_cast
      ring
    · intro a ha b hb hab
      have ha2 : a + 1 ≤ 2 * k := by
        have := Finset.mem_range.mp ha; omega
      have hb2 : b + 1 ≤ 2 * k := by
        have := Finset.mem_range.mp hb; omega
      have := iterate_inj_of_no_short_cycle σ k hno ha2 hb2 hab
      omega
  have hGsum : ∑ j ∈ G, bandCov σ ρ k i j ^ 2
      = ∑ a ∈ Finset.range k, (ρ + ρ ^ 2 * (k - (a + 1))) ^ 2 := by
    rw [hG, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      have hd1 : 1 ≤ a + 1 := by omega
      have hdk : a + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp ha)
      set x : ι := (σ.symm^[a + 1]) i with hxdef
      have hx : (σ^[a + 1]) x = i := perm_iterate_symm_iterate σ (a + 1) i
      have hno' : ∀ e, 1 ≤ e → e ≤ 2 * k → (σ^[e]) x ≠ x := by
        intro e he1 he2 hcontra
        apply hno e he1 he2
        have h2 := congrArg (σ^[a + 1]) hcontra
        rw [hx] at h2
        rw [← hx, iterate_comm_apply σ e (a + 1) x, hx]
        exact h2
      have hval : bandCov σ ρ k i x = ρ + ρ ^ 2 * (k - (a + 1)) := by
        rw [bandCov_comm]
        rw [bandCov_forward σ ρ k (i := x) (j := i) (d := a + 1) hd1 hdk hx.symm hno']
        push_cast
        ring
      rw [hval]
    · intro a ha b hb hab
      have ha2 : a + 1 ≤ 2 * k := by
        have := Finset.mem_range.mp ha; omega
      have hb2 : b + 1 ≤ 2 * k := by
        have := Finset.mem_range.mp hb; omega
      have := iterate_inj_of_no_short_cycle σ.symm k hno_symm ha2 hb2 hab
      omega
  rw [hFsum, hGsum, bandCov_diag σ ρ k hno]
  ring


lemma sum_range_cast_id (n : ℕ) :
    ∑ t ∈ Finset.range n, (t : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum_range_sq (n : ℕ) :
    ∑ t ∈ Finset.range n, (t : ℝ) ^ 2
      = (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum_range_sub_one (k : ℕ) :
    ∑ a ∈ Finset.range k, ((k : ℝ) - ((a : ℝ) + 1)) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · have href := Finset.sum_range_reflect (fun a : ℕ => (a : ℝ)) k
    rw [← sum_range_cast_id]
    rw [← href]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' : a ≤ k - 1 := by have := Finset.mem_range.mp ha; omega
    rw [Nat.cast_sub ha']
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    push_cast
    ring

lemma sum_range_sub_one_sq (k : ℕ) :
    ∑ a ∈ Finset.range k, ((k : ℝ) - ((a : ℝ) + 1)) ^ 2
      = ((k : ℝ) - 1) * (k : ℝ) * (2 * (k : ℝ) - 1) / 6 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · have href := Finset.sum_range_reflect (fun a : ℕ => (a : ℝ) ^ 2) k
    have hsq : ∑ t ∈ Finset.range k, (t : ℝ) ^ 2
        = ((k : ℝ) - 1) * (k : ℝ) * (2 * (k : ℝ) - 1) / 6 := by
      rw [sum_range_sq k]
      ring
    rw [← hsq]
    rw [← href]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' : a ≤ k - 1 := by have := Finset.mem_range.mp ha; omega
    rw [Nat.cast_sub ha']
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    ring

lemma band_sum_closed (ρ : ℝ) (k : ℕ) :
    (∑ a ∈ Finset.range k, (ρ + ρ ^ 2 * ((k : ℝ) - ((a : ℝ) + 1))) ^ 2)
      = ρ ^ 2 * ((k : ℝ) + ρ * ((k : ℝ) * ((k : ℝ) - 1))
          + ρ ^ 2 * (((k : ℝ) - 1) * (k : ℝ) * (2 * (k : ℝ) - 1) / 6)) := by
  have hterm : ∀ a : ℕ, (ρ + ρ ^ 2 * ((k : ℝ) - ((a : ℝ) + 1))) ^ 2
      = ρ ^ 2 * (1 + 2 * ρ * ((k : ℝ) - ((a : ℝ) + 1))
          + ρ ^ 2 * ((k : ℝ) - ((a : ℝ) + 1)) ^ 2) := by
    intro a
    ring
  simp only [hterm]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [sum_range_sub_one, sum_range_sub_one_sq]
  ring

/-- **The width-`k` band covariance is Hilbert–Schmidt**, with squared norm
`card ι * ((1 + ρ²k)² + 2ρ²(k + ρk(k-1) + ρ²(k-1)k(2k-1)/6))` when every site has no short
cycle up to `2k`. -/
theorem bandCov_hsNormSq {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ)
    (hno : ∀ i a, 1 ≤ a → a ≤ 2 * k → (σ^[a]) i ≠ i) :
    (∑ i, ∑ j, bandCov σ ρ k i j ^ 2)
      = (Fintype.card ι : ℝ) *
          ((1 + ρ ^ 2 * (k : ℝ)) ^ 2
            + 2 * (ρ ^ 2 * ((k : ℝ) + ρ * ((k : ℝ) * ((k : ℝ) - 1))
              + ρ ^ 2 * (((k : ℝ) - 1) * (k : ℝ) * (2 * (k : ℝ) - 1) / 6)))) := by
  classical
  have hrow : ∀ i : ι, ∑ j, bandCov σ ρ k i j ^ 2
      = (1 + ρ ^ 2 * (k : ℝ)) ^ 2
        + 2 * (ρ ^ 2 * ((k : ℝ) + ρ * ((k : ℝ) * ((k : ℝ) - 1))
          + ρ ^ 2 * (((k : ℝ) - 1) * (k : ℝ) * (2 * (k : ℝ) - 1) / 6))) := by
    intro i
    rw [bandCov_row_sum σ ρ k (hno i), band_sum_closed]
  simp only [hrow]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Backward off-diagonal coefficient**: if `j = σ⁻ᵈ i` with `1 ≤ d ≤ k` and `i` has
no short cycle up to `2k`, then `bandCov σ ρ k i j = ρ + ρ² (k - d)`. -/
theorem bandCov_backward {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ) {i j : ι} {d : ℕ}
    (hd : 1 ≤ d) (hdk : d ≤ k) (hj : j = (σ.symm^[d]) i)
    (hno : ∀ a, 1 ≤ a → a ≤ 2 * k → (σ^[a]) i ≠ i) :
    bandCov σ ρ k i j = ρ + ρ ^ 2 * (k - d) := by
  classical
  have hji : i = (σ^[d]) j := by
    rw [hj]
    exact (perm_iterate_symm_iterate σ d i).symm
  have hno_j : ∀ a, 1 ≤ a → a ≤ 2 * k → (σ^[a]) j ≠ j := by
    intro a ha1 ha2 hcontra
    apply hno a ha1 ha2
    have h1 : (σ^[d]) ((σ^[a]) j) = (σ^[d]) j := by rw [hcontra]
    rw [iterate_comm_apply] at h1
    rw [hj, perm_iterate_symm_iterate] at h1
    exact h1
  rw [bandCov_comm]
  exact bandCov_forward σ ρ k (i := j) (j := i) (d := d) hd hdk hji hno_j

/-- **Consistency at `k = 1`**: the width-`1` HS norm is `chainCov_hsNormSq`. -/
theorem bandCov_hsNormSq_one {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ)
    (hno : ∀ i a, 1 ≤ a → a ≤ 2 → (σ^[a]) i ≠ i) :
    (∑ i, ∑ j, bandCov σ ρ 1 i j ^ 2)
      = (Fintype.card ι : ℝ) * ((1 + ρ ^ 2) ^ 2 + 2 * ρ ^ 2) := by
  rw [bandCov_hsNormSq σ ρ 1 hno]
  norm_num

end

end BookProof.OSReconstruction
