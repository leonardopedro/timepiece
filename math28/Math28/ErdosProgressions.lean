import Mathlib

/-!
# Arithmetic progressions: quantitative density and Erdős' reciprocal-sum conjecture
(openai/math family 159)

**Source** (read-only snapshot, Lean v4.34.1, not imported):
`OAI.Erdos3.manuscript_main_theorems :
QuantitativeDensityTheorem ∧ ReciprocalProgressionTheorem` —
`math/OAI/Combinatorics/Progressions/Results/Conclusions.lean`; the statements are in
`math/OAI/Combinatorics/Progressions/Results/Statements.lean` and `…/Progressions/Model.lean`.
The import closure (4,774 modules) contains no `sorry`, `axiom` or `native_decide` and imports
nothing outside `Mathlib` and `OAI`.  It was not re-elaborated here (the snapshot pins Lean
v4.34.1).  `ReciprocalProgressionTheorem` is Erdős' conjecture on arithmetic progressions
(`∑_{n ∈ A} 1/n = ∞` forces arbitrarily long progressions in `A`); treat both statements
strictly as named hypotheses.

## What this module states

* `HasAP`, `APFree`, `extremalNumber`, `reciprocalTerm`, `QuantitativeDensityBound`,
  `QuantitativeDensityTheorem`, `ReciprocalProgressionTheorem` — verbatim transcriptions.
* `ManuscriptMainTheorems` — the conjunction proved by the source.

## Proved here (Lean v4.28.0, no hypothesis beyond the stated one)

* `reciprocalProgressionTheorem_of_quantitativeDensity` — **the density theorem implies the
  reciprocal theorem.**  The dyadic argument is a port of the source file
  `math/OAI/Combinatorics/Progressions/Results/Reciprocal.lean` (which takes the summability of
  the dyadic series as a hypothesis); the summability itself, from the
  `exp(-c (log log N)^{1+η})` bound, is proved here (`summable_dyadic_of_densityBound`).  So the
  source's two conclusions reduce to the single named input `QuantitativeDensityTheorem`.
-/

namespace Math28.Erdos3

open scoped BigOperators
open Filter

/-! ## Verbatim model (`Progressions/Model.lean`, `Results/Statements.lean`) -/

/-- `A` contains a `k`-term arithmetic progression with positive common difference. -/
def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- `A` contains no `k`-term arithmetic progression. -/
def APFree (A : Set ℕ) (k : ℕ) : Prop := ¬ HasAP A k

/-- `r_k(N)`: the largest size of a `k`-AP-free subset of `{1, …, N}`. -/
noncomputable def extremalNumber (k N : ℕ) : ℕ := by
  classical
  exact (((Finset.Icc 1 N).powerset).filter fun S : Finset ℕ ↦ APFree (S : Set ℕ) k).sup
    Finset.card

/-- `1/n` on `A`, `0` off `A`. -/
noncomputable def reciprocalTerm (A : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact if n ∈ A then (n : ℝ)⁻¹ else 0

/-- `r_k(N) ≤ C N exp(-c (log log N)^{1+η})`. -/
def QuantitativeDensityBound (k : ℕ) : Prop :=
  ∃ C c η : ℝ, 0 < C ∧ 0 < c ∧ 0 < η ∧
    ∀ N : ℕ, 3 ≤ N →
      (extremalNumber k N : ℝ) ≤
        C * N * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η))

/-- **Named hypothesis — `OAI.Erdos3.QuantitativeDensityTheorem`** (as proved by
`OAI.Erdos3.manuscriptQuantitativeDensityTheorem`). -/
def QuantitativeDensityTheorem : Prop :=
  ∀ k : ℕ, 3 ≤ k → QuantitativeDensityBound k

/-- **Named hypothesis — `OAI.Erdos3.ReciprocalProgressionTheorem`** (Erdős' conjecture on
arithmetic progressions, as proved by `OAI.Erdos3.manuscriptReciprocalProgressionTheorem`). -/
def ReciprocalProgressionTheorem : Prop :=
  ∀ A : Set ℕ, ¬ Summable (reciprocalTerm A) → ∀ k : ℕ, HasAP A k

/-- **Named hypothesis — `OAI.Erdos3.manuscript_main_theorems`.** -/
def ManuscriptMainTheorems : Prop :=
  QuantitativeDensityTheorem ∧ ReciprocalProgressionTheorem

/-! ## Elementary facts (ported from `math/OAI/Combinatorics/Progressions/Results/Basic.lean`) -/

theorem HasAP.mono {A B : Set ℕ} {k : ℕ} (h : HasAP A k) (hAB : A ⊆ B) :
    HasAP B k := by
  obtain ⟨a, d, hd, h⟩ := h
  exact ⟨a, d, hd, fun i hi ↦ hAB (h i hi)⟩

theorem HasAP.of_le {A : Set ℕ} {k l : ℕ} (h : HasAP A k) (hlk : l ≤ k) :
    HasAP A l := by
  obtain ⟨a, d, hd, h⟩ := h
  exact ⟨a, d, hd, fun i hi ↦ h i (hi.trans_le hlk)⟩

theorem APFree.mono {A B : Set ℕ} {k : ℕ} (h : APFree B k) (hAB : A ⊆ B) :
    APFree A k := fun hA ↦ h (hA.mono hAB)

theorem HasAP.affine_image {A : Set ℕ} {k : ℕ} (h : HasAP A k)
    (u v : ℕ) (hv : 0 < v) : HasAP ((fun n ↦ u + v * n) '' A) k := by
  obtain ⟨a, d, hd, h⟩ := h
  refine ⟨u + v * a, v * d, Nat.mul_pos hv hd, fun i hi ↦ ?_⟩
  exact ⟨a + i * d, h i hi, by ring⟩

theorem APFree.affine_preimage {A : Set ℕ} {k : ℕ} (h : APFree A k)
    (u v : ℕ) (hv : 0 < v) : APFree ((fun n ↦ u + v * n) ⁻¹' A) k := by
  intro hpre
  exact h ((hpre.affine_image u v hv).mono (Set.image_preimage_subset _ _))

theorem card_le_extremalNumber {k N : ℕ} {S : Finset ℕ}
    (hSN : S ⊆ Finset.Icc 1 N) (hS : APFree (S : Set ℕ) k) :
    S.card ≤ extremalNumber k N := by
  classical
  unfold extremalNumber
  apply Finset.le_sup (f := Finset.card)
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hSN, hS⟩

theorem card_le_extremalNumber_of_interval {k N t : ℕ} {S : Finset ℕ}
    (hSN : S ⊆ Finset.Icc (t + 1) (t + N)) (hS : APFree (S : Set ℕ) k) :
    S.card ≤ extremalNumber k N := by
  classical
  let T := S.image (fun n ↦ n - t)
  have hT : T ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    have hxN := Finset.mem_Icc.mp (hSN hx)
    apply Finset.mem_Icc.mpr
    omega
  have hfree : APFree (T : Set ℕ) k := by
    apply (hS.affine_preimage t 1 (by omega)).mono
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    have hxN := Finset.mem_Icc.mp (hSN hx)
    have heq : t + 1 * (x - t) = x := by omega
    simpa only [Set.mem_preimage, heq, Finset.mem_coe] using hx
  have hcard : T.card = S.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hxN := Finset.mem_Icc.mp (hSN hx)
    have hyN := Finset.mem_Icc.mp (hSN hy)
    change x - t = y - t at hxy
    omega
  rw [← hcard]
  exact card_le_extremalNumber hT hfree

theorem reciprocalTerm_nonneg (A : Set ℕ) (n : ℕ) : 0 ≤ reciprocalTerm A n := by
  classical
  unfold reciprocalTerm
  split_ifs <;> positivity

/-! ## The dyadic argument (ported from `math/OAI/Combinatorics/Progressions/Results/Reciprocal.lean`) -/

theorem dyadic_sum_le {k m : ℕ} {S : Finset ℕ}
    (hS : APFree (S : Set ℕ) k)
    (hSm : ∀ n ∈ S, 2 ^ m ≤ n ∧ n < 2 ^ (m + 1)) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤ (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m := by
  have hp : 0 < (2 : ℕ) ^ m := by positivity
  have hinterval : S ⊆ Finset.Icc (2 ^ m - 1 + 1) (2 ^ m - 1 + 2 ^ m) := by
    intro n hn
    have h := hSm n hn
    rw [pow_succ] at h
    apply Finset.mem_Icc.mpr
    omega
  have hcard := card_le_extremalNumber_of_interval hinterval hS
  calc
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤ ∑ _n ∈ S, ((2 : ℝ) ^ m)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      apply inv_anti₀ (by positivity)
      exact_mod_cast (hSm n hn).1
    _ = (S.card : ℝ) / 2 ^ m := by simp [div_eq_mul_inv]
    _ ≤ (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard

theorem reciprocal_sum_le_dyadic_tsum {k : ℕ}
    (hseries : Summable fun m : ℕ ↦ (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m)
    {S : Finset ℕ} (hS : APFree (S : Set ℕ) k) (hpos : ∀ n ∈ S, n ≠ 0) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤
      ∑' m : ℕ, (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m := by
  classical
  calc
    (∑ n ∈ S, (n : ℝ)⁻¹) =
        ∑ m ∈ S.image (Nat.log 2), ∑ n ∈ S with Nat.log 2 n = m, (n : ℝ)⁻¹ :=
      (Finset.sum_fiberwise_of_maps_to (s := S) (g := Nat.log 2)
        (fun n hn ↦ Finset.mem_image.mpr ⟨n, hn, rfl⟩)
        (fun n : ℕ ↦ (n : ℝ)⁻¹)).symm
    _ ≤ ∑ m ∈ S.image (Nat.log 2), (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m := by
      apply Finset.sum_le_sum
      intro m hm
      apply dyadic_sum_le (hS.mono (by intro n hn; exact (Finset.mem_filter.mp hn).1))
      intro n hn
      obtain ⟨hn, heq⟩ := Finset.mem_filter.mp hn
      rw [← heq]
      exact ⟨Nat.pow_log_le_self 2 (hpos n hn), Nat.lt_pow_succ_log_self (by omega) n⟩
    _ ≤ ∑' m : ℕ, (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m :=
      hseries.sum_le_tsum _ (fun _ _ ↦ by positivity)

theorem summable_reciprocal_of_APFree {k : ℕ}
    (hseries : Summable fun m : ℕ ↦ (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m)
    {A : Set ℕ} (hA : APFree A k) : Summable (reciprocalTerm A) := by
  classical
  apply summable_of_sum_le (fun n ↦ reciprocalTerm_nonneg A n)
    (c := ∑' m : ℕ, (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m)
  intro S
  let T := S.filter (fun n ↦ n ∈ A ∧ n ≠ 0)
  have hT : APFree (T : Set ℕ) k :=
    hA.mono (by intro n hn; exact (Finset.mem_filter.mp hn).2.1)
  have hpos : ∀ n ∈ T, n ≠ 0 := fun n hn ↦ (Finset.mem_filter.mp hn).2.2
  have heq : (∑ n ∈ S, reciprocalTerm A n) = ∑ n ∈ T, (n : ℝ)⁻¹ := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hmem : n ∈ A <;> by_cases hn0 : n = 0 <;>
      simp [reciprocalTerm, hmem, hn0]
  rw [heq]
  exact reciprocal_sum_le_dyadic_tsum hseries hT hpos

theorem hasAP_of_not_summable_reciprocal {k : ℕ}
    (hseries : Summable fun m : ℕ ↦ (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m)
    {A : Set ℕ} (hA : ¬ Summable (reciprocalTerm A)) : HasAP A k := by
  by_contra hfree
  exact hA (summable_reciprocal_of_APFree hseries hfree)

/-! ## Summability of the dyadic series from the density bound (new) -/

/-- Eventually `exp(-c (log (m log 2))^{1+η}) ≤ 1/m²`. -/
theorem eventually_exp_le_inv_sq {c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      Real.exp (-c * (Real.log ((m : ℝ) * Real.log 2)) ^ (1 + η)) ≤ ((m : ℝ) ^ 2)⁻¹ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Tendsto (fun m : ℕ => Real.log ((m : ℝ) * Real.log 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const hl2)
  have hlogm : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hL.eventually_ge_atTop (max 1 ((4 / c) ^ (1 / η))),
    hlogm.eventually_ge_atTop (-2 * Real.log (Real.log 2)), eventually_ge_atTop 1]
    with m hLm hlm hm1
  set L := Real.log ((m : ℝ) * Real.log 2) with hLdef
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hLm
  have hLpos : 0 < L := by linarith
  -- `L^η ≥ 4/c`
  have hLeta : 4 / c ≤ L ^ η := by
    have h1 : (4 / c) ^ (1 / η) ≤ L := le_trans (le_max_right _ _) hLm
    have h2 := Real.rpow_le_rpow (by positivity) h1 hη.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hη.ne', Real.rpow_one] at h2
  -- `2 L ≥ log m`
  have hsplit : L = Real.log m + Real.log (Real.log 2) := by
    rw [hLdef, Real.log_mul hmpos.ne' hl2.ne']
  have h2L : Real.log m ≤ 2 * L := by rw [hsplit]; linarith
  -- `c L^{1+η} ≥ 2 log m`
  have hpow : L ^ (1 + η) = L * L ^ η := by
    rw [Real.rpow_add hLpos, Real.rpow_one]
  have hkey : 2 * Real.log m ≤ c * L ^ (1 + η) := by
    rw [hpow]
    have : c * (L * L ^ η) ≥ c * (L * (4 / c)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLeta hLpos.le) hc.le
    have h4 : c * (L * (4 / c)) = 4 * L := by field_simp
    linarith
  calc Real.exp (-c * L ^ (1 + η)) ≤ Real.exp (-(2 * Real.log m)) := by
        apply Real.exp_le_exp.mpr; linarith
    _ = ((m : ℝ) ^ 2)⁻¹ := by
        rw [Real.exp_neg, show 2 * Real.log (m : ℝ) = Real.log ((m : ℝ) ^ 2) by
          rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]

/-- **The dyadic series converges under the density bound.** -/
theorem summable_dyadic_of_densityBound {k : ℕ} (hk : QuantitativeDensityBound k) :
    Summable fun m : ℕ ↦ (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m := by
  obtain ⟨C, c, η, hC, hc, hη, hbound⟩ := hk
  have hsum : Summable fun m : ℕ => C * ((m : ℝ) ^ 2)⁻¹ :=
    (Real.summable_nat_pow_inv.mpr (by norm_num)).mul_left C
  refine Summable.of_norm_bounded_eventually_nat hsum ?_
  filter_upwards [eventually_exp_le_inv_sq hc hη, eventually_ge_atTop 2] with m hexp hm2
  have hN : 3 ≤ 2 ^ m := by
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have hb := hbound (2 ^ m) hN
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hlog : Real.log ((2 ^ m : ℕ) : ℝ) = (m : ℝ) * Real.log 2 := by
    push_cast; rw [Real.log_pow]
  rw [hlog] at hb
  rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ h2m]
  calc (extremalNumber k (2 ^ m) : ℝ)
      ≤ C * ((2 ^ m : ℕ) : ℝ) * Real.exp (-c * Real.log ((m : ℝ) * Real.log 2) ^ (1 + η)) := hb
    _ ≤ C * ((2 ^ m : ℕ) : ℝ) * ((m : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = C * ((m : ℝ) ^ 2)⁻¹ * 2 ^ m := by push_cast; ring

/-- **The density theorem implies Erdős' reciprocal-sum theorem.** -/
theorem reciprocalProgressionTheorem_of_quantitativeDensity (h : QuantitativeDensityTheorem) :
    ReciprocalProgressionTheorem := by
  intro A hA k
  -- a `k`-AP for `k ≤ 2` is contained in a `3`-AP
  have hk3 : HasAP A (max k 3) :=
    hasAP_of_not_summable_reciprocal (summable_dyadic_of_densityBound (h _ (le_max_right _ _)))
      hA
  exact hk3.of_le (le_max_left _ _)

/-- Consequently the source's main theorem is equivalent to its density half. -/
theorem manuscriptMainTheorems_iff : ManuscriptMainTheorems ↔ QuantitativeDensityTheorem :=
  ⟨fun h => h.1, fun h => ⟨h, reciprocalProgressionTheorem_of_quantitativeDensity h⟩⟩

end Math28.Erdos3
