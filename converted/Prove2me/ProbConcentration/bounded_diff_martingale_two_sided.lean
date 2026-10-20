/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : d4c63a61-b6ba-4033-a9b4-f21de9fc90a7
* original name       : `bounded_diff_martingale_two_sided`
* title               : Two-sided bounded-differences martingale concentration
* statement author    : Grace
* solution author     : Grace (submission 68daf458-6e6b-4994-835b-c5f6e845e151,
                        accepted 2026-09-03T22:36:07.262482+00:00)
* source              : Boucheron, Lugosi, Massart, Concentration Inequalities (Oxford 2013), Sec 6.1 (Theorem 6.1, the Azuma-Hoeffding / bounded-differences martingale inequality); Azuma 1967; Hoeffding 1963.
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/prob-concentration/bounded_diff_martingale_two_sided.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/bounded_diff_martingale_two_sided.diff`.
-/
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Kernel.Condexp
import Mathlib.MeasureTheory.Measure.Real
import Theorems.Thm_hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero
import Theorems.Thm_azuma_hoeffding_two_sided

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

theorem _root_.Prove2me.Solution.bounded_diff_martingale_two_sided
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {D : ℕ → Ω → ℝ} {c : ℕ → ℝ≥0} {ℱ : Filtration ℕ mΩ}
    (h_adapted : StronglyAdapted ℱ D)
    (h_meas : ∀ i, Measurable (D i))
    (h_bdd : ∀ i, ∀ᵐ ω ∂μ, D i ω ∈ Set.Icc (-(c i : ℝ)) (c i))
    (h_cent0 : μ[D 0] = 0)
    (h_cent : ∀ i, μ[D (i + 1) | ℱ i] =ᵐ[μ] 0)
    (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, D i ω|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, (c i : ℝ) ^ 2)) := by
  -- sub-Gaussian parameter of an increment bounded in `[-(c i), c i]` is `(c i)²`.
  set cY : ℕ → ℝ≥0 := fun i => (‖(c i : ℝ) - (-(c i : ℝ))‖₊ / 2) ^ 2 with hcY
  -- term 0: unconditionally sub-Gaussian by Hoeffding's lemma.
  have h0 : HasSubgaussianMGF (D 0) (cY 0) μ := by
    have := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (μ := μ) (X := D 0) (a := -(c 0 : ℝ)) (b := (c 0 : ℝ))
      (h_meas 0).aemeasurable (h_bdd 0) h_cent0
    simpa [hcY] using this
  -- later terms: conditionally sub-Gaussian by the conditional Hoeffding lemma (imported node).
  have h_subG : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (D (i + 1)) (cY (i + 1)) μ := by
    intro i _
    have := hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero
      (μ := μ) (m := ℱ i) (ℱ.le i) (X := D (i + 1))
      (a := -(c (i + 1) : ℝ)) (b := (c (i + 1) : ℝ))
      (h_meas (i + 1)) (h_bdd (i + 1)) (h_cent i)
    simpa [hcY] using this
  -- two-sided Azuma–Hoeffding (imported node).
  have hazuma := azuma_hoeffding_two_sided
    (μ := μ) (Y := D) (cY := cY) (ℱ := ℱ) h_adapted h0 n h_subG hε
  -- identify the parameter `cY i = (c i)²` as reals.
  have hcY_eq : ∀ i, ((cY i : ℝ≥0) : ℝ) = (c i : ℝ) ^ 2 := by
    intro i
    have hcnn : (0 : ℝ) ≤ (c i : ℝ) := (c i).coe_nonneg
    simp only [hcY]
    push_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (c i : ℝ) - -(c i : ℝ))]
    ring
  have hsum_eq : ((∑ i ∈ Finset.range n, cY i : ℝ≥0) : ℝ)
      = ∑ i ∈ Finset.range n, (c i : ℝ) ^ 2 := by
    push_cast
    apply Finset.sum_congr rfl
    intro i _; exact hcY_eq i
  rw [hsum_eq] at hazuma
  exact hazuma

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

theorem bounded_diff_martingale_two_sided
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {D : ℕ → Ω → ℝ} {c : ℕ → ℝ≥0} {ℱ : Filtration ℕ mΩ}
    (h_adapted : StronglyAdapted ℱ D)
    (h_meas : ∀ i, Measurable (D i))
    (h_bdd : ∀ i, ∀ᵐ ω ∂μ, D i ω ∈ Set.Icc (-(c i : ℝ)) (c i))
    (h_cent0 : μ[D 0] = 0)
    (h_cent : ∀ i, μ[D (i + 1) | ℱ i] =ᵐ[μ] 0)
    (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, D i ω|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, (c i : ℝ) ^ 2)) := by
  first
  | exact _root_.Prove2me.Solution.bounded_diff_martingale_two_sided h_adapted h_meas h_bdd h_cent0 h_cent n hε
  | (apply _root_.Prove2me.Solution.bounded_diff_martingale_two_sided <;> assumption)


end Prove2meStatement
