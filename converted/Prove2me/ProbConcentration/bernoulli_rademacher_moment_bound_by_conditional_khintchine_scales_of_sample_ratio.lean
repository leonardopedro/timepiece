/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 48ccbfdf-42f9-49aa-8d70-5d6ae0af91da
* original name       : `bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio`
* title               : None
* statement author    : Shuze Chen
* solution author     : Shuze Chen (submission 22658e20-ba1d-4d3c-bd6b-ad351f4c971e,
                        accepted 2026-06-21T19:32:34.662691+00:00)
* source              : Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/prob-concentration/bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio.diff`.
-/
import Definitions.Def_matrix_completion_rademacher
import Mathlib.Tactic

open MatrixCompletion

open scoped Classical BigOperators

private lemma bernoulliObservationWeight_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp _)
    (pow_nonneg (sub_nonneg.mpr hp_one) _)

private lemma bernoulliExpectation_mono
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    {F G : Finset (Fin n₁ × Fin n₂) → ℝ} :
    (∀ Omega, F Omega ≤ G Omega) →
    bernoulliExpectation p F ≤ bernoulliExpectation p G := by
  intro hFG
  unfold bernoulliExpectation
  apply Finset.sum_le_sum
  intro Omega _
  exact mul_le_mul_of_nonneg_left (hFG Omega)
    (bernoulliObservationWeight_nonneg hp hp_one Omega)

private lemma sample_ratio_nonneg
    {n₁ n₂ m : ℕ} :
    0 ≤ ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
  exact div_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

private lemma sample_ratio_le_one
    {n₁ n₂ m : ℕ} :
    0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ≤ 1 := by
  intro hn₁ hn₂ hm
  have hden_pos : 0 < (n₁ : ℝ) * (n₂ : ℝ) :=
    mul_pos (Nat.cast_pos.mpr hn₁) (Nat.cast_pos.mpr hn₂)
  have hnum_le_den : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by
    exact_mod_cast hm
  rw [div_le_iff₀ hden_pos]
  simpa using hnum_le_den

theorem _root_.Prove2me.Solution.bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio
    (Ckh : ℝ) :
    ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      (∀ Omega : Finset (Fin n₁ × Fin n₂),
        rademacherExpectation
            (fun eps =>
              spectralNorm
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Ckh * Real.sqrt (q : ℝ) *
            (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
            Real.sqrt
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X))) ^ q) →
      bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            rademacherExpectation
              (fun eps =>
                spectralNorm
                  (rademacherSampledMatrix Omega eps
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) ≤
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            (Ckh * Real.sqrt (q : ℝ) *
              (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
              Real.sqrt
                (max (sampledRowEnergyMax Omega X)
                  (sampledColumnEnergyMax Omega X))) ^ q) := by
  intro n₁ n₂ m q X hn₁ hn₂ hm hPointwise
  exact bernoulliExpectation_mono sample_ratio_nonneg
    (sample_ratio_le_one hn₁ hn₂ hm) hPointwise

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open MatrixCompletion

theorem bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio
    (Ckh : ℝ) :
    ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      (∀ Omega : Finset (Fin n₁ × Fin n₂),
        rademacherExpectation
            (fun eps =>
              spectralNorm
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Ckh * Real.sqrt (q : ℝ) *
            (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
            Real.sqrt
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X))) ^ q) →
      bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            rademacherExpectation
              (fun eps =>
                spectralNorm
                  (rademacherSampledMatrix Omega eps
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) ≤
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            (Ckh * Real.sqrt (q : ℝ) *
              (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
              Real.sqrt
                (max (sampledRowEnergyMax Omega X)
                  (sampledColumnEnergyMax Omega X))) ^ q) := by
  first
  | exact _root_.Prove2me.Solution.bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio Ckh
  | (apply _root_.Prove2me.Solution.bernoulli_rademacher_moment_bound_by_conditional_khintchine_scales_of_sample_ratio <;> assumption)


end Prove2meStatement
