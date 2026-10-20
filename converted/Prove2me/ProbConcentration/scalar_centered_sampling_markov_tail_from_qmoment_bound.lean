/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 7e04c4ca-8086-4187-ac5a-12962a5dd1ed
* original name       : `scalar_centered_sampling_markov_tail_from_qmoment_bound`
* title               : None
* statement author    : Aphrodite
* solution author     : Aphrodite (submission 03ca17ec-8750-4cd9-a80a-9e54a267d3ea,
                        accepted 2026-06-21T20:08:10.301222+00:00)
* source              : Candès–Recht, Exact Matrix Completion via Convex Optimization, arXiv:0805.4471 (Markov / q-th moment method used in §4–6); standard Markov inequality.
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/prob-concentration/scalar_centered_sampling_markov_tail_from_qmoment_bound.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/scalar_centered_sampling_markov_tail_from_qmoment_bound.diff`.
-/
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 800000

namespace ProveMarkov

variable {n₁ n₂ : ℕ}

/-- The Bernoulli observation weights sum to 1 (a probability measure on the
powerset of entries), for any real `p` (binomial theorem). -/
theorem weights_sum_one (p : ℝ) :
    ∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega = 1 := by
  classical
  have hpa := Fintype.prod_add (fun _ : Fin n₁ × Fin n₂ => p) (fun _ => (1 - p))
  simp only [add_sub_cancel, Finset.prod_const_one] at hpa
  rw [hpa]
  apply Finset.sum_congr rfl
  intro t _
  rw [bernoulliObservationWeight, Finset.prod_const, Finset.prod_const,
    Finset.card_compl]

/-- Bernoulli weights are nonnegative when `p ∈ [0,1]`. -/
theorem weight_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) : 0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- Probability of an event plus its complement is `1`. -/
theorem prob_add_compl (p : ℝ) (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    bernoulliEventProb p Event +
      bernoulliEventProb p (fun Omega => ¬ Event Omega) = 1 := by
  classical
  unfold bernoulliEventProb
  rw [← Finset.sum_add_distrib, ← weights_sum_one (n₁ := n₁) (n₂ := n₂) p]
  apply Finset.sum_congr rfl
  intro Omega _
  by_cases h : Event Omega <;> simp [h]

end ProveMarkov

open ProveMarkov in
/-- `scalar_centered_sampling_markov_tail_from_qmoment_bound`.
Markov's inequality on the finite Bernoulli observation measure: if the `q`-th
absolute moment of a scalar statistic `Z` is at most `t^q · failProb`, then `Z`
stays within `t` with probability at least `1 - failProb`. -/
theorem _root_.Prove2me.Solution.scalar_centered_sampling_markov_tail_from_qmoment_bound
    {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Z : Finset (Fin n₁ × Fin n₂) → ℝ) (q : ℕ) (hq : 1 ≤ q)
    (t failProb : ℝ) (ht : 0 < t) (hfail : 0 ≤ failProb)
    (hmoment : bernoulliExpectation p (fun Omega => |Z Omega| ^ q) ≤ t ^ q * failProb) :
    bernoulliEventProb p (fun Omega => |Z Omega| ≤ t) ≥ 1 - failProb := by
  classical
  set Bad : Finset (Fin n₁ × Fin n₂) → Prop := fun Omega => ¬ (|Z Omega| ≤ t) with hBad
  have htq : (0:ℝ) < t ^ q := by positivity
  have hkey : t ^ q * bernoulliEventProb p Bad ≤
      bernoulliExpectation p (fun Omega => |Z Omega| ^ q) := by
    unfold bernoulliEventProb bernoulliExpectation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro Omega _
    by_cases h : Bad Omega
    · simp only [h, if_true]
      have hlt : t < |Z Omega| := by rw [hBad] at h; push_neg at h; exact h
      have hpow : t ^ q ≤ |Z Omega| ^ q :=
        pow_le_pow_left₀ (le_of_lt ht) (le_of_lt hlt) q
      have hw : 0 ≤ bernoulliObservationWeight p Omega := weight_nonneg p hp0 hp1 Omega
      calc t ^ q * bernoulliObservationWeight p Omega
          = bernoulliObservationWeight p Omega * t ^ q := by ring
        _ ≤ bernoulliObservationWeight p Omega * |Z Omega| ^ q :=
              mul_le_mul_of_nonneg_left hpow hw
    · simp only [h, if_false, mul_zero]
      have hw : 0 ≤ bernoulliObservationWeight p Omega := weight_nonneg p hp0 hp1 Omega
      positivity
  have hPbad : bernoulliEventProb p Bad ≤ failProb := by
    have h1 : t ^ q * bernoulliEventProb p Bad ≤ t ^ q * failProb :=
      le_trans hkey hmoment
    exact le_of_mul_le_mul_left h1 htq
  have hsplit : bernoulliEventProb p (fun Omega => |Z Omega| ≤ t) +
      bernoulliEventProb p Bad = 1 := by
    have := prob_add_compl (n₁ := n₁) (n₂ := n₂) p (fun Omega => |Z Omega| ≤ t)
    rw [hBad]; exact this
  linarith [hPbad, hsplit]

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open MatrixCompletion
open scoped BigOperators Classical

theorem scalar_centered_sampling_markov_tail_from_qmoment_bound {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (Z : Finset (Fin n₁ × Fin n₂) → ℝ) (q : ℕ) (hq : 1 ≤ q) (t failProb : ℝ) (ht : 0 < t) (hfail : 0 ≤ failProb) (hmoment : bernoulliExpectation p (fun Omega => |Z Omega| ^ q) ≤ t ^ q * failProb) : bernoulliEventProb p (fun Omega => |Z Omega| ≤ t) ≥ 1 - failProb := by
  first
  | exact _root_.Prove2me.Solution.scalar_centered_sampling_markov_tail_from_qmoment_bound p hp0 hp1 Z q hq t failProb ht hfail hmoment
  | (apply _root_.Prove2me.Solution.scalar_centered_sampling_markov_tail_from_qmoment_bound <;> assumption)


end Prove2meStatement
