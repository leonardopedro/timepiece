# Implementation Plan - Rigorous Variance Bound

This plan replaces the shortcut proof of `uniform_variance_bound` in `Basic.lean` with a mathematically faithful proof using the `Var_orthogonal_sum`, `Var_smul`, `Var_X_bound`, and `X_orthogonal` axioms, as specified in the priority attack order of `AGENTS.md`.

## User Review Required

We propose:
1. Modifying the signature of `uniform_variance_bound` in `Basic.lean` to explicitly include `E : ∀ N, (Ω N → ℂ) → ℂ` as a parameter. This is necessary because Lean 4 only includes section variables in a theorem's parameter list if they are referenced in its type signature, and we need `E` to call the expectation axioms.
2. Replacing the shortcut proof of `uniform_variance_bound` with a complete proof that decomposes the variance of the sum, applies orthogonality to cancel cross-terms, bounds each mode using the logarithmic variance bound, and factors out `ε`.

## Proposed Changes

### RiemannProof

#### [MODIFY] [Basic.lean](file:///media/leo/e7ed9d6f-5f0a-4e19-a74e-83424bc154ba/timepiece/RiemannProof/RiemannProof/Basic.lean)

We will replace the definition of `uniform_variance_bound` with:

```lean
lemma uniform_variance_bound (E : ∀ N, (Ω N → ℂ) → ℂ) (ε : ℝ) (hε : ε > 0) (N : ℕ) (s : ℂ)
    (_hs : s.re > 1 / 2) :
    ∃ M : ℝ, Var N (S_random X ε N s) ≤ ε * M := by
  use ∑ n ∈ Icc 1 N, ‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 * Real.log n
  have hE (k : ℕ) (hk : k ≤ N) : E N (fun ω ↦ ((μ k : ℂ) * X ε k N ω) / (k : ℂ) ^ s) = (μ k : ℂ) / (k : ℂ) ^ s := by
    have : (fun ω ↦ ((μ k : ℂ) * X ε k N ω) / (k : ℂ) ^ s) = (fun ω ↦ ((μ k : ℂ) / (k : ℂ) ^ s) * X ε k N ω) := by
      ext ω; ring
    rw [this, E_smul E N, exp_X_eq_one E X ε hε N k hk]
    ring
  have h_orth : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, m ≠ n →
      E N (fun ω ↦ (((μ m : ℂ) * X ε m N ω) / (m : ℂ) ^ s - E N (fun ω ↦ ((μ m : ℂ) * X ε m N ω) / (m : ℂ) ^ s)) *
                   (((μ n : ℂ) * X ε n N ω) / (n : ℂ) ^ s - E N (fun ω ↦ ((μ n : ℂ) * X ε n N ω) / (n : ℂ) ^ s))) = 0 := by
    intro m hm n hn hmn
    have hm_le : m ≤ N := (mem_Icc.mp hm).2
    have hn_le : n ≤ N := (mem_Icc.mp hn).2
    rw [hE m hm_le, hE n hn_le]
    have h_prod : (fun ω ↦ (((μ m : ℂ) * X ε m N ω) / (m : ℂ) ^ s - (μ m : ℂ) / (m : ℂ) ^ s) *
                           (((μ n : ℂ) * X ε n N ω) / (n : ℂ) ^ s - (μ n : ℂ) / (n : ℂ) ^ s)) =
                  (fun ω ↦ (((μ m : ℂ) / (m : ℂ) ^ s) * ((μ n : ℂ) / (n : ℂ) ^ s)) *
                           ((X ε m N ω - 1) * (X ε n N ω - 1))) := by
      ext ω; ring
    rw [h_prod, E_smul E N, X_orthogonal E X ε hε N m n hm_le hn_le hmn]
    ring
  have h_var_sum := Var_orthogonal_sum E Var N (Icc 1 N) (fun n ω ↦ ((μ n : ℂ) * X ε n N ω) / (n : ℂ) ^ s) h_orth
  have h_S_rand : S_random X ε N s = (fun ω ↦ ∑ n ∈ Icc 1 N, ((μ n : ℂ) * X ε n N ω) / (n : ℂ) ^ s) := by
    rfl
  rw [h_S_rand, h_var_sum]
  have h_var_term (n : ℕ) : Var N (fun ω ↦ ((μ n : ℂ) * X ε n N ω) / (n : ℂ) ^ s) =
                            ‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 * Var N (X ε n N) := by
    have : (fun ω ↦ ((μ n : ℂ) * X ε n N ω) / (n : ℂ) ^ s) = (fun ω ↦ ((μ n : ℂ) / (n : ℂ) ^ s) * X ε n N ω) := by
      ext ω; ring
    rw [this]
    exact Var_smul Var N ((μ n : ℂ) / (n : ℂ) ^ s) (X ε n N)
  have h_bound (n : ℕ) (hn : n ∈ Icc 1 N) : Var N (fun ω ↦ ((μ n : ℂ) * X ε n N ω) / (n : ℂ) ^ s) ≤
                                            ‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 * (ε * Real.log (n : ℝ)) := by
    rw [h_var_term n]
    have hnN : n ≤ N := (mem_Icc.mp hn).2
    have h_le := Var_X_bound Var X ε hε N n hnN
    have h_pos : ‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 ≥ 0 := sq_nonneg _
    exact mul_le_mul_of_nonneg_left h_le h_pos
  have h_sum_le : ∑ n ∈ Icc 1 N, Var N (fun ω ↦ ((μ n : ℂ) * X ε n N ω) / (n : ℂ) ^ s) ≤
                  ∑ n ∈ Icc 1 N, ‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 * (ε * Real.log (n : ℝ)) :=
    sum_le_sum (fun n hn ↦ h_bound n hn)
  have h_rw : (∑ n ∈ Icc 1 N, ‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 * (ε * Real.log (n : ℝ))) =
              ε * ∑ n ∈ Icc 1 N, ‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 * Real.log (n : ℝ) := by
    have h_term (n : ℕ) : ‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 * (ε * Real.log (n : ℝ)) =
                          ε * (‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 * Real.log (n : ℝ)) := by
      ring
    simp only [h_term]
    rw [← mul_sum]
  rw [h_rw] at h_sum_le
  exact h_sum_le
```

## Verification Plan

### Automated Tests
- Run `lake build` to verify the codebase compiles successfully with no warnings or errors.
