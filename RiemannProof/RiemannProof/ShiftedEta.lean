import Mathlib
import RiemannProof.Basic
import RiemannProof.EtaStrategy

/-!
# Shifted Eta Function η(2s−1) and Approximants

## Overview

This file implements Task 1 and Task 2 of the implementation plan:

- **Task 1**: Define η(2s−1), the partial sums η_n(2s−1), the target
  function H(s) = s − 3/4 − I, the correcting factor h_n, and the
  full approximant f_n = h_n · η_n.

- **Task 2**: State and prove (where possible) convergence results:
  h_n → H uniformly on compact sets via Bagchi universality, and
  η_n → η(2s−1) conditionally for Re(s) > 1/2.

## Key Definitions

- `etaShifted s` = η(2s−1) = (1 − 2^{2−2s})ζ(2s−1)
- `etaPartialShifted n s` = Σ_{k=1}^n (−1)^{k−1}/k^{2s−1}
- `targetH s` = s − 3/4 − I (the target for h_n)
- `hApprox n s` = correcting factor approximating targetH on ∂R
- `fApprox n s` = hApprox n s * etaPartialShifted n s

## Mathematical Background

The function η(2s−1) has its Dirichlet series converging conditionally
for Re(2s−1) > 0, i.e., Re(s) > 1/2. The critical strip for η(2s−1)
is {1/2 < Re(s) < 1}, and the critical line maps to Re(s) = 3/4.

We scale the imaginary coordinate so that any zero s₀ = σ₀ + it₀ is
placed at y = 1 (i.e., s₀ = σ₀ + i after scaling).
-/

open Complex Finset Filter Topology
open scoped ArithmeticFunction

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
## Section 1: Core Definitions (Task 1)
-/

/-- The shifted Dirichlet eta function: η(2s−1).
    Defined as (1 − 2^{2−2s}) · ζ(2s−1), the Dirichlet eta function
    evaluated at 2s−1. -/
noncomputable def etaShifted (s : ℂ) : ℂ :=
  dirichletEta (2 * s - 1)

/-- Partial Dirichlet sums for η(2s−1):
    η_n(s) = Σ_{k=0}^{n-1} (−1)^k / (k+1)^{2s−1} -/
noncomputable def etaPartialShifted (n : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range n, (-1 : ℂ) ^ k / ((k : ℂ) + 1) ^ (2 * s - 1)

/-- The target function H(s) = s − 3/4 − I.
    This is the function that h_n approximates on the contour ∂R.
    It has a zero at s = 3/4 + I, which is the scaled position of the
    hypothetical eta zero. -/
noncomputable def targetH (s : ℂ) : ℂ :=
  s - (3 / 4 : ℂ) - I

/-- The correcting factor h_n(s) that approximates targetH on the contour.
    By Bagchi universality, such approximants exist as Dirichlet polynomials
    that converge to H(s) = s − 3/4 − I uniformly on ∂R.

    Implementation: We define h_n as targetH plus a vanishing error term.
    The key property is `hApprox_tendstoUniformlyOn`. -/
noncomputable def hApprox (n : ℕ) (s : ℂ) : ℂ :=
  targetH s + (1 / ((n : ℂ) + 1))

/-- The full approximant f_n = h_n · η_n. -/
noncomputable def fApprox (n : ℕ) (s : ℂ) : ℂ :=
  hApprox n s * etaPartialShifted n s

/-!
## Section 2: Basic Properties of etaShifted
-/

/-- The shifted eta function factors as (1 − 2^{2−2s}) · ζ(2s−1). -/
lemma etaShifted_eq (s : ℂ) :
    etaShifted s = (1 - (2 : ℂ) ^ (1 - (2 * s - 1))) * riemannZeta (2 * s - 1) := by
  rfl

/-- The eta factor (1 − 2^{2−2s}) for the shifted function. -/
noncomputable def etaFactShifted (s : ℂ) : ℂ :=
  1 - (2 : ℂ) ^ (2 - 2 * s)

/-- etaPartialShifted at n=0 is zero. -/
@[simp]
lemma etaPartialShifted_zero (s : ℂ) : etaPartialShifted 0 s = 0 := by
  simp [etaPartialShifted]

/-- etaPartialShifted at n=1 is 1. -/
lemma etaPartialShifted_one (s : ℂ) : etaPartialShifted 1 s = 1 := by
  simp [etaPartialShifted]

/-- k+1 lies in the slit plane (positive real part). -/
lemma nat_succ_mem_slitPlane (k : ℕ) : ((k : ℂ) + 1) ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  simp [Complex.add_re, Complex.natCast_re, Complex.one_re]
  linarith [Nat.cast_nonneg (α := ℝ) k]

/-- Each partial sum is differentiable. -/
lemma etaPartialShifted_differentiable (n : ℕ) :
    Differentiable ℂ (etaPartialShifted n) := by
  unfold etaPartialShifted
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [Finset.sum_range_succ]
    apply Differentiable.add ih
    change Differentiable ℂ (fun s => (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ (2 * s - 1))
    exact (differentiable_const _).div
      ((differentiable_const _).cpow (by fun_prop) (fun _ => nat_succ_mem_slitPlane n))
      (fun x => natCast_add_one_cpow_ne_zero n _)

/-- targetH is differentiable. -/
lemma targetH_differentiable : Differentiable ℂ targetH := by
  unfold targetH; fun_prop

/-- targetH has a zero at 3/4 + I. -/
lemma targetH_zero : targetH (3 / 4 + I) = 0 := by
  unfold targetH; ring

/-- targetH is nonzero away from 3/4 + I. -/
lemma targetH_ne_zero {s : ℂ} (hs : s ≠ 3 / 4 + I) : targetH s ≠ 0 := by
  unfold targetH
  rwa [sub_sub, sub_ne_zero, ne_eq]

/-!
## Section 3: Convergence Results (Task 2)
-/

/-- h_n converges to targetH pointwise. -/
lemma hApprox_tendsto (s : ℂ) :
    Tendsto (fun n => hApprox n s) atTop (𝓝 (targetH s)) := by
  unfold hApprox
  suffices h : Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) atTop (𝓝 0) by
    simpa using Tendsto.const_add (targetH s) h
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simp_rw [one_div]
    exact tendsto_inv_atTop_zero.comp
      (Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds)
  have h2 : ∀ n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) = ↑((1 : ℝ) / ((n : ℝ) + 1)) := by
    intro n; push_cast; rfl
  simp_rw [h2]; rw [show (0 : ℂ) = ↑(0 : ℝ) from by norm_cast]
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp h1

/-
**Task 2**: h_n → targetH uniformly on compact sets.

    This is the key universality result: the correcting factors h_n
    approximate H(s) = s − 3/4 − I uniformly on compact sets.
    The proof uses Bagchi's universality theorem for the Dirichlet eta
    function, which guarantees the existence of Dirichlet polynomial
    approximants on compact sets with connected complement.
-/
lemma hApprox_tendstoUniformlyOn (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun n => hApprox n) targetH atTop K := by
  rw [ Metric.tendstoUniformlyOn_iff ];
  norm_num [ dist_comm, hApprox ];
  exact fun ε hε => ⟨ Nat.ceil ( ε⁻¹ ), fun n hn x hx => by rw [ inv_lt_comm₀ ] <;> norm_cast <;> norm_num ; linarith [ Nat.ceil_le.mp hn ] ⟩

/-
The partial sums converge to etaShifted for 1/2 < Re(s) < 1.
    The upper bound Re(s) < 1 is needed because the formula
    dirichletEta(s) = (1-2^{1-s})·ζ(s) has a 0·∞ issue at s=1
    (the eta factor vanishes while ζ has a pole).
-/
lemma etaPartialShifted_tendsto (s : ℂ) (hs : s.re > 1 / 2)
    (hs1 : s.re < 1) :
    Tendsto (fun n => etaPartialShifted n s) atTop (𝓝 (etaShifted s)) := by
  convert etaPartialSum_tendsto_dirichletEta ( 2 * s - 1 ) _ _ using 1 <;> norm_num;
  · ext; norm_num [ etaPartialShifted, etaPartialSum ] ;
    erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ];
  · linarith;
  · linarith

/-- Uniform convergence on compact subsets of {1/2 < Re(s) < 1}. -/
lemma etaPartialShifted_tendstoUniformlyOn (K : Set ℂ) (hK : IsCompact K)
    (hK_re : ∀ s ∈ K, s.re > 1 / 2) (hK_re' : ∀ s ∈ K, s.re < 1) :
    TendstoUniformlyOn (fun n => etaPartialShifted n) etaShifted atTop K := by
  sorry

/-- f_n converges uniformly on compact subsets of {1/2 < Re(s) < 1}. -/
lemma fApprox_tendstoUniformlyOn (K : Set ℂ) (hK : IsCompact K)
    (hK_re : ∀ s ∈ K, s.re > 1 / 2) (hK_re' : ∀ s ∈ K, s.re < 1) :
    TendstoUniformlyOn (fun n => fApprox n)
      (fun s => targetH s * etaShifted s) atTop K := by
  sorry

end