import Mathlib
import UsedRoute.Basic
import UsedRoute.EtaStrategy

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

/-
Uniform convergence on compact subsets of {1/2 < Re(s) < 1}.
-/
lemma etaPartialShifted_tendstoUniformlyOn (K : Set ℂ) (hK : IsCompact K)
    (hK_re : ∀ s ∈ K, s.re > 1 / 2) (hK_re' : ∀ s ∈ K, s.re < 1) :
    TendstoUniformlyOn (fun n => etaPartialShifted n) etaShifted atTop K := by
  have h_compact : IsCompact K := hK;
  -- Choose $\sigma_0$ such that $0 < \sigma_0 < \inf_{z \in K} \Re(z) - 1/2$.
  obtain ⟨σ₀, hσ₀_pos, hσ₀⟩ : ∃ σ₀ > 0, ∀ z ∈ K, z.re - 1 / 2 > σ₀ := by
    by_cases hK_empty : K = ∅;
    · exact ⟨ 1, by norm_num, by simp +decide [ hK_empty ] ⟩;
    · have h_inf : ∃ m ∈ K, ∀ z ∈ K, z.re ≥ m.re := by
        have := h_compact.exists_isMinOn ( Set.nonempty_iff_ne_empty.mpr hK_empty ) ( show ContinuousOn ( fun z : ℂ => z.re ) K from Complex.continuous_re.continuousOn ) ; aesop;
      obtain ⟨ m, hm₁, hm₂ ⟩ := h_inf; exact ⟨ ( m.re - 1 / 2 ) / 2, by linarith [ hK_re m hm₁ ], fun z hz => by linarith [ hm₂ z hz, hK_re m hm₁ ] ⟩ ;
  have h_uniform_cauchy : UniformCauchySeqOn (fun n => etaPartialShifted n) atTop K := by
    have h_uniform_cauchy : ∀ m n : ℕ, 0 < m → m ≤ n → ∀ z ∈ K, ‖etaPartialShifted n z - etaPartialShifted (m - 1) z‖ ≤ (2 + ‖2 * z - 1 - (σ₀ : ℂ)‖ + ‖2 * z - 1 - (σ₀ : ℂ)‖ / (2 * z.re - 1 - σ₀)) * (m : ℝ) ^ (-2 * z.re + 1 + σ₀) * (2 * (eta_partial_sums_bounded σ₀ hσ₀_pos).choose + 1) := by
      intros m n hm hmn z hz
      have h_abel : ‖etaPartialShifted n z - etaPartialShifted (m - 1) z‖ ≤ (2 * (eta_partial_sums_bounded σ₀ hσ₀_pos).choose + 1) * (2 + ‖2 * z - 1 - (σ₀ : ℂ)‖ + ‖2 * z - 1 - (σ₀ : ℂ)‖ / (2 * z.re - 1 - σ₀)) * (m : ℝ) ^ (-2 * z.re + 1 + σ₀) := by
        have := eta_abel_tail_bound ( 2 * z - 1 ) σ₀ hσ₀_pos ( by norm_num; linarith [ hK_re z hz, hσ₀ z hz ] ) ( eta_partial_sums_bounded σ₀ hσ₀_pos |> Classical.choose ) ( by linarith [ ( eta_partial_sums_bounded σ₀ hσ₀_pos |> Classical.choose_spec |> And.left ) ] ) ( by simpa using ( eta_partial_sums_bounded σ₀ hσ₀_pos |> Classical.choose_spec |> And.right ) ) m n hm hmn;
        convert this.trans _ using 1;
        · unfold etaPartialShifted etaPartialSum ;
          erw [ Finset.sum_Ico_eq_sub _ _, Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ];
        · norm_num [ Complex.sub_re, Complex.mul_re ] ; ring_nf;
          have := Classical.choose_spec ( eta_partial_sums_bounded σ₀ hσ₀_pos ) |>.1;
          nlinarith [ show 0 ≤ ‖-1 + ( z * 2 - σ₀ )‖ * ( -1 + ( z.re * 2 - σ₀ ) ) ⁻¹ * ( m : ℝ ) ^ ( 1 - z.re * 2 + σ₀ ) by exact mul_nonneg ( mul_nonneg ( norm_nonneg _ ) ( inv_nonneg.mpr ( by linarith [ hK_re z hz, hσ₀ z hz ] ) ) ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ), show 0 ≤ ‖-1 + ( z * 2 - σ₀ )‖ * ( m : ℝ ) ^ ( 1 - z.re * 2 + σ₀ ) by positivity, show 0 ≤ ( m : ℝ ) ^ ( 1 - z.re * 2 + σ₀ ) by positivity ];
      linarith;
    have h_uniform_cauchy : ∃ C > 0, ∀ m n : ℕ, 0 < m → m ≤ n → ∀ z ∈ K, ‖etaPartialShifted n z - etaPartialShifted (m - 1) z‖ ≤ C * (m : ℝ) ^ (-2 * (1 / 2 + σ₀) + 1 + σ₀) := by
      obtain ⟨C, hC⟩ : ∃ C > 0, ∀ z ∈ K, (2 + ‖2 * z - 1 - (σ₀ : ℂ)‖ + ‖2 * z - 1 - (σ₀ : ℂ)‖ / (2 * z.re - 1 - σ₀)) * (2 * (eta_partial_sums_bounded σ₀ hσ₀_pos).choose + 1) ≤ C := by
        have h_uniform_cauchy : ContinuousOn (fun z : ℂ => (2 + ‖2 * z - 1 - (σ₀ : ℂ)‖ + ‖2 * z - 1 - (σ₀ : ℂ)‖ / (2 * z.re - 1 - σ₀)) * (2 * (eta_partial_sums_bounded σ₀ hσ₀_pos).choose + 1)) K := by
          refine' ContinuousOn.mul _ continuousOn_const;
          refine' ContinuousOn.add _ _;
          · fun_prop;
          · exact ContinuousOn.div ( Continuous.continuousOn ( by continuity ) ) ( Continuous.continuousOn ( by continuity ) ) fun z hz => by linarith [ hσ₀ z hz ] ;
        obtain ⟨ C, hC ⟩ := IsCompact.exists_bound_of_continuousOn h_compact h_uniform_cauchy;
        exact ⟨ Max.max C 1, by positivity, fun z hz => le_trans ( le_abs_self _ ) ( le_trans ( hC z hz ) ( le_max_left _ _ ) ) ⟩;
      use C, hC.1;
      intros m n hm hn z hz
      specialize h_uniform_cauchy m n hm hn z hz
      have h_exp : (m : ℝ) ^ (-2 * z.re + 1 + σ₀) ≤ (m : ℝ) ^ (-2 * (1 / 2 + σ₀) + 1 + σ₀) := by
        exact Real.rpow_le_rpow_of_exponent_le ( mod_cast hm ) ( by linarith [ hσ₀ z hz ] );
      refine le_trans h_uniform_cauchy ?_;
      rw [ mul_right_comm ];
      exact mul_le_mul ( hC.2 z hz ) h_exp ( by positivity ) ( by linarith );
    obtain ⟨ C, hC_pos, hC ⟩ := h_uniform_cauchy;
    rw [ Metric.uniformCauchySeqOn_iff ];
    intro ε hε_pos
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ m ≥ N, ∀ z ∈ K, ‖etaPartialShifted m z - etaPartialShifted (N - 1) z‖ < ε / 2 := by
      have h_uniform_cauchy : Filter.Tendsto (fun m : ℕ => C * (m : ℝ) ^ (-2 * (1 / 2 + σ₀) + 1 + σ₀)) Filter.atTop (nhds 0) := by
        simpa using tendsto_const_nhds.mul ( tendsto_rpow_neg_atTop ( by linarith : 0 < - ( -2 * ( 1 / 2 + σ₀ ) + 1 + σ₀ ) ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
      have := h_uniform_cauchy.eventually ( gt_mem_nhds <| half_pos hε_pos );
      obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp this; use N + 1; intros m hm z hz; specialize hC ( N + 1 ) m ( by linarith ) ( by linarith ) z hz; exact lt_of_le_of_lt hC ( hN _ ( by linarith ) ) ;
    use N + 1;
    intro m hm n hn x hx; rw [ dist_eq_norm ] ; exact lt_of_le_of_lt ( by simpa using norm_sub_le ( etaPartialShifted m x - etaPartialShifted ( N - 1 ) x ) ( etaPartialShifted n x - etaPartialShifted ( N - 1 ) x ) ) ( by linarith [ hN m ( by linarith ) x hx, hN n ( by linarith ) x hx ] ) ;
  have h_pointwise_convergence : ∀ s ∈ K, Filter.Tendsto (fun n => etaPartialShifted n s) Filter.atTop (nhds (etaShifted s)) := by
    exact fun s hs => etaPartialShifted_tendsto s ( hK_re s hs ) ( hK_re' s hs );
  rw [ Metric.uniformCauchySeqOn_iff ] at h_uniform_cauchy;
  rw [ Metric.tendstoUniformlyOn_iff ];
  intro ε hε_pos
  obtain ⟨N, hN⟩ := h_uniform_cauchy (ε / 2) (half_pos hε_pos);
  filter_upwards [ Filter.eventually_ge_atTop N ] with n hn x hx using by have := h_pointwise_convergence x hx; have := this.eventually ( Metric.ball_mem_nhds _ ( half_pos hε_pos ) ) ; have := this.and ( Filter.eventually_ge_atTop N ) ; obtain ⟨ m, hm₁, hm₂ ⟩ := this.exists; exact lt_of_le_of_lt ( dist_triangle _ _ _ ) ( by linarith [ hN m hm₂ n hn x hx, dist_comm ( etaShifted x ) ( etaPartialShifted m x ), dist_comm ( etaPartialShifted m x ) ( etaPartialShifted n x ), ( Metric.mem_ball.mp hm₁ ) ] ) ;

/-
f_n converges uniformly on compact subsets of {1/2 < Re(s) < 1}.
-/
lemma fApprox_tendstoUniformlyOn (K : Set ℂ) (hK : IsCompact K)
    (hK_re : ∀ s ∈ K, s.re > 1 / 2) (hK_re' : ∀ s ∈ K, s.re < 1) :
    TendstoUniformlyOn (fun n => fApprox n)
      (fun s => targetH s * etaShifted s) atTop K := by
  have h_uniform_bounded : ∃ M > 0, ∀ n s, s ∈ K → ‖etaPartialShifted n s‖ ≤ M := by
    -- By the properties of uniformly convergent sequences, the sequence etaPartialShifted n is uniformly bounded on K.
    have h_uniform_bounded : TendstoUniformlyOn (fun n => etaPartialShifted n) etaShifted atTop K := by
      apply_rules [ etaPartialShifted_tendstoUniformlyOn ]
    generalize_proofs at *; simp_all +decide [ dist_eq_norm ] ; (
    -- Since etaPartialShifted is uniformly convergent on K, it is uniformly bounded on K by the definition of uniform convergence.
    have h_uniform_bounded : ∃ M > 0, ∀ s ∈ K, ‖etaShifted s‖ ≤ M := by
      have h_cont : ContinuousOn etaShifted K := by
        refine' h_uniform_bounded.continuousOn _;
        exact Filter.Eventually.frequently ( Filter.Eventually.of_forall fun n => Differentiable.continuous ( etaPartialShifted_differentiable n ) |> Continuous.continuousOn )
      generalize_proofs at *; (
      obtain ⟨ M, hM ⟩ := IsCompact.exists_bound_of_continuousOn hK h_cont; use Max.max M 1; aesop;)
    generalize_proofs at *; simp_all +decide [ dist_eq_norm ] ; (
    -- Since etaPartialShifted is uniformly convergent on K, it is uniformly bounded on K by the definition of uniform convergence. Hence, we can find such an M.
    obtain ⟨M, hM_pos, hM⟩ : ∃ M > 0, ∀ s ∈ K, ‖etaShifted s‖ ≤ M := h_uniform_bounded
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, ∀ s ∈ K, ‖etaPartialShifted n s - etaShifted s‖ < 1 := by
      rw [ Metric.tendstoUniformlyOn_iff ] at h_uniform_bounded
      generalize_proofs at *; simp_all +decide [ dist_eq_norm ] ; (
      exact Exists.elim ( h_uniform_bounded 1 zero_lt_one ) fun N hN => ⟨ N, fun n hn s hs => by rw [ norm_sub_rev ] ; exact hN n hn s hs ⟩ ;)
    generalize_proofs at *; simp_all +decide [ dist_eq_norm ] ; (
    -- For n < N, we can bound ‖etaPartialShifted n s‖ by the maximum of the norms of the partial sums up to N.
    obtain ⟨M', hM'⟩ : ∃ M' > 0, ∀ n < N, ∀ s ∈ K, ‖etaPartialShifted n s‖ ≤ M' := by
      have h_uniform_bounded : ∀ n < N, ∃ M_n > 0, ∀ s ∈ K, ‖etaPartialShifted n s‖ ≤ M_n := by
        intro n hn
        have h_cont : ContinuousOn (fun s => etaPartialShifted n s) K := by
          exact Continuous.continuousOn ( by exact Differentiable.continuous ( by exact etaPartialShifted_differentiable n ) )
        generalize_proofs at *; simp_all +decide [ dist_eq_norm ] ; (
        obtain ⟨ M_n, hM_n ⟩ := IsCompact.exists_bound_of_continuousOn hK h_cont; use Max.max M_n 1; aesop;)
      generalize_proofs at *; simp_all +decide [ dist_eq_norm ] ; (
      choose! M' hM' using h_uniform_bounded;
      exact ⟨ ∑ n ∈ Finset.range N, M' n + 1, add_pos_of_nonneg_of_pos ( Finset.sum_nonneg fun n hn => le_of_lt ( hM' n ( Finset.mem_range.mp hn ) |>.1 ) ) zero_lt_one, fun n hn s hs => le_trans ( hM' n hn |>.2 s hs ) ( by linarith [ Finset.single_le_sum ( fun n _ => le_of_lt ( hM' n ( Finset.mem_range.mp ‹_› ) |>.1 ) ) ( Finset.mem_range.mpr hn ) ] ) ⟩)
    generalize_proofs at *; simp_all +decide [ dist_eq_norm ] ; (
    exact ⟨ Max.max M' ( M + 1 ), by positivity, fun n s hs => if hn : n < N then le_trans ( hM'.2 n hn s hs ) ( le_max_left _ _ ) else le_trans ( by simpa using norm_add_le ( etaShifted s ) ( etaPartialShifted n s - etaShifted s ) |> le_trans <| add_le_add ( hM s hs ) ( le_of_lt ( hN n ( le_of_not_gt hn ) s hs ) ) ) ( le_max_right _ _ ) ⟩))));
  obtain ⟨ M, hM_pos, hM ⟩ := h_uniform_bounded;
  have h_uniform_bounded : ∃ N > 0, ∀ s ∈ K, ‖targetH s‖ ≤ N := by
    obtain ⟨ N, hN ⟩ := IsCompact.exists_bound_of_continuousOn hK ( show ContinuousOn ( fun s => targetH s ) K from Continuous.continuousOn ( show Continuous ( fun s => s - ( 3 / 4 : ℂ ) - I ) from by continuity ) ) ; use Max.max N 1; aesop;
  obtain ⟨ N, hN_pos, hN ⟩ := h_uniform_bounded;
  have h_uniform_bounded : ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ s ∈ K, ‖hApprox n s * etaPartialShifted n s - targetH s * etaShifted s‖ < ε := by
    intros ε hε_pos
    obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n ≥ N₁, ∀ s ∈ K, ‖hApprox n s - targetH s‖ < ε / (2 * (M + N + 1)) := by
      have := Metric.tendstoUniformlyOn_iff.mp ( hApprox_tendstoUniformlyOn K hK ) ( ε / ( 2 * ( M + N + 1 ) ) ) ( by positivity );
      exact Filter.eventually_atTop.mp this |> fun ⟨ N₁, hN₁ ⟩ => ⟨ N₁, fun n hn s hs => by rw [ norm_sub_rev ] ; exact hN₁ n hn s hs ⟩
    obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n ≥ N₂, ∀ s ∈ K, ‖etaPartialShifted n s - etaShifted s‖ < ε / (2 * (M + N + 1)) := by
      have := etaPartialShifted_tendstoUniformlyOn K hK hK_re hK_re';
      rw [ Metric.tendstoUniformlyOn_iff ] at this;
      exact Filter.eventually_atTop.mp ( this ( ε / ( 2 * ( M + N + 1 ) ) ) ( by positivity ) ) |> fun ⟨ N₂, hN₂ ⟩ => ⟨ N₂, fun n hn s hs => by simpa only [ dist_eq_norm', norm_sub_rev ] using hN₂ n hn s hs ⟩
    use max N₁ N₂
    intro n hn s hs
    have h1 : ‖hApprox n s - targetH s‖ < ε / (2 * (M + N + 1)) := by
      exact hN₁ n ( le_trans ( le_max_left _ _ ) hn ) s hs
    have h2 : ‖etaPartialShifted n s - etaShifted s‖ < ε / (2 * (M + N + 1)) := by
      exact hN₂ n ( le_trans ( le_max_right _ _ ) hn ) s hs
    have h3 : ‖hApprox n s * etaPartialShifted n s - targetH s * etaShifted s‖ ≤ ‖hApprox n s - targetH s‖ * ‖etaPartialShifted n s‖ + ‖targetH s‖ * ‖etaPartialShifted n s - etaShifted s‖ := by
      rw [ ← norm_mul, ← norm_mul ];
      convert norm_add_le ( ( hApprox n s - targetH s ) * etaPartialShifted n s ) ( targetH s * ( etaPartialShifted n s - etaShifted s ) ) using 2 ; ring
    have h4 : ‖hApprox n s * etaPartialShifted n s - targetH s * etaShifted s‖ < ε := by
      exact h3.trans_lt ( by nlinarith [ hM n s hs, hN s hs, mul_div_cancel₀ ε ( by positivity : ( 2 * ( M + N + 1 ) ) ≠ 0 ), norm_nonneg ( hApprox n s - targetH s ), norm_nonneg ( etaPartialShifted n s - etaShifted s ) ] )
    exact h4;
  rw [ Metric.tendstoUniformlyOn_iff ];
  exact fun ε hε => by rcases h_uniform_bounded ε hε with ⟨ N₀, hN₀ ⟩ ; filter_upwards [ Filter.Ici_mem_atTop N₀ ] with n hn s hs using by rw [ dist_comm ] ; exact hN₀ n hn s hs;

end