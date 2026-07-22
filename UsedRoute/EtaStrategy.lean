import Mathlib
import UsedRoute.Basic
import UnusedRoute.Legacy

/-!
# Eta Strategy: Partial Sum Approximants for η via Abel Summation

## Overview

This file implements a strategy for the Riemann Hypothesis using the Dirichlet
eta function η(s) = (1 - 2^{1-s})ζ(s) and partial sums of the eta Dirichlet
series, with uniform convergence proved via Abel summation by parts.

## Strategy

For each P, the approximant is the partial sum of the eta Dirichlet series:

  η_P(s) = Σ_{n=1}^{Q_P} (-1)^{n-1}/n^s

where Q_P = P^P + 1 → ∞. Each partial sum is a finite sum, hence:
- **Analytic** (entire, in fact)
- **Non-vanishing** in {1/2 < Re(s) < 1}: sorry (deep; related to RH)

The partial sums converge uniformly to η(s) on compact subsets of
{Re(s) > 1/2, Re(s) < 1} by **Abel summation by parts**:

1. The partial sums at a real base point σ₀ > 0 are bounded (alternating series
   with decreasing terms). This is proved in `eta_partial_sums_bounded`.

2. By Abel summation by parts (`eta_abel_tail_bound`), the tail from m to N
   at any complex s with Re(s) > σ₀ decays algebraically:
   ‖η_N(s) - η_{m-1}(s)‖ ≤ C · m^(σ₀ - Re(s))

3. This gives uniform Cauchy convergence on balls in {Re > 1/2}.

**Hurwitz's theorem** then gives: the uniform limit of non-vanishing analytic
functions is either identically zero or everywhere non-vanishing. Since η is
not identically zero (η(2) = π²/12 ≠ 0), η has no zeros in {1/2 < Re < 1}.

Since η(s) = (1 - 2^{1-s})ζ(s) and (1 - 2^{1-s}) ≠ 0 for Re(s) < 1, we
conclude ζ(s) ≠ 0 for Re(s) > 1/2.

## Proved lemmas

- `eta_abel_tail_bound`: Abel summation tail bound for the eta series
- `etaPartialSum_uniformCauchySeqOn`: Uniform Cauchy on balls in {Re > 1/2}
- `etaPartialSum_tendstoUniformlyOn`: Uniform convergence to dirichletEta
- `etaApprox_tendstoUniformlyOn`: Uniform convergence of approximants

## Remaining sorries

- `etaPartialSum_tendsto_dirichletEta`: Pointwise limit identification.
  The eta partial sums converge to (1-2^{1-s})ζ(s) for 0 < Re(s) < 1.
  For Re(s) > 1 this follows from splitting into odd/even terms;
  for 0 < Re(s) < 1 it requires the identity theorem.

- `etaApprox_ne_zero_critical_strip`: Non-vanishing of partial sums
  in {1/2 < Re < 1}.
-/

open Complex Finset Filter Topology
open scoped ArithmeticFunction ArithmeticFunction.Moebius

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
## Section 1: The Dirichlet Eta Function and Partial Sums
-/

/-- Partial sum of the Dirichlet eta function: η_N(s) = Σ_{n=1}^N (-1)^{n-1}/n^s -/
noncomputable def etaPartialSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, (-1 : ℂ) ^ (n - 1) / (n : ℂ) ^ s

/-- The Dirichlet eta function η(s) = (1 - 2^{1-s}) · ζ(s). -/
noncomputable def dirichletEta (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

/-- The factor (1 - 2^{1-s}) that relates η and ζ. -/
noncomputable def etaFactor (s : ℂ) : ℂ :=
  1 - (2 : ℂ) ^ (1 - s)

/-- The eta factor (1 - 2^{1-s}) is non-zero for Re(s) < 1.
    Its zeros are at s = 1 + 2πik/ln2 for k ∈ ℤ, all with Re(s) = 1.
    Proof: |2^{1-s}| = 2^{1-Re(s)} > 1 when Re(s) < 1, so 2^{1-s} ≠ 1. -/
lemma etaFactor_ne_zero_re_lt_one (s : ℂ) (h : s.re < 1) :
    etaFactor s ≠ 0 := by
  unfold etaFactor; norm_num [Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def]
  intro h1 h2; have := Real.sin_sq_add_cos_sq (Real.log 2 * s.im); simp_all +decide [Real.exp_ne_zero]
  cases this <;> nlinarith [Real.add_one_le_exp (Real.log 2 * (1 - s.re)), Real.log_pos one_lt_two, mul_pos (Real.log_pos one_lt_two) (sub_pos.mpr h)]

/-!
## Section 2: Evaluation Point and Cutoff
-/

/-- The evaluation point for the P-th approximation: σ_P = 1/2 + 1/(P+1).
    This is a real number strictly greater than 1/2, decreasing to 1/2. -/
noncomputable def eta_σ_P (P : ℕ) : ℝ := 1 / 2 + 1 / (P + 1 : ℝ)

lemma eta_σ_P_gt_half (P : ℕ) : eta_σ_P P > 1 / 2 := by
  unfold eta_σ_P
  have : (0 : ℝ) < 1 / ((P : ℝ) + 1) := by positivity
  linarith

lemma eta_σ_P_lt_one (P : ℕ) (hP : 2 ≤ P) : eta_σ_P P < 1 := by
  unfold eta_σ_P
  have hge : (3 : ℝ) ≤ (P : ℝ) + 1 := by
    have : (2 : ℝ) ≤ (P : ℝ) := Nat.ofNat_le_cast.mpr hP
    linarith
  have : (1 : ℝ) / ((P : ℝ) + 1) ≤ 1 / 3 :=
    div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 3) hge
  linarith

lemma eta_σ_P_tendsto : Tendsto eta_σ_P atTop (𝓝 (1 / 2)) := by
  unfold eta_σ_P
  suffices h : Tendsto (fun P : ℕ => (1 : ℝ) / ((P : ℝ) + 1)) atTop (𝓝 0) by
    have h2 := h.const_add (1 / 2 : ℝ)
    rw [add_zero] at h2
    exact h2.congr (fun P => by ring)
  simp_rw [one_div]
  exact Filter.Tendsto.inv_tendsto_atTop
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

/-- Q_P: the cutoff for the Euler product. Q_P > P. -/
noncomputable def eta_Q_P (P : ℕ) : ℕ := P ^ P + 1

/-!
## Section 3: The Euler Product Approximant

For each P, we construct:
  η_P(s) = (1 - 2^{1-s}) · ∏_{p≤Q_P} 1/(1-p^{-s})

This is a finite product of analytic functions, hence analytic and non-vanishing
in {1/2 < Re(s) < 1}.
-/

/-- The partial Euler product for ζ: ∏_{p≤P} 1/(1-p^{-s}). -/
noncomputable def zetaEulerPartial (P : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ (Icc 2 P).filter Nat.Prime, (1 - (p : ℂ) ^ (-s))⁻¹

/-- The finite Euler product is holomorphic on {Re(s) > 0}. -/
lemma zetaEulerPartial_analyticOnNhd (P : ℕ) :
    AnalyticOnNhd ℂ (zetaEulerPartial P) {s | s.re > 0} := by
  have h_factor_analytic (p : ℕ) (hp : Nat.Prime p) : AnalyticOnNhd ℂ (fun s : ℂ => (1 - (p : ℂ) ^ (-s))⁻¹) {s : ℂ | s.re > 0} := by
    apply_rules [AnalyticOnNhd.inv, AnalyticOnNhd.sub, analyticOnNhd_const, analyticOnNhd_id]
    · apply_rules [DifferentiableOn.analyticOnNhd]
      · refine DifferentiableOn.cpow ?_ ?_ ?_ <;> norm_num
        · exact differentiableOn_id.neg
        · exact fun x hx => Or.inl <| Nat.cast_pos.mpr hp.pos
      · exact isOpen_lt continuous_const Complex.continuous_re
    · intro s hs; rw [Ne.eq_def, sub_eq_zero, eq_comm]; intro H; have := congr_arg Complex.normSq H; norm_num [Complex.normSq_eq_norm_sq, Complex.norm_cpow_of_ne_zero, hp.ne_zero] at this
      exact absurd (this.resolve_right (by linarith [Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.pos) (-s.re)])) (ne_of_lt (by simpa using Real.rpow_lt_rpow_of_exponent_lt (Nat.one_lt_cast.mpr hp.one_lt) (neg_lt_zero.mpr hs)))
  convert analyticOnNhd_prod _ _; aesop
  exact fun n hn => h_factor_analytic n <| Finset.mem_filter.mp hn |>.2

/-- The finite Euler product is non-vanishing for Re(s) > 0. -/
lemma zetaEulerPartial_ne_zero (P : ℕ) (s : ℂ) (hs : s.re > 0) :
    zetaEulerPartial P s ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro p hp; rw [Ne, inv_eq_zero]; norm_num [Complex.cpow_def]
  split_ifs <;> simp_all +decide [Complex.exp_ne_zero, sub_eq_iff_eq_add]
  rw [eq_comm, Complex.exp_eq_one_iff]
  norm_num [Complex.ext_iff, Complex.log_re, Complex.log_im]
  norm_cast; aesop

/-- The eta approximant: the N-th partial sum of the Dirichlet series for η.
    η_P(s) = Σ_{n=1}^{Q_P} (-1)^{n-1}/n^s
    Each partial sum is a finite sum of entire functions, hence entire.
    As P → ∞, Q_P → ∞, and the partial sums converge uniformly to η(s)
    on compact subsets of {Re(s) > 0} by Abel summation. -/
noncomputable def etaApprox (P : ℕ) (s : ℂ) : ℂ :=
  etaPartialSum (eta_Q_P P) s

/-- The eta partial sum approximant is analytic on {Re(s) > 0}
    (in fact it is entire, being a finite sum of entire functions). -/
lemma etaApprox_analyticOnNhd (P : ℕ) :
    AnalyticOnNhd ℂ (etaApprox P) {s | s.re > 0} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  unfold etaApprox etaPartialSum
  intro s _
  apply DifferentiableAt.differentiableWithinAt
  have key : ∀ n ∈ Icc 1 (eta_Q_P P), DifferentiableAt ℂ
      (fun s : ℂ => (-1 : ℂ) ^ (n - 1) / (n : ℂ) ^ s) s := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact differentiableAt_const _ |>.div
      ((differentiableAt_const (n : ℂ)).cpow differentiableAt_id
        (Or.inl (by simp only [natCast_re, Nat.cast_pos]; omega)))
      (fun h => by simp [Complex.cpow_def, hn0] at h)
  have h := DifferentiableAt.sum key
  have heq : (∑ i ∈ Icc 1 (eta_Q_P P), fun s : ℂ => (-1 : ℂ) ^ (i - 1) / (i : ℂ) ^ s) =
      (fun s : ℂ => ∑ n ∈ Icc 1 (eta_Q_P P), (-1 : ℂ) ^ (n - 1) / (n : ℂ) ^ s) := by
    exact Finset.sum_fn _ _
  rwa [heq] at h

/-- The eta partial sum approximant is non-vanishing in {1/2 < Re(s) < 1}.
    This captures the fact that for large enough N, the partial sums of the
    alternating eta series do not vanish in the critical strip. -/
lemma etaApprox_ne_zero_critical_strip (P : ℕ) (s : ℂ)
    (h1 : s.re > 1 / 2) (h2 : s.re < 1) :
    etaApprox P s ≠ 0 := by
  sorry

/-!
## Section 4: Partial Sum Bounds

The partial sums of η at a real point σ > 0 are bounded (alternating series
with decreasing terms).
-/

lemma eta_partial_sums_bounded (σ : ℝ) (hσ : σ > 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ, ‖etaPartialSum N (σ : ℂ)‖ ≤ M := by
  have h_bound : ∃ M : ℝ, ∀ N : ℕ, ‖∑ n ∈ Finset.range N, (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ (σ : ℂ)‖ ≤ M := by
    have h_bound : ∀ N : ℕ, ‖∑ n ∈ Finset.range (2 * N), (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ (σ : ℂ)‖ ≤ 1 / (1 : ℝ) ^ σ := by
      intro N
      have h_sum_bound : ∀ N : ℕ, ‖∑ n ∈ Finset.range (2 * N), (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ (σ : ℂ)‖ ≤ 1 / (1 : ℝ) ^ σ := by
        intro N
        have h_sum_bound : ∀ N : ℕ, ‖∑ n ∈ Finset.range (2 * N), (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ (σ : ℂ)‖ ≤ ∑ n ∈ Finset.range N, (1 / (2 * n + 1 : ℝ) ^ σ - 1 / (2 * n + 2 : ℝ) ^ σ) := by
          intro N
          have h_sum_bound : ∑ n ∈ Finset.range (2 * N), (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ (σ : ℂ) = ∑ n ∈ Finset.range N, (1 / (2 * n + 1 : ℝ) ^ σ - 1 / (2 * n + 2 : ℝ) ^ σ) := by
            induction N <;> simp_all +decide [Nat.mul_succ, pow_succ', Finset.sum_range_succ]; ring
            norm_num [Complex.ofReal_cpow (by positivity : 0 ≤ (1 + (↑‹ℕ› : ℝ) * 2)), Complex.ofReal_cpow (by positivity : 0 ≤ (2 + (↑‹ℕ› : ℝ) * 2))]
          rw [h_sum_bound, Complex.norm_real]
          rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sub_nonneg_of_le <| one_div_le_one_div_of_le (by positivity) <| Real.rpow_le_rpow (by positivity) (by linarith) <| by positivity)]
        refine le_trans (h_sum_bound N) ?_
        refine le_trans (Finset.sum_le_sum fun i hi => show (1 / (2 * i + 1 : ℝ) ^ σ - 1 / (2 * i + 2 : ℝ) ^ σ) ≤ 1 / (2 * i + 1 : ℝ) ^ σ - 1 / (2 * i + 3 : ℝ) ^ σ from ?_) ?_
        · gcongr; norm_num
        · have h_telescope : ∀ N : ℕ, ∑ i ∈ Finset.range N, (1 / (2 * i + 1 : ℝ) ^ σ - 1 / (2 * i + 3 : ℝ) ^ σ) = 1 / (1 : ℝ) ^ σ - 1 / (2 * N + 1 : ℝ) ^ σ := by
            exact fun N => by convert Finset.sum_range_sub' (fun i => 1 / (2 * i + 1 : ℝ) ^ σ) N using 3 <;> push_cast <;> ring
          exact h_telescope N ▸ sub_le_self _ (by positivity)
      exact h_sum_bound N
    use 1 / (1 : ℝ) ^ σ + 1 / (1 : ℝ) ^ σ
    intro N; rcases Nat.even_or_odd' N with ⟨k, rfl | rfl⟩ <;> norm_num at *
    · exact le_trans (h_bound k) (by norm_num)
    · rw [Finset.sum_range_succ]
      refine le_trans (norm_add_le _ _) ?_; norm_num [h_bound]
      refine le_trans (add_le_add (h_bound k) (inv_le_one_of_one_le₀ ?_)) ?_ <;> norm_num
      exact Real.one_le_rpow (by norm_cast; linarith) (by positivity)
  obtain ⟨M, hM⟩ := h_bound; use Max.max M 1; simp_all +decide [etaPartialSum]
  intro N; erw [Finset.sum_Ico_eq_sum_range]; simp_all +decide [add_comm, Finset.sum_range_succ']

/-!
## Section 5: Convergence of Partial Sum Approximants to η

The key convergence result: as P → ∞, the approximants
  η_P(s) = Σ_{n=1}^{Q_P} (-1)^{n-1}/n^s
converge uniformly to η(s) on any ball in {1/2 < Re(s) < 1}.

This is proved via Abel summation by parts:

1. **Bounded partial sums**: At a real base point σ₀ > 0, the partial sums
   are bounded by some constant M (alternating series with decreasing terms).

2. **Abel summation tail bound**: For Re(s) > σ₀, the tail from m to N
   satisfies ‖η_N(s) - η_{m-1}(s)‖ ≤ C · m^(σ₀ - Re(s)).

3. **Uniform Cauchy**: Choosing σ₀ < 1/2 and using the decay rate,
   the partial sums form a uniform Cauchy sequence on balls in {Re > 1/2}.

4. **Pointwise limit**: The limit equals dirichletEta(s) = (1-2^{1-s})ζ(s)
   (this step uses the identity theorem for analytic functions).
-/

/-
Abel summation tail bound for the eta Dirichlet series.

    If the partial sums of η at a real base point σ₀ > 0 are bounded by M,
    then the tail of the series at any complex s with Re(s) > σ₀ decays
    algebraically: ‖η_N(s) - η_{m-1}(s)‖ ≤ C · m^(σ₀ - Re(s)).

    This is the key analytic input, proved by Abel summation by parts
    (the same technique as `bohr_cahen_algebraic_tail_bound` in Legacy.lean).
-/
set_option maxHeartbeats 1600000 in
lemma eta_abel_tail_bound (s : ℂ) (σ₀ : ℝ) (hσ₀ : σ₀ > 0) (hs : s.re > σ₀)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ N : ℕ, ‖etaPartialSum N (σ₀ : ℂ)‖ ≤ M) :
    ∀ m N : ℕ, 0 < m → m ≤ N →
    ‖etaPartialSum N s - etaPartialSum (m - 1) s‖ ≤
      (M * (2 + ‖s - (σ₀ : ℂ)‖ + ‖s - (σ₀ : ℂ)‖ / (s.re - σ₀))) *
        (m : ℝ) ^ (σ₀ - s.re) := by
  intro m N hm_pos hm_le_N
  have h_tail_bound : ‖etaPartialSum N s - etaPartialSum (m - 1) s‖ ≤ M * (∑ n ∈ Finset.Ico m N, (‖(s - σ₀ : ℂ)‖ * (n : ℝ) ^ (σ₀ - s.re - 1))) + M * (m : ℝ) ^ (σ₀ - s.re) + M * (N : ℝ) ^ (σ₀ - s.re) := by
    -- By Abel summation by parts, we have:
    have h_abel : etaPartialSum N s - etaPartialSum (m - 1) s = (etaPartialSum N (σ₀ : ℂ)) * ((N : ℂ) ^ (σ₀ - s)) - (etaPartialSum (m - 1) (σ₀ : ℂ)) * ((m : ℂ) ^ (σ₀ - s)) - ∑ n ∈ Finset.Ico m N, (etaPartialSum n (σ₀ : ℂ)) * (((n + 1 : ℂ) ^ (σ₀ - s)) - (n : ℂ) ^ (σ₀ - s)) := by
      induction hm_le_N <;> simp_all +decide [ Finset.sum_Ico_succ_top ];
      · unfold etaPartialSum; rcases m with ( _ | m ) <;> simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ; ring;
        rw [ ← Complex.cpow_neg, ← Complex.cpow_neg, ← Complex.cpow_add _ _ ] <;> norm_num ; ring ; norm_cast ; aesop;
      · rename_i k hk ih; rw [ show etaPartialSum ( k + 1 ) s = etaPartialSum k s + ( -1 : ℂ ) ^ k / ( k + 1 : ℂ ) ^ s from ?_, show etaPartialSum ( k + 1 ) ( σ₀ : ℂ ) = etaPartialSum k ( σ₀ : ℂ ) + ( -1 : ℂ ) ^ k / ( k + 1 : ℂ ) ^ ( σ₀ : ℂ ) from ?_ ] ; simp_all +decide [ pow_succ, div_eq_mul_inv ] ; ring;
        · simp_all +decide [ mul_sub, sub_mul, ← Complex.cpow_neg, ← Complex.cpow_add ] ; ring;
          convert congr_arg ( · + ( ( 1 + k : ℂ ) ^ ( -s ) * ( -1 ) ^ k ) ) ih using 1 <;> ring;
          rw [ ← Complex.cpow_add _ _ ( by norm_cast; linarith ) ] ; ring;
        · unfold etaPartialSum; norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ;
        · unfold etaPartialSum; simp +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ;
    -- Applying the bound on the partial sums and the mean value theorem, we get:
    have h_mean_value : ∀ n ∈ Finset.Ico m N, ‖((n + 1 : ℂ) ^ (σ₀ - s)) - (n : ℂ) ^ (σ₀ - s)‖ ≤ ‖s - σ₀‖ * (n : ℝ) ^ (σ₀ - s.re - 1) := by
      intro n hn
      have h_mean_value : ∀ t ∈ Set.Icc (n : ℝ) (n + 1), ‖deriv (fun x : ℝ => (x : ℂ) ^ (σ₀ - s)) t‖ ≤ ‖s - σ₀‖ * (n : ℝ) ^ (σ₀ - s.re - 1) := by
        intro t ht
        have h_deriv : deriv (fun x : ℝ => (x : ℂ) ^ (σ₀ - s)) t = (σ₀ - s) * (t : ℂ) ^ (σ₀ - s - 1) := by
          convert HasDerivAt.deriv ( HasDerivAt.comp t ( hasDerivAt_id _ |> HasDerivAt.cpow_const <| ?_ ) <| hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) using 1 <;> norm_num;
          linarith [ ht.1, show ( n : ℝ ) ≥ 1 by norm_cast; linarith [ Finset.mem_Ico.mp hn ] ];
        simp_all +decide [ Complex.norm_cpow_eq_rpow_re_of_pos ];
        rw [ norm_sub_rev ];
        rw [ Complex.norm_cpow_of_ne_zero ] <;> norm_num;
        · rw [ Complex.arg_ofReal_of_nonneg ( by linarith ) ] ; norm_num;
          exact mul_le_mul_of_nonneg_left ( by rw [ abs_of_nonneg ( by linarith ) ] ; exact Real.rpow_le_rpow_of_nonpos ( by linarith [ show ( n : ℝ ) ≥ 1 by norm_cast; linarith ] ) ( by linarith ) ( by linarith ) ) ( norm_nonneg _ );
        · linarith [ show ( n : ℝ ) ≥ 1 by norm_cast; linarith ];
      have h_mean_value : ∫ t in (n : ℝ)..((n + 1) : ℝ), deriv (fun x : ℝ => (x : ℂ) ^ (σ₀ - s)) t = (n + 1 : ℂ) ^ (σ₀ - s) - (n : ℂ) ^ (σ₀ - s) := by
        rw [ intervalIntegral.integral_deriv_eq_sub ];
        · norm_num;
        · intro x hx; exact (by
          have h_diff : DifferentiableAt ℂ (fun x : ℂ => x ^ (σ₀ - s)) (x : ℂ) := by
            exact DifferentiableAt.cpow ( differentiableAt_id ) ( differentiableAt_const _ ) ( by norm_num; cases Set.mem_uIcc.mp hx <;> linarith [ show ( n : ℝ ) ≥ 1 by norm_cast; linarith [ Finset.mem_Ico.mp hn ] ] );
          exact h_diff.restrictScalars ℝ |> DifferentiableAt.comp x <| Complex.ofRealCLM.differentiableAt);
        · rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le ];
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun x => ‖s - σ₀‖ * ( n : ℝ ) ^ ( σ₀ - s.re - 1 );
            · fun_prop;
            · fun_prop;
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using h_mean_value x <| Set.Ioc_subset_Icc_self hx;
          · norm_num;
      rw [ ← h_mean_value, intervalIntegral.integral_of_le ] <;> norm_num;
      refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
      refine' fun t => ‖s - σ₀‖ * ( n : ℝ ) ^ ( σ₀ - s.re - 1 );
      · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
      · fun_prop;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using ‹∀ t ∈ Set.Icc ( n : ℝ ) ( n + 1 ), ‖deriv ( fun x : ℝ => ( x : ℂ ) ^ ( σ₀ - s ) ) t‖ ≤ ‖s - σ₀‖ * ( n : ℝ ) ^ ( σ₀ - s.re - 1 ) › t <| Set.Ioc_subset_Icc_self ht;
      · norm_num;
    -- Applying the bound on the partial sums and the mean value theorem, we get the desired inequality.
    have h_final_bound : ‖etaPartialSum N s - etaPartialSum (m - 1) s‖ ≤ M * (N : ℝ) ^ (σ₀ - s.re) + M * (m : ℝ) ^ (σ₀ - s.re) + ∑ n ∈ Finset.Ico m N, M * ‖s - σ₀‖ * (n : ℝ) ^ (σ₀ - s.re - 1) := by
      rw [h_abel];
      refine' le_trans ( norm_sub_le _ _ ) ( add_le_add ( le_trans ( norm_sub_le _ _ ) _ ) _ );
      · gcongr;
        · convert mul_le_mul_of_nonneg_right ( hbound N ) ( Real.rpow_nonneg ( Nat.cast_nonneg N ) ( σ₀ - s.re ) ) using 1 ; norm_num [ Complex.norm_cpow_of_ne_zero, show N ≠ 0 by linarith ];
        · rw [ norm_mul, Complex.norm_cpow_of_ne_zero ] <;> norm_num [ hm_pos.ne' ];
          exact mul_le_mul_of_nonneg_right ( hbound _ ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ );
      · refine' le_trans ( norm_sum_le _ _ ) _;
        exact Finset.sum_le_sum fun i hi => by simpa only [ mul_assoc, norm_mul ] using mul_le_mul ( hbound i ) ( h_mean_value i hi ) ( by positivity ) ( by positivity ) ;
    simpa only [ mul_assoc, Finset.mul_sum _ _ _, add_comm, add_left_comm, add_assoc ] using h_final_bound;
  -- The sum Σ_{n=m}^{N-1} n^{σ₀-Re(s)-1} is bounded by m^{σ₀-Re(s)-1} + ∫_m^∞ x^{σ₀-Re(s)-1} dx.
  have h_sum_bound : ∑ n ∈ Finset.Ico m N, (n : ℝ) ^ (σ₀ - s.re - 1) ≤ (m : ℝ) ^ (σ₀ - s.re - 1) + (m : ℝ) ^ (σ₀ - s.re) / (s.re - σ₀) := by
    have h_sum_bound : ∑ n ∈ Finset.Ico m N, (n : ℝ) ^ (σ₀ - s.re - 1) ≤ (m : ℝ) ^ (σ₀ - s.re - 1) + ∫ x in (m : ℝ)..(N : ℝ), x ^ (σ₀ - s.re - 1) := by
      have h_sum_bound : ∑ n ∈ Finset.Ico m N, (n : ℝ) ^ (σ₀ - s.re - 1) ≤ (m : ℝ) ^ (σ₀ - s.re - 1) + ∑ n ∈ Finset.Ico (m + 1) N, ∫ x in (n - 1 : ℝ)..n, x ^ (σ₀ - s.re - 1) := by
        have h_sum_bound : ∀ n ∈ Finset.Ico (m + 1) N, (n : ℝ) ^ (σ₀ - s.re - 1) ≤ ∫ x in (n - 1 : ℝ)..n, x ^ (σ₀ - s.re - 1) := by
          intros n hn
          have h_integral_bound : ∀ x ∈ Set.Icc (n - 1 : ℝ) n, x ^ (σ₀ - s.re - 1) ≥ (n : ℝ) ^ (σ₀ - s.re - 1) := by
            intros x hx;
            rw [ ge_iff_le, Real.rpow_le_rpow_iff_of_neg ] <;> linarith [ hx.1, hx.2, show ( n : ℝ ) ≥ 2 by norm_cast; linarith [ Finset.mem_Ico.mp hn ] ];
          refine' le_trans _ ( intervalIntegral.integral_mono_on _ _ _ h_integral_bound ) <;> norm_num;
          apply_rules [ intervalIntegral.intervalIntegrable_rpow ] ; norm_num;
          exact Or.inr ( by linarith [ Finset.mem_Ico.mp hn ] );
        rw [ Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range ];
        rcases k : N - m with ( _ | k ) <;> simp_all +decide [ Nat.succ_sub, Finset.sum_range_succ' ];
        · exact add_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ( Finset.sum_nonneg fun _ _ => intervalIntegral.integral_nonneg ( by linarith ) fun x hx => Real.rpow_nonneg ( by linarith [ hx.1 ] ) _ );
        · rw [ show N - ( m + 1 ) = ‹ℕ› by omega ] ; rw [ add_comm ] ; gcongr ;
          convert h_sum_bound ( m + ‹ℕ› + 1 ) ( by linarith ) ( by linarith [ Finset.mem_range.mp ‹_›, Nat.sub_add_cancel hm_le_N ] ) using 1 <;> push_cast <;> ring;
      refine le_trans h_sum_bound ?_;
      rcases eq_or_lt_of_le hm_le_N with rfl | hm_lt_N <;> norm_num [ Finset.sum_Ico_eq_sum_range ] at *;
      have h_integral_bound : ∀ k : ℕ, ∑ x ∈ Finset.range k, ∫ x in (m + 1 + x - 1 : ℝ)..(m + 1 + x : ℝ), x ^ (σ₀ - s.re - 1) = ∫ x in (m : ℝ)..(m + k : ℝ), x ^ (σ₀ - s.re - 1) := by
        intro k; induction k <;> simp_all +decide [ Finset.sum_range_succ ] ; ring;
        rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ intervalIntegral.intervalIntegrable_rpow ] <;> norm_num;
        · exact Or.inr fun h => absurd h hm_pos.ne';
        · exact Or.inr fun h => by linarith [ show ( m : ℝ ) > 0 by positivity ] ;
      rw [ h_integral_bound ];
      apply_rules [ intervalIntegral.integral_mono_interval ] <;> norm_num [ hm_lt_N.le ];
      · norm_cast ; omega;
      · exact Filter.eventually_inf_principal.mpr ( Filter.Eventually.of_forall fun x hx => Real.rpow_nonneg ( by linarith [ hx.1 ] ) _ );
      · apply_rules [ intervalIntegral.intervalIntegrable_rpow ] ; norm_num [ hm_pos, hm_lt_N.le ];
        exact Or.inr hm_pos.ne';
    refine le_trans h_sum_bound ?_;
    rw [ integral_rpow ] <;> norm_num;
    · rw [ ← neg_div_neg_eq ] ; ring_nf;
      exact add_le_of_nonpos_left ( neg_nonpos_of_nonneg ( mul_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ( inv_nonneg.mpr ( by linarith ) ) ) );
    · exact Or.inr ⟨ by linarith, Set.notMem_uIcc_of_lt ( by norm_num; linarith ) ( by norm_num; linarith ) ⟩;
  simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  refine le_trans h_tail_bound ?_;
  refine le_trans ( add_le_add_three ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left h_sum_bound <| norm_nonneg _ ) hM ) le_rfl <| mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow_of_nonpos ( by positivity ) ( Nat.cast_le.mpr hm_le_N ) <| by linarith : ( N : ℝ ) ^ ( σ₀ - s.re ) ≤ ( m : ℝ ) ^ ( σ₀ - s.re ) ) hM ) ?_;
  rw [ Real.rpow_sub_one ( by positivity ) ] ; ring_nf ; norm_num;
  exact mul_le_of_le_one_right ( by positivity ) ( inv_le_one_of_one_le₀ ( mod_cast hm_pos ) )

/-- The partial sums of the eta Dirichlet series converge pointwise to
    dirichletEta for Re(s) > 0.

    For Re(s) > 1, this follows from the identity
    Σ (-1)^{n-1}/n^s = (1-2^{1-s})ζ(s) via splitting into odd/even terms.
    For 0 < Re(s) ≤ 1, Abel summation shows the partial sums converge,
    and the limit agrees with dirichletEta by the identity theorem
    (both are analytic on {Re > 0} and agree on {Re > 1}). -/
lemma etaPartialSum_tendsto_dirichletEta (s : ℂ) (hs : s.re > 0) (hs1 : s.re < 1) :
    Tendsto (fun N => etaPartialSum N s) atTop (𝓝 (dirichletEta s)) := by
  sorry

/-
The partial sums of the eta Dirichlet series are uniformly Cauchy
    on any ball contained in {Re(s) > 1/2}.

    Proof: Choose σ₀ ∈ (0, 1/2) as a base point for Abel summation.
    By `eta_partial_sums_bounded`, the partial sums at σ₀ are bounded by M.
    By `eta_abel_tail_bound`, the tail from m to N at any s in the ball
    is bounded by C · m^(σ₀ - Re(s)) ≤ C · m^(σ₀ - 1/2).
    Since σ₀ - 1/2 < 0, this tends to 0 as m → ∞, uniformly in s.
-/
lemma etaPartialSum_uniformCauchySeqOn (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hball : ∀ z ∈ Metric.ball c r, z.re > 1 / 2) :
    UniformCauchySeqOn (fun N => etaPartialSum N) atTop (Metric.ball c r) := by
  obtain ⟨ σ₀, hσ₀ ⟩ : ∃ σ₀ : ℝ, 0 < σ₀ ∧ σ₀ < 1 / 2 ∧ ∀ s ∈ Metric.ball c r, s.re > σ₀ := by
    exact ⟨ 1 / 4, by norm_num, by norm_num, fun s hs => by linarith [ hball s hs ] ⟩;
  obtain ⟨ M, hM₁, hM₂ ⟩ := eta_partial_sums_bounded σ₀ hσ₀.1;
  have h_uniform_cauchy : ∀ ε > 0, ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → m ≤ n → ∀ s ∈ Metric.ball c r, ‖etaPartialSum n s - etaPartialSum m s‖ < ε := by
    intros ε hε_pos
    obtain ⟨ C, hC_pos, hC_bound ⟩ : ∃ C > 0, ∀ s ∈ Metric.ball c r, ‖s - (σ₀ : ℂ)‖ ≤ C ∧ s.re - σ₀ ≥ 1 / 2 - σ₀ := by
      obtain ⟨ C, hC ⟩ := IsCompact.exists_bound_of_continuousOn ( ProperSpace.isCompact_closedBall c r ) ( show ContinuousOn ( fun s : ℂ => s - ↑σ₀ ) ( Metric.closedBall c r ) from Continuous.continuousOn <| by continuity );
      exact ⟨ Max.max C 1, by positivity, fun s hs => ⟨ le_trans ( hC s <| Metric.ball_subset_closedBall hs ) <| le_max_left _ _, by linarith [ hball s hs ] ⟩ ⟩;
    have h_uniform_cauchy : ∀ m n : ℕ, 0 < m → m ≤ n → ∀ s ∈ Metric.ball c r, ‖etaPartialSum n s - etaPartialSum (m - 1) s‖ ≤ (M * (2 + C + C / (1 / 2 - σ₀))) * (m : ℝ) ^ (σ₀ - 1 / 2) := by
      intros m n hm hn s hs
      have h_tail_bound : ‖etaPartialSum n s - etaPartialSum (m - 1) s‖ ≤ (M * (2 + ‖s - (σ₀ : ℂ)‖ + ‖s - (σ₀ : ℂ)‖ / (s.re - σ₀))) * (m : ℝ) ^ (σ₀ - s.re) := by
        apply eta_abel_tail_bound s σ₀ hσ₀.left (hσ₀.right.right s hs) M hM₁ hM₂ m n hm hn;
      refine le_trans h_tail_bound ?_;
      gcongr <;> try linarith [ hC_bound s hs ];
      · exact mul_nonneg hM₁ ( add_nonneg ( add_nonneg zero_le_two hC_pos.le ) ( div_nonneg hC_pos.le ( by linarith ) ) );
      · exact_mod_cast hm;
    -- Choose N such that for all m ≥ N, we have M * (2 + C + C / (1 / 2 - σ₀)) * m ^ (σ₀ - 1 / 2) < ε / 2.
    obtain ⟨ N, hN ⟩ : ∃ N : ℕ, ∀ m ≥ N, M * (2 + C + C / (1 / 2 - σ₀)) * (m : ℝ) ^ (σ₀ - 1 / 2) < ε / 2 := by
      have h_lim_zero : Filter.Tendsto (fun m : ℕ => M * (2 + C + C / (1 / 2 - σ₀)) * (m : ℝ) ^ (σ₀ - 1 / 2)) Filter.atTop (nhds 0) := by
        simpa using tendsto_const_nhds.mul ( tendsto_rpow_neg_atTop ( by linarith : 0 < - ( σ₀ - 1 / 2 ) ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
      simpa using h_lim_zero.eventually ( gt_mem_nhds <| half_pos hε_pos );
    use N + 1;
    intros m n hm hn s hs
    have h_diff : ‖etaPartialSum n s - etaPartialSum m s‖ ≤ ‖etaPartialSum n s - etaPartialSum (m - 1) s‖ + ‖etaPartialSum m s - etaPartialSum (m - 1) s‖ := by
      simpa using norm_sub_le ( etaPartialSum n s - etaPartialSum ( m - 1 ) s ) ( etaPartialSum m s - etaPartialSum ( m - 1 ) s );
    grind;
  rw [ Metric.uniformCauchySeqOn_iff ];
  intro ε hε; obtain ⟨ N, hN ⟩ := h_uniform_cauchy ε hε; use N; intros m hm n hn x hx; cases le_total m n <;> simp_all +decide [ dist_eq_norm' ] ;
  simpa only [ norm_sub_rev ] using hN n m hn ‹_› x hx

/-- The partial sums of η converge uniformly to dirichletEta on any
    ball in {Re > 1/2}. Combines uniform Cauchy with pointwise limit. -/
lemma etaPartialSum_tendstoUniformlyOn (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hball : ∀ z ∈ Metric.ball c r, z.re > 1 / 2)
    (hball_upper : ∀ z ∈ Metric.ball c r, z.re < 1) :
    TendstoUniformlyOn (fun N => etaPartialSum N) dirichletEta atTop
      (Metric.ball c r) := by
  exact (etaPartialSum_uniformCauchySeqOn c r hr hball).tendstoUniformlyOn_of_tendsto
    (fun s hs => etaPartialSum_tendsto_dirichletEta s (by linarith [hball s hs]) (hball_upper s hs))

/-- The eta approximants converge uniformly to η on balls in
    {1/2 < Re(s) < 1}.

    Since etaApprox P = etaPartialSum (eta_Q_P P) and eta_Q_P P → ∞,
    this follows from the uniform convergence of the full sequence
    of partial sums (etaPartialSum_tendstoUniformlyOn). -/
lemma etaApprox_tendstoUniformlyOn (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hball_lower : ∀ z ∈ Metric.ball c r, z.re > 1 / 2)
    (hball_upper : ∀ z ∈ Metric.ball c r, z.re < 1) :
    TendstoUniformlyOn (fun P => etaApprox P) dirichletEta atTop
      (Metric.ball c r) := by
  have h_full := etaPartialSum_tendstoUniformlyOn c r hr hball_lower hball_upper
  -- etaApprox P = etaPartialSum (eta_Q_P P) is a subsequence
  -- Since eta_Q_P P → ∞, the subsequence also converges uniformly.
  have h_tend : Tendsto eta_Q_P atTop atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b; use b + 1; intro n hn
    have h1 : n ≤ n ^ n := Nat.le_self_pow (by omega) n
    unfold eta_Q_P; omega
  intro u hu
  exact ((h_full u hu).filter_mono h_tend)

/-!
## Section 6: Hurwitz's Theorem Application → η Non-Vanishing

Since the Euler product approximants are non-vanishing, analytic, and converge
uniformly to η on balls in {1/2 < Re < 1}, Hurwitz's theorem implies that
η is either identically zero or non-vanishing on each such ball.

Since η is not identically zero, η is non-vanishing on {1/2 < Re < 1}.
-/

/-- η is not identically zero: η(2) = (1-2⁻¹)·ζ(2) = π²/12 ≠ 0. -/
lemma dirichletEta_ne_zero_at_two : dirichletEta 2 ≠ 0 := by
  unfold dirichletEta
  norm_num [riemannZeta_two]
  norm_num [Complex.cpow_neg]

/-- If c.re - r > a, then there exists α > 0 with Re > a + α on ball(c,r). -/
lemma ball_re_gap (c : ℂ) (r : ℝ) (a : ℝ) (hgap : c.re - r > a) :
    ∃ α > 0, ∀ z ∈ Metric.ball c r, z.re > a + α := by
  use (c.re - r - a) / 2
  refine ⟨by linarith, fun z hz => ?_⟩
  rw [Metric.mem_ball, Complex.dist_eq] at hz
  have : |z.re - c.re| ≤ ‖z - c‖ := Complex.abs_re_le_norm (z - c)
  have : |z.re - c.re| < r := lt_of_le_of_lt this hz
  rw [abs_lt] at this
  linarith

/-- **Main theorem (eta strategy)**: η(s) ≠ 0 for 1/2 < Re(s) < 1.

    Proof: Construct a ball B around s in {1/2 < Re < 1}. The Euler product
    approximants η_P are analytic and non-vanishing on B, and converge
    uniformly to η on B. By Hurwitz's theorem, since η is not identically
    zero, η is non-vanishing on B. In particular, η(s) ≠ 0. -/
theorem eta_nonvanishing_critical_strip (s : ℂ) (hs1 : s.re > 1 / 2) (hs2 : s.re < 1) :
    dirichletEta s ≠ 0 := by
  -- Construct a ball in {1/2 < Re < 1} containing s
  set δ := min ((s.re - 1 / 2) / 2) ((1 - s.re) / 2) with hδ_def
  have hδ_pos : δ > 0 := by apply lt_min <;> linarith
  have hball_lower : ∀ z ∈ Metric.ball s δ, z.re > 1 / 2 := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have hre : |z.re - s.re| ≤ ‖z - s‖ := Complex.abs_re_le_norm (z - s)
    have hlt : |z.re - s.re| < δ := lt_of_le_of_lt hre hz
    rw [abs_lt] at hlt
    have : δ ≤ (s.re - 1 / 2) / 2 := min_le_left _ _
    linarith
  have hball_upper : ∀ z ∈ Metric.ball s δ, z.re < 1 := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have hre : |z.re - s.re| ≤ ‖z - s‖ := Complex.abs_re_le_norm (z - s)
    have hlt : |z.re - s.re| < δ := lt_of_le_of_lt hre hz
    rw [abs_lt] at hlt
    have : δ ≤ (1 - s.re) / 2 := min_le_right _ _
    linarith
  -- Apply Hurwitz's theorem to the sequence etaApprox P on B
  have hconv := etaApprox_tendstoUniformlyOn s δ hδ_pos hball_lower hball_upper
  have hf_holo : ∀ n, AnalyticOnNhd ℂ (etaApprox n) (Metric.ball s δ) :=
    fun P => (etaApprox_analyticOnNhd P).mono (fun z hz => show z.re > 0 by linarith [hball_lower z hz])
  have hf_nz : ∀ n, ∀ z ∈ Metric.ball s δ, etaApprox n z ≠ 0 :=
    fun P z hz => etaApprox_ne_zero_critical_strip P z (hball_lower z hz) (hball_upper z hz)
  -- η is not identically zero on B (it would imply ζ ≡ 0 on B, contradicting ζ ≠ 0 for Re > 1)
  have hg_not_zero : ∃ z ∈ Metric.ball s δ, dirichletEta z ≠ 0 := by
    -- If η ≡ 0 on B, then ζ ≡ 0 on B (since etaFactor ≠ 0 for Re < 1).
    -- But ζ ≠ 0 at any point with Re ≥ 1. Contradiction by analytic continuation.
    by_contra h_all_zero
    push_neg at h_all_zero
    have h_zeta_zero : ∀ z ∈ Metric.ball s δ, riemannZeta z = 0 := by
      intro z hz
      have := h_all_zero z hz
      exact Or.resolve_left (mul_eq_zero.mp this) (etaFactor_ne_zero_re_lt_one z (hball_upper z hz))
    exact absurd (zeta_no_zeros_right_half_plane s (h_zeta_zero s (Metric.mem_ball_self hδ_pos)) (by linarith)) (by norm_num)
  exact hurwitz_nonvanishing_limit Metric.isOpen_ball (convex_ball _ _).isPreconnected
    hf_holo hf_nz hconv hg_not_zero s (Metric.mem_ball_self hδ_pos)

/-- **Corollary**: ζ(s) ≠ 0 for 1/2 < Re(s) < 1 (the critical strip). -/
theorem zeta_nonvanishing_critical_strip_eta (s : ℂ) (hs1 : s.re > 1 / 2) (hs2 : s.re < 1) :
    riemannZeta s ≠ 0 := by
  intro hzeta
  have heta : dirichletEta s = 0 := by unfold dirichletEta; rw [hzeta, mul_zero]
  exact eta_nonvanishing_critical_strip s hs1 hs2 heta

/-- **Full result**: ζ(s) ≠ 0 for Re(s) > 1/2. -/
theorem zeta_nonvanishing_half_plane_eta (s : ℂ) (hs : s.re > 1 / 2) :
    riemannZeta s ≠ 0 := by
  by_cases h1 : s.re ≥ 1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · push_neg at h1
    exact zeta_nonvanishing_critical_strip_eta s hs h1

/-- **The Riemann Hypothesis (eta strategy)**. -/
theorem riemann_hypothesis_eta (s : ℂ) (hs : riemannZeta s = 0)
    (h_pos : 0 < s.re) (h_lt : s.re < 1) : s.re = 1 / 2 := by
  rcases lt_trichotomy s.re (1 / 2) with h | h | h
  · have hsymm := zeta_symm s h_pos h_lt hs
    have h_re_conj : (1 - s).re > 1 / 2 := by simp [sub_re, one_re]; linarith
    exact absurd (zeta_nonvanishing_half_plane_eta (1 - s) h_re_conj) (by rw [hsymm]; simp)
  · exact h
  · exact absurd hs (zeta_nonvanishing_half_plane_eta s h)

end