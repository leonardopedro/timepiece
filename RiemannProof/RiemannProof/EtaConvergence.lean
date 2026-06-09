import Mathlib
import RiemannProof.EtaStrategy

/-!
# Uniform convergence of Dirichlet eta partial sums

We prove that the partial sums η_n(s) = ∑_{k=1}^n (-1)^{k-1}/k^s converge
uniformly to η(s) = (1 - 2^{1-s})ζ(s) on compact subsets of {1/2 < Re(s) < 1}.

The proof uses:
1. Weierstrass M-test on paired terms to get absolute/uniform convergence
2. Algebraic identification of the limit for Re > 1
3. The identity theorem to extend to Re < 1
-/

open Complex Finset Filter Topology
open scoped ArithmeticFunction

noncomputable section

/-- Partial sum of the Dirichlet eta function: η_n(s) = Σ_{k=1}^n (-1)^{k-1}/k^s -/
noncomputable def etaPartial' (n : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Icc 1 n, (-1 : ℂ) ^ (k - 1) / (k : ℂ) ^ s

-- dirichletEta is imported from EtaStrategy.lean: (1 - 2^(1-s)) * riemannZeta s

/-!
## Step 1: Paired sum and Weierstrass M-test

We pair consecutive terms: f_j(s) = 1/(2j+1)^s - 1/(2j+2)^s.
Each |f_j(s)| ≤ C · (2j+1)^{-σ-1} for σ = Re(s), so the sum converges
absolutely and uniformly on compact sets with Re > 0.
-/

/-- The j-th paired term of the eta series (0-indexed). -/
noncomputable def etaPairedTerm (j : ℕ) (s : ℂ) : ℂ :=
  1 / ((2 * (j : ℂ) + 1) ^ s) - 1 / ((2 * (j : ℂ) + 2) ^ s)

/-
The even partial sum η_{2m}(s) equals the sum of paired terms.
-/
lemma etaPartial'_even_eq_paired_sum (m : ℕ) (s : ℂ) :
    etaPartial' (2 * m) s = ∑ j ∈ Finset.range m, etaPairedTerm j s := by
  induction m <;> simp_all +decide [ Nat.mul_succ, Finset.sum_range_succ ];
  · exact Finset.sum_empty;
  · unfold etaPartial' at *; simp_all +decide [ Nat.mul_succ, Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ;
    unfold etaPairedTerm; norm_num [ pow_succ' ] ; ring;

/-
Bound on the norm of each paired term.
-/
lemma norm_etaPairedTerm_le (j : ℕ) (s : ℂ) (hσ : s.re > 1 / 2) :
    ‖etaPairedTerm j s‖ ≤ (‖s‖ + 1) / (2 * (j : ℝ) + 1) ^ (s.re + 1) := by
  -- By the integral bound, we have |1/(2j+1)^s - 1/(2j+2)^s| ≤ ∫_{2j+1}^{2j+2} |s| · t^{-σ-1} dt.
  have h_integral_bound : ‖etaPairedTerm j s‖ ≤ ‖s‖ * ∫ t in (2 * j + 1 : ℝ).. (2 * j + 2 : ℝ), t ^ (-s.re - 1) := by
    -- By the fundamental theorem of calculus, we can write the difference as an integral.
    have h_ftc : etaPairedTerm j s = ∫ t in (2 * j + 1 : ℝ).. (2 * j + 2 : ℝ), s * t ^ (-s - 1 : ℂ) := by
      rw [ intervalIntegral.integral_const_mul, integral_cpow ] <;> norm_num;
      · unfold etaPairedTerm; ring;
        by_cases hs : s = 0 <;> simp_all +decide [ mul_comm s, Complex.cpow_neg ] ; ring;
      · exact Or.inr ⟨ by rintro rfl; norm_num at hσ, by intros; linarith ⟩;
    norm_num [ h_ftc, intervalIntegral.integral_of_le ];
    convert MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℂ ) using 1;
    rw [ ← MeasureTheory.integral_const_mul ] ; refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => _ ; norm_num [ Complex.norm_cpow_eq_rpow_re_of_pos ( show 0 < x by linarith [ hx.1 ] ) ] ;
  -- Evaluate the integral $\int_{2j+1}^{2j+2} t^{-s.re-1} dt$.
  have h_integral_eval : ∫ t in (2 * j + 1 : ℝ).. (2 * j + 2 : ℝ), t ^ (-s.re - 1) ≤ 1 / (2 * j + 1 : ℝ) ^ (s.re + 1) := by
    -- Since $t^{-s.re-1}$ is decreasing, we have $\int_{2j+1}^{2j+2} t^{-s.re-1} dt \leq \int_{2j+1}^{2j+2} (2j+1)^{-s.re-1} dt$.
    have h_integral_le : ∫ t in (2 * j + 1 : ℝ).. (2 * j + 2 : ℝ), t ^ (-s.re - 1) ≤ ∫ t in (2 * j + 1 : ℝ).. (2 * j + 2 : ℝ), (2 * j + 1 : ℝ) ^ (-s.re - 1) := by
      refine' intervalIntegral.integral_mono_on _ _ _ _ <;> norm_num;
      · apply_rules [ intervalIntegral.intervalIntegrable_rpow ] ; norm_num;
        exact Or.inr fun h => by linarith;
      · intro x hx₁ hx₂; rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith;
    convert h_integral_le using 1 ; norm_num [ Real.rpow_add, Real.rpow_neg ( by positivity : 0 ≤ ( 2 * j + 1 : ℝ ) ) ] ; ring;
    rw [ ← Real.rpow_neg ( by positivity ) ] ; ring;
  refine le_trans h_integral_bound <| le_trans ( mul_le_mul_of_nonneg_left h_integral_eval <| norm_nonneg _ ) ?_ ; ring_nf;
  exact le_add_of_nonneg_right ( by positivity )

/-
The paired sum converges absolutely for Re(s) > 1/2.
-/
lemma summable_etaPairedTerm (s : ℂ) (hσ : s.re > 1 / 2) :
    Summable (fun j : ℕ => etaPairedTerm j s) := by
  refine' .of_norm <| Summable.of_nonneg_of_le ( fun j => norm_nonneg _ ) ( fun j => norm_etaPairedTerm_le j s hσ ) _;
  exact Summable.mul_left _ <| by exact_mod_cast Summable.comp_injective ( Real.summable_nat_rpow_inv.2 <| by linarith ) fun x y h => by simpa using h;

/-
The paired sum converges uniformly on compact K ⊂ {Re > 1/2}.
-/
lemma paired_tendstoUniformlyOn (K : Set ℂ) (hK : IsCompact K)
    (hK_lower : ∀ z ∈ K, z.re > 1 / 2) :
    TendstoUniformlyOn
      (fun m s => ∑ j ∈ Finset.range m, etaPairedTerm j s)
      (fun s => ∑' j, etaPairedTerm j s)
      atTop K := by
  obtain ⟨σ_min, hσ_min⟩ : ∃ σ_min > 1 / 2, ∀ z ∈ K, z.re ≥ σ_min := by
    by_cases h_empty : K.Nonempty;
    · have := hK.exists_isMinOn h_empty ( show ContinuousOn ( fun z => z.re ) K from Complex.continuous_re.continuousOn );
      exact ⟨ _, hK_lower _ this.choose_spec.1, fun z hz => this.choose_spec.2 hz ⟩;
    · exact ⟨ 1, by norm_num, fun z hz => False.elim <| h_empty ⟨ z, hz ⟩ ⟩;
  obtain ⟨R, hR⟩ : ∃ R > 0, ∀ z ∈ K, ‖z‖ ≤ R := by
    exact Exists.elim ( hK.isBounded.exists_pos_norm_le ) fun R hR => ⟨ R, hR.1, fun z hz => hR.2 z hz ⟩;
  have h_uniform_bound : ∀ j : ℕ, ∀ z ∈ K, ‖etaPairedTerm j z‖ ≤ (R + 1) / (2 * (j : ℝ) + 1) ^ (σ_min + 1) := by
    intros j z hz
    have h_bound : ‖etaPairedTerm j z‖ ≤ (‖z‖ + 1) / (2 * (j : ℝ) + 1) ^ (z.re + 1) := by
      apply norm_etaPairedTerm_le j z (hK_lower z hz);
    exact h_bound.trans ( by exact div_le_div₀ ( by linarith [ norm_nonneg z ] ) ( by linarith [ hR.2 z hz ] ) ( by positivity ) ( by exact Real.rpow_le_rpow_of_exponent_le ( by linarith ) ( by linarith [ hσ_min.2 z hz ] ) ) );
  have h_summable : Summable (fun j : ℕ => (R + 1) / (2 * (j : ℝ) + 1) ^ (σ_min + 1)) := by
    exact Summable.mul_left _ <| by exact_mod_cast Summable.comp_injective ( Real.summable_nat_rpow_inv.2 <| by linarith ) fun a b h => by simpa using h;
  apply_rules [ tendstoUniformlyOn_tsum_nat ]

/-
The odd partial sums differ from even by 1/(2m+1)^s which → 0 uniformly.
-/
lemma etaPartial'_odd_minus_even (m : ℕ) (s : ℂ) :
    etaPartial' (2 * m + 1) s - etaPartial' (2 * m) s =
      1 / ((2 * (m : ℂ) + 1) ^ s) := by
  unfold etaPartial';
  erw [ Finset.sum_Ico_succ_top, Finset.sum_Ico_eq_sub _ ] <;> norm_num

/-
The correction term 1/(2m+1)^s → 0 uniformly on compact K ⊂ {Re > 1/2}.
-/
lemma odd_correction_tendstoUniformlyOn (K : Set ℂ) (hK : IsCompact K)
    (hK_lower : ∀ z ∈ K, z.re > 1 / 2) :
    TendstoUniformlyOn
      (fun (m : ℕ) (s : ℂ) => (1 : ℂ) / ((2 * (m : ℂ) + 1) ^ s))
      (fun _ => (0 : ℂ)) atTop K := by
  -- We'll use the fact that |(2m+1)^s| = (2m+1)^{Re(s)} and show that this tends to 0 uniformly.
  have h_abs : ∀ m : ℕ, ∀ s ∈ K, ‖1 / ((2 * (m : ℂ) + 1) ^ s)‖ ≤ 1 / (2 * m + 1) ^ (1 / 2 : ℝ) := by
    intro m s hs;
    rw [ norm_div, Complex.norm_cpow_of_ne_zero ] <;> norm_cast ; norm_num;
    exact inv_anti₀ ( by positivity ) ( Real.rpow_le_rpow_of_exponent_le ( by linarith ) ( le_of_lt ( hK_lower s hs ) ) );
  -- Since $1 / (2 * m + 1) ^ (1 / 2 : ℝ)$ tends to $0$ as $m$ tends to infinity, we can apply the squeeze theorem.
  have h_lim : Filter.Tendsto (fun m : ℕ => 1 / (2 * (m : ℝ) + 1) ^ (1 / 2 : ℝ)) Filter.atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop ( tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| Filter.tendsto_atTop_mono ( fun m => by linarith ) tendsto_natCast_atTop_atTop );
  rw [ Metric.tendstoUniformlyOn_iff ];
  exact fun ε ε_pos => by filter_upwards [ h_lim.eventually ( gt_mem_nhds ε_pos ) ] with m hm using fun s hs => by simpa using lt_of_le_of_lt ( h_abs m s hs ) hm;

/-!
## Step 2: Limit identification for Re > 1

For Re(s) > 1, the Dirichlet series for ζ converges absolutely, and we can
verify algebraically that ∑ (-1)^{k-1}/k^s = (1-2^{1-s})ζ(s).
-/

/-
For Re(s) > 1, the paired tsum equals dirichletEta.
-/
lemma paired_tsum_eq_dirichletEta_re_gt_one (s : ℂ) (hs : s.re > 1) :
    ∑' j, etaPairedTerm j s = dirichletEta s := by
  -- For Re(s) > 1, we can use the Dirichlet series representation of the zeta function.
  have h_zeta_series : ∑' n : ℕ, (1 : ℂ) / (n + 1 : ℂ) ^ s = riemannZeta s := by
    exact?;
  -- We can split the sum into two separate sums, one over odd terms and one over even terms.
  have h_split_sum : (∑' n : ℕ, ((-1 : ℂ) ^ n) / (n + 1 : ℂ) ^ s) = (∑' j : ℕ, (1 : ℂ) / ((2 * j + 1 : ℂ) ^ s)) - (∑' j : ℕ, (1 : ℂ) / ((2 * j + 2 : ℂ) ^ s)) := by
    rw [ ← tsum_even_add_odd ] <;> norm_num;
    · norm_num [ neg_div, tsum_neg, sub_eq_add_neg ] ; ring;
    · have h_summable : Summable (fun n : ℕ => (1 : ℂ) / (n + 1 : ℂ) ^ s) := by
        contrapose! h_zeta_series;
        rw [ tsum_eq_zero_of_not_summable h_zeta_series ] ; norm_num;
        rw [ eq_comm ] ; intro H; exact absurd ( H ▸ riemannZeta_ne_zero_of_one_lt_re hs ) ( by norm_num ) ;
      convert h_summable.comp_injective ( show Function.Injective ( fun k : ℕ => 2 * k ) from fun a b h => by simpa using h ) using 2 ; norm_num;
    · have h_summable : Summable (fun n : ℕ => (1 : ℂ) / (n + 1 : ℂ) ^ s) := by
        contrapose! h_zeta_series;
        rw [ tsum_eq_zero_of_not_summable h_zeta_series ] ; norm_num;
        rw [ eq_comm ] ; intro H; exact absurd ( H ▸ riemannZeta_ne_zero_of_one_lt_re hs ) ( by norm_num ) ;
      convert h_summable.comp_injective ( show Function.Injective ( fun k : ℕ => 2 * k + 1 ) from fun a b h => by simpa using h ) |> Summable.mul_left ( -1 ) using 2 ; norm_num ; ring;
  convert h_split_sum using 1;
  · convert h_split_sum.symm using 3 ; norm_num [ etaPairedTerm ] ; ring;
    rw [ ← Summable.tsum_sub ];
    · have h_summable : Summable (fun n : ℕ => (1 : ℂ) / (n + 1 : ℂ) ^ s) := by
        contrapose! h_zeta_series;
        rw [ tsum_eq_zero_of_not_summable h_zeta_series ] ; norm_num;
        exact Ne.symm <| riemannZeta_ne_zero_of_one_lt_re hs;
      convert h_summable.comp_injective ( show Function.Injective ( fun j : ℕ => 2 * j ) from fun a b h => by simpa using h ) using 2 ; norm_num ; ring;
    · have h_summable : Summable (fun n : ℕ => (1 : ℂ) / (n + 1 : ℂ) ^ s) := by
        contrapose! h_zeta_series;
        rw [ tsum_eq_zero_of_not_summable h_zeta_series ] ; norm_num;
        exact Ne.symm <| riemannZeta_ne_zero_of_one_lt_re hs;
      convert h_summable.comp_injective ( show Function.Injective ( fun j : ℕ => 2 * j + 1 ) from fun a b h => by simpa using h ) using 2 ; norm_num ; ring;
  · -- We can split the sum into two separate sums, one over odd terms and one over even terms, and then combine them.
    have h_split_sum : (∑' n : ℕ, (1 : ℂ) / (n + 1 : ℂ) ^ s) = (∑' j : ℕ, (1 : ℂ) / ((2 * j + 1 : ℂ) ^ s)) + (∑' j : ℕ, (1 : ℂ) / ((2 * j + 2 : ℂ) ^ s)) := by
      rw [ ← tsum_even_add_odd ];
      · norm_cast;
      · have h_summable : Summable (fun n : ℕ => (1 : ℂ) / (n + 1 : ℂ) ^ s) := by
          contrapose! h_zeta_series;
          rw [ tsum_eq_zero_of_not_summable h_zeta_series ] ; norm_num;
          exact Ne.symm <| riemannZeta_ne_zero_of_one_lt_re hs;
        exact h_summable.comp_injective fun a b h => by simpa using h;
      · have h_summable : Summable (fun n : ℕ => (1 : ℂ) / (n + 1 : ℂ) ^ s) := by
          contrapose! h_zeta_series;
          rw [ tsum_eq_zero_of_not_summable h_zeta_series ] ; norm_num;
          exact Ne.symm <| riemannZeta_ne_zero_of_one_lt_re hs;
        exact h_summable.comp_injective fun a b h => by simpa using h;
    -- We can factor out $2^{-s}$ from the second sum.
    have h_factor : (∑' j : ℕ, (1 : ℂ) / ((2 * j + 2 : ℂ) ^ s)) = (2 : ℂ) ^ (-s) * (∑' j : ℕ, (1 : ℂ) / ((j + 1 : ℂ) ^ s)) := by
      rw [ ← tsum_mul_left ] ; refine' tsum_congr fun j => _ ; rw [ show ( 2 * j + 2 : ℂ ) = 2 * ( j + 1 ) by ring ] ; rw [ Complex.cpow_neg ] ; ring;
      rw [ ← mul_inv, ← mul_comm, Complex.cpow_def_of_ne_zero, Complex.cpow_def_of_ne_zero, Complex.cpow_def_of_ne_zero ] <;> norm_num <;> ring <;> norm_cast <;> norm_num;
      rw [ ← mul_inv, ← Complex.exp_add ] ; rw [ show ( 2 + j * 2 : ℝ ) = 2 * ( 1 + j ) by ring, Real.log_mul ( by positivity ) ( by positivity ) ] ; push_cast ; ring;
      norm_num [ add_comm, mul_comm ];
    rw [ dirichletEta, Complex.cpow_sub ] at * <;> norm_num at *;
    rw [ Complex.cpow_neg ] at *;
    grind

/-!
## Step 3: Identity theorem application

Both the paired tsum and dirichletEta are analytic on {Re > 1/2} \ {1}.
They agree on {Re > 1}. By the identity theorem, they agree on {1/2 < Re < 1}.
-/

/-
The paired tsum defines an analytic function on {Re > 1/2}.
-/
lemma analyticOnNhd_paired_tsum :
    AnalyticOnNhd ℂ (fun s => ∑' j, etaPairedTerm j s) {s | s.re > 1 / 2} := by
  have h_analytic : ∀ m : ℕ, AnalyticOn ℂ (fun s => ∑ j ∈ Finset.range m, etaPairedTerm j s) {s : ℂ | s.re > 1 / 2} := by
    intro m;
    induction' m with m ih <;> simp_all +decide [ Finset.sum_range_succ ];
    · exact analyticOn_const;
    · apply_rules [ AnalyticOn.sub, AnalyticOn.add, AnalyticOn.div, analyticOn_const, analyticOn_id ];
      · apply_rules [ AnalyticOn.cpow, analyticOn_const, analyticOn_id ];
        exact fun z hz => Or.inl <| by norm_num; linarith [ hz.out ] ;
      · norm_num [ Complex.cpow_def ];
        norm_cast ; norm_num [ Complex.exp_ne_zero ];
      · apply_rules [ AnalyticOn.cpow, analyticOn_const, analyticOn_id ];
        exact fun z hz => Or.inl <| by norm_num; linarith;
      · norm_num [ Complex.cpow_eq_zero_iff ];
        norm_cast ; aesop;
  have h_uniform : TendstoLocallyUniformlyOn (fun m s => ∑ j ∈ Finset.range m, etaPairedTerm j s) (fun s => ∑' j, etaPairedTerm j s) atTop {s : ℂ | s.re > 1 / 2} := by
    rw [ Metric.tendstoLocallyUniformlyOn_iff ];
    intro ε hε x hx
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, Metric.ball x δ ⊆ {s : ℂ | s.re > 1 / 2} := by
      exact Metric.mem_nhds_iff.mp ( IsOpen.mem_nhds ( isOpen_lt continuous_const Complex.continuous_re ) hx );
    have := paired_tendstoUniformlyOn ( Metric.closedBall x ( δ / 2 ) ) ( ProperSpace.isCompact_closedBall x ( δ / 2 ) ) ?_;
    · rw [ Metric.tendstoUniformlyOn_iff ] at this;
      exact ⟨ Metric.ball x ( δ / 2 ), mem_nhdsWithin_of_mem_nhds ( Metric.ball_mem_nhds _ ( half_pos hδ_pos ) ), by filter_upwards [ this ε hε ] with n hn y hy using hn y <| Metric.mem_closedBall.mpr <| le_of_lt hy ⟩;
    · exact fun z hz => hδ <| Metric.mem_ball.mpr <| lt_of_le_of_lt ( Metric.mem_closedBall.mp hz ) <| half_lt_self hδ_pos;
  apply_rules [ DifferentiableOn.analyticOnNhd, h_uniform.differentiableOn ];
  · exact Filter.Eventually.of_forall fun n => ( h_analytic n |> AnalyticOn.differentiableOn );
  · exact isOpen_lt continuous_const Complex.continuous_re;
  · exact isOpen_lt continuous_const Complex.continuous_re

/-
dirichletEta is analytic on {Re > 1/2, s ≠ 1}.
-/
lemma analyticOnNhd_dirichletEta :
    AnalyticOnNhd ℂ dirichletEta {s | s.re > 1 / 2 ∧ s ≠ 1} := by
  apply_rules [ DifferentiableOn.analyticOnNhd ];
  · refine' fun s hs => DifferentiableAt.differentiableWithinAt _;
    refine' DifferentiableAt.mul _ _;
    · exact DifferentiableAt.sub ( differentiableAt_const _ ) ( DifferentiableAt.cpow ( differentiableAt_const _ ) ( differentiableAt_id.const_sub _ ) ( by norm_num ) );
    · apply_rules [ differentiableAt_riemannZeta ];
      exact hs.2;
  · exact isOpen_Ioi.preimage Complex.continuous_re |> IsOpen.inter <| isOpen_ne

/-
The open half-plane {Re > 1/2} minus the point {1} is preconnected.
-/
lemma isPreconnected_halfplane_minus_one :
    IsPreconnected {s : ℂ | s.re > 1 / 2 ∧ s ≠ 1} := by
  have h_preconnected : IsPathConnected {s : ℂ | s.re > 1 / 2 ∧ s ≠ 1} := by
    refine' ⟨ 2, _, _ ⟩ <;> norm_num;
    intro y hy hy';
    -- Since $y \neq 1$, we can construct a path from $2$ to $y$ that avoids $1$.
    by_cases h_case : y.im = 0;
    · -- Since $y \neq 1$ and $y.im = 0$, we can construct a path from $2$ to $y$ that avoids $1$ by moving vertically.
      have h_path : JoinedIn {s : ℂ | s.re > 1 / 2 ∧ s ≠ 1} 2 (2 + Complex.I) ∧ JoinedIn {s : ℂ | s.re > 1 / 2 ∧ s ≠ 1} (2 + Complex.I) (y + Complex.I) ∧ JoinedIn {s : ℂ | s.re > 1 / 2 ∧ s ≠ 1} (y + Complex.I) y := by
        refine' ⟨ _, _, _ ⟩;
        · refine' ⟨ _, _ ⟩;
          refine' ⟨ _, _, _ ⟩;
          exact ⟨ fun t => 2 + t * Complex.I, by continuity ⟩;
          all_goals norm_num [ Complex.ext_iff ];
        · refine' ⟨ _, _ ⟩;
          refine' ⟨ _, _, _ ⟩;
          exact ⟨ fun t => ( 1 - t ) * ( 2 + Complex.I ) + t * ( y + Complex.I ), by continuity ⟩;
          all_goals norm_num;
          intro a ha₁ ha₂; refine' ⟨ _, _ ⟩ <;> norm_num [ Complex.ext_iff ] at *;
          · cases lt_or_ge a ( 1 / 2 ) <;> nlinarith;
          · grind;
        · refine' ⟨ _, _ ⟩;
          refine' ⟨ _, _, _ ⟩;
          exact ⟨ fun t => y + Complex.I * ( 1 - t ), by continuity ⟩;
          all_goals norm_num [ Complex.ext_iff, h_case ];
          exact fun a ha₁ ha₂ => ⟨ hy, fun h => by contrapose! hy'; exact Complex.ext ( by norm_num [ h ] ) ( by norm_num [ h_case ] ) ⟩;
      exact h_path.1.trans ( h_path.2.1.trans h_path.2.2 );
    · refine' ⟨ _, _ ⟩;
      refine' ⟨ _, _, _ ⟩;
      exact ⟨ fun t => 2 + t * ( y - 2 ), by continuity ⟩;
      all_goals norm_num;
      intro a ha₁ ha₂; refine' ⟨ _, _ ⟩ <;> norm_num [ Complex.ext_iff ] at *;
      · cases lt_or_ge y.re 2 <;> nlinarith;
      · exact fun h => ⟨ by rintro rfl; norm_num at h, h_case ⟩;
  exact h_preconnected.isConnected.isPreconnected

/-
The paired tsum equals dirichletEta on {Re > 1/2, s ≠ 1}, by the identity theorem.
-/
lemma paired_tsum_eq_dirichletEta (s : ℂ) (hs : s.re > 1 / 2) (hs1 : s ≠ 1) :
    ∑' j, etaPairedTerm j s = dirichletEta s := by
  have h_eq : ∀ᶠ z in nhds 2, ∑' j, etaPairedTerm j z = dirichletEta z := by
    filter_upwards [ IsOpen.mem_nhds ( isOpen_lt continuous_const Complex.continuous_re ) ( show ( 2 : ℂ ).re > 1 by norm_num ) ] with z hz using paired_tsum_eq_dirichletEta_re_gt_one z hz;
  have := @AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq;
  specialize this ( analyticOnNhd_paired_tsum.mono ( show { s : ℂ | s.re > 1 / 2 ∧ s ≠ 1 } ⊆ { s : ℂ | s.re > 1 / 2 } from fun x hx => hx.1 ) ) ( analyticOnNhd_dirichletEta ) ( isPreconnected_halfplane_minus_one ) ( show ( 2 : ℂ ) ∈ { s : ℂ | s.re > 1 / 2 ∧ s ≠ 1 } from ⟨ by norm_num, by norm_num ⟩ );
  exact this ( h_eq.filter_mono nhdsWithin_le_nhds |> fun h => h.frequently ) ⟨ hs, hs1 ⟩

/-!
## Main result: Uniform convergence of eta partial sums
-/

/-
The eta partial sums converge uniformly to dirichletEta on compact K ⊂ {1/2 < Re < 1}.
-/
theorem etaPartial'_tendstoUniformlyOn (K : Set ℂ) (hK : IsCompact K)
    (hK_lower : ∀ z ∈ K, z.re > 1 / 2)
    (hK_upper : ∀ z ∈ K, z.re < 1) :
    TendstoUniformlyOn (fun n => etaPartial' n) dirichletEta atTop K := by
  rw [ Metric.tendstoUniformlyOn_iff ];
  intro ε hε;
  -- By paired_tendstoUniformlyOn, the even partial sums converge uniformly to the paired tsum on K.
  have h_even : ∀ᶠ m in Filter.atTop, ∀ s ∈ K, ‖etaPartial' (2 * m) s - ∑' j, etaPairedTerm j s‖ < ε / 2 := by
    have := paired_tendstoUniformlyOn K hK hK_lower;
    rw [ Metric.tendstoUniformlyOn_iff ] at this;
    simp_all +decide [ dist_eq_norm', etaPartial'_even_eq_paired_sum ];
  -- By odd_correction_tendstoUniformlyOn, the odd partial sums converge uniformly to 0 on K.
  have h_odd : ∀ᶠ m in Filter.atTop, ∀ s ∈ K, ‖etaPartial' (2 * m + 1) s - etaPartial' (2 * m) s‖ < ε / 2 := by
    have := odd_correction_tendstoUniformlyOn K hK hK_lower;
    rw [ Metric.tendstoUniformlyOn_iff ] at this;
    simp_all +decide [ etaPartial'_odd_minus_even ];
  obtain ⟨ m₁, hm₁ ⟩ := Filter.eventually_atTop.mp h_even; obtain ⟨ m₂, hm₂ ⟩ := Filter.eventually_atTop.mp h_odd; refine' Filter.eventually_atTop.mpr ⟨ 2 * m₁ + 2 * m₂, fun n hn s hs => _ ⟩ ; rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩;
  · rw [ dist_comm ];
    rw [ dist_eq_norm, show dirichletEta s = ∑' j : ℕ, etaPairedTerm j s from paired_tsum_eq_dirichletEta s ( hK_lower s hs ) ( by rintro rfl; exact absurd ( hK_upper _ hs ) ( by norm_num ) ) ▸ rfl ] ; exact lt_of_lt_of_le ( hm₁ k ( by linarith ) s hs ) ( by linarith );
  · rw [ dist_comm ];
    rw [ show dirichletEta s = ∑' j, etaPairedTerm j s from paired_tsum_eq_dirichletEta s ( hK_lower s hs ) ( by rintro rfl; exact absurd ( hK_upper _ hs ) ( by norm_num ) ) ▸ rfl ];
    rw [ dist_eq_norm ];
    have := hm₁ k ( by linarith ) s hs; have := hm₂ k ( by linarith ) s hs; rw [ show etaPartial' ( 2 * k + 1 ) s - ∑' j : ℕ, etaPairedTerm j s = ( etaPartial' ( 2 * k + 1 ) s - etaPartial' ( 2 * k ) s ) + ( etaPartial' ( 2 * k ) s - ∑' j : ℕ, etaPairedTerm j s ) by ring ] ; exact lt_of_le_of_lt ( norm_add_le _ _ ) ( by linarith ) ;

end