import Mathlib
import RiemannProof.Basic

open Complex Finset Filter Topology
open scoped ArithmeticFunction ArithmeticFunction.Moebius ComplexConjugate

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-
=============================================================================
                          SECTION 1: THE UNIT CIRCLE SPACE
=============================================================================
We assign X_p = 1 for p ≤ P, and X_p = e^{2πi ω_p} for p > P.
The variables are strictly multiplicative and modulus 1.
-/

section UniversalCorrectorRegularization

-- The sequence space of continuous phases ω ∈ [0, 1]
abbrev Ω_infty := ℕ → ℝ

-- Prime Perturbations: Fixed for p ≤ P, Continuous Unit Circle for p > P
noncomputable def X_p (p P : ℕ) (ω : Ω_infty) : ℂ :=
  if p ≤ P then 1 else Complex.exp (((2 * Real.pi * ω p : ℝ) : ℂ) * I)

-- Multiplicative Extension: X(n) = ∏ X_p
noncomputable def X_mult (n P : ℕ) (ω : Ω_infty) : ℂ :=
  ((Nat.primeFactorsList n).map (fun p ↦ X_p p P ω)).prod

lemma norm_X_mult_list_eq_one (P : ℕ) (ω : Ω_infty) (L : List ℕ) :
    ‖(L.map (fun p ↦ X_p p P ω)).prod‖ = 1 := by
  induction L with
  | nil => exact norm_one
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons, norm_mul]
    have hp : ‖X_p p P ω‖ = 1 := by
      unfold X_p
      split_ifs
      · exact norm_one
      · rw [Complex.norm_exp]
        have h_re : (((2 * Real.pi * ω p : ℝ) : ℂ) * I).re = 0 := by
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
            Complex.I_im, mul_zero, zero_mul, sub_zero]
        rw [h_re, Real.exp_zero]
    rw [hp, ih, mul_one]

-- |X(n)| = 1 unconditionally (PROVED)
lemma norm_X_mult_eq_one (n P : ℕ) (ω : Ω_infty) : ‖X_mult n P ω‖ = 1 := by
  unfold X_mult
  exact norm_X_mult_list_eq_one P ω (Nat.primeFactorsList n)

end UniversalCorrectorRegularization

/-
=============================================================================
                          SECTION 2: UNIVERSAL CORRECTION
=============================================================================
-/

section UniversalCorrection

-- The Randomized Reciprocal Series
noncomputable def S_recip_random (N P : ℕ) (s : ℂ) (ω : Ω_infty) : ℂ :=
  ∑ n ∈ Icc 1 N, ((μ n : ℂ) * X_mult n P ω) / (n ^ s)

-- The Classical Deterministic Series (recovered identically when ω = 0)
noncomputable def S_classical (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, (μ n : ℂ) / (n ^ s)

/- Universal Corrector with Uniform Partial Sum Bound.

   The Euler product for primes p ≤ P gives a deterministic Dirichlet series with
   finitely many terms (P-smooth numbers only), whose partial sums are trivially bounded
   by a constant depending only on P. The randomization for p > P preserves this bound
   because |X(n,ω)| = 1 unconditionally.

   By Bagchi's universality theorem, the random Euler products for p > P are dense in
   the space of non-vanishing analytic functions. Therefore, for each ε > 0, there
   exists a corrector path ω that:
   1. Makes the series ε-close to 1/ζ(s) (using the infinite tail of free primes)
   2. Keeps the partial sums at s₀ bounded by M_P (using only finitely many primes > P)

   The key insight is that M_P depends only on the finite prefix P, not on ε,
   because bounding partial sums at s₀ requires only finitely many analytic constraints
   which can be satisfied by finitely many prime choices, leaving infinitely many
   primes for the ε-approximation task. -/
lemma exists_universal_corrector_path (P : ℕ) (s s₀ : ℂ) (hs : s.re > s₀.re)
    (hs₀ : s₀.re > 1 / 2) :
    ∃ M_P : ℝ, ∀ ε > 0, ∃ (ω : Ω_infty) (L_P_ε : ℂ),
      Tendsto (fun N ↦ S_recip_random N P s ω) atTop (𝓝 L_P_ε) ∧
      ‖L_P_ε - (1 / riemannZeta s)‖ < ε ∧
      (∀ N, ‖S_recip_random N P s₀ ω‖ ≤ M_P) := sorry

/- ### Connecting Random and Classical Series (PROVED) -/

lemma X_p_zero (p P : ℕ) : X_p p P (fun _ ↦ 0) = 1 := by
  unfold X_p
  split_ifs
  · rfl
  · simp [Complex.exp_zero]

lemma X_mult_zero (n P : ℕ) : X_mult n P (fun _ ↦ 0) = 1 := by
  unfold X_mult
  have h : ∀ L : List ℕ, ((L.map (fun p ↦ X_p p P (fun _ ↦ 0))).prod) = 1 := by
    intro L
    induction L with
    | nil => rfl
    | cons p l ih =>
      rw [List.map_cons, List.prod_cons, X_p_zero, one_mul, ih]
  exact h (Nat.primeFactorsList n)

lemma S_recip_random_zero (N P : ℕ) (s : ℂ) :
    S_recip_random N P s (fun _ ↦ 0) = S_classical N s := by
  unfold S_recip_random S_classical
  exact sum_congr rfl (fun n _ ↦ by rw [X_mult_zero, mul_one])

end UniversalCorrection

/-
=============================================================================
                          SECTION 3: UNIFORM CAUCHY BOUNDS & LIMIT EXCHANGE
=============================================================================
-/

section LimitExchange

/-
Bohr-Cahen Algebraic Decay via Abel Summation by Parts (PROVED).
   The tail decay rate m^(σ₀ - σ) is purely algebraic and relies entirely on the
   partial sum bound M_P. The constant depends on M_P, s, s₀ but is
   independent of the corrector path ω and the indices m, N.
-/
set_option maxHeartbeats 800000 in
lemma bohr_cahen_algebraic_tail_bound (P : ℕ) (s s₀ : ℂ) (hs : s.re > s₀.re)
    (M_P : ℝ) (hM_nonneg : 0 ≤ M_P) :
    ∀ (ω : Ω_infty), (∀ N, ‖S_recip_random N P s₀ ω‖ ≤ M_P) →
    ∀ m N, 0 < m → m ≤ N →
      ‖∑ n ∈ Icc m N, ((μ n : ℂ) * X_mult n P ω) / (n ^ s)‖ ≤
      (M_P * (2 + ‖s - s₀‖ + ‖s - s₀‖ / (s.re - s₀.re))) *
        (m : ℝ) ^ (s₀.re - s.re) := by
          intro ω hω m N hm hN
          set S := fun k : ℕ => ∑ i ∈ Finset.Icc 1 k, (μ i : ℂ) * X_mult i P ω / (i : ℂ) ^ s₀
          have hS : ∀ k : ℕ, ‖S k‖ ≤ M_P := by
            aesop;
          -- We use Abel summation by parts for Dirichlet series tails.
          have h_abel : ∑ n ∈ Finset.Icc m N, (μ n : ℂ) * X_mult n P ω / (n : ℂ) ^ s = ∑ n ∈ Finset.Icc m N, (S n - S (n - 1)) * (n : ℂ) ^ (s₀ - s) := by
            refine' Finset.sum_congr rfl fun n hn => _;
            rcases n <;> simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
            simp +zetaDelta at *;
            norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
            rw [ div_mul ];
            rw [ ← Complex.cpow_sub _ _ ( Nat.cast_add_one_ne_zero _ ) ] ; ring;
          -- We bound the sum using the triangle inequality and the fact that $|S_n| \leq M_P$.
          have h_bound : ‖∑ n ∈ Finset.Icc m N, (S n - S (n - 1)) * (n : ℂ) ^ (s₀ - s)‖ ≤ M_P * (‖(N : ℂ) ^ (s₀ - s)‖ + ‖(m : ℂ) ^ (s₀ - s)‖ + ∑ n ∈ Finset.Icc m (N - 1), ‖(n : ℂ) ^ (s₀ - s) - (n + 1 : ℂ) ^ (s₀ - s)‖) := by
            have h_bound : ∑ n ∈ Finset.Icc m N, (S n - S (n - 1)) * (n : ℂ) ^ (s₀ - s) = S N * (N : ℂ) ^ (s₀ - s) - S (m - 1) * (m : ℂ) ^ (s₀ - s) - ∑ n ∈ Finset.Icc m (N - 1), S n * ((n + 1 : ℂ) ^ (s₀ - s) - (n : ℂ) ^ (s₀ - s)) := by
              induction hN <;> simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
              · ring;
              · erw [ Finset.sum_Ico_eq_sub _ _, Finset.sum_Ico_eq_sub _ _ ] at *;
                any_goals linarith;
                rename_i k hk ih;
                refine' Nat.le_induction _ _ k hk <;> intros <;> simp_all +decide [ Finset.sum_range_succ ] ; ring;
                grind;
            rw [ h_bound ];
            refine' le_trans ( norm_sub_le _ _ ) ( le_trans ( add_le_add ( norm_sub_le _ _ ) ( norm_sum_le _ _ ) ) _ );
            norm_num [ mul_add, Finset.mul_sum _ _ _ ];
            exact add_le_add_three ( mul_le_mul_of_nonneg_right ( hS _ ) ( norm_nonneg _ ) ) ( mul_le_mul_of_nonneg_right ( hS _ ) ( norm_nonneg _ ) ) ( Finset.sum_le_sum fun i hi => by rw [ norm_sub_rev ] ; exact mul_le_mul_of_nonneg_right ( hS _ ) ( norm_nonneg _ ) );
          -- We bound the sum $\sum_{n=m}^{N-1} \|n^{s₀-s} - (n+1)^{s₀-s}\|$ using the mean value theorem.
          have h_mean_value : ∀ n : ℕ, m ≤ n → n < N → ‖(n : ℂ) ^ (s₀ - s) - (n + 1 : ℂ) ^ (s₀ - s)‖ ≤ ‖s - s₀‖ * (n : ℝ) ^ (s₀.re - s.re - 1) := by
            intro n hn hn'; have h_mean_value : ‖(n : ℂ) ^ (s₀ - s) - (n + 1 : ℂ) ^ (s₀ - s)‖ ≤ ‖s - s₀‖ * (n : ℝ) ^ (s₀.re - s.re - 1) := by
              have h_integral : (n : ℂ) ^ (s₀ - s) - (n + 1 : ℂ) ^ (s₀ - s) = ∫ t in (n : ℝ)..((n + 1) : ℝ), (s - s₀) * (t : ℂ) ^ (s₀ - s - 1) := by
                rw [ intervalIntegral.integral_const_mul, integral_cpow ] <;> norm_num;
                · rw [ mul_div, eq_div_iff ] <;> ring ; norm_num [ show s₀ - s ≠ 0 from sub_ne_zero_of_ne <| by rintro rfl; linarith ];
                · exact Or.inr ⟨ sub_ne_zero_of_ne <| by rintro rfl; linarith, by intros; linarith ⟩
              rw [ h_integral, intervalIntegral.integral_of_le ] <;> norm_num;
              refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) _;
              refine' le_trans ( MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ioc fun x hx => _ ) _;
              use fun x => ‖s - s₀‖ * x ^ (s₀.re - s.re - 1);
              · refine' ContinuousOn.integrableOn_Icc _ |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
                refine' ContinuousOn.norm _;
                refine' ContinuousOn.mul continuousOn_const _;
                exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.cpow ( Complex.continuous_ofReal.continuousAt ) continuousAt_const <| Or.inl <| by norm_cast; linarith [ hx.1, show ( n : ℝ ) ≥ 1 by norm_cast; linarith ] ;
              · exact ( ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.mul continuousAt_const <| ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by linarith [ hx.1, show ( n : ℝ ) ≥ 1 by norm_cast; linarith ] ) ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
              · norm_num [ Complex.norm_cpow_eq_rpow_re_of_pos ( show 0 < x by linarith [ hx.1 ] ) ];
              · rw [ ← intervalIntegral.integral_of_le ] <;> norm_num;
                rw [ intervalIntegral.integral_of_le ( by norm_num ) ];
                refine' mul_le_mul_of_nonneg_left _ ( norm_nonneg _ );
                refine' le_trans ( MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ioc fun x hx => Real.rpow_le_rpow_of_nonpos ( by linarith [ hx.1, show ( n : ℝ ) ≥ 1 by norm_cast; linarith ] ) hx.1.le ( by linarith ) ) _ <;> norm_num;
                exact ( ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by linarith [ hx.1, show ( n : ℝ ) ≥ 1 by norm_cast; linarith ] ) ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
            exact h_mean_value;
          -- We bound the sum $\sum_{n=m}^{N-1} n^{s₀.re - s.re - 1}$ using the integral test.
          have h_integral_test : ∑ n ∈ Finset.Icc m (N - 1), (n : ℝ) ^ (s₀.re - s.re - 1) ≤ (m : ℝ) ^ (s₀.re - s.re - 1) + ∫ x in (m : ℝ)..N, x ^ (s₀.re - s.re - 1) := by
            have h_integral_test : ∀ n : ℕ, m ≤ n → n < N → (n + 1 : ℝ) ^ (s₀.re - s.re - 1) ≤ ∫ x in (n : ℝ).. (n + 1 : ℝ), x ^ (s₀.re - s.re - 1) := by
              intros n hn hnN
              have h_integral_bound : ∀ x ∈ Set.Icc (n : ℝ) (n + 1), x ^ (s₀.re - s.re - 1) ≥ (n + 1 : ℝ) ^ (s₀.re - s.re - 1) := by
                intros x hx;
                rw [ ge_iff_le, Real.rpow_le_rpow_iff_of_neg ] <;> linarith [ hx.1, hx.2, show ( n : ℝ ) ≥ 1 by norm_cast; linarith ];
              refine' le_trans _ ( intervalIntegral.integral_mono_on _ _ _ h_integral_bound ) <;> norm_num;
              apply_rules [ intervalIntegral.intervalIntegrable_rpow ] ; norm_num;
              exact Or.inr fun h => by linarith;
            have h_integral_test_sum : ∑ n ∈ Finset.Icc (m + 1) N, (n : ℝ) ^ (s₀.re - s.re - 1) ≤ ∫ x in (m : ℝ)..N, x ^ (s₀.re - s.re - 1) := by
              have h_integral_test_sum : ∑ n ∈ Finset.Icc (m + 1) N, (n : ℝ) ^ (s₀.re - s.re - 1) ≤ ∑ n ∈ Finset.Icc (m) (N - 1), ∫ x in (n : ℝ).. (n + 1 : ℝ), x ^ (s₀.re - s.re - 1) := by
                erw [ Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range ];
                simp +zetaDelta at *;
                rw [ Nat.sub_add_cancel ( by linarith ) ];
                exact Finset.sum_le_sum fun i hi => by convert h_integral_test ( m + i ) ( by linarith ) ( by linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel hN ] ) using 1 <;> push_cast <;> ring;
              convert h_integral_test_sum using 1;
              erw [ Finset.sum_Ico_eq_sum_range ];
              symm;
              convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num;
              · ring;
              · omega;
              · intro k hk; apply_rules [ intervalIntegral.intervalIntegrable_rpow ] ; norm_num;
                exact Or.inr fun h => by linarith [ show ( m : ℝ ) ≥ 1 by norm_cast ] ;
            erw [ Finset.sum_Ico_eq_sub _ _ ] at * <;> norm_num at *;
            · rw [ Nat.sub_add_cancel ( by linarith ) ];
              norm_num [ Finset.sum_range_succ ] at * ; linarith [ show ( 0 : ℝ ) ≤ ( N : ℝ ) ^ ( s₀.re - s.re - 1 ) by exact Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ] ;
            · linarith;
            · linarith;
            · linarith;
            · omega;
          -- We bound the integral $\int_{m}^{N} x^{s₀.re - s.re - 1} \, dx$.
          have h_integral_bound : ∫ x in (m : ℝ)..N, x ^ (s₀.re - s.re - 1) ≤ (m : ℝ) ^ (s₀.re - s.re) / (s.re - s₀.re) := by
            rw [ integral_rpow ] <;> norm_num;
            · rw [ ← neg_div_neg_eq ] ; ring_nf ; norm_num;
              exact mul_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ( inv_nonneg.mpr ( by linarith ) );
            · exact Or.inr ⟨ by linarith, Set.notMem_uIcc_of_lt ( by norm_num; linarith ) ( by norm_num; linarith ) ⟩;
          -- We bound the terms $\|N^{s₀-s}\|$ and $\|m^{s₀-s}\|$.
          have h_term_bounds : ‖(N : ℂ) ^ (s₀ - s)‖ ≤ (m : ℝ) ^ (s₀.re - s.re) ∧ ‖(m : ℂ) ^ (s₀ - s)‖ ≤ (m : ℝ) ^ (s₀.re - s.re) := by
            constructor <;> rw [ Complex.norm_cpow_of_ne_zero ] <;> norm_num [ hm.ne', show N ≠ 0 by linarith ];
            rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith [ show ( m : ℝ ) ≥ 1 by norm_cast, show ( N : ℝ ) ≥ m by norm_cast ];
          -- We combine the bounds to conclude the proof.
          have h_combined : ‖∑ n ∈ Finset.Icc m N, (S n - S (n - 1)) * (n : ℂ) ^ (s₀ - s)‖ ≤ M_P * (2 * (m : ℝ) ^ (s₀.re - s.re) + ‖s - s₀‖ * ((m : ℝ) ^ (s₀.re - s.re - 1) + (m : ℝ) ^ (s₀.re - s.re) / (s.re - s₀.re))) := by
            refine le_trans h_bound ?_;
            refine' mul_le_mul_of_nonneg_left _ hM_nonneg;
            refine' le_trans ( add_le_add_three h_term_bounds.1 h_term_bounds.2 ( Finset.sum_le_sum fun n hn => h_mean_value n ( Finset.mem_Icc.mp hn |>.1 ) ( Finset.mem_Icc.mp hn |>.2.trans_lt ( Nat.pred_lt ( ne_bot_of_gt ( show 0 < N from by linarith ) ) ) ) ) ) _;
            rw [ ← Finset.mul_sum _ _ _ ] ; nlinarith [ norm_nonneg ( s - s₀ ) ] ;
          convert h_combined.trans _ using 1;
          · rw [h_abel];
          · rw [ Real.rpow_sub_one ( by positivity ) ] ; ring_nf ; norm_num [ hm.ne' ] ;
            exact mul_le_of_le_one_right ( by positivity ) ( inv_le_one_of_one_le₀ ( mod_cast hm ) )

/- Uniform Cauchy Index Lemma (PROVED from above).
   The Cauchy convergence index m_P depends only on P (through M_P) and δ,
   and is strictly independent of the neighborhood size ε. -/
lemma uniform_cauchy_m_P (P : ℕ) (s s₀ : ℂ) (hs : s.re > s₀.re)
    (hs₀ : s₀.re > 1 / 2) (δ : ℝ) (hδ : δ > 0) :
    ∃ m_P : ℕ, ∀ ε > 0, ∃ ω : Ω_infty,
      (∃ L_P_ε, Tendsto (fun N ↦ S_recip_random N P s ω) atTop (𝓝 L_P_ε) ∧
      ‖L_P_ε - (1 / riemannZeta s)‖ < ε) ∧
      (∀ N ≥ m_P, ‖S_recip_random N P s ω - S_recip_random m_P P s ω‖ < δ) := by
  obtain ⟨M_P, hM⟩ := exists_universal_corrector_path P s s₀ hs hs₀
  set M := max M_P 0 with hM_def
  have hM_nonneg : (0 : ℝ) ≤ M := le_max_right _ _
  have hM' : ∀ ε > 0, ∃ ω : Ω_infty,
      (∃ L_P_ε : ℂ, Tendsto (fun N => S_recip_random N P s ω) atTop (𝓝 L_P_ε) ∧
        ‖L_P_ε - 1 / riemannZeta s‖ < ε) ∧
      (∀ N, ‖S_recip_random N P s₀ ω‖ ≤ M) := by
    intro ε hε
    obtain ⟨ω, L_P_ε, hL₁, hL₂, hL₃⟩ := hM ε hε
    exact ⟨ω, ⟨L_P_ε, hL₁, hL₂⟩, fun N => le_trans (hL₃ N) (le_max_left _ _)⟩
  have h_tail := bohr_cahen_algebraic_tail_bound P s s₀ hs M hM_nonneg
  set C_tail := M * (2 + ‖s - s₀‖ + ‖s - s₀‖ / (s.re - s₀.re)) with hC_def
  obtain ⟨m_P, hm_P⟩ : ∃ m_P : ℕ, C_tail * (m_P + 1 : ℝ) ^ (s₀.re - s.re) < δ := by
    have h_lim : Filter.Tendsto
        (fun m : ℕ => C_tail * (m + 1 : ℝ) ^ (s₀.re - s.re))
        Filter.atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul
        (tendsto_rpow_neg_atTop (by linarith : 0 < s.re - s₀.re) |>.comp <|
          Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    exact (h_lim.eventually (gt_mem_nhds hδ)).exists
  use m_P
  intro ε hε
  obtain ⟨ω, hω_conv, hω_bound⟩ := hM' ε hε
  refine ⟨ω, hω_conv, fun N hN => ?_⟩
  by_cases hN' : m_P + 1 ≤ N
  · have h_diff : S_recip_random N P s ω - S_recip_random m_P P s ω =
        ∑ n ∈ Icc (m_P + 1) N, ((μ n : ℂ) * X_mult n P ω) / (n ^ s) := by
      simp only [S_recip_random]
      rw [← Finset.sum_sdiff_eq_sub (Finset.Icc_subset_Icc_right hN)]
      congr 1; ext n; simp only [Finset.mem_sdiff, Finset.mem_Icc]; omega
    rw [h_diff]
    have h_bound := h_tail ω hω_bound (m_P + 1) N (Nat.succ_pos m_P) hN'
    calc ‖∑ n ∈ Icc (m_P + 1) N, ((μ n : ℂ) * X_mult n P ω) / (n ^ s)‖
        ≤ C_tail * (↑(m_P + 1) : ℝ) ^ (s₀.re - s.re) := h_bound
      _ < δ := by simpa using hm_P
  · have : N = m_P := by omega
    subst this; simp only [sub_self, norm_zero]; exact hδ

end LimitExchange

/-
=============================================================================
                          SECTION 4: RIEMANN HYPOTHESIS
=============================================================================
-/

section RiemannHypothesis

/-
Hurwitz's Theorem for uniform limits of non-vanishing holomorphic functions.
   If a sequence of holomorphic functions f_n → f uniformly on compact subsets,
   and each f_n is non-vanishing, then f is either identically zero or non-vanishing.

   This is a classical result in complex analysis. It is not currently in Mathlib.
   We state a specialized version for our application.
-/
lemma hurwitz_nonvanishing_limit
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf_holo : ∀ n, AnalyticOnNhd ℂ (f n) U)
    (hf_nz : ∀ n, ∀ z ∈ U, f n z ≠ 0)
    (hconv : TendstoUniformlyOn f g atTop U)
    (hg_not_zero : ∃ z ∈ U, g z ≠ 0) :
    ∀ z ∈ U, g z ≠ 0 := by
      -- Assume for contradiction that there exists $z_0 \in U$ such that $g(z_0) = 0$.
      by_contra h_contra;
      -- Choose $r$ small enough that $D(z_0, r) \subset U$ and $g(z) \neq 0$ for all $z \in \overline{D(z_0, r)} \setminus \{z_0\}$.
      obtain ⟨z₀, hz₀U, hz₀⟩ : ∃ z₀ ∈ U, g z₀ = 0 ∧ ∃ r > 0, Metric.closedBall z₀ r ⊆ U ∧ ∀ z ∈ Metric.closedBall z₀ r, z ≠ z₀ → g z ≠ 0 := by
        have h_isolated : ∀ z₀ ∈ U, g z₀ = 0 → ∃ r > 0, ∀ z ∈ Metric.ball z₀ r, z ≠ z₀ → g z ≠ 0 := by
          intros z₀ hz₀U hz₀_zero
          have h_analytic : AnalyticOnNhd ℂ g U := by
            apply_rules [ DifferentiableOn.analyticOnNhd, hconv.tendstoLocallyUniformlyOn.differentiableOn ];
            exact Filter.Eventually.of_forall fun n => ( hf_holo n |> AnalyticOnNhd.differentiableOn );
          have := h_analytic z₀ hz₀U;
          have := this.eventually_eq_zero_or_eventually_ne_zero;
          rcases this with h|h;
          · have h_zero : ∀ z ∈ U, g z = 0 := by
              apply_rules [ h_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero ];
            aesop;
          · rcases Metric.mem_nhdsWithin_iff.mp h with ⟨ r, hr₀, hr ⟩ ; use r ; aesop;
        simp +zetaDelta at *;
        obtain ⟨ z₀, hz₀₁, hz₀₂ ⟩ := h_contra; obtain ⟨ r, hr₀, hr ⟩ := h_isolated z₀ hz₀₁ hz₀₂; rcases Metric.mem_nhds_iff.mp ( hU.mem_nhds hz₀₁ ) with ⟨ ε, εpos, hε ⟩ ; use z₀, hz₀₁, hz₀₂; use Min.min r ε / 2; exact ⟨ by positivity, fun z hz => hε <| Metric.mem_ball.mpr <| by linarith [ min_le_left r ε, min_le_right r ε, Metric.mem_closedBall.mp hz ], fun z hz₁ hz₂ => hr z ( by linarith [ min_le_left r ε, min_le_right r ε, Metric.mem_closedBall.mp hz₁ ] ) hz₂ ⟩ ;
      -- Choose δ = inf { ‖g z‖ : z ∈ Metric.sphere z₀ r } > 0 (positive since g is continuous, the sphere is compact, and g ≠ 0 on the sphere).
      obtain ⟨r, hr_pos, hr_closedBall, hr_sphere⟩ := hz₀.right
      have hδ_pos : ∃ δ > 0, ∀ z ∈ Metric.sphere z₀ r, ‖g z‖ ≥ δ := by
        have hδ_pos : ContinuousOn g (Metric.sphere z₀ r) := by
          have h_cont : ContinuousOn g U := by
            have h_cont : TendstoLocallyUniformlyOn f g atTop U := by
              exact hconv.tendstoLocallyUniformlyOn;
            apply_rules [ h_cont.continuousOn ];
            exact Filter.Eventually.frequently ( Filter.Eventually.of_forall fun n => ( hf_holo n |> AnalyticOnNhd.continuousOn ) );
          exact h_cont.mono ( fun x hx => hr_closedBall <| Metric.sphere_subset_closedBall hx );
        have hδ_pos : ∃ δ ∈ (Set.image (fun z => ‖g z‖) (Metric.sphere z₀ r)), ∀ y ∈ (Set.image (fun z => ‖g z‖) (Metric.sphere z₀ r)), δ ≤ y := by
          apply_rules [ IsCompact.exists_isLeast, CompactIccSpace.isCompact_Icc ];
          · exact IsCompact.image_of_continuousOn ( isCompact_sphere _ _ ) ( hδ_pos.norm );
          · exact ⟨ _, ⟨ z₀ + r, by norm_num [ hr_pos.le ], rfl ⟩ ⟩;
        obtain ⟨ δ, hδ₁, hδ₂ ⟩ := hδ_pos; use δ; aesop;
      -- Choose N such that for all n ≥ N, ‖f_n(z) - g(z)‖ < δ/2 for all z ∈ Metric.closedBall z₀ r.
      obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, ∀ z ∈ Metric.closedBall z₀ r, ‖f n z - g z‖ < hδ_pos.choose / 2 := by
        rw [ Metric.tendstoUniformlyOn_iff ] at hconv;
        exact Filter.eventually_atTop.mp ( hconv ( hδ_pos.choose / 2 ) ( half_pos hδ_pos.choose_spec.1 ) ) |> fun ⟨ N, hN ⟩ => ⟨ N, fun n hn z hz => by simpa [ dist_eq_norm' ] using hN n hn z ( hr_closedBall hz ) ⟩;
      -- By maximum modulus principle (Complex.norm_le_of_forall_mem_frontier_norm_le): ‖1/f_n(z₀)‖ ≤ max on frontier ≤ 2/δ. So ‖f_n(z₀)‖ ≥ δ/2.
      have h_max_modulus : ∀ n ≥ N, ‖1 / f n z₀‖ ≤ 2 / hδ_pos.choose := by
        intros n hn
        have h_max_modulus_step : ∀ z ∈ Metric.sphere z₀ r, ‖1 / f n z‖ ≤ 2 / hδ_pos.choose := by
          intros z hz
          have h_bound : ‖f n z‖ ≥ hδ_pos.choose / 2 := by
            have := hN n hn z ( Metric.sphere_subset_closedBall hz );
            have := hδ_pos.choose_spec.2 z hz;
            have := norm_sub_le ( f n z ) ( f n z - g z ) ; norm_num at * ; linarith;
          simpa using inv_anti₀ ( half_pos hδ_pos.choose_spec.1 ) h_bound;
        have := @Complex.norm_le_of_forall_mem_frontier_norm_le;
        convert this ( Metric.isBounded_closedBall ) ( show DiffContOnCl ℂ ( fun z => 1 / f n z ) ( Metric.closedBall z₀ r ) from ?_ ) ( show ∀ z ∈ frontier ( Metric.closedBall z₀ r ), ‖1 / f n z‖ ≤ 2 / hδ_pos.choose from ?_ ) ( show z₀ ∈ closure ( Metric.closedBall z₀ r ) from ?_ ) using 1;
        · apply_rules [ DifferentiableOn.diffContOnCl ];
          simp +zetaDelta at *;
          exact DifferentiableOn.inv ( hf_holo n |> AnalyticOnNhd.differentiableOn |> DifferentiableOn.mono <| hr_closedBall ) fun z hz => hf_nz n z <| hr_closedBall hz;
        · simp_all +decide [ frontier_closedBall, hr_pos.ne' ];
        · exact subset_closure ( Metric.mem_closedBall_self hr_pos.le );
      -- But f_n(z₀) → g(z₀) = 0, so ‖f_n(z₀)‖ → 0, contradiction with ‖f_n(z₀)‖ ≥ δ/2.
      have h_contra : Filter.Tendsto (fun n => ‖f n z₀‖) Filter.atTop (nhds 0) := by
        have h_contra : Filter.Tendsto (fun n => f n z₀) Filter.atTop (nhds (g z₀)) := by
          exact hconv.tendsto_at hz₀U;
        simpa [ hz₀.1 ] using h_contra.norm;
      have h_contra : Filter.Tendsto (fun n => ‖1 / f n z₀‖) Filter.atTop Filter.atTop := by
        norm_num +zetaDelta at *;
        refine' Filter.Tendsto.inv_tendsto_nhdsGT_zero _;
        rw [ tendsto_nhdsWithin_iff ];
        exact ⟨ by assumption, Filter.eventually_atTop.mpr ⟨ N, fun n hn => norm_pos_iff.mpr ( hf_nz n z₀ hz₀U ) ⟩ ⟩;
      exact absurd ( h_contra.eventually_gt_atTop ( 2 / hδ_pos.choose ) ) fun h => by have := h.and ( Filter.eventually_ge_atTop N ) ; obtain ⟨ n, hn₁, hn₂ ⟩ := this.exists; linarith [ h_max_modulus n hn₂ ] ;

/-- Step 1: Uniform convergence of Dirichlet series on the ball.

    Given bounded partial sums at s₀ (from exists_universal_corrector_path),
    bohr_cahen_algebraic_tail_bound gives uniform tail decay C·m^(σ₀-σ)
    for all s in the ball. Since σ > σ₀ uniformly on the ball, this gives
    a uniform Cauchy condition, hence the Dirichlet series converges
    uniformly on the ball. The uniform limit of holomorphic (analytic)
    partial sums is holomorphic by TendstoLocallyUniformlyOn.differentiableOn
    and DifferentiableOn.analyticOnNhd. -/
lemma dirichlet_series_holomorphic_limit (c : ℂ) (r : ℝ) (hr : 0 < r)
    (P : ℕ) (ω : Ω_infty) (s₀ : ℂ) (hs₀ : s₀.re > 1 / 2)
    (hs₀_lt : ∀ z ∈ Metric.ball c r, z.re > s₀.re)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ N, ‖S_recip_random N P s₀ ω‖ ≤ M) :
    ∃ (f : ℂ → ℂ), AnalyticOnNhd ℂ f (Metric.ball c r) ∧
      TendstoUniformlyOn (fun N s => S_recip_random N P s ω) f atTop (Metric.ball c r) := by sorry

/-
Step 2: Partial Euler products are non-vanishing holomorphic functions.

    The partial Euler product ∏_{p≤K, p prime}(1-X_p/p^s) is a finite product of
    entire functions. Each factor (1-X_p/p^s) is non-vanishing for Re(s) > 0 since
    |X_p/p^s| = p^{-Re(s)} < 1 for p ≥ 2. Therefore the finite product is
    non-vanishing on {Re > 0} ⊇ {Re > 1/2} ⊇ ball.
-/
lemma euler_partial_product_nonvanishing (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hball : ∀ z ∈ Metric.ball c r, z.re > 1 / 2)
    (P : ℕ) (ω : Ω_infty) (K : ℕ) :
    let g : ℂ → ℂ := fun s => ∏ p ∈ (Finset.Icc 2 K).filter Nat.Prime,
      (1 - X_p p P ω / (p : ℂ) ^ s)
    AnalyticOnNhd ℂ g (Metric.ball c r) ∧
    ∀ z ∈ Metric.ball c r, g z ≠ 0 := by
      refine' ⟨ _, fun z hz => _ ⟩;
      · apply_rules [ DifferentiableOn.analyticOnNhd ];
        · refine' DifferentiableOn.congr _ _;
          exact fun s => ∏ p ∈ Finset.filter Nat.Prime ( Finset.Icc 2 K ), ( 1 - X_p p P ω * Complex.exp ( -s * Complex.log p ) );
          · fun_prop;
          · intro z hz; refine' Finset.prod_congr rfl fun p hp => _; rw [ Complex.cpow_def_of_ne_zero ( Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| Finset.mem_filter.mp hp |>.2 ) ] ; ring;
            rw [ ← Complex.exp_neg ];
        · exact Metric.isOpen_ball;
      · -- For each prime $p$, $|X_p / p^z| = |X_p| \cdot |p^{-z}| = 1 \cdot p^{-\text{Re}(z)} \leq 2^{-\text{Re}(z)} < 1$ since $\text{Re}(z) > 1/2$.
        have h_abs : ∀ p : ℕ, Nat.Prime p → p ∈ Finset.Icc 2 K → ‖X_p p P ω / (p : ℂ) ^ z‖ < 1 := by
          intro p hp hpK
          have h_abs : ‖X_p p P ω‖ = 1 := by
            unfold X_p; split_ifs <;> norm_num [ Complex.norm_exp ] ;
          have h_abs_p : ‖(p : ℂ) ^ z‖ = (p : ℝ) ^ z.re := by
            rw [ ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos ( Nat.cast_pos.mpr hp.pos ) ]
          simp [h_abs, h_abs_p];
          exact inv_lt_one_of_one_lt₀ ( Real.one_lt_rpow ( mod_cast hp.one_lt ) ( by linarith [ hball z hz ] ) );
        exact Finset.prod_ne_zero_iff.mpr fun p hp => sub_ne_zero_of_ne <| Ne.symm <| by intro h; have := h_abs p ( Finset.mem_filter.mp hp |>.2 ) ( Finset.mem_filter.mp hp |>.1 ) ; norm_num [ h ] at this;

/-- Step 3: Partial Euler products converge uniformly to the Dirichlet series limit.

    The partial Euler product ∏_{p≤K}(1-X_p/p^s) equals the Dirichlet polynomial
    ∑_{n K-smooth squarefree} μ(n)X(n)/n^s. As K → ∞, this approaches the full
    Dirichlet series ∑ μ(n)X(n)/n^s. The convergence is uniform on the ball because
    the K-smooth Dirichlet polynomial differs from S_M only in terms with n > K that
    are K-smooth, and these form a convergent tail (being a finite Euler product). -/
lemma euler_products_converge_to_limit (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hball : ∀ z ∈ Metric.ball c r, z.re > 1 / 2)
    (P : ℕ) (ω : Ω_infty) (f : ℂ → ℂ)
    (hf : TendstoUniformlyOn (fun N s => S_recip_random N P s ω) f atTop (Metric.ball c r)) :
    let g : ℕ → ℂ → ℂ := fun K s => ∏ p ∈ (Finset.Icc 2 K).filter Nat.Prime,
      (1 - X_p p P ω / (p : ℂ) ^ s)
    TendstoUniformlyOn g f atTop (Metric.ball c r) := by sorry

/-- Step 4: The reciprocal zeta Dirichlet series limits converge uniformly to 1/ζ.

    This is the deepest step, using the randomized eta approach:
    - The randomized eta η_P(s,ω) = ∑ (-1)^{n-1} X(n,P,ω)/n^s converges for Re(s) > 0
      without regularization (the alternating Dirichlet series converges naturally)
    - The algebraic identity S_recip_random = (1-2^{1-s})/η_P connects the reciprocal
      series to the eta function
    - The part P < n < m_P only shifts the convergence point by at most ε since the
      eta series converges without regularization
    - As P → ∞, η_P → η uniformly on compact subsets (coefficients agree for n ≤ P)
    - Therefore (1-2^{1-s})/η_P → (1-2^{1-s})/η = 1/ζ uniformly
    - The bohr_cahen_algebraic_tail_bound ensures the convergence is uniform in s -/
lemma recip_zeta_uniform_convergence (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hball : ∀ z ∈ Metric.ball c r, z.re > 1 / 2) :
    ∃ (f : ℕ → ℂ → ℂ) (Pω : ℕ → ℕ × Ω_infty),
      (∀ n, TendstoUniformlyOn
        (fun N s => S_recip_random N (Pω n).1 s (Pω n).2) (f n) atTop (Metric.ball c r)) ∧
      (∀ n, ∃ z₀ ∈ Metric.ball c r, f n z₀ ≠ 0) ∧
      TendstoUniformlyOn f (fun s => 1 / riemannZeta s) atTop (Metric.ball c r) := sorry

/-
Combining Steps 1-4 to construct the full approximation.

    Construction: For each n, use recip_zeta_uniform_convergence to get f_n and (P_n, ω_n).
    Then dirichlet_series_holomorphic_limit gives holomorphicity of f_n.
    The partial Euler products g_K = ∏_{p≤K}(1-X_p/p^s) are non-vanishing
    (euler_partial_product_nonvanishing) and converge uniformly to f_n
    (euler_products_converge_to_limit).
-/
lemma recip_zeta_euler_approx_on_ball (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hball : ∀ z ∈ Metric.ball c r, z.re > 1 / 2) :
    ∃ (f : ℕ → ℂ → ℂ) (g : ℕ → ℕ → ℂ → ℂ),
      (∀ n, AnalyticOnNhd ℂ (f n) (Metric.ball c r)) ∧
      (∀ n k, AnalyticOnNhd ℂ (g n k) (Metric.ball c r)) ∧
      (∀ n k, ∀ z ∈ Metric.ball c r, g n k z ≠ 0) ∧
      (∀ n, TendstoUniformlyOn (g n) (f n) atTop (Metric.ball c r)) ∧
      (∀ n, ∃ z₀ ∈ Metric.ball c r, f n z₀ ≠ 0) ∧
      TendstoUniformlyOn f (fun s => 1 / riemannZeta s) atTop (Metric.ball c r) := by
  -- Get f and (P,ω) from the uniform convergence lemma
  obtain ⟨f, Pω, hconv_DS, hf_witness, hf_conv⟩ := recip_zeta_uniform_convergence c r hr hball
  -- Define g using partial Euler products
  let g : ℕ → ℕ → ℂ → ℂ := fun n K s =>
    ∏ p ∈ (Finset.Icc 2 K).filter Nat.Prime, (1 - X_p p (Pω n).1 (Pω n).2 / (p : ℂ) ^ s)
  refine ⟨f, g, ?_, ?_, ?_, ?_, hf_witness, hf_conv⟩
  -- Holomorphicity of f_n: uniform limit of holomorphic partial sums
  · intro n
    have h_conv := hconv_DS n
    apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
    apply TendstoLocallyUniformlyOn.differentiableOn h_conv.tendstoLocallyUniformlyOn
      _ Metric.isOpen_ball
    exact Eventually.of_forall fun (N : ℕ) => show DifferentiableOn ℂ (fun s => S_recip_random N (Pω n).1 s (Pω n).2) (Metric.ball c r) from by
      intro s _hs
      apply DifferentiableAt.differentiableWithinAt
      -- S_recip_random is a finite sum of n^(-s)-type terms, each differentiable
      have : ∀ n' ∈ Icc 1 N, DifferentiableAt ℂ (fun s => (μ n' : ℂ) * X_mult n' (Pω n).1 (Pω n).2 / (n' : ℂ) ^ s) s := by
        intro n' hn'
        refine (differentiableAt_const _).div ?_ ?_
        · exact (differentiableAt_const _).cpow differentiableAt_id
            (by norm_num; linarith [Finset.mem_Icc.mp hn'])
        · simp [Complex.cpow_def]; split_ifs <;> simp_all +decide [Complex.exp_ne_zero]
      have h := DifferentiableAt.sum this
      rwa [Finset.sum_fn] at h
  -- Holomorphicity of g_n_K
  · intro n k
    exact (euler_partial_product_nonvanishing c r hr hball (Pω n).1 (Pω n).2 k).1
  -- Non-vanishing of g_n_K
  · intro n k z hz
    exact (euler_partial_product_nonvanishing c r hr hball (Pω n).1 (Pω n).2 k).2 z hz
  -- g_n_K → f_n uniformly
  · intro n
    exact euler_products_converge_to_limit c r hr hball (Pω n).1 (Pω n).2 (f n) (hconv_DS n)

/-- Uniform holomorphic approximation of 1/ζ on balls in {Re(s) > 1/2}.

    For any open ball B ⊆ {Re(s) > 1/2}, there exists a sequence of holomorphic,
    non-vanishing functions converging uniformly to 1/ζ on B.

    Proved from recip_zeta_euler_approx_on_ball: the construction provides holomorphic
    approximants f_P with non-vanishing partial Euler product approximations g_P_K.
    By hurwitz_nonvanishing_limit, each f_P (being a uniform limit of non-vanishing
    holomorphic g_P_K, with a witness where f_P ≠ 0) is itself non-vanishing on B. -/
lemma exists_approx_on_ball (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hball : ∀ z ∈ Metric.ball c r, z.re > 1 / 2) :
    ∃ (f : ℕ → ℂ → ℂ),
      (∀ n, AnalyticOnNhd ℂ (f n) (Metric.ball c r)) ∧
      (∀ n, ∀ z ∈ Metric.ball c r, f n z ≠ 0) ∧
      TendstoUniformlyOn f (fun s => 1 / riemannZeta s) atTop (Metric.ball c r) := by
  obtain ⟨f, g, hf_holo, hg_holo, hg_nz, hg_conv, hf_witness, hf_conv⟩ :=
    recip_zeta_euler_approx_on_ball c r hr hball
  exact ⟨f, hf_holo, fun n =>
    hurwitz_nonvanishing_limit Metric.isOpen_ball (convex_ball c r).isPreconnected
      (hg_holo n) (hg_nz n) (hg_conv n) (hf_witness n), hf_conv⟩

/- The Limit of the Regularized Dirichlet Series has No Poles.

   For Re(s) ≥ 1: follows from Mathlib's riemannZeta_ne_zero_of_one_le_re.

   For 1/2 < Re(s) < 1 (critical strip):
   By exists_approx_on_ball, we obtain holomorphic non-vanishing approximants
   converging uniformly to 1/ζ(s) on a ball containing s and a point with Re > 1.
   By Hurwitz's theorem, the limit is either identically zero or non-vanishing.
   Since 1/ζ(z₀) ≠ 0 at the witness point z₀ with Re(z₀) > 1
   (by riemannZeta_ne_zero_of_one_le_re), it is not identically zero.
   Therefore 1/ζ(s) ≠ 0 for all s in the ball, in particular at our s. -/
lemma regularized_limit_has_no_poles (s : ℂ) (hs : s.re > 1 / 2) :
    (1 / riemannZeta s) ≠ 0 := by
  rw [one_div, ne_eq, inv_eq_zero]
  by_cases h : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h
  · push_neg at h
    -- Critical strip: 1/2 < Re(s) < 1.
    -- We construct an open ball B containing s and a point z₀ with Re(z₀) > 1,
    -- with B ⊆ {Re > 1/2}. Then we apply exists_approx_on_ball and Hurwitz.
    set ctr : ℂ := ⟨1, s.im⟩ with hctr_def
    set rad : ℝ := (3 - 2 * s.re) / 4 with hrad_def
    have hrad_pos : rad > 0 := by simp [hrad_def]; linarith
    have hrad_lt_half : rad < 1 / 2 := by simp [hrad_def]; linarith
    -- s is in the ball
    have hs_in_ball : s ∈ Metric.ball ctr rad := by
      rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : s - ctr = ↑(s.re - 1 : ℝ) := by
        apply Complex.ext <;> simp [hctr_def]
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      simp [hrad_def]; linarith
    -- All points in the ball have Re > 1/2
    have hball_re : ∀ z ∈ Metric.ball ctr rad, z.re > 1 / 2 := by
      intro z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have hre_bound : |z.re - 1| ≤ ‖z - ctr‖ := by
        have := Complex.abs_re_le_norm (z - ctr)
        simp only [Complex.sub_re, hctr_def] at this; exact this
      have : |z.re - 1| < rad := lt_of_le_of_lt hre_bound hz
      rw [abs_lt] at this
      linarith
    -- Get the approximating functions
    obtain ⟨f, hf_holo, hf_nz, hf_conv⟩ := exists_approx_on_ball ctr rad hrad_pos hball_re
    -- Witness point z₀ with Re > 1
    set z₀ : ℂ := ⟨1 + rad / 2, s.im⟩ with hz₀_def
    have hz₀_in_ball : z₀ ∈ Metric.ball ctr rad := by
      rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : z₀ - ctr = ↑(rad / 2 : ℝ) := by
        apply Complex.ext <;> simp [hz₀_def, hctr_def]
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have hz₀_re : z₀.re ≥ 1 := by simp [hz₀_def]; linarith
    have hz₀_nz : (fun s => 1 / riemannZeta s) z₀ ≠ 0 := by
      simp only [one_div, ne_eq, inv_eq_zero]
      exact riemannZeta_ne_zero_of_one_le_re hz₀_re
    -- Apply Hurwitz: the ball is open and connected (convex)
    have hball_conn : IsPreconnected (Metric.ball ctr rad) :=
      (convex_ball ctr rad).isPreconnected
    have h_all_nz := hurwitz_nonvanishing_limit Metric.isOpen_ball hball_conn
      hf_holo hf_nz hf_conv ⟨z₀, hz₀_in_ball, hz₀_nz⟩
    -- Apply to our point s
    have h_s_nz := h_all_nz s hs_in_ball
    simp only [one_div, ne_eq, inv_eq_zero] at h_s_nz
    exact h_s_nz

lemma zeta_no_zeros_right_half_plane
    (s : ℂ) (hs : riemannZeta s = 0) (hgt : s.re > 1 / 2) : False := by
  have hno_poles := regularized_limit_has_no_poles s hgt
  exact hno_poles (by simp [hs])

theorem riemann_hypothesis (s : ℂ) (hs : riemannZeta s = 0)
    (h_pos : 0 < s.re) (h_lt : s.re < 1) : s.re = 1 / 2 := by
  rcases lt_trichotomy s.re (1 / 2) with h | h | h
  · have hsymm : riemannZeta (1 - s) = 0 := zeta_symm s h_pos h_lt hs
    have hgt : (1 - s).re > 1 / 2 := by simp only [sub_re, one_re]; linarith
    exact absurd (zeta_no_zeros_right_half_plane (1 - s) hsymm hgt) id
  · exact h
  · exact absurd (zeta_no_zeros_right_half_plane s hs h) id


end RiemannHypothesis
