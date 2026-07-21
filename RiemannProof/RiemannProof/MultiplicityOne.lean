import Mathlib
import RiemannProof.ConjugateReflection

/-!
# Multiplicity-One Theorem for η(2s−1)
-/

open Complex Finset Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
## Helper: Uniform convergence of conjugate composition
-/

/-
If f_n → g uniformly on K, then conj(f_n(conj(·))) → conj(g(conj(·)))
    uniformly on conj(K). In particular, if K = conj(K), the convergence
    is on K itself.
-/
lemma tendstoUniformlyOn_conj_comp {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {K : Set ℂ}
    (hf : TendstoUniformlyOn f g atTop (starRingEnd ℂ '' K)) :
    TendstoUniformlyOn (fun n s => starRingEnd ℂ (f n (starRingEnd ℂ s)))
      (fun s => starRingEnd ℂ (g (starRingEnd ℂ s))) atTop K := by
  rw [ Metric.tendstoUniformlyOn_iff ] at *;
  simp_all +decide [ dist_comm ]

/-
Product of two uniformly convergent bounded sequences converges uniformly.
-/
lemma tendstoUniformlyOn_mul {f₁ f₂ : ℕ → ℂ → ℂ} {g₁ g₂ : ℂ → ℂ} {K : Set ℂ}
    (hf₁ : TendstoUniformlyOn f₁ g₁ atTop K)
    (hf₂ : TendstoUniformlyOn f₂ g₂ atTop K)
    (hb₁ : ∃ M, ∀ n, ∀ s ∈ K, ‖f₁ n s‖ ≤ M)
    (hb₂ : ∃ M, ∀ n, ∀ s ∈ K, ‖f₂ n s‖ ≤ M) :
    TendstoUniformlyOn (fun n s => f₁ n s * f₂ n s) (fun s => g₁ s * g₂ s) atTop K := by
  -- Let's choose any two points z and w in the set K and apply the triangle inequality.
  have h_triangle : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ z ∈ K, ‖f₁ n z * f₂ n z - g₁ z * g₂ z‖ < ε := by
    intro ε hε
    obtain ⟨M₁, hM₁⟩ := hb₁
    obtain ⟨M₂, hM₂⟩ := hb₂
    have h_tendsto : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ z ∈ K, ‖f₁ n z - g₁ z‖ < ε ∧ ‖f₂ n z - g₂ z‖ < ε := by
      rw [ Metric.tendstoUniformlyOn_iff ] at hf₁ hf₂;
      exact fun ε hε => by rcases Filter.eventually_atTop.mp ( hf₁ ε hε ) with ⟨ N₁, hN₁ ⟩ ; rcases Filter.eventually_atTop.mp ( hf₂ ε hε ) with ⟨ N₂, hN₂ ⟩ ; exact ⟨ Max.max N₁ N₂, fun n hn z hz => ⟨ by simpa [ dist_eq_norm' ] using hN₁ n ( le_trans ( le_max_left _ _ ) hn ) z hz, by simpa [ dist_eq_norm' ] using hN₂ n ( le_trans ( le_max_right _ _ ) hn ) z hz ⟩ ⟩ ;
    obtain ⟨ N₁, hN₁ ⟩ := h_tendsto ( ε / ( 2 * ( |M₁| + |M₂| + 1 ) ) ) ( by positivity ) ; use N₁; intros n hn z hz; specialize hN₁ n hn z hz; rw [ show f₁ n z * f₂ n z - g₁ z * g₂ z = ( f₁ n z - g₁ z ) * f₂ n z + g₁ z * ( f₂ n z - g₂ z ) by ring ] ; norm_num at *; (
                                                                                                                                                      refine' lt_of_le_of_lt ( norm_add_le _ _ ) _ ; norm_num at * ; (
                                                                                                                                                      refine' lt_of_le_of_lt ( add_le_add ( mul_le_mul_of_nonneg_left ( hM₂ n z hz ) ( norm_nonneg _ ) ) ( mul_le_mul_of_nonneg_right ( show ‖g₁ z‖ ≤ M₁ by
                                                                                                                                                                                                                                                                                          have h_g₁_bound : Filter.Tendsto (fun n => f₁ n z) atTop (nhds (g₁ z)) := by
                                                                                                                                                                                                                                                                                            exact Metric.tendsto_atTop.mpr fun ε hε => by rcases h_tendsto ε hε with ⟨ N, hN ⟩ ; exact ⟨ N, fun n hn => by simpa using hN n hn z hz |>.1 ⟩ ;
                                                                                                                                                                                                                                                                                          generalize_proofs at *; (
                                                                                                                                                                                                                                                                                          exact le_of_tendsto' ( h_g₁_bound.norm ) fun n => hM₁ n z hz) ) ( norm_nonneg _ ) ) ) _;
                                                                                                                                                      cases abs_cases M₁ <;> cases abs_cases M₂ <;> nlinarith [ mul_div_cancel₀ ε ( by linarith : ( 2 * ( |M₁| + |M₂| + 1 ) ) ≠ 0 ), norm_nonneg ( f₁ n z - g₁ z ), norm_nonneg ( f₂ n z - g₂ z ), hM₁ n z hz, hM₂ n z hz ] ;));
  rw [ Metric.tendstoUniformlyOn_iff ];
  exact fun ε hε => by rcases h_triangle ε hε with ⟨ N, hN ⟩ ; filter_upwards [ Filter.Ici_mem_atTop N ] with n hn z hz using by rw [ dist_comm ] ; exact hN n hn z hz;

/-
conjReflApprox n converges uniformly to conjReflLimit on compact
    subsets of {1/2 < Re(s) < 1}.
-/
lemma conjReflApprox_tendstoUniformlyOn (K : Set ℂ) (hK : IsCompact K)
    (hK_re : ∀ s ∈ K, s.re > 1 / 2) (hK_re' : ∀ s ∈ K, s.re < 1) :
    TendstoUniformlyOn (fun n => conjReflApprox n) conjReflLimit atTop K := by
  refine' tendstoUniformlyOn_mul _ _ _ _;
  · convert tendstoUniformlyOn_conj_comp _ using 1;
    rotate_left;
    exact fun s => targetH s * etaShifted s;
    · refine' fApprox_tendstoUniformlyOn _ _ _ _;
      · exact hK.image ( Complex.continuous_conj );
      · aesop;
      · aesop;
    · rfl;
  · exact fApprox_tendstoUniformlyOn K hK hK_re hK_re';
  · have h_bounded : ∃ M, ∀ n, ∀ s ∈ starRingEnd ℂ '' K, ‖fApprox n s‖ ≤ M := by
      have h_bounded : ∃ M, ∀ s ∈ starRingEnd ℂ '' K, ‖targetH s * etaShifted s‖ ≤ M := by
        have h_bounded : ContinuousOn (fun s => targetH s * etaShifted s) (starRingEnd ℂ '' K) := by
          apply_rules [ ContinuousOn.mul, continuousOn_const ];
          · exact Continuous.continuousOn ( by unfold targetH; continuity );
          · fun_prop;
          · refine' continuousOn_of_forall_continuousAt _;
            intro s hs;
            refine' ContinuousAt.comp ( show ContinuousAt ( fun s => riemannZeta s ) ( 2 * s - 1 ) from _ ) ( ContinuousAt.sub ( continuousAt_const.mul continuousAt_id ) continuousAt_const );
            refine' ( differentiableAt_riemannZeta _ ).continuousAt;
            rcases hs with ⟨ s, hs, rfl ⟩ ; norm_num [ Complex.ext_iff ] ; intros ; linarith [ hK_re s hs, hK_re' s hs ];
        exact IsCompact.exists_bound_of_continuousOn ( hK.image <| Complex.continuous_conj ) h_bounded;
      have h_bounded : ∀ᶠ n in atTop, ∀ s ∈ starRingEnd ℂ '' K, ‖fApprox n s‖ ≤ ‖targetH s * etaShifted s‖ + 1 := by
        have h_bounded : TendstoUniformlyOn (fun n => fApprox n) (fun s => targetH s * etaShifted s) atTop (starRingEnd ℂ '' K) := by
          apply fApprox_tendstoUniformlyOn;
          · exact hK.image ( Complex.continuous_conj );
          · aesop;
          · aesop;
        rw [ Metric.tendstoUniformlyOn_iff ] at h_bounded;
        filter_upwards [ h_bounded 1 zero_lt_one ] with n hn using fun s hs => by have := hn s hs; rw [ dist_eq_norm ] at this; exact le_trans ( norm_le_of_mem_closedBall <| by simpa [ dist_eq_norm' ] using this.le ) ( by norm_num ) ;
      obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, ∀ s ∈ starRingEnd ℂ '' K, ‖fApprox n s‖ ≤ ‖targetH s * etaShifted s‖ + 1 := by
        exact Filter.eventually_atTop.mp h_bounded;
      have h_bounded : ∃ M, ∀ n < N, ∀ s ∈ starRingEnd ℂ '' K, ‖fApprox n s‖ ≤ M := by
        have h_bounded : ∀ n < N, ∃ M, ∀ s ∈ starRingEnd ℂ '' K, ‖fApprox n s‖ ≤ M := by
          intro n hn
          have h_cont : ContinuousOn (fun s => fApprox n s) (starRingEnd ℂ '' K) := by
            refine' ContinuousOn.mul _ _;
            · refine' ContinuousOn.add _ _;
              · exact Continuous.continuousOn ( by exact Continuous.sub ( continuous_id.sub continuous_const ) continuous_const );
              · exact continuousOn_const;
            · refine' continuousOn_finset_sum _ fun i hi => ContinuousOn.div _ _ _;
              · exact continuousOn_const;
              · refine' continuousOn_of_forall_continuousAt fun s hs => _;
                refine' ContinuousAt.cpow _ _ _;
                · exact continuousAt_const;
                · exact ContinuousAt.sub ( continuousAt_const.mul continuousAt_id ) continuousAt_const;
                · exact Or.inl ( by norm_cast; linarith );
              · norm_num [ Complex.cpow_def ];
                norm_cast ; norm_num [ Complex.exp_ne_zero ];
          exact IsCompact.exists_bound_of_continuousOn ( hK.image ( Complex.continuous_conj ) ) h_cont;
        choose! M hM using h_bounded;
        exact ⟨ ∑ n ∈ Finset.range N, M n, fun n hn s hs => le_trans ( hM n hn s hs ) ( Finset.single_le_sum ( fun n _ => show 0 ≤ M n from le_trans ( norm_nonneg _ ) ( hM n ( Finset.mem_range.mp ‹_› ) s hs ) ) ( Finset.mem_range.mpr hn ) ) ⟩;
      obtain ⟨ M, hM ⟩ := h_bounded;
      obtain ⟨ M', hM' ⟩ := ‹∃ M, ∀ s ∈ ⇑ ( starRingEnd ℂ ) '' K, ‖targetH s * etaShifted s‖ ≤ M›;
      exact ⟨ Max.max M ( M' + 1 ), fun n s hs => if hn : n < N then le_trans ( hM n hn s hs ) ( le_max_left _ _ ) else le_trans ( hN n ( le_of_not_gt hn ) s hs ) ( by linarith [ hM' s hs, le_max_right M ( M' + 1 ) ] ) ⟩;
    aesop;
  · have h_bounded : ∃ M, ∀ s ∈ K, ‖targetH s * etaShifted s‖ ≤ M := by
      have h_bounded : ContinuousOn (fun s => targetH s * etaShifted s) K := by
        apply_rules [ ContinuousOn.mul, continuousOn_const, continuousOn_id ];
        · exact Continuous.continuousOn ( by unfold targetH; continuity );
        · exact continuousOn_of_forall_continuousAt fun s hs => ContinuousAt.sub continuousAt_const <| ContinuousAt.cpow continuousAt_const ( ContinuousAt.sub continuousAt_const <| ContinuousAt.sub ( continuousAt_const.mul continuousAt_id ) continuousAt_const ) <| Or.inl <| by norm_num;
        · refine' continuousOn_of_forall_continuousAt fun s hs => _;
          refine' ContinuousAt.comp ( show ContinuousAt ( fun s => riemannZeta s ) ( 2 * s - 1 ) from _ ) ( ContinuousAt.sub ( continuousAt_const.mul continuousAt_id ) continuousAt_const );
          refine' differentiableAt_riemannZeta _ |> DifferentiableAt.continuousAt;
          exact ne_of_apply_ne Complex.re ( by norm_num; linarith [ hK_re s hs, hK_re' s hs ] );
      exact IsCompact.exists_bound_of_continuousOn hK h_bounded;
    have h_fApprox_bounded : ∀ᶠ n in atTop, ∀ s ∈ K, ‖fApprox n s‖ ≤ h_bounded.choose + 1 := by
      have := fApprox_tendstoUniformlyOn K hK hK_re hK_re';
      rw [ Metric.tendstoUniformlyOn_iff ] at this;
      filter_upwards [ this 1 zero_lt_one ] with n hn s hs using by have := hn s hs; rw [ dist_eq_norm' ] at this; exact le_trans ( norm_le_of_mem_closedBall <| by simpa using this.le ) ( by linarith [ h_bounded.choose_spec s hs ] ) ;
    obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp h_fApprox_bounded;
    use Max.max ( ∑ n ∈ Finset.range N, ( SupSet.sSup ( Set.image ( fun s => ‖fApprox n s‖ ) K ) ) ) ( h_bounded.choose + 1 );
    intro n s hs; by_cases hn : n < N <;> simp_all +decide [ Finset.sum_range_succ ] ;
    exact Or.inl ( le_trans ( by exact le_csSup ( by exact IsCompact.bddAbove ( hK.image ( show Continuous fun s => ‖fApprox n s‖ from by exact Continuous.norm <| by exact Continuous.mul ( show Continuous fun s => hApprox n s from by exact Continuous.add ( show Continuous fun s => targetH s from by exact targetH_differentiable.continuous ) <| by continuity ) <| show Continuous fun s => etaPartialShifted n s from by exact etaPartialShifted_differentiable n |> Differentiable.continuous ) ) ) <| Set.mem_image_of_mem _ hs ) <| Finset.single_le_sum ( fun a _ => by exact ( show 0 ≤ sSup ( ( fun s => ‖fApprox a s‖ ) '' K ) from by apply_rules [ Real.sSup_nonneg ] ; rintro x ⟨ y, hy, rfl ⟩ ; exact norm_nonneg _ ) ) <| Finset.mem_range.mpr hn )

/-!
## Section 1: Edge Integrals Converge (Task 5)
-/

/-
The integral of conjReflApprox over the top edge converges to the
    integral of conjReflLimit.
-/
lemma top_edge_integral_converges (R : Rect) (s₀ : ℂ)
    (hs₀ : s₀ ∈ R.openInt)
    (hR_re : ∀ s ∈ R.closure, s.re > 1 / 2)
    (hR_re' : ∀ s ∈ R.closure, s.re < 1)
    (h_unique : ∀ z ∈ R.closure, etaShifted z = 0 → z = s₀)
    (h_boundary_ne : ∀ z ∈ R.closure \ R.openInt, etaShifted z ≠ 0) :
    Tendsto (fun n => ∫ x in R.x_lo..R.x_hi,
      conjReflApprox n (x + R.y_hi * I))
      atTop (𝓝 (∫ x in R.x_lo..R.x_hi,
        conjReflLimit (x + R.y_hi * I))) := by
  have h_cont : TendstoUniformlyOn (fun n => fun x : ℝ => conjReflApprox n (x + R.y_hi * I)) (fun x : ℝ => conjReflLimit (x + R.y_hi * I)) atTop (Set.Icc R.x_lo R.x_hi) := by
    have h_cont : TendstoUniformlyOn (fun n => conjReflApprox n) conjReflLimit atTop R.closure := by
      convert conjReflApprox_tendstoUniformlyOn R.closure ( Rect.isCompact_closure R ) hR_re hR_re' using 1;
    intro ε hε; specialize h_cont ε hε; filter_upwards [ h_cont ] with n hn; intro x hx; convert hn ( x + R.y_hi * I ) _ using 1; simp +decide [ hx, Rect.closure ] ;
    exact ⟨ hx.1, hx.2, R.hy.le ⟩;
  have h_cont_int : ∀ n, ContinuousOn (fun x : ℝ => conjReflApprox n (x + R.y_hi * I)) (Set.Icc R.x_lo R.x_hi) := by
    intro n;
    refine' Continuous.continuousOn _;
    refine' Continuous.mul _ _;
    · refine' Continuous.star _;
      refine' Continuous.mul _ _;
      · refine' Continuous.add _ _;
        · exact Continuous.sub ( Complex.continuous_conj.comp <| by continuity ) continuous_const |> Continuous.sub <| continuous_const;
        · exact continuous_const;
      · refine' continuous_finset_sum _ fun i hi => _;
        refine' continuous_const.div _ _;
        · exact continuous_const.cpow ( by continuity ) ( by intro x; exact Or.inl <| by norm_cast; linarith );
        · intro x; norm_num [ Complex.cpow_def ] ;
          norm_cast ; norm_num [ Complex.exp_ne_zero ];
    · refine' Continuous.mul _ _;
      · exact Continuous.add ( targetH_differentiable.continuous.comp <| by continuity ) <| continuous_const;
      · refine' continuous_finset_sum _ fun i hi => _;
        refine' continuous_const.div _ _;
        · exact Continuous.cpow ( continuous_const ) ( by continuity ) ( by intro x; exact Or.inl <| by norm_cast; linarith );
        · intro x; norm_num [ Complex.cpow_def ] ;
          norm_cast ; norm_num [ Complex.exp_ne_zero ];
  have h_cont_int : ContinuousOn (fun x : ℝ => conjReflLimit (x + R.y_hi * I)) (Set.Icc R.x_lo R.x_hi) := by
    refine' h_cont.continuousOn _;
    exact Filter.Eventually.frequently ( Filter.Eventually.of_forall h_cont_int );
  rw [ Metric.tendstoUniformlyOn_iff ] at h_cont;
  refine' intervalIntegral.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
  use fun x => ‖conjReflLimit ( x + R.y_hi * I )‖ + 1;
  · filter_upwards [ h_cont 1 zero_lt_one ] with n hn using ContinuousOn.aestronglyMeasurable ( by solve_by_elim ) measurableSet_Icc |> fun h => h.mono_set <| by intro x hx; constructor <;> cases Set.mem_uIoc.mp hx <;> linarith [ R.hx, R.hy ] ;
  · filter_upwards [ h_cont 1 zero_lt_one ] with n hn;
    filter_upwards [ ] with x hx using by have := hn x ( by constructor <;> cases Set.mem_uIoc.mp hx <;> linarith [ R.hx ] ) ; rw [ dist_eq_norm ] at this ; exact le_trans ( norm_le_norm_add_norm_sub _ _ ) ( by linarith ) ;
  · apply_rules [ ContinuousOn.intervalIntegrable ];
    simpa only [ Set.uIcc_of_le R.hx.le ] using h_cont_int.norm.add continuousOn_const;
  · filter_upwards [ ] with x hx using Metric.tendsto_atTop.mpr fun ε hε => by simpa [ dist_comm ] using h_cont ε hε |> fun h => h.mono fun n hn => hn x <| by constructor <;> cases Set.mem_uIoc.mp hx <;> linarith [ R.hx ] ;

/-
The integral of conjReflApprox over the left edge converges.
-/
lemma left_edge_integral_converges (R : Rect) (s₀ : ℂ)
    (hs₀ : s₀ ∈ R.openInt)
    (hR_re : ∀ s ∈ R.closure, s.re > 1 / 2)
    (hR_re' : ∀ s ∈ R.closure, s.re < 1)
    (h_unique : ∀ z ∈ R.closure, etaShifted z = 0 → z = s₀)
    (h_boundary_ne : ∀ z ∈ R.closure \ R.openInt, etaShifted z ≠ 0) :
    Tendsto (fun n => ∫ y in R.y_lo..R.y_hi,
      conjReflApprox n (R.x_lo + y * I))
      atTop (𝓝 (∫ y in R.y_lo..R.y_hi,
        conjReflLimit (R.x_lo + y * I))) := by
  -- Apply the uniform convergence of `conjReflApprox` to `conjReflLimit` on the compact set `R.closure`.
  have h_uniform_converge : TendstoUniformlyOn (fun n => conjReflApprox n) conjReflLimit atTop (Set.Icc R.x_lo R.x_lo ×ℂ Set.Icc R.y_lo R.y_hi) := by
    apply TendstoUniformlyOn.mono (conjReflApprox_tendstoUniformlyOn (R.closure) (Rect.isCompact_closure R) hR_re hR_re') (by
    intro z hz; exact ⟨by linarith [hz.1.1, hz.1.2], by linarith [hz.1.1, hz.1.2, R.hx], by linarith [hz.2.1, hz.2.2], by linarith [hz.2.1, hz.2.2, R.hy]⟩;);
  have h_integral_converge : Tendsto (fun n => ∫ y in (R.y_lo)..R.y_hi, conjReflApprox n (R.x_lo + y * Complex.I)) atTop (𝓝 (∫ y in (R.y_lo)..R.y_hi, conjReflLimit (R.x_lo + y * Complex.I))) := by
    have h_cont : ContinuousOn (fun y : ℝ => conjReflLimit (R.x_lo + y * Complex.I)) (Set.Icc R.y_lo R.y_hi) := by
      have h_cont : ContinuousOn (fun s : ℂ => conjReflLimit s) (Set.Icc R.x_lo R.x_lo ×ℂ Set.Icc R.y_lo R.y_hi) := by
        refine' h_uniform_converge.continuousOn _;
        refine' Filter.Eventually.frequently _;
        refine' Filter.Eventually.of_forall fun n => _;
        refine' ContinuousOn.mul _ _;
        · refine' Continuous.continuousOn _;
          refine' Continuous.star _;
          refine' Continuous.mul _ _;
          · refine' Continuous.add _ _;
            · exact Continuous.sub ( Complex.continuous_conj ) continuous_const |> Continuous.sub <| continuous_const;
            · exact continuous_const;
          · refine' continuous_finset_sum _ fun i hi => _;
            refine' continuous_const.div _ _;
            · refine' Continuous.cpow _ _ _ <;> norm_num [ Complex.cpow_def ];
              · exact continuous_const;
              · exact Continuous.sub ( continuous_const.mul ( Complex.continuous_conj ) ) continuous_const;
              · exact Or.inl ( by norm_num; linarith );
            · norm_num [ Complex.cpow_def ];
              norm_cast ; norm_num [ Complex.exp_ne_zero ];
        · refine' ContinuousOn.mul _ _;
          · exact Continuous.continuousOn ( by exact Continuous.add ( continuous_id.sub continuous_const |> Continuous.sub <| continuous_const ) <| continuous_const );
          · refine' Continuous.continuousOn _;
            refine' continuous_finset_sum _ fun i hi => _;
            refine' continuous_const.div _ _;
            · exact continuous_const.cpow ( by continuity ) ( by intro x; exact Or.inl <| by norm_cast; linarith );
            · intro x; rw [ Ne.eq_def, Complex.cpow_eq_zero_iff ] ; norm_cast ; norm_num;
      convert h_cont.comp ( show ContinuousOn ( fun y : ℝ => ( R.x_lo : ℂ ) + y * Complex.I ) ( Set.Icc R.y_lo R.y_hi ) from Continuous.continuousOn <| by continuity ) _ using 1;
      simp +decide [ Set.MapsTo, Complex.mem_reProdIm ]
    refine' intervalIntegral.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
    use fun y => ‖conjReflLimit ( R.x_lo + y * Complex.I )‖ + 1;
    · refine' Filter.Eventually.of_forall fun n => Continuous.aestronglyMeasurable _;
      refine' Continuous.mul _ _;
      · refine' Continuous.star _;
        refine' Continuous.mul _ _;
        · refine' Continuous.add _ _;
          · exact Continuous.sub ( by continuity ) ( by continuity );
          · exact continuous_const;
        · refine' continuous_finset_sum _ fun i hi => _;
          refine' continuous_const.div _ _;
          · refine' Continuous.cpow _ _ _;
            · exact continuous_const;
            · fun_prop;
            · exact fun x => Or.inl <| by norm_num; linarith;
          · intro x; norm_num [ Complex.cpow_def ] ;
            norm_cast ; norm_num [ Complex.exp_ne_zero ];
      · refine' Continuous.mul _ _;
        · refine' Continuous.add _ _;
          · exact Continuous.sub ( by continuity ) ( by continuity );
          · exact continuous_const;
        · refine' continuous_finset_sum _ fun i hi => _;
          refine' Continuous.div _ _ _;
          · exact continuous_const;
          · exact Continuous.cpow ( continuous_const ) ( by continuity ) ( by intro y; exact Or.inl <| by norm_cast; linarith );
          · norm_num [ Complex.cpow_def ];
            norm_cast ; norm_num [ Complex.exp_ne_zero ];
    · rw [ Metric.tendstoUniformlyOn_iff ] at h_uniform_converge;
      filter_upwards [ h_uniform_converge 1 zero_lt_one ] with n hn;
      filter_upwards [ ] with x hx;
      have := hn ( R.x_lo + x * Complex.I ) ?_;
      · rw [ dist_eq_norm ] at this;
        have := norm_sub_le ( conjReflLimit ( R.x_lo + x * Complex.I ) ) ( conjReflLimit ( R.x_lo + x * Complex.I ) - conjReflApprox n ( R.x_lo + x * Complex.I ) ) ; norm_num at * ; linarith;
      · simp +decide [ Complex.mem_reProdIm, hx ];
        cases Set.mem_uIoc.mp hx <;> constructor <;> linarith [ R.hy ];
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      simpa only [ Set.uIcc_of_le R.hy.le ] using h_cont.norm.add continuousOn_const;
    · refine' Filter.Eventually.of_forall fun x hx => _;
      convert h_uniform_converge.tendsto_at _ using 1;
      exact ⟨ ⟨ by norm_num, by norm_num ⟩, ⟨ by cases Set.mem_uIoc.mp hx <;> norm_num <;> linarith [ R.hy ], by cases Set.mem_uIoc.mp hx <;> norm_num <;> linarith [ R.hy ] ⟩ ⟩;
  convert h_integral_converge using 1

/-
The integral of conjReflApprox over the right edge converges.
-/
lemma right_edge_integral_converges (R : Rect) (s₀ : ℂ)
    (hs₀ : s₀ ∈ R.openInt)
    (hR_re : ∀ s ∈ R.closure, s.re > 1 / 2)
    (hR_re' : ∀ s ∈ R.closure, s.re < 1)
    (h_unique : ∀ z ∈ R.closure, etaShifted z = 0 → z = s₀)
    (h_boundary_ne : ∀ z ∈ R.closure \ R.openInt, etaShifted z ≠ 0) :
    Tendsto (fun n => ∫ y in R.y_lo..R.y_hi,
      conjReflApprox n (R.x_hi + y * I))
      atTop (𝓝 (∫ y in R.y_lo..R.y_hi,
        conjReflLimit (R.x_hi + y * I))) := by
  have h_int_right : TendstoUniformlyOn (fun n => fun y : ℝ => conjReflApprox n (R.x_hi + y * I)) (fun y : ℝ => conjReflLimit (R.x_hi + y * I)) atTop (Set.Icc R.y_lo R.y_hi) := by
    have h_int_right : TendstoUniformlyOn (fun n => conjReflApprox n) conjReflLimit atTop (R.closure) := by
      apply conjReflApprox_tendstoUniformlyOn R.closure R.isCompact_closure hR_re hR_re';
    intro ε hε; filter_upwards [ h_int_right ε hε ] with n hn x hx; convert hn ( R.x_hi + x * I ) _ using 1; simp +decide [ Rect.closure ] ;
    exact ⟨ R.hx.le, hx.1, hx.2 ⟩;
  have h_int_right : ∀ n, ContinuousOn (fun y : ℝ => conjReflApprox n (R.x_hi + y * I)) (Set.Icc R.y_lo R.y_hi) := by
    intro n;
    refine' Continuous.continuousOn _;
    refine' Continuous.mul _ _;
    · refine' Continuous.comp ( Complex.continuous_conj ) _;
      refine' Continuous.mul _ _;
      · refine' Continuous.add _ _;
        · exact Continuous.sub ( continuous_id' ) continuous_const |> Continuous.comp <| by continuity;
        · exact continuous_const;
      · refine' continuous_finset_sum _ fun _ _ => _;
        refine' Continuous.div _ _ _;
        · exact continuous_const;
        · exact continuous_const.cpow ( by continuity ) ( by intro y; exact Or.inl <| by norm_cast; linarith );
        · norm_num [ Complex.cpow_def ];
          norm_cast ; norm_num [ Complex.exp_ne_zero ];
    · refine' Continuous.mul _ _;
      · refine' Continuous.add _ _;
        · exact Continuous.sub ( by continuity ) ( by continuity );
        · exact continuous_const;
      · refine' continuous_finset_sum _ fun i hi => _;
        refine' Continuous.div _ _ _;
        · exact continuous_const;
        · exact continuous_const.cpow ( by continuity ) ( by intro y; exact Or.inl <| by norm_cast; linarith );
        · intro x; norm_num [ Complex.cpow_def ] ;
          norm_cast ; norm_num [ Complex.exp_ne_zero ];
  have h_int_right : TendstoUniformlyOn (fun n => fun y : ℝ => conjReflApprox n (R.x_hi + y * I)) (fun y : ℝ => conjReflLimit (R.x_hi + y * I)) atTop (Set.Icc R.y_lo R.y_hi) → Filter.Tendsto (fun n => ∫ y in R.y_lo..R.y_hi, conjReflApprox n (R.x_hi + y * I)) atTop (nhds (∫ y in R.y_lo..R.y_hi, conjReflLimit (R.x_hi + y * I))) := by
    intro h_uniform_converge
    have h_integral_converge : Filter.Tendsto (fun n => ∫ y in (Set.Icc R.y_lo R.y_hi), conjReflApprox n (R.x_hi + y * I)) atTop (nhds (∫ y in (Set.Icc R.y_lo R.y_hi), conjReflLimit (R.x_hi + y * I))) := by
      refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
      use fun y => ‖conjReflLimit ( R.x_hi + y * I )‖ + 1;
      · exact Filter.Eventually.of_forall fun n => ( h_int_right n |> ContinuousOn.aestronglyMeasurable <| measurableSet_Icc );
      · rw [ Metric.tendstoUniformlyOn_iff ] at h_uniform_converge;
        filter_upwards [ h_uniform_converge 1 zero_lt_one ] with n hn using Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Icc ) fun x hx => by simpa using norm_le_of_mem_closedBall <| mem_closedBall_iff_norm.mpr <| le_of_lt <| by simpa [ dist_eq_norm' ] using hn x hx;
      · refine' ContinuousOn.integrableOn_Icc _;
        refine' ContinuousOn.add ( ContinuousOn.norm _ ) continuousOn_const;
        refine' h_uniform_converge.continuousOn _;
        exact Filter.Eventually.frequently ( Filter.Eventually.of_forall h_int_right );
      · rw [ MeasureTheory.ae_restrict_iff' ] <;> norm_num;
        filter_upwards [ ] with x hx₁ hx₂ using h_uniform_converge.tendsto_at ( Set.mem_Icc.mpr ⟨ hx₁, hx₂ ⟩ );
    simpa only [ MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le R.hy.le ] using h_integral_converge;
  exact h_int_right ‹_›

/-
**S5 (original statement — NOT PROVABLE AS STATED).**

The original `nonreal_edges_sum_zero` claimed that the three non-real edge
integrals of `conjReflLimit` sum to zero.  It is not provable as written and
has no proved consumers, so it is commented out (per the implementation plan,
S5).  Problems:
* Lean's `∫ x in a..b, e` notation extends to the end of the expression, so the
  first integrand silently swallows the `+ ∫ … - ∫ …` that follows.
* Even with the intended parenthesization, the combination lacks the
  `I`-weights of the Cauchy/Green boundary orientation and omits the bottom
  edge, so it does not follow from holomorphy.
* There are no `Re`-bounds, so `1` may lie in `R.closure`, where `conjReflLimit`
  is not even continuous.

The correct, provable statement is `conjReflLimit_boundaryIntegral_zero` below.

lemma nonreal_edges_sum_zero (R : Rect) (s₀ : ℂ)
    (hs₀ : s₀ ∈ R.openInt)
    (h_boundary_ne : ∀ z ∈ R.closure \ R.openInt, conjReflLimit z ≠ 0) :
    ∫ x in R.x_lo..R.x_hi, conjReflLimit (x + R.y_hi * I) +
    ∫ y in R.y_lo..R.y_hi, conjReflLimit (R.x_hi + y * I) -
    ∫ y in R.y_lo..R.y_hi, conjReflLimit (R.x_lo + y * I) = 0 := by
  sorry

**S5 (correct replacement): the boundary integral of `conjReflLimit`
    vanishes** whenever the contour stays in the region `Re < 1`, where
    `conjReflLimit` is holomorphic.  This is the genuine Cauchy statement
    (with the proper orientation weights and including the bottom edge).
-/
lemma conjReflLimit_boundaryIntegral_zero (R : Rect)
    (hR_re' : ∀ s ∈ R.closure, s.re < 1) :
    R.boundaryIntegral conjReflLimit = 0 := by
  apply rect_cauchy R conjReflLimit;
  exact fun s hs => DifferentiableAt.differentiableWithinAt ( conjReflLimit_differentiableOn.differentiableAt ( IsOpen.mem_nhds isOpen_ne ( show s ≠ 1 from by rintro rfl; exact absurd ( hR_re' _ hs ) ( by norm_num ) ) ) )

/-!
## Section 2: Real-Axis Integral is Positive (Task 6)
-/

/-- F_n is non-negative on the real axis. -/
lemma conjReflApprox_nonneg_on_reals (n : ℕ) (σ : ℝ) :
    0 ≤ (conjReflApprox n (σ : ℂ)).re := by
  exact (conjReflApprox_real_nonneg n σ).2

/-- The real-axis integral of F_n is non-negative. -/
lemma real_axis_integral_nonneg (n : ℕ) (a b : ℝ) (hab : a < b) :
    0 ≤ (∫ σ in a..b, conjReflApprox n (σ : ℂ)).re := by
  have h_integral_nonneg : ∀ {f : ℝ → ℝ}, (∀ x, 0 ≤ f x) → 0 ≤ ∫ x in a..b, f x := by
    exact fun { f } hf => intervalIntegral.integral_nonneg hab.le fun x hx => hf x;
  convert h_integral_nonneg fun x => conjReflApprox_nonneg_on_reals n x using 1;
  convert Complex.ofReal_re _;
  rw [ intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le ];
  convert integral_ofReal using 2;
  exact funext fun x => by rw [ Complex.ext_iff ] ; norm_num [ conjReflApprox_real_nonneg ] ;

/-
For sufficiently large n, f_n is not identically zero on [a,b].
-/
lemma fApprox_not_identically_zero (a b : ℝ) (hab : a < b)
    (ha : a > 1 / 2) (hb : b < 1) :
    ∀ᶠ n in atTop, ∃ σ ∈ Set.Icc a b, fApprox n (σ : ℂ) ≠ 0 := by
  -- Since the limit function targetH * etaShifted is not identically zero on [a,b], there exists some σ₀ ∈ [a,b] where targetH(σ₀) * etaShifted(σ₀) ≠ 0.
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ ∈ Set.Icc a b, targetH σ₀ * etaShifted σ₀ ≠ 0 := by
    apply Classical.byContradiction
    intro h_no_sigma₀;
    have h_etaShifted_zero : ∀ σ ∈ Set.Icc a b, etaShifted σ = 0 := by
      intro σ hσ; specialize h_no_sigma₀; contrapose! h_no_sigma₀; use σ; simp_all +decide [ targetH ] ;
      norm_num [ Complex.ext_iff ];
    have h_etaShifted_zero : ∀ σ ∈ Set.Icc a b, riemannZeta (2 * σ - 1) = 0 := by
      intros σ hσ
      have h_etaShifted_zero : etaShifted σ = 0 := h_etaShifted_zero σ hσ
      rw [etaShifted_eq] at h_etaShifted_zero
      simp at h_etaShifted_zero
      exact (by
      rw [ sub_eq_zero, eq_comm ] at h_etaShifted_zero;
      norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def ] at h_etaShifted_zero;
      exact Complex.ext ( h_etaShifted_zero.resolve_left ( by linarith [ hσ.1, hσ.2 ] ) |>.1 ) ( h_etaShifted_zero.resolve_left ( by linarith [ hσ.1, hσ.2 ] ) |>.2 ));
    have h_etaShifted_zero : ∀ σ ∈ Set.Icc (2 * a - 1) (2 * b - 1), riemannZeta σ = 0 := by
      intro σ hσ; specialize h_etaShifted_zero ( ( σ + 1 ) / 2 ) ⟨ by linarith [ hσ.1 ], by linarith [ hσ.2 ] ⟩ ; convert h_etaShifted_zero using 1 ; ring;
      norm_num ; ring;
    have h_etaShifted_zero : ∀ σ ∈ Set.Icc (2 * a - 1) (2 * b - 1), σ = 1 / 2 := by
      intros σ hσ
      apply riemann_hypothesis_rect (σ : ℂ) (h_etaShifted_zero σ hσ) (by
      norm_num; linarith [ hσ.1, hσ.2 ]) (by
      norm_num; linarith [ hσ.2 ]);
    linarith [ h_etaShifted_zero ( 2 * a - 1 ) ⟨ by linarith, by linarith ⟩, h_etaShifted_zero ( 2 * b - 1 ) ⟨ by linarith, by linarith ⟩ ];
  have h_uniform_convergence : Filter.Tendsto (fun n => fApprox n σ₀) Filter.atTop (nhds (targetH σ₀ * etaShifted σ₀)) := by
    have h_pointwise : Tendsto (fun n => etaPartialShifted n (σ₀ : ℂ)) atTop (nhds (etaShifted (σ₀ : ℂ))) := by
      apply etaPartialShifted_tendsto;
      · exact lt_of_lt_of_le ha hσ₀.1.1;
      · exact_mod_cast hσ₀.1.2.trans_lt hb;
    convert Filter.Tendsto.mul ( hApprox_tendsto ( σ₀ : ℂ ) ) h_pointwise using 1
  generalize_proofs at *; (
  filter_upwards [ h_uniform_convergence.eventually_ne hσ₀.2 ] with n hn using ⟨ σ₀, hσ₀.1, hn ⟩)

/-
**Task 6**: The real-axis integral of F_n is strictly positive
    for sufficiently large n.
-/
lemma real_axis_integral_pos (a b : ℝ) (hab : a < b)
    (ha : a > 1 / 2) (hb : b < 1) :
    ∀ᶠ n in atTop, 0 < (∫ σ in a..b, conjReflApprox n (σ : ℂ)).re := by
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ∀ n ≥ n₀, ∃ σ₀ ∈ Set.Icc a b, fApprox n (σ₀ : ℂ) ≠ 0 := by
    exact Filter.eventually_atTop.mp ( fApprox_not_identically_zero a b hab ha hb );
  have h_integral_pos_aux : ∀ n ≥ n₀, 0 < (∫ σ in Set.Icc a b, Complex.normSq (fApprox n (σ : ℂ))) := by
    intro n hn; specialize hn₀ n hn; obtain ⟨ σ₀, hσ₀₁, hσ₀₂ ⟩ := hn₀; rw [ MeasureTheory.integral_pos_iff_support_of_nonneg_ae ] ; simp_all +decide [ Complex.normSq_eq_norm_sq ] ;
    · -- Since $fApprox n$ is continuous and $fApprox n (σ₀ : ℂ) ≠ 0$, there exists an open interval around $σ₀$ where $fApprox n$ is non-zero.
      obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ σ : ℝ, abs (σ - σ₀) < ε → fApprox n (σ : ℂ) ≠ 0 := by
        have h_cont : ContinuousAt (fun σ : ℝ => fApprox n (σ : ℂ)) σ₀ := by
          refine' Continuous.continuousAt _;
          refine' Continuous.mul _ _;
          · exact Continuous.add ( Continuous.sub ( Complex.continuous_ofReal ) continuous_const |> Continuous.sub <| continuous_const ) <| continuous_const;
          · refine' continuous_finset_sum _ fun i hi => _;
            refine' continuous_const.div _ _;
            · exact continuous_const.cpow ( by continuity ) ( by intro x; exact Or.inl <| by norm_cast; linarith );
            · exact fun x => by norm_num [ Complex.cpow_def_of_ne_zero, show ( i : ℂ ) + 1 ≠ 0 from Nat.cast_add_one_ne_zero i ] ;
        exact Metric.mem_nhds_iff.mp ( h_cont.eventually_ne hσ₀₂ );
      -- Since $fApprox n$ is non-zero on an open interval around $\sigma₀$, the volume of this interval is positive.
      have h_volume_pos : 0 < volume (Set.Ioo (max a (σ₀ - ε)) (min b (σ₀ + ε))) := by
        simp +zetaDelta at *;
        exact ⟨ ⟨ hab, by linarith ⟩, by linarith, by linarith ⟩;
      refine' h_volume_pos.trans_le ( MeasureTheory.measure_mono _ ) ; intro x hx ; simp_all +decide [ Function.support ] ; (
      grind);
    · exact Filter.Eventually.of_forall fun x => Complex.normSq_nonneg _;
    · refine' Continuous.integrableOn_Icc _;
      refine' Continuous.comp ( Complex.continuous_normSq ) _;
      refine' Continuous.mul _ _;
      · exact Continuous.add ( Continuous.sub ( Complex.continuous_ofReal ) continuous_const |> Continuous.sub <| continuous_const ) continuous_const;
      · refine' continuous_finset_sum _ fun i hi => _;
        refine' continuous_const.div _ _;
        · exact continuous_const.cpow ( by continuity ) ( by intro x; exact Or.inl <| by norm_cast; linarith );
        · exact fun x => by norm_num [ Complex.cpow_def_of_ne_zero, show ( i : ℂ ) + 1 ≠ 0 from Nat.cast_add_one_ne_zero i ] ;
  simp_all +decide [ intervalIntegral.integral_of_le hab.le, MeasureTheory.integral_Icc_eq_integral_Ioc ];
  use n₀; intro n hn; specialize h_integral_pos_aux n hn; simp_all +decide [ conjReflApprox_eq_normSq ] ;
  erw [ integral_ofReal ] ; norm_cast

/-!
## Section 3: The Residue Contradiction (Task 7)
-/

/-!
### Normalization layer (N)

The contour argument runs in *normalized coordinates*: the hypothetical zero
`s₀ = σ₀ + i·t₀` is moved to the reference point `3/4 + I` by the
complex-affine map `normMap` (real coefficients, so it is holomorphic and
respects Schwarz reflection).  The pulled-back junk point `s = 1` becomes the
*real* point `normBadPoint`, which the normalized rectangle excludes.
-/

/-- Affine normalization sending the normalized plane to the original one:
    `x ↦ t₀·x + (σ₀ - (3/4)·t₀)`, `y ↦ t₀·y`.  Sends `3/4 + I` to
    `s₀ = σ₀ + i·t₀`. -/
noncomputable def normMap (σ₀ t₀ : ℝ) (z : ℂ) : ℂ :=
  (t₀ : ℂ) * z + ((σ₀ : ℂ) - (3 / 4) * (t₀ : ℂ))

/-- The shifted eta function in normalized coordinates. -/
noncomputable def etaShiftedNorm (σ₀ t₀ : ℝ) (z : ℂ) : ℂ :=
  etaShifted (normMap σ₀ t₀ z)

/-- The pulled-back singular point: `normMap σ₀ t₀ (normBadPoint σ₀ t₀) = 1`.
    Note it is a *real* point. -/
noncomputable def normBadPoint (σ₀ t₀ : ℝ) : ℂ :=
  (3 / 4 : ℂ) + ((1 - σ₀) / t₀ : ℂ)

/-
**S4 (original statement — do not prove as written; inconsistent hypothesis).**

The original `even_multiplicity_contradiction` quantifies the factorization
`∀ s, etaShifted s = (s - s₀)^m * φ s` over *all* of ℂ with `φ` entire.  That
forces `etaShifted` to be continuous at `s = 1`, contradicting `H1`/`H2`
(value `0` there, but limit `log 2 ≠ 0`).  Hence `h_order` is inconsistent and
the statement is only *vacuously* provable, which formalizes nothing.  It has
no proved consumers, so it is commented out (per the implementation plan, S4).

lemma even_multiplicity_contradiction (R : Rect) (s₀ : ℂ) (m : ℕ)
    (hm : m ≥ 2)
    (hs₀ : s₀ ∈ R.openInt)
    (hR_bottom : R.y_lo = 0)
    (hR_re : ∀ s ∈ R.closure, s.re > 1 / 2)
    (hR_re' : ∀ s ∈ R.closure, s.re < 1)
    (h_unique : ∀ z ∈ R.closure, etaShifted z = 0 → z = s₀)
    (h_boundary_ne : ∀ z ∈ R.closure \ R.openInt, etaShifted z ≠ 0)
    (h_order : ∃ φ : ℂ → ℂ, Differentiable ℂ φ ∧ φ s₀ ≠ 0 ∧
      ∀ s, etaShifted s = (s - s₀) ^ m * φ s) :
    False := by
  sorry
-/

/-- **S4 (honest restatement, normalized coordinates) — GENUINE OPEN CORE.**

    In normalized coordinates the factorization lives on
    `ℂ \ {normBadPoint σ₀ t₀}` — exactly the set where `etaShiftedNorm` is
    differentiable — so the order hypothesis is *consistent*.  The claim is
    that the normalized shifted eta has no zero of order `≥ 2` at the
    reference point `3/4 + I`.

    This is the research-level open core of the multiplicity-one argument:
    the residue/argument-principle computation (S4 step 5 of the plan) has no
    complete mathematical writeup, and simplicity of zeta zeros is open.  It is
    therefore left as an explicitly marked `sorry`. -/
lemma even_multiplicity_contradiction' (σ₀ t₀ : ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hσ : 1 / 2 < σ₀) (hσ' : σ₀ < 1) (ht : 0 < t₀)
    (h_zero : etaShifted (σ₀ + t₀ * I) = 0)
    (h_order : ∃ φ : ℂ → ℂ,
      (∀ z, z ≠ normBadPoint σ₀ t₀ → DifferentiableAt ℂ φ z) ∧
      φ (3 / 4 + I) ≠ 0 ∧
      ∀ z, z ≠ normBadPoint σ₀ t₀ →
        etaShiftedNorm σ₀ t₀ z = (z - (3 / 4 + I)) ^ m * φ z) :
    False := by
  sorry

/-- **S7 Layer 1 (provable): every strip zero of `etaShifted` has finite,
    positive order.**

    There is a natural number `m > 0` and a function `φ`, analytic at `s₀` with
    `φ s₀ ≠ 0`, such that locally near `s₀`,
    `etaShifted s = (s - s₀)^m • φ s`.  This is the honest replacement for the
    (false) global simple-factorization statement. -/
theorem etaShifted_zero_finite_order (s₀ : ℂ) (hσ₁ : s₀.re > 1 / 2)
    (hσ₂ : s₀.re < 1) (h_zero : etaShifted s₀ = 0) :
    ∃ (m : ℕ) (φ : ℂ → ℂ), 0 < m ∧ AnalyticAt ℂ φ s₀ ∧ φ s₀ ≠ 0 ∧
      ∀ᶠ s in 𝓝 s₀, etaShifted s = (s - s₀) ^ m • φ s := by
  sorry

/-- **S7 Layer 2 (GENUINE OPEN CORE): simplicity of strip zeros.**

    Every strip zero of `etaShifted` is *simple*: in `etaShifted_zero_finite_order`
    the order `m` equals `1`, i.e. there is a function `φ`, analytic at `s₀`
    with `φ s₀ ≠ 0`, and locally `etaShifted s = (s - s₀) • φ s`.

    Simplicity of zeta zeros is a famous open problem, so this is left as an
    explicitly marked `sorry`.

    Note: the *original* statement `etaShifted_zeros_simple` (a *global*
    factorization `∀ s, etaShifted s = (s - s₀) * φ s` with `φ` entire) is
    **false** — it would force `etaShifted` to be continuous at `s = 1`,
    contradicting `H1`/`H2`.  It is therefore replaced by this local form. -/
theorem etaShifted_order_eq_one (s₀ : ℂ) (hσ₁ : s₀.re > 1 / 2)
    (hσ₂ : s₀.re < 1) (h_zero : etaShifted s₀ = 0) :
    ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ s₀ ∧ φ s₀ ≠ 0 ∧
      ∀ᶠ s in 𝓝 s₀, etaShifted s = (s - s₀) • φ s := by
  sorry

end