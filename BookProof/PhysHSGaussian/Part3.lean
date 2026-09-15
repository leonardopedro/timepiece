import Mathlib
import BookProof.PhysMeasureBasis
import BookProof.PhysHSGaussian.Part2

/-!
# Part 3b: The uniform sphere measure and the Gaussian limit (G0–G7)

The Gegenbauer → Hermite limit, the weight → Gaussian limit, the
normalization-constant limit, and the uniform-sphere ↔ Gaussian
identification.  This module is independent of the main chain.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace PhysHSGaussian

open PhysMeasureBasis
/-! ### G4 (first half). The normalization-constant limit via dominated convergence

The statement below is the chapter's normalization limit *after* the change of
variables `x_old = x/√λ` has been carried out (the substitution is baked into the
interval `[-√λ, √λ]` and the `gegenbauerScaled`/weight integrand), as permitted by
the plan. -/

/-
The rescaled three-term recurrence for `gegenbauerScaled` (for `λ > 0`).
-/
theorem gegenbauerScaled_rec (n : ℕ) (lam x : ℝ) (hl : 0 < lam) :
    ((n : ℝ) + 2) * gegenbauerScaled (n+2) lam x
      = 2 * x * (1 + (n + 1) / lam) * gegenbauerScaled (n+1) lam x
        - (2 + n / lam) * gegenbauerScaled n lam x := by
  unfold gegenbauerScaled;
  convert congr_arg ( fun y => lam ^ ( ( -2 + -n : ℝ ) / 2 ) * y ) ( gegenbauer_rec n lam ( x /
    Real.sqrt lam ) ) using 1 <;> ring;
  · push_cast; ring;
  · norm_num [ Real.sqrt_eq_rpow, Real.rpow_add hl, Real.rpow_neg hl.le ] ; ring;
    rw [ Real.rpow_add hl, Real.rpow_mul hl.le ] ; norm_num [ hl.ne' ] ; ring

/-
A uniform-in-`λ` polynomial bound on the rescaled Gegenbauer functions.
-/
theorem gegenbauerScaled_bound (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ lam : ℝ, 1 ≤ lam → ∀ x : ℝ,
      |gegenbauerScaled n lam x| ≤ B * (1 + |x|)^n := by
  induction n using Nat.strong_induction_on with | _ n ih => ?_
  rcases n with ( _ | _ | n );
  · unfold gegenbauerScaled; aesop;
  · refine ⟨ 2, by norm_num, fun lam hl x => ?_ ⟩ ; norm_num [ gegenbauerScaled ];
    rw [ Real.rpow_neg ( by positivity ), abs_of_nonneg ( by positivity : 0 ≤ lam ) ];
    rw [ ← Real.sqrt_eq_rpow, abs_of_nonneg ( by positivity ), abs_div, abs_of_nonneg (
        Real.sqrt_nonneg _ ) ];
    field_simp;
    rw [ Real.sq_sqrt ] <;> nlinarith [ abs_nonneg x ];
  · obtain ⟨ B₁, hB₁, hB₁' ⟩ := ih ( n + 1 ) ( by linarith )
    ( obtain ⟨ B₂, hB₂, hB₂' ⟩ := ih n ( by linarith ) ; use 2 * ( B₁ + B₂ ) ; norm_num ; )
    refine ⟨ by positivity, fun lam hl x => ?_ ⟩
    have h_recurrence : (n + 2) * |gegenbauerScaled (n + 2) lam x| ≤ 2 * |x| * (1 + (n + 1) / lam) *
      |gegenbauerScaled (n + 1) lam x| + (2 + n / lam) * |gegenbauerScaled n lam x| := by
      have h_recurrence : (n + 2) * gegenbauerScaled (n + 2) lam x = 2 * x * (1 + (n + 1) / lam) *
        gegenbauerScaled (n + 1) lam x - (2 + n / lam) * gegenbauerScaled n lam x := by
        exact gegenbauerScaled_rec n lam x ( by positivity )
      generalize_proofs at *; (
      have h_abs : |(n + 2) * gegenbauerScaled (n + 2) lam x| ≤ |2 * x * (1 + (n + 1) / lam) *
        gegenbauerScaled (n + 1) lam x| + |(2 + n / lam) * gegenbauerScaled n lam x| := by
        exact h_recurrence ▸ abs_sub _ _
      generalize_proofs at *; (
      convert h_abs using 1 <;> norm_num [ abs_mul, abs_of_nonneg, add_nonneg, div_nonneg, hl ]
      ring
      rw [ abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ 1 + n * lam⁻¹ + lam⁻¹ ), abs_of_nonneg (
          by positivity : ( 0 : ℝ ) ≤ 2 + n * lam⁻¹ ) ]
      ring
      ))
    generalize_proofs at *; (
    -- Apply the induction hypothesis to bound the terms involving `gegenbauerScaled`.
    have h_bound : (n + 2) * |gegenbauerScaled (n + 2) lam x| ≤ 2 * |x| * (1 + (n + 1)) * B₁ * (1 +
      |x|) ^ (n + 1) + (2 + n) * B₂ * (1 + |x|) ^ n := by
      refine le_trans h_recurrence ?_;
      refine add_le_add ?_ ?_;
      · refine le_trans ( mul_le_mul_of_nonneg_left ( hB₁' lam hl x ) ( by positivity ) ) ?_;
        norm_num [ mul_assoc ];
        exact mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_right ( by rw [ add_div', div_le_iff₀
            ] <;> nlinarith ) ( by positivity ) ) ( by positivity );
      · exact le_trans ( mul_le_mul_of_nonneg_left ( hB₂' lam hl x ) ( by positivity ) ) (
          by nlinarith [ show ( n : ℝ ) / lam ≤ n by rw [ div_le_iff₀ ] <;> nlinarith, show ( 0 : ℝ
          ) ≤ B₂ * ( 1 + |x| ) ^ n by positivity ] )
    generalize_proofs at *; (
    ring_nf at h_bound ⊢;
    nlinarith [ show 0 ≤ |x| * B₁ * ( 1 + |x| ) ^ n by positivity, show 0 ≤ |x| * B₂ * ( 1 + |x|
        ) ^ n by positivity, show 0 ≤ |x| ^ 2 * B₁ * ( 1 + |x|
        ) ^ n by positivity, show 0 ≤ |x| ^ 2 * B₂ * ( 1 + |x| ) ^ n by positivity, show 0 ≤ B₁ * (
        1 + |x| ) ^ n by positivity, show 0 ≤ B₂ * ( 1 + |x| ) ^ n by positivity ]))

theorem normalization_tendsto (n : ℕ) :
    Filter.Tendsto
      (fun lam => ∫ x in (-Real.sqrt lam)..(Real.sqrt lam),
          (gegenbauerScaled n lam x)^2 * (1 - x^2/lam) ^ (lam - 1/2))
      Filter.atTop
      (𝓝 (∫ x : ℝ, (physHermite n x / n.factorial)^2 * Real.exp (-x^2))) := by
  -- Apply the Dominated Convergence Theorem.
  have h_dominated : Filter.Tendsto (fun lam => ∫ x : ℝ, (if |x| ≤ Real.sqrt lam then
    (gegenbauerScaled n lam x)^2 * (1 - x^2 / lam)^(lam - 1/2) else 0)) Filter.atTop (nhds (∫ x : ℝ,
    (physHermite n x / n.factorial)^2 * Real.exp (-x^2))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      ( fun x => ( gegenbauerScaled_bound n |> Classical.choose ) ^ 2 * ( 1 + |x| ) ^ ( 2 * n ) *
        Real.exp ( -x ^ 2 / 2 ) ) ?_ ?_ ?_ ?_
    · refine Filter.eventually_atTop.mpr ⟨ 1, fun lam hl => ?_ ⟩
      refine Measurable.aestronglyMeasurable ?_
      refine Measurable.ite ?_ ?_ ?_ <;> norm_num
      · exact measurableSet_Iic.mem.comp measurable_norm;
      · refine Measurable.mul ?_ ?_;
        · refine Measurable.pow_const ?_ _;
          refine Measurable.mul ?_ ?_;
          · exact measurable_const;
          · refine Measurable.comp ( show Measurable ( gegenbauer n lam ) from ?_ ) (
            measurable_id'.div_const _ );
            induction n using Nat.strong_induction_on with | _ n ih => ?_
            rcases n with ( _ | _ | n ) <;> simp_all? +decide [ gegenbauer ];
            · exact measurable_const.mul measurable_id';
            · exact Measurable.mul ( Measurable.sub ( Measurable.mul ( measurable_const.mul
                measurable_id' ) measurable_const |> Measurable.mul <| ih _ <| by linarith ) <|
                Measurable.mul measurable_const <| ih _ <| by linarith ) measurable_const;
        · exact Measurable.pow_const ( by exact Measurable.sub measurable_const (
            by exact Measurable.div_const ( measurable_id.pow_const 2 ) _ ) ) _;
    · refine Filter.eventually_atTop.mpr ⟨ 1, fun lam hl => Filter.Eventually.of_forall fun x => ?_
      ⟩
      split_ifs <;> norm_num
      · refine le_trans ( mul_le_mul_of_nonneg_right ( show ( gegenbauerScaled n lam x ) ^ 2 ≤ (
        Classical.choose ( gegenbauerScaled_bound n ) ) ^ 2 * ( 1 + |x| ) ^ ( 2 * n ) by
                                                          have := Classical.choose_spec (
                                                            gegenbauerScaled_bound n ) |>.2 lam hl
                                                            x;
                                                          convert pow_le_pow_left₀ ( abs_nonneg _ )
                                                            this 2 using 1 <;> norm_num [ mul_pow,
                                                            pow_mul' ] ) ( abs_nonneg _ ) ) ?_;
        gcongr;
        have hlam : (0:ℝ) ≤ lam := by positivity
        have hxx : x ^ 2 ≤ lam := by
          nlinarith [ abs_le.mp ‹_›, Real.mul_self_sqrt hlam ]
        have hsub : (0:ℝ) ≤ 1 - x ^ 2 / lam :=
          sub_nonneg.2 <| div_le_one_of_le₀ hxx ( by positivity )
        rw [ abs_of_nonneg ( Real.rpow_nonneg hsub _ ) ]
        refine le_trans ( Real.rpow_le_rpow hsub
          ( show 1 - x ^ 2 / lam ≤ Real.exp ( -x ^ 2 / lam ) from ?_ ) <| by linarith ) ?_;
        · exact le_trans ( by ring_nf; norm_num ) ( Real.add_one_le_exp _ );
        · rw [ ← Real.exp_mul ] ; ring_nf ; norm_num;
          nlinarith [ inv_mul_cancel_left₀ ( by positivity : lam ≠ 0 ) ( x ^ 2 ), abs_le.mp ‹_›,
              Real.mul_self_sqrt ( show 0 ≤ lam by positivity ) ];
      · exact mul_nonneg ( mul_nonneg ( sq_nonneg _ ) ( pow_nonneg ( by positivity ) _ ) ) (
          Real.exp_nonneg _ );
    · have h_integrable : MeasureTheory.Integrable (fun x : ℝ => (1 + |x|)^(2 * n) * Real.exp (-x^2
      / 2)) MeasureTheory.volume := by
        have h_poly_exp : ∀ k : ℕ, MeasureTheory.Integrable (fun x : ℝ => |x|^k * Real.exp (-x^2 /
          2)) MeasureTheory.volume := by
          intro k
          have := @integrable_rpow_mul_exp_neg_mul_sq
          simp_all? +decide [ div_eq_inv_mul ]
          specialize @this ( 1 / 2 ) ( by norm_num ) ( k : ℝ ) ( by linarith );
          convert this.norm using 2 ; norm_num [ abs_mul, abs_of_nonneg, Real.exp_nonneg ];
        simp_all? +decide [ add_comm ( 1 : ℝ ), add_pow, mul_comm ];
        simp_all +decide only [ Finset.mul_sum _ _ _, mul_comm, mul_assoc ]
        exact MeasureTheory.integrable_finset_sum _ fun i hi => by
          simpa only [ mul_assoc, mul_left_comm, mul_comm ] using h_poly_exp i |> fun h =>
            h.const_mul ( Nat.choose ( n * 2 ) i : ℝ )
      simpa only [ mul_assoc ] using h_integrable.const_mul _;
    · refine Filter.Eventually.of_forall fun x => ?_;
      -- We'll use the fact that if the denominator grows faster than the numerator, the limit will
      -- be zero.
      have h_lim : Filter.Tendsto (fun lam => (gegenbauerScaled n lam x)^2 * (1 - x^2 / lam)^(lam -
        1/2)) Filter.atTop (nhds ((physHermite n x / n.factorial)^2 * Real.exp (-x^2))) := by
        refine Filter.Tendsto.mul ?_ ?_;
        · exact Filter.Tendsto.pow ( gegenbauerScaled_tendsto_hermite n x ) _;
        · convert weight_tendsto_gaussian x using 1;
      refine h_lim.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop ( x ^ 2 ) ] with lam hl using by
        rw [ if_pos ( Real.abs_le_sqrt <| by nlinarith ) ]
  refine h_dominated.congr' ?_ |> fun h => h.trans ?_;
  · filter_upwards [ Filter.eventually_gt_atTop 0 ] with lam hl;
    rw [ intervalIntegral.integral_of_le ( by linarith [ Real.sqrt_nonneg lam ] ), ←
        MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
    rw [ ← MeasureTheory.integral_congr_ae ];
    filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (
      MeasureTheory.measure_singleton ( -Real.sqrt lam ) ) ] with x hx;
    grind;
  · grind

/-! ### G6–G7. Poincaré–Borel: sphere marginals → Gaussian

Everything is realized on the single probability space `γ = gammaMeasure`, the
infinite product of standard Gaussians on `ℕ → ℝ`. -/

/-- The infinite product of standard Gaussians (the law of an i.i.d. Gaussian
    sequence). -/
def gammaMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.gaussianReal 0 1)

instance gammaMeasure_isProbability : IsProbabilityMeasure gammaMeasure := by
  unfold gammaMeasure; infer_instance

/-- Empirical squared norm of the first `k` coordinates. -/
def normSq (k : ℕ) (ω : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range k, (ω i)^2

/-
a.s. concentration (the strong law): the normalized empirical squared norm
    of the first `k` coordinates converges to `1`.
-/
theorem gaussian_concentration_sphere :
    ∀ᵐ ω ∂gammaMeasure,
      Filter.Tendsto (fun k => normSq k ω / k) Filter.atTop (𝓝 1) := by
  convert ProbabilityTheory.strong_law_ae _ _ _ _ using 1;
  case convert_4 => exact ℝ;
  case convert_10 => exact fun i ω => ( ω i ) ^ 2;
  all_goals try infer_instance;
  · have h_integral : ∫ x : ℕ → ℝ, x 0 ^ 2 ∂gammaMeasure = 1 := by
      have h_gauss : ∫ x : ℝ, x ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) = 1 := by
        have := @ProbabilityTheory.variance_id_gaussianReal 0 1;
        rw [ ProbabilityTheory.variance, ProbabilityTheory.evariance_eq_lintegral_ofReal, ←
          MeasureTheory.integral_eq_lintegral_of_nonneg_ae ] at this <;> norm_num at *;
        · exact this;
        · exact Filter.Eventually.of_forall fun x => sq_nonneg x;
        · exact Continuous.aestronglyMeasurable ( continuous_pow 2 );
      have h_gauss : ∫ x : ℕ → ℝ, x 0 ^ 2 ∂gammaMeasure = ∫ x : ℝ, x ^ 2
        ∂(ProbabilityTheory.gaussianReal 0 1) := by
        have h_map : MeasureTheory.Measure.map (fun x : ℕ → ℝ => x 0) gammaMeasure =
          ProbabilityTheory.gaussianReal 0 1 := by
          convert MeasureTheory.Measure.infinitePi_map_eval _ _ using 1;
          exact fun _ => by infer_instance;
        rw [ ← h_map, MeasureTheory.integral_map ];
        · exact measurable_pi_apply 0 |> Measurable.aemeasurable;
        · exact Continuous.aestronglyMeasurable ( continuous_pow 2 );
      linarith;
    simp_all +decide [ div_eq_inv_mul, normSq ];
  · have h_integrable : MeasureTheory.Integrable (fun x : ℝ => x^2) (ProbabilityTheory.gaussianReal
    0 1) := by
      have h_gauss_integrable : ∫ x, x ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) = 1 := by
        have := @ProbabilityTheory.variance_id_gaussianReal 0 1;
        rw [ ProbabilityTheory.variance, ProbabilityTheory.evariance_eq_lintegral_ofReal, ←
          MeasureTheory.integral_eq_lintegral_of_nonneg_ae ] at this <;> norm_num at *;
        · exact this;
        · exact Filter.Eventually.of_forall fun x => sq_nonneg x;
        · exact Continuous.aestronglyMeasurable ( continuous_pow 2 );
      exact ( by contrapose! h_gauss_integrable; rw [ MeasureTheory.integral_undef
          h_gauss_integrable ] ; norm_num );
    have h_integrable : MeasureTheory.Integrable (fun ω : ℕ → ℝ => ω 0 ^ 2) (Measure.infinitePi (fun
      _ : ℕ => ProbabilityTheory.gaussianReal 0 1)) := by
      have h_map : (Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.gaussianReal 0 1)).map (fun ω
        : ℕ → ℝ => ω 0) = ProbabilityTheory.gaussianReal 0 1 := by
        convert MeasureTheory.Measure.infinitePi_map_eval _ _ using 1;
        exact fun _ => inferInstance
      rw [ ← h_map ] at h_integrable;
      rwa [ MeasureTheory.integrable_map_measure ] at h_integrable;
      · exact h_integrable.1;
      · exact measurable_pi_apply 0 |> Measurable.aemeasurable;
    exact h_integrable;
  · have h_indep : ProbabilityTheory.iIndepFun (fun i : ℕ => fun ω : ℕ → ℝ => ω i) gammaMeasure
    := by
      convert ProbabilityTheory.iIndepFun_infinitePi ( fun i => measurable_id ) using 1;
      infer_instance;
    exact fun i j hij => h_indep.indepFun hij |> fun h => h.comp ( measurable_id.pow_const 2 ) (
      measurable_id.pow_const 2 );
  · intro i
    have h_ident : ProbabilityTheory.IdentDistrib (fun ω : ℕ → ℝ => ω i) (fun ω : ℕ → ℝ => ω 0)
      gammaMeasure gammaMeasure := by
      constructor;
      · exact measurable_pi_apply i |> Measurable.aemeasurable;
      · exact measurable_pi_apply 0 |> Measurable.aemeasurable;
      · have h_map : ∀ i : ℕ, Measure.map (fun ω : ℕ → ℝ => ω i) gammaMeasure =
        ProbabilityTheory.gaussianReal 0 1 := by
          intro i
          generalize_proofs at *; (
          convert MeasureTheory.Measure.infinitePi_map_eval ( fun _ =>
            ProbabilityTheory.gaussianReal 0 1 ) i using 1);
        rw [ h_map i, h_map 0 ]
    generalize_proofs at *; (
    exact h_ident.comp ( measurable_id.pow_const 2 ))

/-
a.s. Poincaré–Borel: the `√k`-sphere normalization of the first `k` Gaussian
    coordinates converges coordinatewise to the coordinates themselves.
-/
theorem poincare_borel_ae :
    ∀ᵐ ω ∂gammaMeasure, ∀ i : ℕ,
      Filter.Tendsto
        (fun k : ℕ => (Real.sqrt k / Real.sqrt (normSq k ω)) * ω i)
        Filter.atTop (𝓝 (ω i)) := by
  have h_ae_all : ∀ᵐ ω ∂gammaMeasure, ∀ i : ℕ, Filter.Tendsto (fun k : ℕ => Real.sqrt k / Real.sqrt
    (normSq k ω)) Filter.atTop (nhds 1) := by
    have h_ae_all : ∀ᵐ ω ∂gammaMeasure, Filter.Tendsto (fun k : ℕ => Real.sqrt (normSq k ω / k))
      Filter.atTop (nhds 1) := by
      have := @gaussian_concentration_sphere;
      exact this.mono fun ω hω => by simpa using Filter.Tendsto.sqrt hω;
    filter_upwards [ h_ae_all ] with ω hω using by simpa using hω.inv₀;
  filter_upwards [ h_ae_all ] with ω hω using fun i => by
    simpa using hω i |> Filter.Tendsto.mul_const ( ω i )

end PhysHSGaussian
