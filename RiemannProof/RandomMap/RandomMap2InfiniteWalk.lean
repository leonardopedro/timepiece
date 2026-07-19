import RandomMap.RandomMap2Walk
import Mathlib.Probability.ProductMeasure

/-!
# RandomMap2 Phase 6: compatible infinite walk laws

This module supplies the projective-law infrastructure identified as the next
requirement after the finite Phase-6 estimates.  Given a center and a positive
radius for every natural coordinate, `infiniteWalkMeasure` is the countable
product of the corresponding scalar bump laws.  Its restriction to every
finite set of coordinates is exactly the expected finite product law, so these
finite marginals form one compatible family.

Under a summability hypothesis on the squared radii, the module also proves
almost-sure summability of the centered squared increments, bounds their total
energy by the radius budget, proves convergence of ordinary partial energies
to that total, bounds its expectation by the same radius budget, and computes
the exact expectation as one third of that budget.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

noncomputable section

namespace RandomMap2InfiniteWalk

/-- A countable product of centered scalar bump laws. -/
def infiniteWalkMeasure (x ε : ℕ → ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun n => scalarBumpMeasure (x n) (ε n))

/-
Positive coordinate radii make the infinite product a probability measure.
-/
instance infiniteWalkMeasure_isProbability (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] : IsProbabilityMeasure (infiniteWalkMeasure x ε) := by
  constructor ; simp +decide [ infiniteWalkMeasure ]

/-
The finite marginal indexed by `I` is the finite product of the same scalar
bump laws.  This is the projective compatibility missing from the earlier
finite-only construction.
-/
theorem map_restrict_infiniteWalkMeasure (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (I : Finset ℕ) :
    (infiniteWalkMeasure x ε).map I.restrict =
      Measure.pi (fun i : I => scalarBumpMeasure (x i) (ε i)) := by
  convert Measure.infinitePi_map_restrict ( fun n => scalarBumpMeasure ( x n ) ( ε n ) )

/-
Every coordinate marginal is its prescribed centered scalar bump.
-/
theorem map_eval_infiniteWalkMeasure (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (n : ℕ) :
    (infiniteWalkMeasure x ε).map (fun y => y n) =
      scalarBumpMeasure (x n) (ε n) := by
  convert Measure.infinitePi_map_eval ( fun n => scalarBumpMeasure ( x n ) ( ε n ) ) n using 1

/-
Restrictions are mutually compatible: restricting first to `J` and then to
`I ⊆ J` has the same law as restricting the infinite walk directly to `I`.
-/
theorem finite_marginals_compatible (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (I J : Finset ℕ) (hIJ : I ⊆ J) :
    (Measure.pi (fun j : J => scalarBumpMeasure (x j) (ε j))).map
        (fun (y : J → ℝ) (i : I) => y ⟨i.1, hIJ i.2⟩) =
      Measure.pi (fun i : I => scalarBumpMeasure (x i) (ε i)) := by
  rw [ MeasureTheory.Measure.pi_eq ];
  rw [ MeasureTheory.Measure.pi_eq ];
  any_goals exact Measure.pi fun i : J => scalarBumpMeasure ( x i ) ( ε i );
  · intro s hs; rw [ MeasureTheory.Measure.map_apply ];
    · rw [ show ( fun y : J → ℝ => fun i : I => y ⟨ i, hIJ i.2 ⟩ ) ⁻¹' univ.pi s = ( Set.pi ( Set.univ : Set J ) fun i => if h : i.val ∈ I then s ⟨ i.val, h ⟩ else Set.univ ) from ?_ ];
      · rw [ MeasureTheory.Measure.pi_pi ];
        rw [ ← Finset.prod_subset ( show Finset.image ( fun i : I => ⟨ i, hIJ i.2 ⟩ : I → J ) Finset.univ ⊆ Finset.univ from Finset.subset_univ _ ) ];
        · rw [ Finset.prod_image ] ; aesop;
          exact fun i _ j _ hij => by aesop;
        · simp +contextual [ Finset.mem_image ];
      · grind;
    · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
    · exact MeasurableSet.univ_pi hs;
  · intro s hs; rw [ MeasureTheory.Measure.pi_pi ] ;

/-
Every centered coordinate has mean zero under the compatible infinite law.
-/
theorem coordinate_centered (x ε : ℕ → ℝ) [∀ n, Fact (0 < ε n)] (n : ℕ) :
    ∫ y, (y n - x n) ∂infiniteWalkMeasure x ε = 0 := by
  have h_mean_zero : ∫ y : ℝ, (y - x n) ∂scalarBumpMeasure (x n) (ε n) = 0 := by
    unfold scalarBumpMeasure;
    rw [ ProbabilityTheory.cond ];
    rw [ MeasureTheory.integral_smul_measure ] ; norm_num [ Real.volume_Icc ];
    rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ] <;> norm_num ; ring ; norm_num [ (Fact.out : 0 < ε n).le ];
    linarith [ Fact.out ( p := 0 < ε n ) ];
  convert h_mean_zero using 1;
  rw [ ← map_eval_infiniteWalkMeasure x ε n, MeasureTheory.integral_map ];
  · exact measurable_pi_apply n |> Measurable.aemeasurable;
  · exact Measurable.aestronglyMeasurable ( measurable_id.sub measurable_const )

/-
Every coordinate has second moment at most its prescribed squared radius.
-/
theorem coordinate_secondMoment_bound (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (n : ℕ) :
    ∫ y, (y n - x n) ^ 2 ∂infiniteWalkMeasure x ε ≤ (ε n) ^ 2 := by
  -- By definition of $ε$, we know that $ε n > 0$.
  have hε_pos : 0 < ε n := by
    exact Fact.out ( p := 0 < ε n );
  have h_var_bound : ∫ y : ℝ, (y - x n) ^ 2 ∂scalarBumpMeasure (x n) (ε n) ≤ (ε n) ^ 2 := by
    have h_var_bound : ∫ y in Set.Icc (x n - ε n) (x n + ε n), (y - x n) ^ 2 ∂volume ≤ (ε n) ^ 2 * (2 * ε n) := by
      rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ] <;> norm_num [ sub_sq, mul_comm ] <;> ring <;> norm_num [ hε_pos.le ];
      nlinarith [ pow_pos hε_pos 3 ];
    unfold scalarBumpMeasure; rw [ ProbabilityTheory.cond ] ; norm_num [ Real.volume_Icc ] ; ring_nf at *;
    rw [ ENNReal.toReal_ofReal ( by positivity ), inv_mul_le_iff₀ ] <;> nlinarith [ pow_pos hε_pos 3 ];
  convert h_var_bound using 1;
  rw [ ← map_eval_infiniteWalkMeasure x ε n, MeasureTheory.integral_map ];
  · exact measurable_pi_apply n |> Measurable.aemeasurable;
  · exact Continuous.aestronglyMeasurable ( by continuity )

/-- Squared centered energy on an arbitrary finite coordinate set. -/
def finiteEnergy (I : Finset ℕ) (x y : ℕ → ℝ) : ℝ :=
  ∑ n ∈ I, (y n - x n) ^ 2

/-
The expected energy on any finite coordinate set is bounded by the sum of
its squared radii.
-/
theorem finiteEnergy_expectation_bound (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (I : Finset ℕ) :
    ∫ y, finiteEnergy I x y ∂infiniteWalkMeasure x ε ≤
      ∑ n ∈ I, (ε n) ^ 2 := by
  rw [ show ( fun y : ℕ → ℝ => finiteEnergy I x y ) = fun y : ℕ → ℝ => ∑ n ∈ I, ( y n - x n ) ^ 2 by rfl, MeasureTheory.integral_finset_sum ];
  · exact Finset.sum_le_sum fun i _ => coordinate_secondMoment_bound x ε i;
  · intro n hn
    have h_integrable : MeasureTheory.Integrable (fun y : ℝ => (y - x n) ^ 2) (scalarBumpMeasure (x n) (ε n)) := by
      unfold scalarBumpMeasure;
      rw [ ProbabilityTheory.cond ];
      rw [ MeasureTheory.integrable_smul_measure ] <;> norm_num;
      · exact Continuous.integrableOn_Icc ( by continuity );
      · exact Fact.out;
    have h_integrable : MeasureTheory.Integrable (fun y : ℝ => (y - x n) ^ 2) (Measure.map (fun y : ℕ → ℝ => y n) (infiniteWalkMeasure x ε)) := by
      rw [ map_eval_infiniteWalkMeasure ] ; aesop;
    convert h_integrable.comp_measurable ( measurable_pi_apply n ) using 1

/-
Each coordinate lies within its prescribed radius almost surely.
-/
theorem coordinate_abs_sub_le_radius (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (n : ℕ) :
    ∀ᵐ y ∂infiniteWalkMeasure x ε, |y n - x n| ≤ ε n := by
  have h_map_eval : (infiniteWalkMeasure x ε).map (fun y => y n) = scalarBumpMeasure (x n) (ε n) :=
    map_eval_infiniteWalkMeasure x ε n
  have h_scalar_bump : ∀ᵐ y ∂scalarBumpMeasure (x n) (ε n), |y - x n| ≤ ε n := by
    unfold scalarBumpMeasure;
    rw [ ProbabilityTheory.cond ];
    rw [ MeasureTheory.ae_iff ] ; norm_num;
    exact MeasureTheory.measure_mono_null ( fun y hy => by cases abs_cases ( y - x n ) <;> linarith [ hy.1.out, hy.2.1, hy.2.2 ] ) ( MeasureTheory.measure_empty );
  rw [ ← h_map_eval, MeasureTheory.ae_map_iff ] at h_scalar_bump;
  · exact h_scalar_bump;
  · exact measurable_pi_apply n |> Measurable.aemeasurable;
  · exact measurableSet_le ( measurable_norm.comp ( measurable_id.sub measurable_const ) ) measurable_const

/-
**Almost-sure finite-energy theorem.** If the squared coordinate radii are
summable, then a sample from the compatible infinite walk has summable squared
centered increments almost surely.
-/
theorem ae_summable_centered_energy (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (hε : Summable (fun n => (ε n) ^ 2)) :
    ∀ᵐ y ∂infiniteWalkMeasure x ε,
      Summable (fun n => (y n - x n) ^ 2) := by
  -- We'll use the fact that if the series of squared radii converges, then the series of squared differences also converges almost surely.
  have h_summable : ∀ᵐ y ∂infiniteWalkMeasure x ε, ∀ n, (y n - x n) ^ 2 ≤ (ε n) ^ 2 := by
    filter_upwards [ MeasureTheory.ae_all_iff.mpr fun n => coordinate_abs_sub_le_radius x ε n ] with y hy using fun n => by nlinarith [ abs_le.mp ( hy n ) ] ;
  filter_upwards [ h_summable ] with y hy using Summable.of_nonneg_of_le ( fun n => sq_nonneg _ ) hy hε

/-
Under summable squared radii, the total centered energy is bounded by the total
radius budget almost surely.
-/
theorem ae_tsum_centered_energy_le (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (hε : Summable (fun n => (ε n) ^ 2)) :
    ∀ᵐ y ∂infiniteWalkMeasure x ε,
      ∑' n, (y n - x n) ^ 2 ≤ ∑' n, (ε n) ^ 2 := by
  have h_bound : ∀ᵐ y ∂infiniteWalkMeasure x ε, Summable (fun n => (y n - x n) ^ 2) := by
    convert ae_summable_centered_energy x ε hε;
  filter_upwards [ h_bound, MeasureTheory.ae_all_iff.mpr fun n => coordinate_abs_sub_le_radius x ε n ] with y hy₁ hy₂;
  exact Summable.tsum_le_tsum ( fun n => by nlinarith only [ abs_le.mp ( hy₂ n ) ] ) hy₁ hε

/-
The ordinary partial energies converge almost surely to the total centered
energy.
-/
theorem ae_tendsto_partial_energy (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (hε : Summable (fun n => (ε n) ^ 2)) :
    ∀ᵐ y ∂infiniteWalkMeasure x ε,
      Tendsto (fun N => ∑ n ∈ Finset.range N, (y n - x n) ^ 2)
        atTop (𝓝 (∑' n, (y n - x n) ^ 2)) := by
  -- For almost every $y$, the series $\sum_{n=0}^{\infty} (y_n - x_n)^2$ converges.
  have h_summable : ∀ᵐ y ∂infiniteWalkMeasure x ε, Summable (fun n => (y n - x n) ^ 2) := by
    convert ae_summable_centered_energy x ε hε;
  filter_upwards [ h_summable ] with y hy using hy.hasSum.tendsto_sum_nat

/-
Each coordinate-energy observable is integrable under the infinite walk law.
-/
theorem integrable_coordinate_energy (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (n : ℕ) :
    Integrable (fun y => (y n - x n) ^ 2) (infiniteWalkMeasure x ε) := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun y => ( ε n ) ^ 2;
  · simp +decide [ MeasureTheory.integrable_const_iff ];
  · exact Measurable.aestronglyMeasurable ( by measurability );
  · filter_upwards [ coordinate_abs_sub_le_radius x ε n ] with y hy using by simpa using pow_le_pow_left₀ ( abs_nonneg _ ) hy 2;

/-
The expected total centered energy is bounded by the total squared-radius
budget.
-/
theorem totalEnergy_expectation_bound (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (hε : Summable (fun n => (ε n) ^ 2)) :
    ∫ y, (∑' n, (y n - x n) ^ 2) ∂infiniteWalkMeasure x ε ≤
      ∑' n, (ε n) ^ 2 := by
  rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
  · refine' le_trans ( ENNReal.toReal_mono _ _ ) _;
    exact ENNReal.ofReal ( ∑' n, ε n ^ 2 );
    · exact ENNReal.ofReal_ne_top;
    · refine' le_trans ( MeasureTheory.lintegral_mono_ae _ ) _;
      use fun y => ENNReal.ofReal ( ∑' n, ( ε n ) ^ 2 );
      · filter_upwards [ ae_tsum_centered_energy_le x ε hε ] with y hy using ENNReal.ofReal_le_ofReal hy;
      · simp +decide [ MeasureTheory.IsProbabilityMeasure.measure_univ ];
    · rw [ ENNReal.toReal_ofReal ( tsum_nonneg fun _ => sq_nonneg _ ) ];
  · exact Filter.Eventually.of_forall fun y => tsum_nonneg fun n => sq_nonneg _;
  · refine' MeasureTheory.AEStronglyMeasurable.congr _ _;
    exact fun y => ENNReal.toReal ( ∑' n, ENNReal.ofReal ( ( y n - x n ) ^ 2 ) );
    · refine' Measurable.aestronglyMeasurable _;
      fun_prop;
    · filter_upwards [ ae_summable_centered_energy x ε hε ] with y hy using ENNReal.tsum_toReal_eq ( by exact fun n => ENNReal.ofReal_ne_top ) |> fun h => h.trans ( tsum_congr fun n => ENNReal.toReal_ofReal ( sq_nonneg _ ) )

/-
For the uniform bump law, each centered coordinate has exact second moment
`ε n ^ 2 / 3`.
-/
theorem coordinate_secondMoment_eq (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (n : ℕ) :
    ∫ y, (y n - x n) ^ 2 ∂infiniteWalkMeasure x ε = (ε n) ^ 2 / 3 := by
  -- Use the fact that the integral of a function over a product measure is the product of the integrals.
  have h_prod : ∫ y : ℕ → ℝ, (y n - x n)^2 ∂(infiniteWalkMeasure x ε) = ∫ y : ℝ, (y - x n)^2 ∂(scalarBumpMeasure (x n) (ε n)) := by
    rw [ ← map_eval_infiniteWalkMeasure x ε n, MeasureTheory.integral_map ];
    · exact measurable_pi_apply n |> Measurable.aemeasurable;
    · exact Continuous.aestronglyMeasurable ( by continuity );
  rw [ h_prod, show ( ∫ y : ℝ, ( y - x n ) ^ 2 ∂scalarBumpMeasure ( x n ) ( ε n ) ) = ( ∫ y : ℝ in Set.Icc ( x n - ε n ) ( x n + ε n ), ( y - x n ) ^ 2 ∂MeasureTheory.volume ) / ( 2 * ε n ) from ?_ ];
  · rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ] <;> norm_num [ sub_sq, mul_comm ] <;> ring <;> norm_num [ ( Fact.out : 0 < ε n ) |> le_of_lt ];
    nlinarith only [ mul_inv_cancel₀ ( ne_of_gt ( Fact.out ( p := 0 < ε n ) ) ) ];
  · unfold scalarBumpMeasure; rw [ ProbabilityTheory.cond ] ; norm_num [ Real.volume_Icc ] ; ring;
    rw [ ENNReal.toReal_ofReal ( by linarith [ Fact.out ( p := 0 < ε n ) ] ) ] ; ring

/-
Consequently, under summable squared radii, the expected total centered energy
is exactly one third of the total squared-radius budget.
-/
theorem totalEnergy_expectation_eq (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (hε : Summable (fun n => (ε n) ^ 2)) :
    ∫ y, (∑' n, (y n - x n) ^ 2) ∂infiniteWalkMeasure x ε =
      (∑' n, (ε n) ^ 2) / 3 := by
  rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
  · have h_interchange : ∫⁻ (a : ℕ → ℝ), ENNReal.ofReal (∑' (n : ℕ), (a n - x n) ^ 2) ∂infiniteWalkMeasure x ε = ∑' (n : ℕ), ∫⁻ (a : ℕ → ℝ), ENNReal.ofReal ((a n - x n) ^ 2) ∂infiniteWalkMeasure x ε := by
      rw [ ← MeasureTheory.lintegral_tsum ];
      · refine' MeasureTheory.lintegral_congr_ae _;
        filter_upwards [ ae_summable_centered_energy x ε hε ] with a ha;
        rw [ ENNReal.ofReal_tsum_of_nonneg fun n => sq_nonneg _ ];
        exact ha;
      · exact fun n => Measurable.aemeasurable ( by measurability );
    rw [ h_interchange, ENNReal.tsum_toReal_eq ];
    · rw [ ← tsum_div_const ] ; congr ; ext n ; rw [ ← MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
      · convert coordinate_secondMoment_eq x ε n using 1;
      · exact Filter.Eventually.of_forall fun _ => sq_nonneg _;
      · exact Measurable.aestronglyMeasurable ( by measurability );
    · intro n; exact ne_of_lt ( MeasureTheory.Integrable.lintegral_lt_top ( by exact integrable_coordinate_energy x ε n ) ) ;
  · exact Filter.Eventually.of_forall fun y => tsum_nonneg fun n => sq_nonneg _;
  · refine' MeasureTheory.AEStronglyMeasurable.congr _ _;
    exact fun y => ENNReal.toReal ( ∑' n, ENNReal.ofReal ( ( y n - x n ) ^ 2 ) );
    · refine' Measurable.aestronglyMeasurable _;
      fun_prop;
    · filter_upwards [ ae_summable_centered_energy x ε hε ] with y hy using ENNReal.tsum_toReal_eq ( by exact fun n => ENNReal.ofReal_ne_top ) |> fun h => h.trans ( tsum_congr fun n => ENNReal.toReal_ofReal ( sq_nonneg _ ) )

/-
The finite-coordinate energy has exact expectation equal to one third of the
corresponding squared-radius budget.
-/
theorem finiteEnergy_expectation_eq (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (I : Finset ℕ) :
    ∫ y, finiteEnergy I x y ∂infiniteWalkMeasure x ε =
      ∑ n ∈ I, (ε n) ^ 2 / 3 := by
  convert MeasureTheory.integral_finset_sum I fun n hn => integrable_coordinate_energy x ε n using 1;
  exact Finset.sum_congr rfl fun n hn => by rw [ coordinate_secondMoment_eq x ε n ] ;

/-
Under summable squared radii, the infinite total-energy observable is
integrable, not merely finite almost surely.

The proof uses the dominated convergence theorem: the partial sums
`∑_{n ∈ range N} (y n - x n)^2` are integrable (finite sum of integrable
coordinate functions), converge monotonically to the total sum, and are
bounded above by the constant `∑' n, (ε n)^2` which is integrable on a
probability space.
-/
theorem integrable_totalEnergy (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (hε : Summable (fun n => (ε n) ^ 2)) :
    Integrable (fun y => ∑' n, (y n - x n) ^ 2)
      (infiniteWalkMeasure x ε) := by
  have h_bound : ∀ᵐ y ∂infiniteWalkMeasure x ε,
      (fun y => ∑' n, (y n - x n) ^ 2) y ≤ (fun _ : ℕ → ℝ => ∑' n, (ε n) ^ 2) y :=
    ae_tsum_centered_energy_le x ε hε
  have h_const_integrable : Integrable (fun _ : ℕ → ℝ => ∑' n, (ε n) ^ 2)
      (infiniteWalkMeasure x ε) := by
    apply integrable_const
  have h_ae_measurable : AEStronglyMeasurable (fun y : ℕ → ℝ => ∑' n, (y n - x n) ^ 2)
      (infiniteWalkMeasure x ε) := by
    have h_partial_meas (N : ℕ) : Measurable (fun y : ℕ → ℝ =>
        ∑ n ∈ Finset.range N, (y n - x n) ^ 2) := by
      refine Finset.measurable_sum (Finset.range N) (fun n hn => ?_)
      exact ((measurable_pi_apply n).sub measurable_const).pow 2
    have h_tsum_eq_sup : (fun y : ℕ → ℝ => ∑' n, (y n - x n) ^ 2) =
        (fun y => ⨆ N : ℕ, ∑ n ∈ Finset.range N, (y n - x n) ^ 2) := by
      ext y
      rw [tsum_eq_iSup_sum (fun n => (y n - x n) ^ 2)]
    rw [h_tsum_eq_sup]
    exact aestronglyMeasurable_iSup h_partial_meas
  exact h_const_integrable.mono h_ae_measurable h_bound

end RandomMap2InfiniteWalk