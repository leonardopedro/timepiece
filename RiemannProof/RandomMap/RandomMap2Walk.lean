import RandomMap.RandomMap2Moments

/-!
# RandomMap2 Phase 6: a concrete finite random-walk law

The earlier proposed Phase-6 estimate quantified over an arbitrary probability
measure and was false.  This module gives the corrected concrete law: a point
`Y` is sampled from the normalized product bump centered at `x`, and the walk
increments are its centered coordinates `Y i - x i`.

The partial energy is the sum of the squared first `n` increments.  Its expected
value is at most `min n N * ε²`; consequently the mean squared energy per active
coordinate is at most `ε²`.  These finite-dimensional estimates are the sound
replacement for the false arbitrary-law bound.  No almost-sure infinite-series
claim is made without an explicitly specified compatible family of laws.
-/

open MeasureTheory ProbabilityTheory Set

noncomputable section

namespace RandomMap2Walk

/-- The first `n` active coordinate indices of an `N`-dimensional walk. -/
def activeCoordinates (N n : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => i.1 < n)

/-- Squared energy of the first `n` centered increments. -/
def partialEnergy {N : ℕ} (n : ℕ) (x y : InnerHead N) : ℝ :=
  ∑ i ∈ activeCoordinates N n, (y i - x i) ^ 2

/-
The number of active coordinates is `min n N`.
-/
theorem card_activeCoordinates (N n : ℕ) :
    (activeCoordinates N n).card = min n N := by
  rw [ Finset.card_eq_of_bijective ];
  use fun i hi => ⟨ i, by linarith [ min_le_right n N ] ⟩;
  · unfold activeCoordinates; aesop;
  · exact fun i hi => Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by linarith [ min_le_left n N ] ⟩;
  · grind

/-
Each finite partial energy is integrable under the concrete product-bump law.
-/
theorem integrable_partialEnergy {N : ℕ} (n : ℕ) (x : InnerHead N) (ε : ℝ)
    [Fact (0 < ε)] :
    Integrable (partialEnergy n x) (normalizedBumpMeasure x ε) := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun y => ( ∑ i : Fin N, ( y i - x i ) ^ 2 );
  · refine' MeasureTheory.integrable_finset_sum _ _;
    intro i _;
    refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun y => ε ^ 2;
    · exact MeasureTheory.integrable_const _;
    · exact Measurable.aestronglyMeasurable ( by measurability );
    · refine' MeasureTheory.measure_mono_null _ _;
      exact { y : InnerHead N | |y i - x i| > ε };
      · simp +decide [ Set.subset_def, abs_le ];
        exact fun y hy => by cases abs_cases ( y i - x i ) <;> nlinarith [ Fact.out ( p := 0 < ε ) ] ;
      · erw [ show { y : Fin N → ℝ | |y i - x i| > ε } = ( Set.pi Set.univ fun j => if j = i then { y : ℝ | |y - x i| > ε } else Set.univ ) by ext; aesop ] ; erw [ MeasureTheory.Measure.pi_pi ] ;
        rw [ Finset.prod_eq_zero ( Finset.mem_univ i ) ] ; simp +decide [ scalarBumpMeasure ];
        rw [ ProbabilityTheory.cond_apply ];
        · rw [ show ( Icc ( x i - ε ) ( x i + ε ) ∩ { y : ℝ | ε < |y - x i| } ) = ∅ from Set.eq_empty_of_forall_notMem fun y hy => by cases abs_cases ( y - x i ) <;> linarith [ hy.1.1, hy.1.2, hy.2.out ] ] ; norm_num;
        · exact measurableSet_Icc;
  · refine' Measurable.aestronglyMeasurable _;
    refine' Finset.measurable_sum _ _;
    fun_prop;
  · refine' Filter.Eventually.of_forall fun y => _;
    exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => abs_nonneg _ ) |> le_trans <| Finset.sum_le_sum fun _ _ => by rw [ abs_sq ] ;

/-
**Corrected Phase-6 bound.** Under the concrete product-bump law, the
expected squared energy of the first `n` increments is at most
`min n N * ε²`.
-/
theorem partialEnergy_expectation_bound {N : ℕ} (n : ℕ) (x : InnerHead N)
    (ε : ℝ) [Fact (0 < ε)] :
    ∫ y, partialEnergy n x y ∂normalizedBumpMeasure x ε ≤
      (min n N : ℝ) * ε ^ 2 := by
  have h_bound : ∀ i ∈ activeCoordinates N n,
      ∫ y : InnerHead N, (y i - x i) ^ 2 ∂normalizedBumpMeasure x ε ≤ ε ^ 2 := by
    intro i _
    exact Var_X_coordinate_bound x ε i
  convert Finset.sum_le_sum h_bound;
  · rw [ ← MeasureTheory.integral_finset_sum ];
    · rfl;
    · intro i hi;
      convert integrable_partialEnergy n x ε |> fun h => h.mono' _ _;
      · exact Measurable.aestronglyMeasurable ( by measurability );
      · filter_upwards [ ] with y using by rw [ Real.norm_of_nonneg ( sq_nonneg _ ) ] ; exact Finset.single_le_sum ( fun i _ => sq_nonneg ( y i - x i ) ) hi;
  · norm_num [ card_activeCoordinates ]

/-
Full-dimensional specialization of the corrected Phase-6 estimate.
-/
theorem fullEnergy_expectation_bound {N : ℕ} (x : InnerHead N) (ε : ℝ)
    [Fact (0 < ε)] :
    ∫ y, partialEnergy N x y ∂normalizedBumpMeasure x ε ≤
      (N : ℝ) * ε ^ 2 := by
  exact le_trans ( partialEnergy_expectation_bound N x ε ) ( by norm_num )

/-
The expected mean squared increment is at most `ε²` in positive dimension.
-/
theorem meanEnergy_expectation_bound {N : ℕ} (hN : 0 < N)
    (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)] :
    ∫ y, partialEnergy N x y / N ∂normalizedBumpMeasure x ε ≤ ε ^ 2 := by
  convert div_le_div_of_nonneg_right ( fullEnergy_expectation_bound x ε ) ( Nat.cast_nonneg N ) using 1;
  · rw [ MeasureTheory.integral_div ];
  · rw [ mul_div_cancel_left₀ _ ( by positivity ) ]

end RandomMap2Walk