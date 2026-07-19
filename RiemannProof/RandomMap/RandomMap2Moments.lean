import RandomMap.RandomMap2

/-!
# RandomMap2 Phase 5: finite-head expectation and moments

This module supplies the sound measure-theoretic content of Phase 5.  A bump on
`Fin N → ℝ` is the product of the one-dimensional uniform probability laws on
`[x i - ε, x i + ε]`.  Defining it as a product of conditional Lebesgue laws
avoids the incorrect normalization formula in the prose roadmap (which also
fails in dimension zero).
-/

open MeasureTheory ProbabilityTheory Complex Set

noncomputable section

/-- The uniform probability law on the interval of radius `ε` centered at `a`. -/
def scalarBumpMeasure (a ε : ℝ) : Measure ℝ :=
  volume[|Icc (a - ε) (a + ε)]

/-- The finite-dimensional product bump centered at `x`. -/
def normalizedBumpMeasure {N : ℕ} (x : InnerHead N) (ε : ℝ) :
    Measure (InnerHead N) :=
  Measure.pi (fun i => scalarBumpMeasure (x i) ε)

instance scalarBumpMeasure_isProbability (a ε : ℝ) [Fact (0 < ε)] :
    IsProbabilityMeasure (scalarBumpMeasure a ε) := by
  constructor;
  unfold scalarBumpMeasure;
  rw [ ProbabilityTheory.cond_apply ];
  · rw [ Set.inter_univ, ENNReal.inv_mul_cancel ] <;> norm_num [ Real.volume_Icc, Fact.out ( p := 0 < ε ) ];
  · exact measurableSet_Icc

instance normalizedBumpMeasure_isProbability {N : ℕ} (x : InnerHead N) (ε : ℝ)
    [Fact (0 < ε)] : IsProbabilityMeasure (normalizedBumpMeasure x ε) := by
  constructor;
  unfold normalizedBumpMeasure;
  simp +decide [ MeasureTheory.Measure.pi_univ ]

/-
Expectation sends the zero observable to zero.
-/
theorem E_zero {N : ℕ} (headDist : Measure (InnerHead N)) :
    ∫ _x : InnerHead N, (0 : ℂ) ∂headDist = 0 := by
  cases isEmpty_or_nonempty ( InnerHead N ) <;> simp_all +decide [ MeasureTheory.MeasureSpace.volume ]

/-
Additivity of expectation for integrable finite-head observables.
-/
theorem E_add {N : ℕ} (headDist : Measure (InnerHead N))
    (f g : InnerHead N → ℂ) (hf : Integrable f headDist) (hg : Integrable g headDist) :
    ∫ x, (f + g) x ∂headDist =
      (∫ x, f x ∂headDist) + ∫ x, g x ∂headDist := by
  convert MeasureTheory.integral_add hf hg using 1

/-
Complex scalar multiplication commutes with expectation.
-/
theorem E_smul {N : ℕ} (headDist : Measure (InnerHead N))
    (c : ℂ) (f : InnerHead N → ℂ) :
    ∫ x, c * f x ∂headDist = c * ∫ x, f x ∂headDist := by
  convert MeasureTheory.integral_const_mul c f using 1

/-
The normalized bump has total expectation one.
-/
theorem exp_X_eq_one {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)] :
    ∫ _y : InnerHead N, (1 : ℂ) ∂normalizedBumpMeasure x ε = 1 := by
  simp +decide [ MeasureTheory.Measure.real ]

/-
Each coordinate of the product bump is centered at the corresponding coordinate of `x`.
-/
theorem X_coordinate_orthogonal {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)]
    (i : Fin N) :
    ∫ y : InnerHead N, (y i - x i) ∂normalizedBumpMeasure x ε = 0 := by
  unfold normalizedBumpMeasure;
  -- By definition of product measure, we can write the integral as the product of the integrals over each coordinate.
  have h_prod_measure : ∫ y : InnerHead N, (y i - x i) ∂Measure.pi (fun i => scalarBumpMeasure (x i) ε) = (∫ y : ℝ, (y - x i) ∂scalarBumpMeasure (x i) ε) * (∏ j ∈ Finset.univ.erase i, ∫ y : ℝ, (1 : ℝ) ∂scalarBumpMeasure (x j) ε) := by
    have h_prod_measure : ∀ (f : Fin N → ℝ → ℂ), (∫ y : InnerHead N, (∏ j, f j (y j)) ∂Measure.pi (fun i => scalarBumpMeasure (x i) ε)) = (∏ j, ∫ y : ℝ, f j y ∂scalarBumpMeasure (x j) ε) := by
      intro f;
      rw [ ← MeasureTheory.integral_fintype_prod_eq_prod ];
    convert h_prod_measure ( fun j y => if j = i then y - x i else 1 ) using 1;
    simp +decide [ Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ];
    rw [ Finset.prod_eq_single i ] <;> simp +contextual [ Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ];
    norm_cast;
    convert Iff.rfl;
    convert Complex.ofReal_inj; all_goals convert integral_ofReal;
  -- By definition of the scalar bump measure, we know that the integral of (y - x_i) over the interval [x_i - ε, x_i + ε] is zero.
  have h_scalar_bump : ∫ y in Set.Icc (x i - ε) (x i + ε), (y - x i) = 0 := by
    rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ] <;> norm_num ; linarith [ Fact.out ( p := 0 < ε ) ];
    linarith [ Fact.out ( p := 0 < ε ) ];
  simp_all +decide [ scalarBumpMeasure, ProbabilityTheory.cond ]

/-
The vector-valued centered bump has mean zero.
-/
theorem X_orthogonal {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)] :
    ∫ y : InnerHead N, (y - x) ∂normalizedBumpMeasure x ε = 0 := by
  by_contra h_nonzero;
  have h_integral : ∀ i : Fin N, ∫ y : InnerHead N, (y i - x i) ∂normalizedBumpMeasure x ε = 0 := by
    intro i
    exact X_coordinate_orthogonal x ε i;
  have h_integral : ∫ y : InnerHead N, (y - x) ∂normalizedBumpMeasure x ε = ∑ i : Fin N, (∫ y : InnerHead N, (y i - x i) ∂normalizedBumpMeasure x ε) • (Pi.single i 1 : InnerHead N) := by
    have h_integrable : MeasureTheory.Integrable (fun y : InnerHead N => y - x) (normalizedBumpMeasure x ε) := by
      exact ( Classical.not_not.1 fun h => h_nonzero <| MeasureTheory.integral_undef h )
    have h_integral : ∀ i : Fin N, ∫ y : InnerHead N, (y i - x i) • (Pi.single i 1 : InnerHead N) ∂normalizedBumpMeasure x ε = (∫ y : InnerHead N, (y i - x i) ∂normalizedBumpMeasure x ε) • (Pi.single i 1 : InnerHead N) := by
      intro i; rw [ integral_smul_const ] ;
    rw [ ← Finset.sum_congr rfl fun i _ => h_integral i, ← MeasureTheory.integral_finset_sum ];
    · congr! 2;
      ext i; simp +decide [ Pi.single_apply ] ;
    · intro i hi;
      refine' MeasureTheory.Integrable.smul_const _ _;
      refine' MeasureTheory.Integrable.mono' _ _ _;
      use fun y => ‖y - x‖;
      · exact h_integrable.norm;
      · exact Continuous.aestronglyMeasurable ( by continuity );
      · exact Filter.Eventually.of_forall fun y => norm_le_pi_norm ( y - x ) i;
  aesop

/-
A coordinate of the centered bump has second moment at most `ε²`.

This is the mathematically sound variance estimate underlying the intended
Phase-5 logarithmic bound; unlike the roadmap's displayed constant-integrand
inequality, it is valid for every positive `ε`.
-/
theorem Var_X_coordinate_bound {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)]
    (i : Fin N) :
    ∫ y : InnerHead N, (y i - x i) ^ 2 ∂normalizedBumpMeasure x ε ≤ ε ^ 2 := by
  refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
  refine' fun y => ε ^ 2;
  · exact Filter.Eventually.of_forall fun y => sq_nonneg _;
  · exact MeasureTheory.integrable_const _;
  · refine' MeasureTheory.measure_mono_null _ _;
    exact { y : InnerHead N | ∃ j : Fin N, y j ∉ Set.Icc ( x j - ε ) ( x j + ε ) };
    · intro y hy; contrapose! hy; simp_all +decide [ Set.subset_def ] ;
      nlinarith [ hy i ];
    · rw [ show { y : InnerHead N | ∃ j, y j ∉ Icc ( x j - ε ) ( x j + ε ) } = ( ⋃ j, { y : InnerHead N | y j ∉ Icc ( x j - ε ) ( x j + ε ) } ) by ext; aesop ];
      refine' MeasureTheory.measure_iUnion_null _;
      intro i; erw [ show { y : InnerHead N | y i ∉ Icc ( x i - ε ) ( x i + ε ) } = ( Set.pi Set.univ fun j => if j = i then Set.univ \ Icc ( x i - ε ) ( x i + ε ) else Set.univ ) from ?_ ] ; erw [ MeasureTheory.Measure.pi_pi ] ; simp +decide [ scalarBumpMeasure ] ;
      · rw [ Finset.prod_eq_zero ( Finset.mem_univ i ) ] ; simp +decide [ ProbabilityTheory.cond ];
      · ext; simp [Set.mem_pi];
  · simp +decide [ MeasureTheory.measureReal_def ]

/-
Expectation sends the zero observable on the full inner space to zero.
-/
theorem E_zero_space {N : ℕ} (headDist : Measure (InnerHead N))
    [IsProbabilityMeasure headDist] :
    ∫ _z : InnerSpace N, (0 : ℂ) ∂stateMeasure N headDist = 0 := by
  exact integral_zero (InnerSpace N) ℂ

/-
Additivity of expectation on the full inner space.
-/
theorem E_add_space {N : ℕ} (headDist : Measure (InnerHead N))
    [IsProbabilityMeasure headDist] (f g : InnerSpace N → ℂ) (hf : Integrable f (stateMeasure N headDist))
    (hg : Integrable g (stateMeasure N headDist)) :
    ∫ z, (f + g) z ∂stateMeasure N headDist =
      (∫ z, f z ∂stateMeasure N headDist) + ∫ z, g z ∂stateMeasure N headDist := by
  convert MeasureTheory.integral_add hf hg using 1

/-
Complex scalar multiplication commutes with expectation on the full inner space.
-/
theorem E_smul_space {N : ℕ} (headDist : Measure (InnerHead N))
    [IsProbabilityMeasure headDist] (c : ℂ) (f : InnerSpace N → ℂ) :
    ∫ z, c * f z ∂stateMeasure N headDist = c * ∫ z, f z ∂stateMeasure N headDist := by
  convert MeasureTheory.integral_const_mul c f using 1