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

instance scalarBumpMeasure_isProbability (a ε : ℝ) [Fact (0 < ε)] :
    IsProbabilityMeasure (scalarBumpMeasure a ε) := by
  constructor;
  unfold scalarBumpMeasure;
  rw [ ProbabilityTheory.cond_apply ];
  · rw [ Set.inter_univ, ENNReal.inv_mul_cancel ]
    <;> norm_num [Real.volume_Icc, Fact.out (p := 0 < ε)]
  · exact measurableSet_Icc

/-
Each coordinate of the product bump is centered at the corresponding coordinate of `x`.
-/
theorem X_coordinate_orthogonal {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)]
    (i : Fin N) :
    ∫ y : InnerHead N, (y i - x i) ∂normalizedBumpMeasure x ε = 0 := by
  have hε_pos : 0 < ε := Fact.out
  have h_smul_def : normalizedBumpMeasure x ε =
      (ENNReal.ofReal (1 / ((2 * ε) ^ N : ℝ))) • bumpMeasure x ε := rfl
  have h_inner : ∫ y : InnerHead N, (y i - x i) ∂(bumpMeasure x ε) = 0 := by
    dsimp [bumpMeasure]
    let f : Fin N → ℝ → ℝ := fun j t => if j = i then t - x i else 1
    have h_eq : (fun y : InnerHead N => y i - x i) =
        (fun y => ∏ j : Fin N, f j (y j)) := by
      ext y; simp [f]
    rw [h_eq]
    rw [integral_fintype_prod_eq_prod f]
    have h_i : ∫ y : ℝ, f i y ∂(volume.restrict (Set.Icc (x i - ε) (x i + ε))) = 0 := by
      simp [f, integral_sub_eq_zero_1d (x i) ε hε_pos]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa
  rw [h_smul_def, integral_smul_measure]
  rw [h_inner]
  simp

/-
A coordinate of the centered bump has second moment at most `ε²`.

This is the mathematically sound variance estimate underlying the intended
Phase-5 logarithmic bound; unlike the roadmap's displayed constant-integrand
inequality, it is valid for every positive `ε`.
-/
theorem Var_X_coordinate_bound {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)]
    (i : Fin N) :
    ∫ y : InnerHead N, (y i - x i) ^ 2 ∂normalizedBumpMeasure x ε ≤ ε ^ 2 := by
  have hε_pos : 0 < ε := Fact.out
  have h_nonneg : 0 ≤ᵐ[normalizedBumpMeasure x ε]
      (fun y : InnerHead N => (y i - x i) ^ 2) := by
    refine Filter.Eventually.of_forall (fun y => sq_nonneg _)
  have h_bound : (fun y : InnerHead N => (y i - x i) ^ 2) ≤ᵐ[normalizedBumpMeasure x ε]
      (fun _ : InnerHead N => ε ^ 2) := by
    have h_set : {y : InnerHead N | (y i - x i) ^ 2 > ε ^ 2} ⊆
        {y : InnerHead N | y i ∉ Set.Icc (x i - ε) (x i + ε)} := by
      intro y hy
      simp_rw [Set.mem_setOf_eq] at hy ⊢
      have hy' : (y i - x i) ^ 2 > ε ^ 2 := hy
      contrapose! hy'
      simp_rw [Set.mem_Icc] at hy'
      nlinarith
    have h_coord_zero : (normalizedBumpMeasure x ε)
        {y : InnerHead N | y i ∉ Set.Icc (x i - ε) (x i + ε)} = 0 := by
      rw [normalizedBumpMeasure, Measure.smul_apply, smul_eq_mul]
      have h_zero : (bumpMeasure x ε)
          {y : InnerHead N | y i ∉ Set.Icc (x i - ε) (x i + ε)} = 0 := by
        dsimp [bumpMeasure]
        have h_set_eq : {y : InnerHead N | y i ∉ Set.Icc (x i - ε) (x i + ε)} =
            Set.univ.pi (fun j : Fin N =>
              if j = i then (Set.Icc (x i - ε) (x i + ε))ᶜ
              else Set.univ) := by
          ext y; simp
        rw [h_set_eq]
        rw [MeasureTheory.Measure.pi_pi]
        have h_i_restrict : (volume.restrict (Set.Icc (x i - ε) (x i + ε)))
            ((Set.Icc (x i - ε) (x i + ε))ᶜ) = 0 := by
          rw [Measure.restrict_apply
            (s := Set.Icc (x i - ε) (x i + ε))
            (t := (Set.Icc (x i - ε) (x i + ε))ᶜ)
            (ht := (measurableSet_Icc (a := x i - ε)
              (b := x i + ε)).compl)]
          simp
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        simp [h_i_restrict]
      rw [h_zero, mul_zero]
    have h_measure_zero : (normalizedBumpMeasure x ε)
        {y : InnerHead N | (y i - x i) ^ 2 > ε ^ 2} = 0 :=
      MeasureTheory.measure_mono_null h_set h_coord_zero
    have h_ae : ∀ᵐ y ∂(normalizedBumpMeasure x ε),
        (y i - x i) ^ 2 ≤ ε ^ 2 := by
      rw [MeasureTheory.ae_iff]
      simpa using h_measure_zero
    simpa [Filter.EventuallyLE] using h_ae
  have h_int_bound : Integrable (fun _ : InnerHead N => ε ^ 2)
      (normalizedBumpMeasure x ε) :=
    integrable_const _
  refine le_trans
    (MeasureTheory.integral_mono_of_nonneg h_nonneg h_int_bound h_bound) ?_
  calc
    ∫ y : InnerHead N, ε ^ 2 ∂(normalizedBumpMeasure x ε) =
        (normalizedBumpMeasure x ε).real Set.univ • (ε ^ 2) := by
      rw [integral_const]
    _ = 1 • (ε ^ 2) := by
      have h_mass : (normalizedBumpMeasure x ε).real Set.univ = 1 := by
        rw [Measure.real_def, measure_univ, ENNReal.toReal_one]
      simp [h_mass]
    _ ≤ ε ^ 2 := by simp

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
    [IsProbabilityMeasure headDist]
    (f g : InnerSpace N → ℂ) (hf : Integrable f (stateMeasure N headDist))
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
