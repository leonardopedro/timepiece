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

/-! ## Phase 11 B2: Martingale Property + L² Distance Bound

We prove the random walk is a martingale w.r.t. the natural filtration and
establish the L² distance bound connecting the walk to the variance axioms.

### B2a — The random walk on `Fin N`

The centered-coordinate random walk maps `(y, x)` to `(y_i - x_i)_{i < N}`.
-/

/-- The centered-coordinate random walk padded to `Fin N → ℝ`.
    For `n ≤ N`, returns `(y_i - x_i)_{i < n}` padded with zeros for `i ≥ n`.
    The walk is frozen at `N` for `n > N`. -/
noncomputable def randomWalk {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)]
    (n : ℕ) (hn : n ≤ N) : InnerHead N → Fin N → ℝ :=
  fun y i =>
    if h : (i : ℕ) < n then
      y (Fin.cast hn ⟨(i : ℕ), h⟩) - x (Fin.cast hn ⟨(i : ℕ), h⟩)
    else
      0

/-- The increment `X(ε,k+1) - X(ε,k)` for `k < N`, padded to `Fin N → ℝ`.
    Only coordinate `k` is non-zero (value `y_k - x_k`); all other coordinates cancel. -/
noncomputable def randomWalkIncrement {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)]
    (k : ℕ) (hk : k < N) : InnerHead N → Fin N → ℝ :=
  fun y i =>
    if (i : ℕ) = k then
      y ⟨k, hk⟩ - x ⟨k, hk⟩
    else
      0

/-- The increment has zero mean (by symmetry of the bump measure on coordinate `k`). -/
lemma randomWalkIncrement_mean_zero {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)]
    (k : ℕ) (hk : k < N) :
    ∫ y : InnerHead N, randomWalkIncrement x ε k hk y ∂(normalizedBumpMeasure x ε) = 0 := by
  -- The increment is y_k - x_k at coordinate k and 0 elsewhere
  have h_increment_eq : (fun (y : InnerHead N) => randomWalkIncrement x ε k hk y) =
      (fun y i => if (i : ℕ) = k then y k - x k else (0 : ℝ)) := by
    ext y i; simp [randomWalkIncrement]
  rw [h_increment_eq]
  ext i
  by_cases hik : (i : ℕ) = k
  · subst hik; simp [X_coordinate_orthogonal x ε k]
  · simp [hik]

/-- The increment has second moment ≤ ε²/3 (per-coordinate variance bound). -/
lemma randomWalkIncrement_second_moment_bound {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)]
    (k : ℕ) (hk : k < N) :
    ∫ y : InnerHead N, (randomWalkIncrement x ε k hk y k)^2 ∂(normalizedBumpMeasure x ε) ≤
      ε^2 / 3 := by
  -- The increment at coordinate k equals y_k - x_k; Var(y_k - x_k) = ε²/3
  have hε_pos : 0 < ε := Fact.out
  have h_increment_eq : (fun (y : InnerHead N) => (randomWalkIncrement x ε k hk y k)^2) =
      (fun y => (y k - x k)^2) := by
    ext y; simp [randomWalkIncrement]
  rw [h_increment_eq]
  -- Use Var_X_coordinate_bound which gives ∫ (y_k - x_k)² ≤ ε²
  -- But we need the sharper bound ε²/3; we prove it directly via the 1D integral
  have h_smul_def : normalizedBumpMeasure x ε =
      (ENNReal.ofReal (1 / ((2 * ε) ^ N : ℝ))) • bumpMeasure x ε := rfl
  rw [h_smul_def, integral_smul_measure]
  · have h_moment : ∫ y : InnerHead N, (y k - x k)^2 ∂(bumpMeasure x ε) = (2 * ε^3) / 3 := by
      have h_map : (MeasureTheory.Measure.pi
          (fun (j : Fin N) => volume.restrict (Set.Icc (x j - ε) (x j + ε)))).map
          (fun (y : Fin N → ℝ) => y k) =
          (∏ j ∈ Finset.univ.erase k,
            (volume.restrict (Set.Icc (x j - ε) (x j + ε))) Set.univ) •
          (volume.restrict (Set.Icc (x k - ε) (x k + ε))) := by
        rw [MeasureTheory.Measure.pi_map_eval]
      have h_sub : (fun (y : Fin N → ℝ) => (y k - x k)^2) =
          (fun (t : ℝ) => (t - x k)^2) ∘ (fun (y : Fin N → ℝ) => y k) := rfl
      rw [h_sub, ← integral_map (hφ := (measurable_pi_apply k).aemeasurable)
        (hfm := ((continuous_id.sub continuous_const).pow 2).aestronglyMeasurable)]
      · rw [h_map, integral_smul_measure]
        · have h_one_d : ∫ t in Set.Icc (x k - ε) (x k + ε), (t - x k)^2 = (2 * ε^3) / 3 := by
            rw [← intervalIntegral.integral_of_le (by linarith : x k - ε ≤ x k + ε)]
            have h_deriv (t : ℝ) : HasDerivAt (fun t : ℝ => (t - x k)^3 / 3) ((t - x k)^2) t := by
              have h1 : HasDerivAt (fun t : ℝ => t - x k) (1 : ℝ) t := by
                simpa using hasDerivAt_id t |>.sub_const (x k)
              have h2 : HasDerivAt (fun u : ℝ => u^3 / 3) ((t - x k)^2) (t - x k) := by
                have h2_inner : HasDerivAt (fun u : ℝ => u^3) (3 * (t - x k)^2) (t - x k) := by
                  simpa using hasDerivAt_pow 3 (t - x k)
                simpa [div_eq_mul_inv] using h2_inner.mul_const (1/3)
              exact HasDerivAt.comp t h2 h1
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (h_deriv _)]
            ring
          rw [h_one_d]
          ring
        · refine ((continuous_id.sub continuous_const).pow 2).integrableOn_Icc
        · refine ENNReal.prod_ne_top (by intro j hj; simp [ENNReal.mul_ne_top])
      · refine ((continuous_id.sub continuous_const).pow 2).aestronglyMeasurable
    rw [h_moment]
    have hpos : (0 : ℝ) < (2 * ε) ^ N := by positivity
    have h_nonneg : 0 ≤ (1 : ℝ) / ((2 * ε) ^ N : ℝ) := by positivity
    have hcalc : (ENNReal.ofReal (1 / ((2 * ε) ^ N : ℝ))).toReal = (1 : ℝ) / ((2 * ε) ^ N) :=
      ENNReal.toReal_ofReal h_nonneg
    rw [hcalc]
    field_simp [hε_pos.ne']
    nlinarith
  · refine ((continuous_id.sub continuous_const).pow 2).integrable_pi_of_fintype ?_
    intro i
    refine ((continuous_id.sub continuous_const).pow 2).integrableOn_Icc.restrict
      (Set.Icc (x i - ε) (x i + ε))

/-! ### B2b — Natural filtration

The natural filtration `F_k` is generated by `{y 0, ..., y k}`, i.e. the
information available after observing the first `k` centered coordinates.
-/

/-- The natural filtration of the random walk: `F_k` is generated by
    the first `k` coordinates of the underlying sample `y`. -/
noncomputable def randomWalkFiltration {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)] :
    Filtration ℕ (InnerHead N) :=
  fun k => MeasurableSpace.comap (fun y : InnerHead N => fun i : Fin (min k N) => y i)
    inferInstance

/-- `F_k` is measurable w.r.t. the cylindrical sigma-algebra (B1). -/
lemma randomWalkFiltration_le_cylindrical {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)]
    (k : ℕ) :
    (randomWalkFiltration x ε k) ≤ cylindricalSigmaAlgebra N := by
  -- Both are comap sigma-algebras; the projection to Fin (min k N) factors
  -- through the projection to Fin N, so the comap is smaller
  refine le_trans ?_ (measurable_fst_cyl N).le
  -- Need: comap (proj to Fin (min k N)) ≤ comap (proj to Fin N)
  -- This follows from `MeasurableSpace.comap_mono` if the projection is measurable
  -- The projection `InnerHead N → Fin (min k N) → ℝ` is measurable because
  -- each coordinate function is a projection
  apply MeasurableSpace.comap_mono
  -- Show: the generating function of the first comap is measurable for the second
  -- i.e., `(fun y i => y i) : InnerHead N → Fin (min k N) → ℝ` is
  -- `MeasurableSpace (Fin N → ℝ)`-measurable
  -- This is true because each coordinate projection is measurable
  exact measurable_pi_lambda _ (fun i => measurable_pi_apply i)

/-- The random walk satisfies the martingale property:
    `E[X_{i+1} | ℱ_i] = X_i` for `i < N`.
    Proved using `condExp_indep_eq` and the independence of coordinate `i`
    from the first `i` coordinates under the product bump measure. -/
theorem randomWalk_martingale_condExp {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)]
    (i : ℕ) (hi : i < N) :
    (normalizedBumpMeasure x ε)[randomWalk x ε (i + 1) (Nat.le_succ_of_le (Nat.le_of_lt hi))
      | randomWalkFiltration x ε i]
    =ᵐ[normalizedBumpMeasure x ε] randomWalk x ε i (Nat.le_of_lt hi) := by
  -- Decompose: X_{i+1} = X_i + increment_i where increment_i = y_i - x_i at coordinate i
  have h_incr_eq : (fun y => randomWalk x ε (i + 1) (Nat.le_succ_of_le (Nat.le_of_lt hi)) y -
      randomWalk x ε i (Nat.le_of_lt hi) y) = randomWalkIncrement x ε i hi := by
    ext y j
    dsimp [randomWalk, randomWalkIncrement]
    by_cases hj_lt_i : (j : ℕ) < i
    · have hj_lt_succ : (j : ℕ) < i + 1 := by omega
      simp [hj_lt_i, hj_lt_succ]
    · by_cases hj_eq_i : (j : ℕ) = i
      · subst hj_eq_i; simp
      · have hj_lt_succ : (j : ℕ) < i + 1 := by omega
        simp [hj_lt_i, hj_eq_i, hj_lt_succ]
  have h_increment_zero_mean : ∫ y, randomWalkIncrement x ε i hi y ∂(normalizedBumpMeasure x ε) = 0 :=
    randomWalkIncrement_mean_zero x ε i hi
  -- The key: increment_i is independent of ℱ_i because it depends only on coordinate i
  -- and ℱ_i is generated by coordinates < i (which are independent of coordinate i)
  have h_ind_sigmaFinite : SigmaFinite ((normalizedBumpMeasure x ε).trim
      (MeasurableSpace.comap_le _ _ : randomWalkFiltration x ε i ≤ inferInstance)) := by
    infer_instance
  have h_condExp_increment : (normalizedBumpMeasure x ε)[randomWalkIncrement x ε i hi
      | randomWalkFiltration x ε i] =ᵐ[normalizedBumpMeasure x ε]
      fun _ => ∫ y, randomWalkIncrement x ε i hi y ∂(normalizedBumpMeasure x ε) := by
    -- Use condExp_indep_eq: increment is independent of ℱ_i
    -- Need to construct the sigma-algebra generated by coordinate i
    -- and show it's independent of ℱ_i
    -- The increment function depends only on the i-th coordinate
    -- So its sigma-algebra is contained in the comap of the i-th projection
    -- ℱ_i is generated by the first i coordinates
    -- These are independent by iIndepFun_pi
    have h_smul_def : normalizedBumpMeasure x ε =
        (ENNReal.ofReal (1 / ((2 * ε) ^ N : ℝ))) • bumpMeasure x ε := rfl
    -- Use the product structure: bumpMeasure = Measure.pi (fun j => scalarBumpMeasure (x j) ε)
    -- iIndepFun_pi gives independence of coordinate projections
    -- We need Indep of the sigma-algebra generated by coordinate i from ℱ_i
    -- ℱ_i is generated by coordinates 0,...,i-1 (the head)
    -- Coordinate i is in the tail (coordinates i,...,N-1)
    -- indep_iSup_of_disjoint gives independence of head from tail
    let coordFuns : Fin N → InnerHead N → ℝ := fun j y => y j
    have h_meas_coord : ∀ j, MeasurableSpace.comap (coordFuns j) inferInstance ≤ inferInstance := by
      intro j; exact MeasurableSpace.comap_le _ _
    have h_indep_coord : iIndepFun coordFuns (bumpMeasure x ε) := by
      -- iIndepFun_pi gives independence of coordinate projections on product spaces
      -- bumpMeasure = Measure.pi (fun j => scalarBumpMeasure (x j) ε)
      -- scalarBumpMeasure is a probability measure (since Fact (0 < ε))
      have h_prob : ∀ j, IsProbabilityMeasure (scalarBumpMeasure (x j) ε) := by
        intro j; infer_instance
      -- iIndepFun_pi is in the Prod namespace, works for any measures
      -- It requires [∀ i, IsProbabilityMeasure (μ i)]
      -- We have that from the instance above
      exact Prod.iIndepFun_pi (fun j => (measurable_pi_apply j).aemeasurable)
    -- Define the head sigma-algebra (coordinates < i) and tail sigma-algebra (coordinates ≥ i)
    let m_head : MeasurableSpace (InnerHead N) :=
      ⨆ j ∈ Finset.filter (fun j => (j : ℕ) < i) Finset.univ, MeasurableSpace.comap (coordFuns j) inferInstance
    let m_tail : MeasurableSpace (InnerHead N) :=
      ⨆ j ∈ Finset.filter (fun j => i ≤ (j : ℕ)) Finset.univ, MeasurableSpace.comap (coordFuns j) inferInstance
    have h_filtration_eq_m_head : randomWalkFiltration x ε i = m_head := by
      -- ℱ_i = comap (proj to Fin (min i N)) Borel = comap (proj to Fin i) Borel
      -- = ⨆ j < i, comap (coordFuns j) Borel
      ext s; simp [randomWalkFiltration, m_head, coordFuns, h_min_eq]
    -- The tail contains coordinate i
    have h_coord_i_le_tail : MeasurableSpace.comap (coordFuns i) inferInstance ≤ m_tail := by
      -- i is in the tail set (since i ≥ i)
      refine iSup₂_le (fun j hj => ?_)
      have hi_mem : i ∈ Finset.filter (fun j => i ≤ (j : ℕ)) Finset.univ := by
        simp [Finset.mem_filter, Finset.mem_univ]
      -- i is in the tail filter (since i ≥ i)
      have hi_mem_tail : i ∈ Finset.filter (fun j => i ≤ (j : ℕ)) Finset.univ := by
        simp [Finset.mem_filter]
      -- Use le_iSup₂: comap (coordFuns i) ≤ ⨆ j ∈ tailSet, comap (coordFuns j)
      refine le_iSup₂ (f := fun (j : Fin N) (_ : i ≤ (j : ℕ)) =>
        MeasurableSpace.comap (coordFuns j) inferInstance) i hi_mem_tail
    -- Indep of head from tail using indep_iSup_of_disjoint
    have h_indep_head_tail : Indep m_head m_tail (bumpMeasure x ε) := by
      -- indep_iSup_of_disjoint requires independent sigma-algebras and disjoint index sets
      -- We have iIndep from iIndepFun_pi on the product measure
      have h_indep_coord : iIndep (fun (j : Fin N) =>
        MeasurableSpace.comap (coordFuns j) inferInstance) (bumpMeasure x ε) := by
        -- iIndepFun_pi gives independence of the coordinate projections
        -- The coordinate functions are (measurable_pi_apply j).aemeasurable
        have h_meas : ∀ (j : Fin N), AEMeasurable (fun (y : InnerHead N) => y j)
          (scalarBumpMeasure (x j) ε) := by
          intro j; exact (measurable_pi_apply j).aemeasurable
        -- We need to adapt iIndepFun_pi to iIndep of MeasurableSpace.comap
        -- iIndepFun_pi gives iIndepFun of the projections; iIndep is the same as iIndepFun
        -- for the identity function on each coordinate
        have h_indep_fun : iIndepFun (fun (j : Fin N) (y : InnerHead N) => y j)
          (bumpMeasure x ε) :=
          Prod.iIndepFun_pi (fun j => (measurable_pi_apply j).aemeasurable)
        -- iIndepFun implies iIndep of the generated sigma-algebras
        -- Use iIndepFun.indepFun or convert to iIndep
        -- iIndepFun for projections is equivalent to iIndep of comap
        -- We can use `h_indep_fun.iIndep` to get iIndep of the MeasurableSpace.comap
        exact h_indep_fun
      -- Convert the Finset disjointness to Set disjointness
      have h_disjoint : Disjoint (Finset.filter (fun j => (j : ℕ) < i) Finset.univ : Set (Fin N))
          (Finset.filter (fun j => i ≤ (j : ℕ)) Finset.univ : Set (Fin N)) := by
        refine Set.disjoint_coe.mp ?_
        refine Finset.disjoint_filter_filter (fun j => ?_)
        intro hj1 hj2
        omega
      -- Now apply indep_iSup_of_disjoint
      -- The lemma: indep_iSup_of_disjoint (hle : ∀ i, m i ≤ mΩ) (hind : iIndep m μ)
      --   {S T : Set ι} (hdisj : Disjoint S T) : Indep (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) μ
      -- Here S = {j | j < i}, T = {j | j ≥ i}
      exact ProbabilityTheory.indep_iSup_of_disjoint
        (fun j => MeasurableSpace.comap_le _ _)
        h_indep_coord
        h_disjoint
    -- Now combine: coordinate i is in the tail, so its sigma-algebra is independent of m_head = ℱ_i
    have h_indep_coord_head : Indep (MeasurableSpace.comap (coordFuns i) inferInstance) m_head
        (bumpMeasure x ε) := by
      -- From h_indep_head_tail and h_coord_i_le_tail
      -- Use Indep.mono: if A ≤ B and Indep B C, then Indep A C
      -- And Indep.mono_right: if Indep A B and B ≤ C, then Indep A C
      -- Here: comap_i ≤ m_tail, so Indep comap_i m_head follows from Indep m_tail m_head
      -- which is h_indep_head_tail.symm
      have h_le : MeasurableSpace.comap (coordFuns i) inferInstance ≤ m_tail := h_coord_i_le_tail
      -- Indep is symmetric: Indep A B → Indep B A
      -- h_indep_head_tail : Indep m_head m_tail → Indep m_tail m_head
      -- Then Indep.mono_right: Indep m_tail m_head → (m_head ≤ m_tail) → Indep m_tail m_head
      -- Wait, we need Indep (comap i) m_head
      -- h_indep_head_tail : Indep m_head m_tail
      -- h_indep_head_tail.symm : Indep m_tail m_head
      -- h_le : comap i ≤ m_tail
      -- So Indep.mono h_indep_head_tail.symm h_le : Indep (comap i) m_head
      -- Actually Indep.mono says: if Indep A B and A' ≤ A and B' ≤ B, then Indep A' B'
      -- But we need: if Indep A B and A' ≤ A, then Indep A' B
      -- That's Indep.mono_left
      exact h_indep_head_tail.symm.mono_left h_le
    -- Scale to normalizedBumpMeasure: independence is preserved under scaling
    have h_indep_norm : Indep (MeasurableSpace.comap (coordFuns i) inferInstance)
        (randomWalkFiltration x ε i) (normalizedBumpMeasure x ε) := by
      rw [h_filtration_eq_m_head]
      -- normalizedBumpMeasure = c • bumpMeasure, independence scales with the measure
      -- Use Indep.smul_measure or Indep.comp
      -- Since normalizedBumpMeasure = (ENNReal.ofReal (1 / ((2*ε)^N))) • bumpMeasure
      -- and this scalar is nonzero, independence is preserved
      have h_smul_def : normalizedBumpMeasure x ε =
          (ENNReal.ofReal (1 / ((2 * ε) ^ N : ℝ))) • bumpMeasure x ε := rfl
      rw [h_smul_def]
      -- Indep.smul_measure: Indep A B μ → Indep A B (c • μ) for c ≠ 0, ∞
      -- ENNReal.ofReal (...) is nonzero and finite
      have hc_ne_zero : ENNReal.ofReal (1 / ((2 * ε) ^ N : ℝ)) ≠ 0 := by
        refine ENNReal.ofReal_ne_zero.mpr ?_
        have hpos : 0 < (2 * ε) ^ N := by positivity
        have hpos_div : 0 < 1 / ((2 * ε) ^ N : ℝ) := div_pos (by norm_num) hpos
        linarith
      have hc_ne_top : ENNReal.ofReal (1 / ((2 * ε) ^ N : ℝ)) ≠ ∞ := ENNReal.ofReal_ne_top
      -- Indep.smul_measure hc_ne_zero hc_ne_top h_indep_coord_head
      -- Actually, the lemma is Indep.smul_measure
      -- Let me check: Indep.smul_measure (h : c ≠ 0) (h' : c ≠ ∞) (h_indep : Indep A B μ) : Indep A B (c • μ)
      -- But Indep.smul_measure might have different arguments
      -- Let me use Indep.comp with the scaling map instead
      -- Simpler: Indep.smul_measure is in Mathlib.Probability.Independence.Basic
      -- It takes (h_indep : Indep m₁ m₂ μ) and returns Indep m₁ m₂ (c • μ)
      -- provided c ≠ 0 and c ≠ ∞
      have hc_pos : ENNReal.ofReal (1 / ((2 * ε) ^ N : ℝ)) > 0 := by
        refine ENNReal.ofReal_pos.mpr ?_
        have hpos : 0 < (2 * ε) ^ N := by positivity
        exact div_pos (by norm_num) hpos
      have hc_ne_zero' : ENNReal.ofReal (1 / ((2 * ε) ^ N : ℝ)) ≠ 0 := by linarith
      exact h_indep_coord_head.smul_measure hc_ne_zero' hc_ne_top
    -- Now apply condExp_indep_eq
    have h_meas : StronglyMeasurable[MeasurableSpace.comap (coordFuns i) inferInstance]
        (randomWalkIncrement x ε i hi) := by
      dsimp [randomWalkIncrement, coordFuns]
      refine stronglyMeasurable_pi_lambda _ (fun j => ?_)
      by_cases hj_eq_i : (j : ℕ) = i
      · subst hj_eq_i; exact ((measurable_pi_apply i).sub measurable_const).stronglyMeasurable
      · exact stronglyMeasurable_const
    have h_le : randomWalkFiltration x ε i ≤ inferInstance := by
      dsimp [randomWalkFiltration]; exact MeasurableSpace.comap_le _ _
    have h_sigmaFinite : SigmaFinite ((normalizedBumpMeasure x ε).trim h_le) := by
      infer_instance
    -- condExp_indep_eq requires m₁ ≤ m, m₂ ≤ m, SigmaFinite (μ.trim m₂), f strongly m₁-measurable
    -- and Indep m₁ m₂ μ
    -- Here m₁ = MeasurableSpace.comap (coordFuns i) inferInstance, m₂ = ℱ_i
    -- We have h_indep_norm : Indep m₁ m₂ normalizedBumpMeasure
    -- So we can apply condExp_indep_eq directly
    -- But wait, condExp_indep_eq uses the independence condition differently
    -- Let me check the exact statement
    -- condExp_indep_eq hle₁ hle₂ h_sigmaFinite hf hindp : μ[f | m₂] =ᵐ[μ] fun _ => μ[f]
    -- where hle₁ : m₁ ≤ m, hle₂ : m₂ ≤ m, hf : StronglyMeasurable[m₁] f, hindp : Indep m₁ m₂ μ
    -- We have all of these!
    -- So:
    have h_le₁ : MeasurableSpace.comap (coordFuns i) inferInstance ≤ inferInstance :=
      MeasurableSpace.comap_le _ _
    refine condExp_indep_eq h_le₁ h_le h_sigmaFinite h_meas h_indep_norm
  rw [h_condExp_increment, h_increment_zero_mean, condExp_const (randomWalkFiltration x ε).le i,
    h_incr_eq] at h_condExp_increment
  -- Now we have: E[increment | ℱ_i] = E[increment] = 0
  -- So E[X_{i+1} | ℱ_i] = E[X_i + increment | ℱ_i] = X_i + E[increment | ℱ_i] = X_i + 0 = X_i
  -- But we need to express this as an ae equality, not a rewrite
  -- Let's use the linearity of condExp
  calc
    (normalizedBumpMeasure x ε)[randomWalk x ε (i + 1) (Nat.le_succ_of_le (Nat.le_of_lt hi))
      | randomWalkFiltration x ε i]
        = (normalizedBumpMeasure x ε)[(fun y => randomWalk x ε i (Nat.le_of_lt hi) y +
            randomWalkIncrement x ε i hi y) | randomWalkFiltration x ε i] := by
      congr 1
      ext y
      have h_incr_eq' := h_incr_eq
      -- X_{i+1} = X_i + increment
      dsimp [randomWalk, randomWalkIncrement]
      ext j
      by_cases hj_lt_i : (j : ℕ) < i
      · have hj_lt_succ : (j : ℕ) < i + 1 := by omega
        simp [hj_lt_i, hj_lt_succ]
      · by_cases hj_eq_i : (j : ℕ) = i
        · subst hj_eq_i; simp
        · have hj_lt_succ : (j : ℕ) < i + 1 := by omega
          simp [hj_lt_i, hj_eq_i, hj_lt_succ]
    _ = (normalizedBumpMeasure x ε)[randomWalk x ε i (Nat.le_of_lt hi) | randomWalkFiltration x ε i] +
        (normalizedBumpMeasure x ε)[randomWalkIncrement x ε i hi | randomWalkFiltration x ε i] := by
      rw [condExp_add (Filtration.le _) ?_ ?_]
      · rfl
      · -- X_i is ℱ_i-measurable
        refine stronglyMeasurable_condExp
      · -- increment is integrable
        -- Already proved in randomWalkIncrement_mean_zero
        have h_int : Integrable (randomWalkIncrement x ε i hi) (normalizedBumpMeasure x ε) := by
          -- randomWalkIncrement is y_i - x_i at coordinate i and 0 elsewhere
          -- First prove integrability against bumpMeasure, then scale to normalizedBumpMeasure
          have h_smul_def : normalizedBumpMeasure x ε =
              (ENNReal.ofReal (1 / ((2 * ε) ^ N : ℝ))) • bumpMeasure x ε := rfl
          have h_int_bump : Integrable (randomWalkIncrement x ε i hi) (bumpMeasure x ε) := by
            dsimp [randomWalkIncrement, bumpMeasure]
            refine integrable_pi_of_fintype (fun j => ?_)
            by_cases hj_eq_i : (j : ℕ) = i
            · subst hj_eq_i
              refine ((continuous_id.sub continuous_const).integrableOn_Icc.restrict
                (Set.Icc (x i - ε) (x i + ε))).integrable.comp_measurable
                (measurable_pi_apply i).aemeasurable
            · exact integrable_const _
          rw [h_smul_def]
          exact h_int_bump.smul_measure ENNReal.ofReal_ne_top
        exact h_int.aestronglyMeasurable
    _ = randomWalk x ε i (Nat.le_of_lt hi) + 0 := by
      rw [h_condExp_increment, condExp_of_stronglyMeasurable
        (Filtration.le _) (by
          -- X_i is ℱ_i-measurable
          refine stronglyMeasurable_pi_lambda _ (fun j => ?_)
          exact ((measurable_pi_apply j).sub measurable_const).stronglyMeasurable.mono
            (randomWalkFiltration x ε).le i
        ) ?_]
      · rfl
      · -- X_i is integrable: each coordinate is bounded by ε, measure is finite
        dsimp [randomWalk]
        have h_smul_def : normalizedBumpMeasure x ε =
            (ENNReal.ofReal (1 / ((2 * ε) ^ N : ℝ))) • bumpMeasure x ε := rfl
        rw [h_smul_def]
        have h_int_bump : Integrable (randomWalk x ε i (Nat.le_of_lt hi)) (bumpMeasure x ε) := by
          dsimp [bumpMeasure]
          refine integrable_pi_of_fintype (fun j => ?_)
          by_cases hj_lt_i : (j : ℕ) < i
          · refine ((continuous_id.sub continuous_const).integrableOn_Icc.restrict
              (Set.Icc (x j - ε) (x j + ε))).integrable.comp_measurable
              (measurable_pi_apply j).aemeasurable
          · exact integrable_const _
        exact h_int_bump.smul_measure ENNReal.ofReal_ne_top
    _ = randomWalk x ε i (Nat.le_of_lt hi) := by simp

/-- The L² distance between `X(ε,n)` and `X(ε,m)` for `n ≤ m ≤ N` is bounded by
    `√(m-n) · ε`. Proved by expanding `‖X_m - X_n‖²` as a sum of squared
    increments and using `Var_X_coordinate_bound`. -/
theorem randomWalk_l2_distance_bound {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)]
    (n m : ℕ) (hn : n ≤ N) (hm : m ≤ N) (hnm : n ≤ m) :
    ∫ y : InnerHead N,
      ‖randomWalk x ε n hn y - randomWalk x ε m hm y‖^2 ∂(normalizedBumpMeasure x ε) ≤
      ((m - n : ℕ) : ℝ) * ε ^ 2 := by
  -- ‖X_m - X_n‖² = Σ_{i=n}^{m-1} (y_i - x_i)²
  -- because X_m and X_n agree on coordinates < n, and differ by y_i - x_i on coordinates n..m-1
  have h_diff_sq (y : InnerHead N) : ‖randomWalk x ε n hn y - randomWalk x ε m hm y‖^2 =
      ∑ i ∈ Finset.Ico n m, (y i - x i)^2 := by
    -- For i < n: both walks have y_i - x_i, so difference is 0
    -- For n ≤ i < m: X_n has 0, X_m has y_i - x_i
    -- For i ≥ m: X_n has 0, X_m has 0
    -- So ‖X_m - X_n‖² = Σ_{i=n}^{m-1} (y_i - x_i)²
    calc
      ‖randomWalk x ε n hn y - randomWalk x ε m hm y‖^2 =
          (∑ i : Fin N, ((randomWalk x ε n hn y - randomWalk x ε m hm y) i)^2) := by
        simp [PiLp.norm_sq_eq_sum]
      _ = ∑ i : Fin N, ((randomWalk x ε n hn y) i - (randomWalk x ε m hm y) i)^2 := by
        simp [Pi.sub_apply]
      _ = ∑ i ∈ Finset.Ico n m, (y i - x i)^2 := by
        -- The terms cancel outside Ico n m:
        -- For i < n: both walks give y_i - x_i, so difference is 0
        -- For n ≤ i < m: X_n gives 0, X_m gives y_i - x_i
        -- For i ≥ m: both walks give 0
        -- So only coordinates i where n ≤ i < m contribute
        have h_eq (i : Fin N) : ((randomWalk x ε n hn y) i - (randomWalk x ε m hm y) i)^2 =
          if (i : ℕ) ∈ Finset.Ico n m then (y i - x i)^2 else 0 := by
          dsimp [randomWalk]
          have hcast_n : ∀ (j : Fin n), ((Fin.cast hn j : Fin N) : ℕ) = (j : ℕ) := by
            intro j; simp
          by_cases hi_lt_n : (i : ℕ) < n
          · have hi_lt_m : (i : ℕ) < m := by omega
            have hmem : (i : ℕ) ∉ Finset.Ico n m := by
              simp [Finset.mem_Ico, hi_lt_n]
            simp [hi_lt_n, hi_lt_m, hcast_n, hmem]
          · by_cases hi_lt_m : (i : ℕ) < m
            · have hmem : (i : ℕ) ∈ Finset.Ico n m := by
                simp [Finset.mem_Ico, hi_lt_n, hi_lt_m]
              simp [hi_lt_n, hi_lt_m, hcast_n, hmem]
            · have hm_le_i : m ≤ (i : ℕ) := by omega
              have hmem : (i : ℕ) ∉ Finset.Ico n m := by
                simp [Finset.mem_Ico, hm_le_i]
              simp [hi_lt_n, hi_lt_m, hm_le_i, hcast_n, hmem]
        rw [Finset.sum_congr rfl (fun i _ => h_eq i)]
        simp [Finset.sum_filter]
  rw [integral_congr_ae (ae_of_all _ h_diff_sq)]
  rw [integral_finset_sum]
  -- Now: Σ_i ∫ (y_i - x_i)² ≤ (m-n)·ε²
  refine Finset.sum_le_sum (fun i hi => ?_)
  -- Var_X_coordinate_bound gives ∫ (y_i - x_i)² ≤ ε²
  exact Var_X_coordinate_bound x ε i