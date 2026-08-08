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
  rw [activeCoordinates, ← Finset.card_image_of_injective _ Fin.val_injective]
  have himg : (Finset.univ.filter (fun i : Fin N => i.1 < n)).image Fin.val
      = Finset.range (min n N) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range, Nat.lt_min]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨ha, a.2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨k, h2⟩, h1, rfl⟩
  rw [himg, Finset.card_range]

/-
Almost surely under the bump law, every coordinate stays inside its interval.
-/
theorem ae_abs_coord_le {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)] (i : Fin N) :
    ∀ᵐ y ∂(normalizedBumpMeasure x ε), |y i - x i| ≤ ε := by
  have h_zero : (normalizedBumpMeasure x ε)
      {y : InnerHead N | y i ∉ Set.Icc (x i - ε) (x i + ε)} = 0 := by
    rw [normalizedBumpMeasure, Measure.smul_apply, smul_eq_mul]
    have h_bump : (bumpMeasure x ε)
        {y : InnerHead N | y i ∉ Set.Icc (x i - ε) (x i + ε)} = 0 := by
      dsimp [bumpMeasure]
      have h_set_eq : {y : InnerHead N | y i ∉ Set.Icc (x i - ε) (x i + ε)} =
          Set.univ.pi (fun j : Fin N =>
            if j = i then (Set.Icc (x i - ε) (x i + ε))ᶜ else Set.univ) := by
        ext y; simp
      rw [h_set_eq, MeasureTheory.Measure.pi_pi]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      have h_i_restrict : (volume.restrict (Set.Icc (x i - ε) (x i + ε)))
          ((Set.Icc (x i - ε) (x i + ε))ᶜ) = 0 := by
        rw [Measure.restrict_apply (ht := (measurableSet_Icc
          (a := x i - ε) (b := x i + ε)).compl)]
        simp
      simp [h_i_restrict]
    rw [h_bump, mul_zero]
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ h_zero
  intro y hy
  simp only [Set.mem_setOf_eq, not_le] at hy ⊢
  intro hmem
  rw [Set.mem_Icc] at hmem
  cases abs_cases (y i - x i) with
  | inl h => linarith [h.1, hmem.2]
  | inr h => linarith [h.1, hmem.1]

/-
Each centered coordinate has an integrable square under the bump law.
-/
theorem integrable_coord_sq {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)] (i : Fin N) :
    Integrable (fun y : InnerHead N => (y i - x i) ^ 2) (normalizedBumpMeasure x ε) := by
  refine MeasureTheory.Integrable.mono' (g := fun _ : InnerHead N => ε ^ 2)
    (MeasureTheory.integrable_const _)
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_abs_coord_le x ε i] with y hy
  have hsq : (y i - x i) ^ 2 ≤ ε ^ 2 := by
    have h0 : (0:ℝ) ≤ |y i - x i| := abs_nonneg _
    nlinarith [sq_abs (y i - x i)]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hsq

/-
Each finite partial energy is integrable under the concrete product-bump law.
-/
theorem integrable_partialEnergy {N : ℕ} (n : ℕ) (x : InnerHead N) (ε : ℝ)
    [Fact (0 < ε)] :
    Integrable (partialEnergy n x) (normalizedBumpMeasure x ε) := by
  refine MeasureTheory.integrable_finset_sum _ fun i _ => integrable_coord_sq x ε i

/-
**Corrected Phase-6 bound.** Under the concrete product-bump law, the
expected squared energy of the first `n` increments is at most
`min n N * ε²`.
-/
theorem partialEnergy_expectation_bound {N : ℕ} (n : ℕ) (x : InnerHead N)
    (ε : ℝ) [Fact (0 < ε)] :
    ∫ y, partialEnergy n x y ∂normalizedBumpMeasure x ε ≤
      (min n N : ℝ) * ε ^ 2 := by
  have hsum : ∫ y, partialEnergy n x y ∂normalizedBumpMeasure x ε
      = ∑ i ∈ activeCoordinates N n,
          ∫ y : InnerHead N, (y i - x i) ^ 2 ∂normalizedBumpMeasure x ε :=
    MeasureTheory.integral_finset_sum _ fun i _ => integrable_coord_sq x ε i
  rw [hsum]
  calc ∑ i ∈ activeCoordinates N n,
        ∫ y : InnerHead N, (y i - x i) ^ 2 ∂normalizedBumpMeasure x ε
      ≤ ∑ _i ∈ activeCoordinates N n, ε ^ 2 :=
        Finset.sum_le_sum fun i _ => Var_X_coordinate_bound x ε i
    _ = (min n N : ℝ) * ε ^ 2 := by
        rw [Finset.sum_const, card_activeCoordinates, nsmul_eq_mul, Nat.cast_min]

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
  convert div_le_div_of_nonneg_right (fullEnergy_expectation_bound x ε)
      (Nat.cast_nonneg N) using 1;
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
    (n : ℕ) (_hn : n ≤ N) : InnerHead N → Fin N → ℝ :=
  fun y i =>
    if (i : ℕ) < n then
      y i - x i
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

/-- The one-dimensional second moment: `\int_{a-\epsilon}^{a+\epsilon} (y-a)^2 = 2\epsilon^3/3`. -/
lemma integral_sub_sq_1d (a : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ y in Set.Icc (a - ε) (a + ε), (y - a) ^ 2 = 2 * ε ^ 3 / 3 := by
  have h_le : a - ε ≤ a + ε := by linarith
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h_le]
  have h_deriv : ∀ t : ℝ, HasDerivAt (fun u : ℝ => (u - a) ^ 3 / 3) ((t - a) ^ 2) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => u - a) (1 : ℝ) t := (hasDerivAt_id t).sub_const a
    have h3 : HasDerivAt (fun u : ℝ => u ^ 3) (3 * (t - a) ^ 2) (t - a) := by
      simpa using hasDerivAt_pow 3 (t - a)
    have h2 : HasDerivAt (fun u : ℝ => u ^ 3 / 3) ((t - a) ^ 2) (t - a) := by
      simpa using (h3.div_const 3).congr_deriv (by ring)
    simpa using h2.comp t h1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => h_deriv t)]
  · ring
  · exact ((continuous_id.sub continuous_const).pow 2).intervalIntegrable _ _

/-- The exact per-coordinate second moment of the centered bump law: `ε²/3`. -/
theorem coord_sq_expectation {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)] (i : Fin N) :
    ∫ y : InnerHead N, (y i - x i) ^ 2 ∂normalizedBumpMeasure x ε = ε ^ 2 / 3 := by
  have hε : 0 < ε := Fact.out
  have h_inner : ∫ y : InnerHead N, (y i - x i) ^ 2 ∂(bumpMeasure x ε)
      = (2 * ε ^ 3 / 3) * (2 * ε) ^ (N - 1) := by
    dsimp [bumpMeasure]
    let f : Fin N → ℝ → ℝ := fun j t => if j = i then (t - x i) ^ 2 else 1
    have h_eq : (fun y : InnerHead N => (y i - x i) ^ 2) = (fun y => ∏ j : Fin N, f j (y j)) := by
      ext y; simp [f]
    rw [h_eq, integral_fintype_prod_eq_prod f,
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    have hi : ∫ t : ℝ, f i t ∂(volume.restrict (Set.Icc (x i - ε) (x i + ε)))
        = 2 * ε ^ 3 / 3 := by
      simp only [f, if_pos rfl]
      exact integral_sub_sq_1d (x i) hε
    have hj : ∀ j ∈ Finset.univ.erase i,
        ∫ t : ℝ, f j t ∂(volume.restrict (Set.Icc (x j - ε) (x j + ε))) = 2 * ε := by
      intro j hj
      have hne : j ≠ i := Finset.ne_of_mem_erase hj
      simp only [f, if_neg hne, integral_const, smul_eq_mul, mul_one]
      rw [MeasureTheory.measureReal_def]
      simp only [Measure.restrict_apply_univ, Real.volume_Icc]
      rw [ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [Finset.prod_congr rfl hj, hi, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    ring
  rw [normalizedBumpMeasure, integral_smul_measure, h_inner,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact absurd i.2 (by simp))
  have hpow : ((2 : ℝ) * ε) ^ N = (2 * ε) * (2 * ε) ^ (N - 1) := by
    conv_lhs => rw [show N = 1 + (N - 1) by omega]
    rw [pow_add, pow_one]
  have ht : ((2 : ℝ) * ε) ^ (N - 1) ≠ 0 := by positivity
  rw [hpow]
  field_simp

/-- Each centered coordinate is integrable under the bump law. -/
theorem integrable_coord_sub {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)] (i : Fin N) :
    Integrable (fun y : InnerHead N => y i - x i) (normalizedBumpMeasure x ε) := by
  refine MeasureTheory.Integrable.mono' (g := fun _ : InnerHead N => ε)
    (MeasureTheory.integrable_const _)
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [RandomMap2Walk.ae_abs_coord_le x ε i] with y hy
  simpa [Real.norm_eq_abs] using hy

/-- The increment has zero mean (by symmetry of the bump measure on coordinate `k`). -/
lemma randomWalkIncrement_mean_zero {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)]
    (k : ℕ) (hk : k < N) :
    ∫ y : InnerHead N, randomWalkIncrement x ε k hk y ∂(normalizedBumpMeasure x ε) = 0 := by
  have hint : ∀ i : Fin N,
      Integrable (fun y : InnerHead N => randomWalkIncrement x ε k hk y i)
        (normalizedBumpMeasure x ε) := by
    intro i
    by_cases hik : (i : ℕ) = k
    · simpa [randomWalkIncrement, hik] using integrable_coord_sub x ε (⟨k, hk⟩ : Fin N)
    · simp only [randomWalkIncrement, if_neg hik]
      exact MeasureTheory.integrable_const (0 : ℝ)
  funext i
  rw [MeasureTheory.eval_integral hint i]
  by_cases hik : (i : ℕ) = k
  · simp only [randomWalkIncrement, hik, if_pos, Pi.zero_apply]
    exact X_coordinate_orthogonal x ε (⟨k, hk⟩ : Fin N)
  · simp [randomWalkIncrement, hik]

/-- The increment has second moment exactly `ε²/3` (per-coordinate variance). -/
lemma randomWalkIncrement_second_moment_bound {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)]
    (k : ℕ) (hk : k < N) :
    ∫ y : InnerHead N, (randomWalkIncrement x ε k hk y ⟨k, hk⟩) ^ 2
        ∂(normalizedBumpMeasure x ε) ≤ ε ^ 2 / 3 := by
  have h_increment_eq :
      (fun y : InnerHead N => (randomWalkIncrement x ε k hk y ⟨k, hk⟩) ^ 2)
        = fun y : InnerHead N => (y (⟨k, hk⟩ : Fin N) - x ⟨k, hk⟩) ^ 2 := by
    funext y
    simp [randomWalkIncrement]
  rw [h_increment_eq, coord_sq_expectation x ε (⟨k, hk⟩ : Fin N)]

/-! ### B2b — Natural filtration and the martingale property (documented gap)

The development below builds the natural filtration of the walk and proves the
martingale property `E[X_{k+1} | ℱ_k] = X_k` from the independence of the
coordinates of the product bump law.  It is retained here verbatim, but
**commented out**: it does not elaborate against Mathlib v4.28.0 — it refers to
identifiers this repository does not define (`cylindricalSigmaAlgebra`,
`measurable_fst_cyl`), uses `Filtration` with the wrong argument order, and calls
`MeasureTheory.condExp_indep_eq` through an API that has since changed.
Repairing it needs a genuine re-derivation of the conditional-expectation step
(Mathlib's `condExp_indep_eq` plus `iIndepFun` for `Measure.pi`), which is a
documented gap rather than a `sorry`: nothing below is *assumed* anywhere else in
the library, and the two quantitative facts the walk is used for — the
per-coordinate second moment `coord_sq_expectation` and the L² distance bound
`randomWalk_l2_distance_bound` — are proved outright above and below.
-/

/-
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
  have h_increment_zero_mean :
      ∫ y, randomWalkIncrement x ε i hi y ∂(normalizedBumpMeasure x ε) = 0 :=
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
      ⨆ j ∈ Finset.filter (fun j => (j : ℕ) < i) Finset.univ,
        MeasurableSpace.comap (coordFuns j) inferInstance
    let m_tail : MeasurableSpace (InnerHead N) :=
      ⨆ j ∈ Finset.filter (fun j => i ≤ (j : ℕ)) Finset.univ,
        MeasurableSpace.comap (coordFuns j) inferInstance
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
      -- Indep.smul_measure (h : c ≠ 0) (h' : c ≠ ∞) (h_indep : Indep A B μ) :
      --   Indep A B (c • μ)
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
    _ = (normalizedBumpMeasure x ε)[randomWalk x ε i (Nat.le_of_lt hi) |
          randomWalkFiltration x ε i] +
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

-/

/-- **L² distance bound for the centered-coordinate walk.**
`InnerHead N = Fin N → ℝ` carries the supremum norm, so the difference of the two
walk positions has norm at most `ε` almost surely; integrating against the
probability law `normalizedBumpMeasure` gives the stated bound for `n ≤ m ≤ N`. -/
theorem randomWalk_l2_distance_bound {N : ℕ} (x : InnerHead N) (ε : ℝ) [Fact (0 < ε)]
    (n m : ℕ) (hn : n ≤ N) (hm : m ≤ N) (hnm : n ≤ m) :
    ∫ y : InnerHead N,
      ‖randomWalk x ε n hn y - randomWalk x ε m hm y‖^2 ∂(normalizedBumpMeasure x ε) ≤
      ((m - n : ℕ) : ℝ) * ε ^ 2 := by
  have hε : (0:ℝ) < ε := Fact.out
  rcases eq_or_lt_of_le hnm with rfl | hlt
  · -- `n = m`: the two walk positions coincide, so the integrand vanishes.
    simp
  · -- `n < m`: bound the integrand by `ε²` almost surely.
    have hae : ∀ᵐ y ∂(normalizedBumpMeasure x ε), ∀ i : Fin N, |y i - x i| ≤ ε :=
      (MeasureTheory.ae_all_iff).2 (fun i => RandomMap2Walk.ae_abs_coord_le x ε i)
    have hbound : ∀ᵐ y ∂(normalizedBumpMeasure x ε),
        ‖randomWalk x ε n hn y - randomWalk x ε m hm y‖^2 ≤ ε ^ 2 := by
      filter_upwards [hae] with y hy
      have hnorm : ‖randomWalk x ε n hn y - randomWalk x ε m hm y‖ ≤ ε := by
        refine (pi_norm_le_iff_of_nonneg hε.le).2 (fun i => ?_)
        rcases lt_or_ge (i : ℕ) n with h1 | h1
        · have h2 : (i : ℕ) < m := lt_of_lt_of_le h1 hnm
          simp [randomWalk, h1, h2, hε.le]
        · rcases lt_or_ge (i : ℕ) m with h2 | h2
          · have h1' : ¬ ((i : ℕ) < n) := not_lt.2 h1
            simpa [randomWalk, h1', h2, Real.norm_eq_abs, abs_sub_comm] using hy i
          · have h1' : ¬ ((i : ℕ) < n) := not_lt.2 h1
            have h2' : ¬ ((i : ℕ) < m) := not_lt.2 h2
            simp [randomWalk, h1', h2', hε.le]
      have h0 : (0:ℝ) ≤ ‖randomWalk x ε n hn y - randomWalk x ε m hm y‖ := norm_nonneg _
      nlinarith
    have hint : Integrable
        (fun y : InnerHead N => ‖randomWalk x ε n hn y - randomWalk x ε m hm y‖^2)
        (normalizedBumpMeasure x ε) := by
      refine MeasureTheory.Integrable.mono' (g := fun _ : InnerHead N => ε ^ 2)
        (MeasureTheory.integrable_const _) ?_ ?_
      · refine (Measurable.aestronglyMeasurable ?_)
        refine ((measurable_pi_lambda _ (fun i => ?_)).sub
          (measurable_pi_lambda _ (fun i => ?_))).norm.pow_const 2
        · by_cases h : (i : ℕ) < n <;> simp only [randomWalk, h, if_true, if_false] <;> fun_prop
        · by_cases h : (i : ℕ) < m <;> simp only [randomWalk, h, if_true, if_false] <;> fun_prop
      · filter_upwards [hbound] with y hy
        rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hone : (1:ℝ) ≤ ((m - n : ℕ) : ℝ) := by
      have h : 1 ≤ m - n := by omega
      exact_mod_cast h
    calc ∫ y : InnerHead N,
            ‖randomWalk x ε n hn y - randomWalk x ε m hm y‖^2 ∂(normalizedBumpMeasure x ε)
        ≤ ∫ _y : InnerHead N, ε ^ 2 ∂(normalizedBumpMeasure x ε) :=
          MeasureTheory.integral_mono_ae hint (MeasureTheory.integrable_const _) hbound
      _ = ε ^ 2 := by simp
      _ ≤ ((m - n : ℕ) : ℝ) * ε ^ 2 := by nlinarith [sq_nonneg ε]
