import Mathlib
import BookProof.OSReconstruction.PriorRefinement

/-!
# B0 on a continuum information space: the measure-theoretic prior and its consistency

Plan: `cftproof.md`, the clause *"Keep the continuous/infinite-information representation and its
consistency estimates as explicit further deliverables."*  `OSReconstruction.PriorRefinement`
delivered the discrete half (an arbitrary information type with a finitely supported mass
function); this module delivers the continuum half: the information space carries a genuine
probability **measure**, and the dictionary is stated with integrals, not sums.

## 1. The continuum prior and its dictionary

`ContPrior n Ω` is a probability measure `μ` on a measurable information space together with `n`
measurable resolved supports `inf : Fin n → Set Ω`.  States are points of `Ω`, so nothing is a
point-evaluation vector of `L²` and no field is evaluated at a spatial vector.

* `ContPrior.mass`, `ContPrior.joint` — the measures of the informing event and of the conjunction,
  in `ℝ` (`Measure.real` of the measurable sets).
* `ContPrior.prop` — the number-density proposition at a point, `1 / mass i` on the informing event
  and `0` off it.
* `ContPrior.expect` — expectation as the integral against `μ`; `ContPrior.corr` — the two-point
  function of the propositions.
* **`ContPrior.expect_prop`** — the proposition is normalized, `∫ prop i ∂μ = 1`, for every prior of
  positive mass at the point.  The normalization of the manuscript is therefore a theorem here,
  not a convention.
* **`ContPrior.corr_eq`** — `corr i j = joint i j / (mass i * mass j)`, and
  **`ContPrior.corr_eq_one_iff`** — correlation `1` exactly when the joint measure factorizes.
  This is the B0 dictionary on a continuum information space.

## 2. Consistency estimates

Two independent consistency statements, both of which the discrete packet had in sum form.

*Refinement invariance* (`ContRefinement`).  Refine `Ω` to `Ω × Γ` with an arbitrary probability
measure on the product (so the auxiliary tag may be correlated with the coarse information) and
pull the supports back along `Prod.fst`; `ContRefinement.coarse` is the pushforward.  Then
`mass_refined_eq_coarse`, `joint_refined_eq_coarse`, `corr_refined_eq_coarse` and
`expect_refined_eq_coarse` say that marginalization changes no B0 number.  The proofs are the
measure-theoretic `Measure.map_apply` / `integral_map`, i.e. the exact continuum analogue of the
finite `Finset` fiber sums.

*Exhaustion/truncation consistency* (`ContPrior.tendsto_mass_of_iUnion`,
`ContPrior.tendsto_pair_of_iUnion`, `ContPrior.tendsto_dictionary_of_iUnion`).  A finite-resolution
regularization of a support is a monotone exhaustion `A k ↑ inf i`; the real masses of the
truncations converge to the continuum mass, likewise for the joint masses (both supports exhausted
at once), and the bundled `tendsto_dictionary_of_iUnion` states the mass vector, the joint matrix
and the correlation matrix in a single coordinatewise `Tendsto`.  So the finite regulator's numbers
are limits of the continuum ones, which is what makes the finite packet a regularization rather
than a different object.

## Boundary

* The continuum *law* is an input: this module states the dictionary and its consistency, not the
  construction of the Euclidean measure.  `IsProbabilityMeasure` is assumed, never derived.
* Supports are measurable sets of positive finite measure; the propositions are normalized
  indicators, not products of independent number densities, exactly as in the discrete packet.
* No point-evaluation vector in `L²`, no spatial translation and no unitary `ℋ_OS → ℱ` is assumed;
  B2/B3 remain conditional.
-/

namespace BookProof.OSReconstruction

open MeasureTheory Filter
open scoped Topology

noncomputable section

/-! ## 1. The continuum prior and its dictionary -/

/-- **The spatial prior on a continuum information space**: a probability measure on a measurable
space `Ω`, together with `n` measurable resolved supports.  The law is arbitrary, so the supports
need not be independent. -/
structure ContPrior (n : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  /-- The prior probability measure. -/
  μ : Measure Ω
  /-- It is a probability measure. -/
  isProb : IsProbabilityMeasure μ
  /-- The resolved spatial supports. -/
  inf : Fin n → Set Ω
  /-- Each support is measurable. -/
  meas : ∀ i, MeasurableSet (inf i)

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The prior measure of the event that the point `i` is informed. -/
def ContPrior.mass (P : ContPrior n Ω) (i : Fin n) : ℝ := P.μ.real (P.inf i)

/-- The prior measure of the event that the points `i` and `j` are both informed. -/
def ContPrior.joint (P : ContPrior n Ω) (i j : Fin n) : ℝ :=
  P.μ.real (P.inf i ∩ P.inf j)

/-- **The normalized number-density proposition at the point `i`.** -/
def ContPrior.prop (P : ContPrior n Ω) (i : Fin n) : Ω → ℝ :=
  (P.inf i).indicator fun _ => (P.mass i)⁻¹

/-- Expectation in the continuum prior. -/
def ContPrior.expect (P : ContPrior n Ω) (f : Ω → ℝ) : ℝ := ∫ x, f x ∂P.μ

/-- The two-point function of the normalized propositions. -/
def ContPrior.corr (P : ContPrior n Ω) (i j : Fin n) : ℝ :=
  P.expect fun x => P.prop i x * P.prop j x

/-- **The proposition is normalized on a continuum information space**: `∫ prop i ∂μ = 1` whenever
the informing event has positive mass.  The manuscript's normalization is a theorem here, not a
convention. -/
theorem ContPrior.expect_prop (P : ContPrior n Ω) (i : Fin n) (h : 0 < P.mass i) :
    P.expect (P.prop i) = 1 := by
  haveI := P.isProb
  have hne : P.mass i ≠ 0 := ne_of_gt h
  rw [ContPrior.expect, ContPrior.prop, integral_indicator (P.meas i), setIntegral_const,
    smul_eq_mul]
  change P.mass i * (P.mass i)⁻¹ = 1
  exact mul_inv_cancel₀ hne

/-- The product of two propositions is the indicator of the intersection, with the product of the
reciprocal masses. -/
theorem ContPrior.prop_mul (P : ContPrior n Ω) (i j : Fin n) :
    (fun x => P.prop i x * P.prop j x)
      = (P.inf i ∩ P.inf j).indicator (fun _ => (P.mass i)⁻¹ * (P.mass j)⁻¹) := by
  classical
  funext x
  simp only [ContPrior.prop, Set.indicator_apply]
  split_ifs <;> simp_all

/-- **The correlation is the joint measure over the product of the marginals.** -/
theorem ContPrior.corr_eq (P : ContPrior n Ω) (i j : Fin n) :
    P.corr i j = P.joint i j / (P.mass i * P.mass j) := by
  haveI := P.isProb
  rw [ContPrior.corr, ContPrior.expect, P.prop_mul i j,
    integral_indicator ((P.meas i).inter (P.meas j)), setIntegral_const, smul_eq_mul]
  change P.joint i j * ((P.mass i)⁻¹ * (P.mass j)⁻¹)
    = P.joint i j / (P.mass i * P.mass j)
  rw [div_eq_mul_inv, mul_inv]

/-- **Correlation `1` exactly when the joint measure factorizes** — the B0 dictionary statement on
a continuum information space. -/
theorem ContPrior.corr_eq_one_iff (P : ContPrior n Ω) (i j : Fin n)
    (hi : 0 < P.mass i) (hj : 0 < P.mass j) :
    P.corr i j = 1 ↔ P.joint i j = P.mass i * P.mass j := by
  have hne : P.mass i * P.mass j ≠ 0 := mul_ne_zero (ne_of_gt hi) (ne_of_gt hj)
  rw [P.corr_eq i j, div_eq_one_iff_eq hne]

/-! ## 2. Consistency: refinement invariance -/

variable {Γ : Type*} [MeasurableSpace Γ]

/-- **A continuum refinement**: an arbitrary probability measure on `Ω × Γ` and resolved supports
on the coarse factor `Ω`.  The law need not factor, so the refinement may correlate the auxiliary
tag with the coarse information. -/
structure ContRefinement (n : ℕ) (Ω Γ : Type*) [MeasurableSpace Ω] [MeasurableSpace Γ] where
  /-- The probability measure on the refined information space. -/
  μ : Measure (Ω × Γ)
  /-- It is a probability measure. -/
  isProb : IsProbabilityMeasure μ
  /-- The resolved supports, read off the coarse factor. -/
  inf : Fin n → Set Ω
  /-- Each support is measurable. -/
  meas : ∀ i, MeasurableSet (inf i)

/-- The refined prior on the full information space `Ω × Γ`. -/
def ContRefinement.refined (R : ContRefinement n Ω Γ) : ContPrior n (Ω × Γ) where
  μ := R.μ
  isProb := R.isProb
  inf i := Prod.fst ⁻¹' R.inf i
  meas i := (R.meas i).preimage measurable_fst

/-- The coarse prior: the pushforward of the refined measure along `Prod.fst`. -/
def ContRefinement.coarse (R : ContRefinement n Ω Γ) : ContPrior n Ω where
  μ := Measure.map Prod.fst R.μ
  isProb := letI := R.isProb; Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  inf := R.inf
  meas := R.meas

/-- **Marginalization preserves the one-point mass.** -/
theorem ContRefinement.mass_refined_eq_coarse (R : ContRefinement n Ω Γ) (i : Fin n) :
    R.refined.mass i = R.coarse.mass i := by
  simp only [ContRefinement.refined, ContRefinement.coarse, ContPrior.mass, Measure.real_def]
  rw [Measure.map_apply measurable_fst (R.meas i)]

/-- **Marginalization preserves the joint mass.** -/
theorem ContRefinement.joint_refined_eq_coarse (R : ContRefinement n Ω Γ) (i j : Fin n) :
    R.refined.joint i j = R.coarse.joint i j := by
  have hm : MeasurableSet (R.inf i ∩ R.inf j) := (R.meas i).inter (R.meas j)
  simp only [ContRefinement.refined, ContRefinement.coarse, ContPrior.joint, Measure.real_def]
  rw [← Set.preimage_inter, Measure.map_apply measurable_fst hm]

/-- **The normalized two-point function is invariant under refinement.** -/
theorem ContRefinement.corr_refined_eq_coarse (R : ContRefinement n Ω Γ) (i j : Fin n) :
    R.refined.corr i j = R.coarse.corr i j := by
  rw [ContPrior.corr_eq R.refined i j, ContPrior.corr_eq R.coarse i j,
    R.mass_refined_eq_coarse, R.mass_refined_eq_coarse, R.joint_refined_eq_coarse]

/-- **Every coarse observable has the same expectation** — the measure-theoretic form of the finite
refinement consistency estimate. -/
theorem ContRefinement.expect_refined_eq_coarse (R : ContRefinement n Ω Γ) (f : Ω → ℝ)
    (hf : Measurable f) :
    R.refined.expect (fun p => f p.1) = R.coarse.expect f := by
  rw [ContPrior.expect, ContPrior.expect]
  exact (integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable).symm

/-! ## 3. Consistency: exhaustion by finite-resolution truncations -/

/-- **Truncation consistency of the mass**: a monotone exhaustion of a support has real masses
converging to the continuum mass.  The finite regulator's numbers are therefore limits of the
continuum ones. -/
theorem ContPrior.tendsto_mass_of_iUnion (P : ContPrior n Ω) (i : Fin n) (A : ℕ → Set Ω)
    (hmono : Monotone A) (hcover : ⋃ k, A k = P.inf i) :
    Tendsto (fun k => P.μ.real (A k)) atTop (𝓝 (P.mass i)) := by
  haveI := P.isProb
  have h := tendsto_measure_iUnion_atTop (μ := P.μ) hmono
  rw [hcover] at h
  have hfin : P.μ (P.inf i) ≠ ⊤ := measure_ne_top P.μ _
  have h2 : Tendsto (fun k => (P.μ (A k)).toReal) atTop (𝓝 ((P.μ (P.inf i)).toReal)) :=
    (ENNReal.tendsto_toReal hfin).comp h
  simpa [Measure.real_def, ContPrior.mass] using h2

/-- **Truncation consistency of the joint mass**, with the second support held fixed. -/
theorem ContPrior.tendsto_joint_of_iUnion (P : ContPrior n Ω) (i j : Fin n) (A : ℕ → Set Ω)
    (hmono : Monotone A) (hcover : ⋃ k, A k = P.inf i) :
    Tendsto (fun k => P.μ.real (A k ∩ P.inf j)) atTop (𝓝 (P.joint i j)) := by
  haveI := P.isProb
  have hmono' : Monotone fun k => A k ∩ P.inf j := fun a b hab =>
    Set.inter_subset_inter_left _ (hmono hab)
  have hcover' : ⋃ k, A k ∩ P.inf j = P.inf i ∩ P.inf j := by
    rw [← Set.iUnion_inter, hcover]
  have h := tendsto_measure_iUnion_atTop (μ := P.μ) hmono'
  rw [hcover'] at h
  have hfin : P.μ (P.inf i ∩ P.inf j) ≠ ⊤ := measure_ne_top P.μ _
  have h2 : Tendsto (fun k => (P.μ (A k ∩ P.inf j)).toReal) atTop
      (𝓝 ((P.μ (P.inf i ∩ P.inf j)).toReal)) :=
    (ENNReal.tendsto_toReal hfin).comp h
  simpa [Measure.real_def, ContPrior.joint] using h2

/-- **Truncation consistency of a pair**, with both supports exhausted at once. -/
theorem ContPrior.tendsto_pair_of_iUnion (P : ContPrior n Ω) (i j : Fin n) (A B : ℕ → Set Ω)
    (hA : Monotone A) (hB : Monotone B)
    (hcA : ⋃ k, A k = P.inf i) (hcB : ⋃ k, B k = P.inf j) :
    Tendsto (fun k => P.μ.real (A k ∩ B k)) atTop (𝓝 (P.joint i j)) := by
  haveI := P.isProb
  have hmono : Monotone fun k => A k ∩ B k :=
    fun a b hab => Set.inter_subset_inter (hA hab) (hB hab)
  have hcover : ⋃ k, A k ∩ B k = P.inf i ∩ P.inf j := by
    rw [Set.iUnion_inter_of_monotone hA hB, hcA, hcB]
  have h := tendsto_measure_iUnion_atTop (μ := P.μ) hmono
  rw [hcover] at h
  have hfin : P.μ (P.inf i ∩ P.inf j) ≠ ⊤ := measure_ne_top P.μ _
  have h2 : Tendsto (fun k => (P.μ (A k ∩ B k)).toReal) atTop
      (𝓝 ((P.μ (P.inf i ∩ P.inf j)).toReal)) :=
    (ENNReal.tendsto_toReal hfin).comp h
  simpa [Measure.real_def, ContPrior.joint] using h2

/-- **Truncation consistency of the whole dictionary.**  Give each support its own monotone
exhaustion.  Then the mass vector, the joint matrix and the correlation matrix of the truncations
converge, coordinatewise, to the continuum dictionary in one statement: the finite regulator
reproduces every B0 number in the limit, not just the masses of one support at a time. -/
theorem ContPrior.tendsto_dictionary_of_iUnion (P : ContPrior n Ω)
    (A : (i : Fin n) → ℕ → Set Ω) (hmono : ∀ i, Monotone (A i))
    (hcover : ∀ i, ⋃ k, A i k = P.inf i) (hpos : ∀ i, 0 < P.mass i) :
    Tendsto (fun k => fun i => P.μ.real (A i k)) atTop (𝓝 fun i => P.mass i) ∧
      Tendsto (fun k => fun i => fun j => P.μ.real (A i k ∩ A j k)) atTop
        (𝓝 fun i => fun j => P.joint i j) ∧
      Tendsto (fun k => fun i => fun j =>
          P.μ.real (A i k ∩ A j k) / (P.μ.real (A i k) * P.μ.real (A j k))) atTop
        (𝓝 fun i => fun j => P.corr i j) := by
  have hm : ∀ i, Tendsto (fun k => P.μ.real (A i k)) atTop (𝓝 (P.mass i)) :=
    fun i => P.tendsto_mass_of_iUnion i (A i) (hmono i) (hcover i)
  have hj : ∀ i j, Tendsto (fun k => P.μ.real (A i k ∩ A j k)) atTop (𝓝 (P.joint i j)) :=
    fun i j => P.tendsto_pair_of_iUnion i j (A i) (A j) (hmono i) (hmono j) (hcover i) (hcover j)
  refine ⟨tendsto_pi_nhds.mpr hm, tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr (hj i), ?_⟩
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  have hden : Tendsto (fun k => P.μ.real (A i k) * P.μ.real (A j k)) atTop
      (𝓝 (P.mass i * P.mass j)) := (hm i).mul (hm j)
  have hne : P.mass i * P.mass j ≠ 0 :=
    mul_ne_zero (ne_of_gt (hpos i)) (ne_of_gt (hpos j))
  have hquot := (hj i j).div hden hne
  rw [ContPrior.corr_eq]
  exact hquot

/-! ## 4. The acceptance test on a continuum information space -/

/-- **The continuum test law**: Lebesgue measure restricted to the unit interval. -/
def unitIntervalLaw : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The test law is a probability measure. -/
instance unitIntervalLaw_isProbability : IsProbabilityMeasure unitIntervalLaw where
  measure_univ := by
    rw [unitIntervalLaw, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
      ENNReal.ofReal_one]

/-- The measure of the half interval under the test law. -/
theorem unitIntervalLaw_half :
    unitIntervalLaw (Set.Icc (0 : ℝ) (1 / 2)) = ENNReal.ofReal (1 / 2) := by
  rw [unitIntervalLaw, Measure.restrict_apply measurableSet_Icc]
  have h : Set.Icc (0 : ℝ) (1 / 2) ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) (1 / 2) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc]
    constructor
    · rintro ⟨h1, _⟩
      exact h1
    · intro h1
      exact ⟨h1, ⟨h1.1, by linarith [h1.2]⟩⟩
  rw [h, Real.volume_Icc, sub_zero]

/-- **The acceptance-test prior on the continuum information space `ℝ`**: two distinct resolved
supports whose informing event is the same half interval, each of prior mass `1/2`. -/
def correlatedInfoCont : ContPrior 2 ℝ where
  μ := unitIntervalLaw
  isProb := unitIntervalLaw_isProbability
  inf _ := Set.Icc (0 : ℝ) (1 / 2)
  meas _ := measurableSet_Icc

/-- The prior mass of each support is one half. -/
theorem correlatedInfoCont_mass (i : Fin 2) : correlatedInfoCont.mass i = 1 / 2 := by
  rw [ContPrior.mass, correlatedInfoCont, Measure.real_def, unitIntervalLaw_half,
    ENNReal.toReal_ofReal (by norm_num)]

/-- The joint mass of the two supports. -/
theorem correlatedInfoCont_joint (i j : Fin 2) : correlatedInfoCont.joint i j = 1 / 2 := by
  rw [ContPrior.joint, correlatedInfoCont, Measure.real_def, Set.inter_self,
    unitIntervalLaw_half, ENNReal.toReal_ofReal (by norm_num)]

/-- **The acceptance test on a continuum information space**: the normalized two-point function of
two distinct supports that share their information is `2`, not `1`. -/
theorem correlatedInfoCont_corr : correlatedInfoCont.corr 0 1 = 2 := by
  rw [ContPrior.corr_eq, correlatedInfoCont_joint, correlatedInfoCont_mass,
    correlatedInfoCont_mass]
  norm_num

/-- ... and it is different from the uncorrelated value. -/
theorem correlatedInfoCont_corr_ne_one : correlatedInfoCont.corr 0 1 ≠ 1 := by
  rw [correlatedInfoCont_corr]
  norm_num

end

end BookProof.OSReconstruction
