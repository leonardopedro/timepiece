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
  constructor ; simp [ infiniteWalkMeasure ]

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
  rw [ MeasureTheory.Measure.pi_eq, MeasureTheory.Measure.pi_eq ]
  any_goals exact Measure.pi fun i : J => scalarBumpMeasure ( x i ) ( ε i )
  · intro s hs
    rw [ MeasureTheory.Measure.map_apply ]
    · rw [ show ( fun y : J → ℝ => fun i : I => y ⟨ i, hIJ i.2 ⟩ ) ⁻¹' univ.pi s =
          ( Set.pi ( Set.univ : Set J ) fun i =>
            if h : i.val ∈ I then s ⟨ i.val, h ⟩ else Set.univ ) from ?_ ]
      · rw [ MeasureTheory.Measure.pi_pi ]
        rw [ ← Finset.prod_subset ( show Finset.image
            ( fun i : I => ⟨ i, hIJ i.2 ⟩ : I → J ) Finset.univ ⊆ Finset.univ from
            Finset.subset_univ _ ) ]
        · rw [ Finset.prod_image ]
          · aesop
          · exact fun i _ j _ hij => by aesop
        · simp +contextual [ Finset.mem_image ]
      · grind
    · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _
    · exact MeasurableSet.univ_pi hs
  · intro s hs; rw [ MeasureTheory.Measure.pi_pi ]

/-! ### Moments of the scalar bump law -/

/-
The integral against the scalar bump law is the normalized interval integral
over its supporting interval.
-/
theorem scalarBump_integral (a r : ℝ) (h : 0 < r) (f : ℝ → ℝ) :
    ∫ y, f y ∂scalarBumpMeasure a r = (2 * r)⁻¹ * ∫ y in (a - r)..(a + r), f y := by
  have hvol : volume (Icc (a - r) (a + r)) = ENNReal.ofReal (2 * r) := by
    rw [Real.volume_Icc]; ring_nf
  unfold scalarBumpMeasure
  rw [ProbabilityTheory.cond, hvol, integral_smul_measure,
    intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    ← ENNReal.ofReal_inv_of_pos (by linarith),
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-
The scalar bump law is centered: its first centered moment vanishes.
-/
theorem scalarBump_centered (a r : ℝ) (h : 0 < r) :
    ∫ y, (y - a) ∂scalarBumpMeasure a r = 0 := by
  rw [scalarBump_integral a r h,
    show ∫ y in (a - r)..(a + r), (y - a) = ∫ u in (-r)..r, u by
      have hshift := intervalIntegral.integral_comp_sub_right (a := a - r) (b := a + r)
        (fun u => u) a
      simpa using hshift,
    integral_id]
  ring

/-
The exact second centered moment of the scalar bump law is `r ^ 2 / 3`.
-/
theorem scalarBump_sq (a r : ℝ) (h : 0 < r) :
    ∫ y, (y - a) ^ 2 ∂scalarBumpMeasure a r = r ^ 2 / 3 := by
  rw [scalarBump_integral a r h,
    show ∫ y in (a - r)..(a + r), (y - a) ^ 2 = ∫ u in (-r)..r, u ^ 2 by
      have hshift := intervalIntegral.integral_comp_sub_right (a := a - r) (b := a + r)
        (fun u => u ^ 2) a
      simpa using hshift,
    integral_pow]
  field_simp
  ring

/-
Coordinates of the infinite walk are distributed by the corresponding scalar
bump law, so integrals of coordinate observables reduce to scalar integrals.
-/
theorem integral_coordinate (x ε : ℕ → ℝ) [∀ n, Fact (0 < ε n)] (n : ℕ) (f : ℝ → ℝ)
    (hf : Continuous f) :
    ∫ y, f (y n) ∂infiniteWalkMeasure x ε = ∫ z, f z ∂scalarBumpMeasure (x n) (ε n) := by
  rw [← map_eval_infiniteWalkMeasure x ε n,
    integral_map (measurable_pi_apply n).aemeasurable hf.aestronglyMeasurable]

/-
Every centered coordinate has mean zero under the compatible infinite law.
-/
theorem coordinate_centered (x ε : ℕ → ℝ) [∀ n, Fact (0 < ε n)] (n : ℕ) :
    ∫ y, (y n - x n) ∂infiniteWalkMeasure x ε = 0 := by
  rw [integral_coordinate x ε n (fun z => z - x n) (continuous_id.sub continuous_const)]
  exact scalarBump_centered (x n) (ε n) Fact.out

/-
For the uniform bump law, each centered coordinate has exact second moment
`ε n ^ 2 / 3`.
-/
theorem coordinate_secondMoment_eq (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (n : ℕ) :
    ∫ y, (y n - x n) ^ 2 ∂infiniteWalkMeasure x ε = (ε n) ^ 2 / 3 := by
  rw [integral_coordinate x ε n (fun z => (z - x n) ^ 2)
    ((continuous_id.sub continuous_const).pow 2)]
  exact scalarBump_sq (x n) (ε n) Fact.out

/-
Every coordinate has second moment at most its prescribed squared radius.
-/
theorem coordinate_secondMoment_bound (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (n : ℕ) :
    ∫ y, (y n - x n) ^ 2 ∂infiniteWalkMeasure x ε ≤ (ε n) ^ 2 := by
  rw [coordinate_secondMoment_eq x ε n]
  nlinarith [sq_nonneg (ε n)]

/-- Squared centered energy on an arbitrary finite coordinate set. -/
def finiteEnergy (I : Finset ℕ) (x y : ℕ → ℝ) : ℝ :=
  ∑ n ∈ I, (y n - x n) ^ 2

/-
Each coordinate lies within its prescribed radius almost surely.
-/
theorem coordinate_abs_sub_le_radius (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (n : ℕ) :
    ∀ᵐ y ∂infiniteWalkMeasure x ε, |y n - x n| ≤ ε n := by
  have h_scalar : ∀ᵐ z ∂scalarBumpMeasure (x n) (ε n), |z - x n| ≤ ε n := by
    have h_restrict :
        ∀ᵐ z ∂(volume.restrict (Icc (x n - ε n) (x n + ε n))), |z - x n| ≤ ε n := by
      rw [ae_restrict_iff' measurableSet_Icc]
      filter_upwards with z hz
      rw [abs_le]
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    unfold scalarBumpMeasure
    rw [ProbabilityTheory.cond]
    exact Measure.ae_smul_measure h_restrict _
  have hmeas : MeasurableSet {z : ℝ | |z - x n| ≤ ε n} :=
    measurableSet_le (by fun_prop) measurable_const
  refine (ae_map_iff (μ := infiniteWalkMeasure x ε) (f := fun y : ℕ → ℝ => y n)
    (measurable_pi_apply n).aemeasurable hmeas).mp ?_
  rwa [map_eval_infiniteWalkMeasure]

/-
Each coordinate-energy observable is integrable under the infinite walk law.
-/
theorem integrable_coordinate_energy (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (n : ℕ) :
    Integrable (fun y => (y n - x n) ^ 2) (infiniteWalkMeasure x ε) := by
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℕ → ℝ => (ε n) ^ 2)
    (by simp)
    (Measurable.aestronglyMeasurable (by measurability)) ?_
  filter_upwards [coordinate_abs_sub_le_radius x ε n] with y hy
  simpa using pow_le_pow_left₀ (abs_nonneg _) hy 2

/-
The finite-coordinate energy has exact expectation equal to one third of the
corresponding squared-radius budget.
-/
theorem finiteEnergy_expectation_eq (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (I : Finset ℕ) :
    ∫ y, finiteEnergy I x y ∂infiniteWalkMeasure x ε =
      ∑ n ∈ I, (ε n) ^ 2 / 3 := by
  convert MeasureTheory.integral_finset_sum I
    (fun n _ => integrable_coordinate_energy x ε n) using 1
  exact Finset.sum_congr rfl fun n _ => by rw [coordinate_secondMoment_eq x ε n]

/-
The expected energy on any finite coordinate set is bounded by the sum of
its squared radii.
-/
theorem finiteEnergy_expectation_bound (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (I : Finset ℕ) :
    ∫ y, finiteEnergy I x y ∂infiniteWalkMeasure x ε ≤
      ∑ n ∈ I, (ε n) ^ 2 := by
  rw [finiteEnergy_expectation_eq x ε I]
  refine Finset.sum_le_sum fun n _ => ?_
  nlinarith [sq_nonneg (ε n)]

/-
**Almost-sure finite-energy theorem.** If the squared coordinate radii are
summable, then a sample from the compatible infinite walk has summable squared
centered increments almost surely.
-/
theorem ae_summable_centered_energy (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (hε : Summable (fun n => (ε n) ^ 2)) :
    ∀ᵐ y ∂infiniteWalkMeasure x ε,
      Summable (fun n => (y n - x n) ^ 2) := by
  -- Each squared increment is dominated by the corresponding squared radius,
  -- and the radii are summable.
  have h_summable : ∀ᵐ y ∂infiniteWalkMeasure x ε, ∀ n, (y n - x n) ^ 2 ≤ (ε n) ^ 2 := by
    filter_upwards [MeasureTheory.ae_all_iff.mpr
      fun n => coordinate_abs_sub_le_radius x ε n] with y hy
    exact fun n => by nlinarith [abs_le.mp (hy n)]
  filter_upwards [h_summable] with y hy
  exact Summable.of_nonneg_of_le (fun n => sq_nonneg _) hy hε

/-
Under summable squared radii, the total centered energy is bounded by the total
radius budget almost surely.
-/
theorem ae_tsum_centered_energy_le (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (hε : Summable (fun n => (ε n) ^ 2)) :
    ∀ᵐ y ∂infiniteWalkMeasure x ε,
      ∑' n, (y n - x n) ^ 2 ≤ ∑' n, (ε n) ^ 2 := by
  filter_upwards [ae_summable_centered_energy x ε hε, MeasureTheory.ae_all_iff.mpr
    fun n => coordinate_abs_sub_le_radius x ε n] with y hy₁ hy₂
  exact Summable.tsum_le_tsum (fun n => by nlinarith only [abs_le.mp (hy₂ n)]) hy₁ hε

/-
The ordinary partial energies converge almost surely to the total centered
energy.
-/
theorem ae_tendsto_partial_energy (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (hε : Summable (fun n => (ε n) ^ 2)) :
    ∀ᵐ y ∂infiniteWalkMeasure x ε,
      Tendsto (fun N => ∑ n ∈ Finset.range N, (y n - x n) ^ 2)
        atTop (𝓝 (∑' n, (y n - x n) ^ 2)) := by
  -- For almost every `y` the series of squared increments converges.
  filter_upwards [ae_summable_centered_energy x ε hε] with y hy
  exact hy.hasSum.tendsto_sum_nat

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
      (infiniteWalkMeasure x ε) := integrable_const _
  have h_ae_measurable : AEStronglyMeasurable (fun y : ℕ → ℝ => ∑' n, (y n - x n) ^ 2)
      (infiniteWalkMeasure x ε) := by
    have h_partial_meas (N : ℕ) : Measurable (fun y : ℕ → ℝ =>
        ∑ n ∈ Finset.range N, (y n - x n) ^ 2) := by
      refine Finset.measurable_sum (Finset.range N) (fun n _ => ?_)
      exact ((measurable_pi_apply n).sub measurable_const).pow_const 2
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (fun N => (h_partial_meas N).aestronglyMeasurable) ?_
    exact ae_tendsto_partial_energy x ε hε
  refine MeasureTheory.Integrable.mono' h_const_integrable h_ae_measurable ?_
  filter_upwards [h_bound] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun n => sq_nonneg _)]
  exact hy

/-
Under summable squared radii, the expected total centered energy is exactly one
third of the total squared-radius budget.
-/
theorem totalEnergy_expectation_eq (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (hε : Summable (fun n => (ε n) ^ 2)) :
    ∫ y, (∑' n, (y n - x n) ^ 2) ∂infiniteWalkMeasure x ε =
      (∑' n, (ε n) ^ 2) / 3 := by
  have h_norm : ∀ n : ℕ,
      ∫ y, ‖(y n - x n) ^ 2‖ ∂infiniteWalkMeasure x ε = (ε n) ^ 2 / 3 := by
    intro n
    simp only [Real.norm_eq_abs, abs_pow, sq_abs]
    exact coordinate_secondMoment_eq x ε n
  have h_summable :
      Summable fun n => ∫ y, ‖(y n - x n) ^ 2‖ ∂infiniteWalkMeasure x ε := by
    rw [funext h_norm]
    exact hε.div_const 3
  have h_swap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (F := fun (n : ℕ) (y : ℕ → ℝ) => (y n - x n) ^ 2)
    (fun n => integrable_coordinate_energy x ε n) h_summable
  rw [← h_swap]
  simp only [coordinate_secondMoment_eq]
  rw [tsum_div_const]

/-
The expected total centered energy is bounded by the total squared-radius
budget.
-/
theorem totalEnergy_expectation_bound (x ε : ℕ → ℝ)
    [∀ n, Fact (0 < ε n)] (hε : Summable (fun n => (ε n) ^ 2)) :
    ∫ y, (∑' n, (y n - x n) ^ 2) ∂infiniteWalkMeasure x ε ≤
      ∑' n, (ε n) ^ 2 := by
  rw [totalEnergy_expectation_eq x ε hε]
  have h_nonneg : 0 ≤ ∑' n, (ε n) ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  linarith

end RandomMap2InfiniteWalk
