import Mathlib

/-!
# Mollification converges in `L²`

The Kato-type essential self-adjointness theorem of `BookProof/ChapterDegKatoEsa.lean` is
proved by mollifying a deficiency vector, and the limit `ε → 0` needs one classical
ingredient that Mathlib does not carry: **mollification converges in `L²`**.

This module supplies it, in the sharp quantitative form

`‖∫ ρ(y)·(u(· − y) − u) dy‖₂ ≤ sup { ‖u(· − y) − u‖₂ : ρ(y) ≠ 0 }`,

together with the continuity of translation in `Lᵖ` that makes the right-hand side small:

* `eLpNorm_translate` — translations are `Lᵖ`-isometries;
* `tendsto_translate_cc` — continuity of translation for a continuous compactly supported
  function, by uniform continuity;
* `tendsto_translate_Lp` — continuity of translation in `Lᵖ`, by density of the compactly
  supported continuous functions;
* `eLpNorm_mollify_sub_le` — the displayed bound, by Cauchy–Schwarz against the probability
  density `ρ` and Tonelli;
* `tendsto_mollify_L2` — the conclusion: for a mollifier family whose supports shrink to
  `0`, the mollifications converge to `u` in `L²`.

Everything is stated for a finite-dimensional real normed space with an additive Haar
measure, so it applies verbatim to `L²(ℝᵈ)`.
-/

namespace BookProof.MollifierL2

open MeasureTheory Filter ENNReal Pointwise
open scoped NNReal Topology

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 1. Continuity of translation -/

/-- Translation is an `Lᵖ` isometry. -/
theorem eLpNorm_translate {p : ℝ≥0∞} {f : E → F} (hf : AEStronglyMeasurable f μ) (a : E) :
    eLpNorm (fun x => f (x - a)) p μ = eLpNorm f p μ :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_sub_right μ a)

/-- **Continuity of translation, compactly supported case.**  For a continuous function with
compact support the `Lᵖ` distance to its translate is controlled by the modulus of
continuity. -/
theorem tendsto_translate_cc {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) {g : E → F}
    (hg : Continuous g) (hcs : HasCompactSupport g) :
    Tendsto (fun a : E => eLpNorm (fun x => g (x - a) - g x) p μ) (𝓝 0) (𝓝 0) := by
  classical
  set K : Set E := (tsupport g) + Metric.closedBall (0 : E) 1 with hK
  have hKc : IsCompact K := hcs.isCompact.add (isCompact_closedBall (0 : E) 1)
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hμK : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  set M : ℝ≥0∞ := μ K ^ (1 / p.toReal) with hM
  have hMne : M ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hμK
  have huc : UniformContinuous g := hcs.uniformContinuous_of_continuous hg
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact Eventually.of_forall fun _ => le_top
  have hM1 : M + 1 ≠ 0 := by positivity
  have hM1top : M + 1 ≠ ⊤ := by simp [hMne]
  set r : ℝ≥0∞ := ε / (M + 1) with hr
  have hrpos : r ≠ 0 := by simp [hr, hε.ne', hM1top]
  have hrtop : r ≠ ⊤ := by
    rw [hr, Ne, ENNReal.div_eq_top]
    push_neg
    exact ⟨fun _ h => absurd h hM1, fun h => absurd h hεtop⟩
  have hrmul : r * (M + 1) = ε := ENNReal.div_mul_cancel hM1 hM1top
  set c : ℝ := r.toReal with hc
  have hc0 : 0 < c := ENNReal.toReal_pos hrpos hrtop
  have hcof : ENNReal.ofReal c = r := ENNReal.ofReal_toReal hrtop
  have hcle : ENNReal.ofReal c * M ≤ ε := by
    rw [hcof, ← hrmul]
    gcongr
    exact le_self_add
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.mp huc c hc0
  have hunif : ∀ᶠ a : E in 𝓝 (0 : E), ∀ x : E, ‖g (x - a) - g x‖ ≤ c := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) hδ0] with a ha x
    have hd : dist (x - a) x < δ := by
      simpa [dist_eq_norm, Metric.mem_ball, sub_sub_cancel_left] using ha
    have hgd := hδ hd
    rw [dist_eq_norm] at hgd
    exact hgd.le
  filter_upwards [hunif, Metric.closedBall_mem_nhds (0 : E) one_pos] with a ha hball
  have hsupp : ∀ x : E, ‖g (x - a) - g x‖ ≤ ‖K.indicator (fun _ => c) x‖ := by
    intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      simpa [Real.norm_eq_abs, abs_of_pos hc0] using ha x
    · have h1 : g x = 0 := by
        have hnm : x ∉ tsupport g := by
          intro hmem
          exact hx ⟨x, hmem, 0, by simp, by simp⟩
        exact image_eq_zero_of_notMem_tsupport hnm
      have h2 : g (x - a) = 0 := by
        have hnm : x - a ∉ tsupport g := by
          intro hmem
          refine hx ⟨x - a, hmem, a, ?_, by abel⟩
          simpa [Metric.mem_closedBall, dist_eq_norm] using hball
        exact image_eq_zero_of_notMem_tsupport hnm
      simp [h1, h2]
  calc eLpNorm (fun x => g (x - a) - g x) p μ
      ≤ eLpNorm (K.indicator (fun _ => c)) p μ := eLpNorm_mono hsupp
    _ = ‖c‖ₑ * μ K ^ (1 / p.toReal) := eLpNorm_indicator_const hKm hp0 hp
    _ ≤ ε := by
        have hcc : ‖c‖ₑ = ENNReal.ofReal c := by
          simp [Real.enorm_eq_ofReal_abs, abs_of_pos hc0]
        rw [hcc, ← hM]
        exact hcle

/-- **Continuity of translation in `Lᵖ`.** -/
theorem tendsto_translate_Lp {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) (hp1 : 1 ≤ p) {f : E → F}
    (hf : MemLp f p μ) :
    Tendsto (fun a : E => eLpNorm (fun x => f (x - a) - f x) p μ) (𝓝 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨g, hgcs, hgle, hgc, hgmem⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (p := p) hp (ε := ε / 4) (by simp [hε.ne'])
  set h : E → F := fun x => f x - g x with hh
  have hhmeas : AEStronglyMeasurable h μ := hf.1.sub hgmem.1
  have hhle : eLpNorm h p μ ≤ ε / 4 := hgle
  have hmid := tendsto_translate_cc (μ := μ) hp0 hp hgc hgcs
  rw [ENNReal.tendsto_nhds_zero] at hmid
  filter_upwards [hmid (ε / 4) (by simp [hε.ne'])] with a hamid
  have hsplit : (fun x => f (x - a) - f x)
      = ((fun y : E => h (y - a)) + (fun y : E => g (y - a) - g y)) + (fun y : E => -h y) := by
    funext x
    simp only [Pi.add_apply, hh]
    abel
  have hm1 : AEStronglyMeasurable (fun x : E => h (x - a)) μ :=
    hhmeas.comp_measurePreserving (measurePreserving_sub_right μ a)
  have hm2 : AEStronglyMeasurable (fun x : E => g (x - a) - g x) μ :=
    ((hgc.comp (continuous_id.sub continuous_const)).sub hgc).aestronglyMeasurable
  have hstep : eLpNorm (fun x => f (x - a) - f x) p μ
      ≤ (eLpNorm (fun x : E => h (x - a)) p μ + eLpNorm (fun x : E => g (x - a) - g x) p μ)
        + eLpNorm (fun x : E => -h x) p μ := by
    rw [hsplit]
    refine le_trans (eLpNorm_add_le (hm1.add hm2) hhmeas.neg hp1) ?_
    gcongr
    exact eLpNorm_add_le hm1 hm2 hp1
  have e1 : eLpNorm (fun x : E => h (x - a)) p μ = eLpNorm h p μ := eLpNorm_translate hhmeas a
  have e3 : eLpNorm (fun x : E => -h x) p μ = eLpNorm h p μ := by
    rw [show (fun x : E => -h x) = -h from rfl, eLpNorm_neg]
  rw [e1, e3] at hstep
  have hbound : eLpNorm h p μ + eLpNorm (fun x : E => g (x - a) - g x) p μ + eLpNorm h p μ
      ≤ ε / 4 + ε / 4 + ε / 4 := by gcongr
  have hfin : ε / 4 + ε / 4 + ε / 4 ≤ ε := by
    have h4 : ε / 4 + ε / 4 + ε / 4 + ε / 4 = ε := by
      rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same,
        show ε + ε + ε + ε = ε * 4 by ring]
      exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
    calc ε / 4 + ε / 4 + ε / 4 ≤ ε / 4 + ε / 4 + ε / 4 + ε / 4 := le_self_add
      _ = ε := h4
  exact hstep.trans (hbound.trans hfin)

/-! ## 2. Mollification in `L²` -/

/-- Cauchy–Schwarz against the probability density `ρ`, pointwise in `x`. -/
theorem enorm_mollify_sq_le (u : E → ℂ) (ρ : E → ℝ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρm : Measurable ρ)
    (hρ1 : ∫⁻ y, ENNReal.ofReal (ρ y) ∂μ = 1) (hu : StronglyMeasurable u) (x : E) :
    ‖∫ y, ρ y • (u (x - y) - u x) ∂μ‖ₑ ^ (2:ℝ)
      ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ) ∂μ := by
  set w : E → ℝ≥0∞ := fun y => ‖u (x - y) - u x‖ₑ with hw
  have hwm : AEMeasurable w μ :=
    ((hu.comp_measurable (by fun_prop)).sub stronglyMeasurable_const).measurable.enorm.aemeasurable
  have hstep1 : ‖∫ y, ρ y • (u (x - y) - u x) ∂μ‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * w y ∂μ := by
    refine le_trans (enorm_integral_le_lintegral_enorm _) (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    rw [enorm_smul]
    congr 1
    simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hρ0 y)]
  have hA : AEMeasurable (fun y => (ENNReal.ofReal (ρ y)) ^ ((1:ℝ)/2)) μ :=
    ((ENNReal.measurable_ofReal.comp hρm).pow_const _).aemeasurable
  have hB : AEMeasurable (fun y => (ENNReal.ofReal (ρ y)) ^ ((1:ℝ)/2) * w y) μ := hA.mul hwm
  have hCS : ∫⁻ y, ENNReal.ofReal (ρ y) * w y ∂μ
      ≤ (∫⁻ y, ((ENNReal.ofReal (ρ y)) ^ ((1:ℝ)/2)) ^ (2:ℝ) ∂μ) ^ ((1:ℝ)/2)
        * (∫⁻ y, ((ENNReal.ofReal (ρ y)) ^ ((1:ℝ)/2) * w y) ^ (2:ℝ) ∂μ) ^ ((1:ℝ)/2) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2)
      (by constructor <;> norm_num) hA hB
    refine le_trans (le_of_eq ?_) h
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hsq1 : ∀ y : E, ((ENNReal.ofReal (ρ y)) ^ ((1:ℝ)/2)) ^ (2:ℝ) = ENNReal.ofReal (ρ y) := by
    intro y
    rw [← ENNReal.rpow_mul]
    norm_num
  have hsq2 : ∀ y : E, ((ENNReal.ofReal (ρ y)) ^ ((1:ℝ)/2) * w y) ^ (2:ℝ)
      = ENNReal.ofReal (ρ y) * w y ^ (2:ℝ) := by
    intro y
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
    norm_num
  simp only [hsq1, hsq2] at hCS
  rw [hρ1] at hCS
  simp only [ENNReal.one_rpow, one_mul] at hCS
  calc ‖∫ y, ρ y • (u (x - y) - u x) ∂μ‖ₑ ^ (2:ℝ)
      ≤ ((∫⁻ y, ENNReal.ofReal (ρ y) * w y ^ (2:ℝ) ∂μ) ^ ((1:ℝ)/2)) ^ (2:ℝ) :=
        ENNReal.rpow_le_rpow (hstep1.trans hCS) (by norm_num)
    _ = ∫⁻ y, ENNReal.ofReal (ρ y) * w y ^ (2:ℝ) ∂μ := by
        rw [← ENNReal.rpow_mul]
        norm_num

/-- **The mollification bound.**  If every translate `u(· − y)` with `ρ y ≠ 0` is within `C`
of `u` in `L²`, then so is the `ρ`-average of the translates. -/
theorem eLpNorm_mollify_sub_le (u : E → ℂ) (hu : StronglyMeasurable u) (ρ : E → ℝ)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρm : Measurable ρ) (hρ1 : ∫⁻ y, ENNReal.ofReal (ρ y) ∂μ = 1)
    {C : ℝ≥0∞} (hC : ∀ y : E, ρ y ≠ 0 → eLpNorm (fun x => u (x - y) - u x) 2 μ ≤ C) :
    eLpNorm (fun x => ∫ y, ρ y • (u (x - y) - u x) ∂μ) 2 μ ≤ C := by
  rcases eq_or_ne C ⊤ with rfl | hCtop
  · exact le_top
  have hmeas : AEMeasurable
      (Function.uncurry fun x y : E => ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ))
      (μ.prod μ) := by
    have h1 : StronglyMeasurable (Function.uncurry fun x y : E => u (x - y) - u x) :=
      (hu.comp_measurable (by fun_prop)).sub (hu.comp_measurable (by fun_prop))
    have h2 : Measurable (Function.uncurry fun x y : E => ENNReal.ofReal (ρ y)) :=
      (ENNReal.measurable_ofReal.comp hρm).comp measurable_snd
    exact (h2.mul (h1.measurable.enorm.pow_const _)).aemeasurable
  have hC2 : C ^ (2:ℝ) ≠ ⊤ := by simp [hCtop]
  have key : ∫⁻ x, ‖∫ y, ρ y • (u (x - y) - u x) ∂μ‖ₑ ^ (2:ℝ) ∂μ ≤ C ^ (2:ℝ) := by
    calc ∫⁻ x, ‖∫ y, ρ y • (u (x - y) - u x) ∂μ‖ₑ ^ (2:ℝ) ∂μ
        ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ) ∂μ ∂μ :=
          lintegral_mono fun x => enorm_mollify_sq_le u ρ hρ0 hρm hρ1 hu x
      _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ) ∂μ ∂μ :=
          lintegral_lintegral_swap hmeas
      _ ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * C ^ (2:ℝ) ∂μ := by
          refine lintegral_mono fun y => ?_
          rw [lintegral_const_mul' _ _ (by simp)]
          by_cases hy : ρ y = 0
          · simp [hy]
          · have hCy := hC y hy
            have hrw : ∫⁻ x, ‖u (x - y) - u x‖ₑ ^ (2:ℝ) ∂μ
                = (eLpNorm (fun x => u (x - y) - u x) 2 μ) ^ (2:ℝ) := by
              rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
                ← ENNReal.rpow_mul]
              norm_num
            rw [hrw]
            gcongr
      _ = C ^ (2:ℝ) := by rw [lintegral_mul_const' _ _ hC2, hρ1, one_mul]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have hstep : (∫⁻ x, ‖∫ y, ρ y • (u (x - y) - u x) ∂μ‖ₑ ^ (2:ℝ) ∂μ) ^ ((1:ℝ)/2)
      ≤ (C ^ (2:ℝ)) ^ ((1:ℝ)/2) := ENNReal.rpow_le_rpow key (by norm_num)
  have hfin : (C ^ (2:ℝ)) ^ ((1:ℝ)/2) = C := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hfin] at hstep
  simpa using hstep

/-- **Mollification converges in `L²`.**  For a family of probability densities whose
supports shrink to the origin, the mollified functions converge to `u` in `L²`. -/
theorem tendsto_mollify_L2 {ι : Type*} {l : Filter ι} (u : E → ℂ) (hu : StronglyMeasurable u)
    (hu2 : MemLp u 2 μ) (ρ : ι → E → ℝ) (r : ι → ℝ)
    (hρ0 : ∀ i y, 0 ≤ ρ i y) (hρm : ∀ i, Measurable (ρ i))
    (hρ1 : ∀ i, ∫⁻ y, ENNReal.ofReal (ρ i y) ∂μ = 1)
    (hsupp : ∀ i, ∀ y : E, ρ i y ≠ 0 → ‖y‖ < r i) (hr : Tendsto r l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (fun x => ∫ y, ρ i y • (u (x - y) - u x) ∂μ) 2 μ) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have htr := tendsto_translate_Lp (μ := μ) (p := 2) (by norm_num) (by norm_num) (by norm_num) hu2
  rw [ENNReal.tendsto_nhds_zero] at htr
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp (htr ε hε)
  have hev : ∀ᶠ i in l, r i < δ := Filter.Tendsto.eventually_lt_const hδ0 hr
  filter_upwards [hev] with i hi
  refine eLpNorm_mollify_sub_le u hu (ρ i) (hρ0 i) (hρm i) (hρ1 i) ?_
  intro y hy
  have hylt : ‖y‖ < r i := hsupp i y hy
  refine hδ ?_
  rw [dist_eq_norm, sub_zero]
  exact hylt.trans hi

end

end BookProof.MollifierL2
