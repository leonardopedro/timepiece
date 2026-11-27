import Mathlib

/-!
# Chapter SatisficingTarget — the satisficing potential, its proper target, and plateau odds

This is packet **S0** of `pcnl.md`'s active S0–S6 work order.  Stage 2 of the five-stage
pipeline halts a warm run at the first entry into the knee set `{L ≤ τ}` and then draws from a
*proper* target built out of the declared nonnegative loss `L` (a supervised data loss or a
differentiable, non-RLCD reinforcement-learning penalty).  This chapter supplies the definitions
and the elementary certificates that target needs.

## Contents

* **§1, the shapes** — `softplus δ` (the smooth hinge `δ log (1 + e^{u/δ})`), `huber` (the `C¹`
  Huberised hinge `½ (max 0 u)²`), and `satPot ψ τ κ α L = κ ψ (L − τ) + α L`, the satisficing
  potential.  Positivity of both shapes, continuity, and the two derivatives
  (`softplus_hasDerivAt`, `huber_hasDerivAt`: the Huberised derivative is `max 0 u`, so it
  vanishes on the knee);
* **§2, the potential is nonnegative and its exponential bounded** — `satPot_nonneg`,
  `softSatPot_nonneg`, `huberSatPot_nonneg`, `exp_neg_satPot_le_one`, and the density
  `satDensity Φ = e^{−Φ}` with `satDensity_le_one`;
* **§3, the target** — `satZ` (the unnormalised evidence `∫ e^{−Φ} dP₀`), `satZ_le_one`
  (`Z ≤ 1`), `satZOn_ge_of_le` / `satZOn_le_of_ge` (a ceiling gives a lower density bound and a
  floor gives an upper one), **`satZ_pos_of_lower_bound`** (`0 < Z` as soon as a set of positive
  prior mass carries a finite ceiling — the explicit `Z ≥ P₀(A) exp(−sup_A Φ)` of the plan), and
  the normalised probability target `satTarget` with **`satTarget_univ`** and
  `isProbabilityMeasure_satTarget`: `0 < Z ≤ 1` is a proper target;
* **§4, plateau-vs-spike odds** — **`plateau_odds_bound`**, the cross-multiplied form of
  `π(B_plat) / π(B_spike) ≥ (P₀ B_plat / P₀ B_spike) · exp(−(φ_plat − φ_spike))`, where
  `φ_plat` is a ceiling on the plateau and `φ_spike` a floor on the spike; and the exact
  Huberised `α = 0` specialisation **`huber_odds_eq_prior_ratio`**: inside the knee the odds are
  the pure prior-volume ratio `P₀(B_plat) / P₀(B_spike)`;
* **§5, the chain rule** — **`hasFDerivAt_satPot`**:
  `∇Φ = (κ ψ'(L − τ) + α) ∇L` for a general Frechet derivative, its two instances
  (`hasFDerivAt_huberPh`, `hasFDerivAt_softPh`), and **`huberPh_fderiv_eq_zero_of_le`**: with
  the Huberised hinge and `α = 0` the gradient vanishes identically on `{L ≤ τ}`.

## Scope

`B` (boundary): every statement is about the *declared* potential on an abstract parameter
space with a probability prior `P₀`; nothing here identifies `L` with an implemented
architecture, and the odds bound is a cross-multiplied `ℝ≥0∞` inequality rather than a claim
that either set has finite positive mass.  No sampler, kernel or dynamics appears in this packet.
-/

namespace BookProof.MCMC.SatisficingTarget

open MeasureTheory Filter Topology

/-! ## §1. The shapes and the potential -/

/-- The softplus smoothing of `u ↦ max 0 u` at width `δ > 0`: `δ log (1 + e^{u/δ})`. -/
noncomputable def softplus (δ u : ℝ) : ℝ := δ * Real.log (1 + Real.exp (u / δ))

/-- The `C¹` Huberised hinge `u ↦ ½ (max 0 u)²`. -/
noncomputable def huber (u : ℝ) : ℝ := (1 / 2) * (max 0 u) ^ 2

/-- The satisficing potential `Φ_{τ,κ,α}(L) = κ ψ (L − τ) + α L`, assembled from a shape `ψ`,
ceiling `τ`, confinement `κ` and gentle tilt `α`. -/
def satPot (ψ : ℝ → ℝ) (τ κ α L : ℝ) : ℝ := κ * ψ (L - τ) + α * L

/-- The softplus satisficing potential. -/
noncomputable def softSatPot (δ τ κ α L : ℝ) : ℝ := satPot (softplus δ) τ κ α L

/-- The Huberised satisficing potential. -/
noncomputable def huberSatPot (τ κ α L : ℝ) : ℝ := satPot huber τ κ α L

theorem softplus_pos {δ : ℝ} (hδ : 0 < δ) (u : ℝ) : 0 < softplus δ u := by
  have harg : 1 < 1 + Real.exp (u / δ) := by
    have := Real.exp_pos (u / δ)
    linarith
  exact mul_pos hδ (Real.log_pos harg)

theorem softplus_nonneg {δ : ℝ} (hδ : 0 < δ) (u : ℝ) : 0 ≤ softplus δ u :=
  le_of_lt (softplus_pos hδ u)

theorem softplus_continuous (δ : ℝ) : Continuous (softplus δ) := by
  unfold softplus
  refine continuous_const.mul (Continuous.log ?_ ?_)
  · exact continuous_const.add (Real.continuous_exp.comp (continuous_id.div_const δ))
  · intro x
    have := Real.exp_pos (x / δ)
    linarith

/-- The softplus derivative, in the sigmoid form `e^{u/δ} / (1 + e^{u/δ})`. -/
theorem softplus_hasDerivAt {δ : ℝ} (hδ : δ ≠ 0) (u : ℝ) :
    HasDerivAt (softplus δ) (Real.exp (u / δ) / (1 + Real.exp (u / δ))) u := by
  unfold softplus
  have hinner : HasDerivAt (fun x : ℝ => 1 + Real.exp (x / δ))
      (Real.exp (u / δ) * (1 / δ)) u := by
    have h1 : HasDerivAt (fun x : ℝ => x / δ) (1 / δ) u := by
      simpa using (hasDerivAt_id u).div_const δ
    simpa using h1.exp.const_add 1
  have hlog := hinner.log (by
    have := Real.exp_pos (u / δ)
    linarith)
  have hmul := hlog.const_mul δ
  have hval : δ * ((Real.exp (u / δ) * (1 / δ)) / (1 + Real.exp (u / δ)))
      = Real.exp (u / δ) / (1 + Real.exp (u / δ)) := by
    field_simp
  rw [hval] at hmul
  exact hmul

theorem huber_nonneg (u : ℝ) : 0 ≤ huber u := by
  unfold huber
  have := sq_nonneg (max 0 u)
  linarith

theorem huber_eq_zero_of_nonpos {u : ℝ} (hu : u ≤ 0) : huber u = 0 := by
  unfold huber
  rw [max_eq_left hu]
  ring

theorem huber_pos_of_pos {u : ℝ} (hu : 0 < u) : 0 < huber u := by
  unfold huber
  rw [max_eq_right (le_of_lt hu)]
  have : 0 < u ^ 2 := pow_pos hu 2
  linarith

/-- The Huberised hinge has derivative `max 0 u`, which is `0` on the knee `{u ≤ 0}`. -/
theorem huber_hasDerivAt (u : ℝ) : HasDerivAt huber (max 0 u) u := by
  rcases lt_trichotomy u 0 with hu | hu | hu
  · have hev : huber =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hu] with y hy
      exact huber_eq_zero_of_nonpos (le_of_lt hy)
    have h := (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hev
    simpa [max_eq_left (le_of_lt hu)] using h
  · subst hu
    rw [hasDerivAt_iff_tendsto_slope]
    have hbound : ∀ h : ℝ, ‖slope huber 0 h‖ ≤ ‖h‖ / 2 := by
      intro h
      rcases lt_trichotomy h 0 with hh | hh | hh
      · have hz : huber h = 0 := huber_eq_zero_of_nonpos (le_of_lt hh)
        have hslope : slope huber 0 h = 0 := by
          rw [slope_def_field, hz, huber_eq_zero_of_nonpos le_rfl]
          simp
        rw [hslope]
        simp only [norm_zero]
        exact div_nonneg (norm_nonneg h) (by norm_num)
      · subst hh
        simp
      · have hpos : huber h = (1 / 2) * h ^ 2 := by
          unfold huber
          rw [max_eq_right (le_of_lt hh)]
        have hslope : slope huber 0 h = h / 2 := by
          rw [slope_def_field, hpos, huber_eq_zero_of_nonpos le_rfl, sub_zero]
          field_simp [hh.ne']
          simp
        rw [hslope, norm_div]
        norm_num
    have hupper : Tendsto (fun h : ℝ => ‖h‖ / 2) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have hn : Tendsto (fun h : ℝ => ‖h‖) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
        simpa using (continuous_norm.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
      simpa using hn.div_const 2
    simpa using squeeze_zero_norm hbound hupper
  · have hev : huber =ᶠ[𝓝 u] (fun y : ℝ => (1 / 2) * y ^ 2) := by
      filter_upwards [Ioi_mem_nhds hu] with y hy
      unfold huber
      rw [max_eq_right (le_of_lt hy)]
    have hbase : HasDerivAt (fun y : ℝ => y ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    have hderiv : HasDerivAt (fun y : ℝ => (1 / 2) * y ^ 2) u u := by
      have h := hbase.const_mul (1 / 2)
      convert h using 1
      ring
    have h' := hderiv.congr_of_eventuallyEq hev
    simpa [max_eq_right (le_of_lt hu)] using h'

theorem continuous_huber : Continuous huber := by
  have hmax : Continuous fun u : ℝ => max 0 u := continuous_const.max continuous_id
  unfold huber
  exact continuous_const.mul (hmax.pow 2)

theorem continuous_satPot {ψ : ℝ → ℝ} (hψ : Continuous ψ) (τ κ α : ℝ) :
    Continuous (fun L => satPot ψ τ κ α L) := by
  unfold satPot
  exact (continuous_const.mul (hψ.comp (continuous_id.sub continuous_const))).add
    (continuous_const.mul continuous_id)

theorem measurable_satPot {Ω : Type*} [MeasurableSpace Ω] {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (τ κ α : ℝ) {L : Ω → ℝ} (hL : Measurable L) :
    Measurable (fun θ => satPot ψ τ κ α (L θ)) :=
  (continuous_satPot hψ τ κ α).measurable.comp hL

theorem satPot_nonneg {ψ : ℝ → ℝ} (hψ : ∀ u, 0 ≤ ψ u) {τ κ α L : ℝ} (hκ : 0 ≤ κ)
    (hα : 0 ≤ α) (hL : 0 ≤ L) : 0 ≤ satPot ψ τ κ α L := by
  unfold satPot
  exact add_nonneg (mul_nonneg hκ (hψ _)) (mul_nonneg hα hL)

theorem softSatPot_nonneg {δ : ℝ} (hδ : 0 < δ) {τ κ α L : ℝ} (hκ : 0 ≤ κ) (hα : 0 ≤ α)
    (hL : 0 ≤ L) : 0 ≤ softSatPot δ τ κ α L :=
  satPot_nonneg (softplus_nonneg hδ) hκ hα hL

theorem huberSatPot_nonneg {τ κ α L : ℝ} (hκ : 0 ≤ κ) (hα : 0 ≤ α) (hL : 0 ≤ L) :
    0 ≤ huberSatPot τ κ α L :=
  satPot_nonneg huber_nonneg hκ hα hL

/-- On the knee `{L ≤ τ}` the Huberised hinge vanishes, so `Φ = α L` there; at `α = 0` the
potential is exactly zero. -/
theorem huberSatPot_eq_zero_of_le {τ κ L : ℝ} (hL : L ≤ τ) :
    huberSatPot τ κ 0 L = 0 := by
  unfold huberSatPot satPot
  rw [huber_eq_zero_of_nonpos (by linarith : L - τ ≤ 0)]
  ring

/-! ## §2. The exponential density -/

theorem exp_neg_le_one {Φ : ℝ} (hΦ : 0 ≤ Φ) : Real.exp (-Φ) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  linarith

/-! ## §3. The target and its normalisation -/

section Target

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The unnormalised target density `e^{−Φ}` as an `ENNReal`-valued function. -/
noncomputable def satDensity (Φ : Ω → ℝ) : Ω → ENNReal := fun θ => ENNReal.ofReal (Real.exp (-Φ θ))

/-- The unnormalised evidence `Z = ∫ e^{−Φ} dP₀`. -/
noncomputable def satZ (P₀ : Measure Ω) (Φ : Ω → ℝ) : ENNReal := ∫⁻ θ, satDensity Φ θ ∂P₀

/-- The unnormalised evidence restricted to a set. -/
noncomputable def satZOn (P₀ : Measure Ω) (Φ : Ω → ℝ) (B : Set Ω) : ENNReal :=
  ∫⁻ θ in B, satDensity Φ θ ∂P₀

/-- The normalised satisficing target `π_{τ,κ,α} = Z⁻¹ e^{−Φ} P₀`. -/
noncomputable def satTarget (P₀ : Measure Ω) (Φ : Ω → ℝ) : Measure Ω :=
  (satZ P₀ Φ)⁻¹ • P₀.withDensity (satDensity Φ)

theorem measurable_satDensity {Φ : Ω → ℝ} (hΦ : Measurable Φ) :
    Measurable (satDensity Φ) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hΦ.neg)

omit [MeasurableSpace Ω] in
theorem satDensity_pos (Φ : Ω → ℝ) (θ : Ω) : 0 < satDensity Φ θ :=
  ENNReal.ofReal_pos.mpr (Real.exp_pos _)

omit [MeasurableSpace Ω] in
theorem satDensity_le_one {Φ : Ω → ℝ} {θ : Ω} (hΦ : 0 ≤ Φ θ) : satDensity Φ θ ≤ 1 := by
  unfold satDensity
  simpa using ENNReal.ofReal_le_ofReal (exp_neg_le_one hΦ)

omit [MeasurableSpace Ω] in
theorem satDensity_eq_one_of_eq_zero {Φ : Ω → ℝ} {θ : Ω} (h : Φ θ = 0) :
    satDensity Φ θ = 1 := by
  unfold satDensity
  simp [h]

/-- `Z ≤ 1` for a probability prior and a nonnegative potential. -/
theorem satZ_le_one {P₀ : Measure Ω} [IsProbabilityMeasure P₀] {Φ : Ω → ℝ}
    (hΦ : ∀ θ, 0 ≤ Φ θ) : satZ P₀ Φ ≤ 1 := by
  have h : satZ P₀ Φ ≤ ∫⁻ _, (1 : ENNReal) ∂P₀ :=
    lintegral_mono fun θ => satDensity_le_one (hΦ θ)
  rwa [lintegral_one, measure_univ] at h

/-- A ceiling `Φ ≤ b` on `B` gives the density floor `e^{−b}` on `B`. -/
theorem satZOn_ge_of_le {P₀ : Measure Ω} {Φ : Ω → ℝ} (hΦ : Measurable Φ) {B : Set Ω}
    {b : ℝ} (hb : ∀ θ ∈ B, Φ θ ≤ b) :
    ENNReal.ofReal (Real.exp (-b)) * P₀ B ≤ satZOn P₀ Φ B := by
  have hmono : satZOn P₀ Φ B ≥ ∫⁻ θ in B, ENNReal.ofReal (Real.exp (-b)) ∂P₀ :=
    setLIntegral_mono (measurable_satDensity hΦ)
      (fun θ hθ => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hb θ hθ])))
  rwa [setLIntegral_const] at hmono

/-- A floor `b ≤ Φ` on `B` gives the density ceiling `e^{−b}` on `B`. -/
theorem satZOn_le_of_ge {P₀ : Measure Ω} {Φ : Ω → ℝ} {B : Set Ω} {b : ℝ}
    (hb : ∀ θ ∈ B, b ≤ Φ θ) :
    satZOn P₀ Φ B ≤ ENNReal.ofReal (Real.exp (-b)) * P₀ B := by
  have hmono : satZOn P₀ Φ B ≤ ∫⁻ θ in B, ENNReal.ofReal (Real.exp (-b)) ∂P₀ :=
    setLIntegral_mono measurable_const
      (fun θ hθ => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hb θ hθ])))
  rwa [setLIntegral_const] at hmono

/-- The plan's explicit lower bound `Z ≥ P₀(A) exp(−b)` when `Φ ≤ b` on `A`. -/
theorem satZ_lower_bound {P₀ : Measure Ω} {Φ : Ω → ℝ} (hΦ : Measurable Φ) {A : Set Ω}
    {b : ℝ} (hb : ∀ θ ∈ A, Φ θ ≤ b) :
    ENNReal.ofReal (Real.exp (-b)) * P₀ A ≤ satZ P₀ Φ := by
  have hmono : ∫⁻ x in A, satDensity Φ x ∂P₀ ≤ ∫⁻ x, satDensity Φ x ∂P₀ := by
    simpa using (lintegral_mono_set (μ := P₀) (f := satDensity Φ) (Set.subset_univ A))
  exact le_trans (satZOn_ge_of_le hΦ hb) hmono

/-- `0 < Z` as soon as a set of positive prior mass carries a finite ceiling. -/
theorem satZ_pos_of_lower_bound {P₀ : Measure Ω} {Φ : Ω → ℝ} (hΦ : Measurable Φ) {A : Set Ω}
    {b : ℝ} (hA : P₀ A ≠ 0) (hb : ∀ θ ∈ A, Φ θ ≤ b) : 0 < satZ P₀ Φ := by
  have hεpos : 0 < ENNReal.ofReal (Real.exp (-b)) :=
    ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hpos : 0 < ENNReal.ofReal (Real.exp (-b)) * P₀ A :=
    ENNReal.mul_pos (ne_of_gt hεpos) hA
  exact lt_of_lt_of_le hpos (satZ_lower_bound hΦ hb)

theorem satZ_ne_top {P₀ : Measure Ω} [IsProbabilityMeasure P₀] {Φ : Ω → ℝ}
    (hΦ : ∀ θ, 0 ≤ Φ θ) : satZ P₀ Φ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (satZ_le_one hΦ)

/-- With `0 < Z ≤ 1`, the normalised target is a probability measure. -/
theorem satTarget_univ {P₀ : Measure Ω} {Φ : Ω → ℝ} (hZ0 : satZ P₀ Φ ≠ 0)
    (hZtop : satZ P₀ Φ ≠ ⊤) : satTarget P₀ Φ Set.univ = 1 := by
  unfold satTarget
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  change (satZ P₀ Φ)⁻¹ * satZ P₀ Φ = 1
  rw [ENNReal.inv_mul_cancel hZ0 hZtop]

theorem isProbabilityMeasure_satTarget {P₀ : Measure Ω} {Φ : Ω → ℝ}
    (hZ0 : satZ P₀ Φ ≠ 0) (hZtop : satZ P₀ Φ ≠ ⊤) :
    IsProbabilityMeasure (satTarget P₀ Φ) :=
  ⟨satTarget_univ hZ0 hZtop⟩

/-! ## §4. Plateau-vs-spike odds

The inequality is written cross-multiplied in `ℝ≥0∞`: it says
`π(B_plat) · e^{−φ_plat} P₀(B_plat) ≥ π(B_spike) · e^{−φ_spike} P₀(B_spike)` in the
unnormalised masses, i.e. after dividing by `Z`,
`π(B_plat) / π(B_spike) ≥ (P₀ B_plat / P₀ B_spike) · exp(−(φ_plat − φ_spike))`.
No finiteness or positivity of either mass is assumed. -/

theorem plateau_odds_bound {P₀ : Measure Ω} {Φ : Ω → ℝ} (hΦ : Measurable Φ)
    {B_plat B_spike : Set Ω} {φ_plat φ_spike : ℝ}
    (hplat : ∀ θ ∈ B_plat, Φ θ ≤ φ_plat)
    (hspike : ∀ θ ∈ B_spike, φ_spike ≤ Φ θ) :
    satZOn P₀ Φ B_spike * (ENNReal.ofReal (Real.exp (-φ_plat)) * P₀ B_plat)
      ≤ satZOn P₀ Φ B_plat * (ENNReal.ofReal (Real.exp (-φ_spike)) * P₀ B_spike) := by
  have hlow := satZOn_ge_of_le (P₀ := P₀) hΦ hplat
  have hup := satZOn_le_of_ge (P₀ := P₀) hspike
  calc satZOn P₀ Φ B_spike * (ENNReal.ofReal (Real.exp (-φ_plat)) * P₀ B_plat)
      = (ENNReal.ofReal (Real.exp (-φ_plat)) * P₀ B_plat) * satZOn P₀ Φ B_spike :=
        mul_comm _ _
    _ ≤ (ENNReal.ofReal (Real.exp (-φ_plat)) * P₀ B_plat)
          * (ENNReal.ofReal (Real.exp (-φ_spike)) * P₀ B_spike) :=
        mul_le_mul_of_nonneg_left hup (zero_le _)
    _ ≤ satZOn P₀ Φ B_plat
          * (ENNReal.ofReal (Real.exp (-φ_spike)) * P₀ B_spike) :=
        mul_le_mul_of_nonneg_right hlow (zero_le _)

/-- On a set where the potential vanishes, the satisficing mass is the prior mass. -/
theorem satZOn_eq_measure_of_eq_zero {P₀ : Measure Ω} {Φ : Ω → ℝ} {B : Set Ω}
    (hB : MeasurableSet B) (h : ∀ θ ∈ B, Φ θ = 0) : satZOn P₀ Φ B = P₀ B := by
  have hcongr : satZOn P₀ Φ B = ∫⁻ _ in B, (1 : ENNReal) ∂P₀ :=
    setLIntegral_congr_fun hB (fun θ hθ => satDensity_eq_one_of_eq_zero (h θ hθ))
  rw [hcongr, setLIntegral_const, one_mul]

/-- The exact Huberised `α = 0` specialisation: inside the knee `{L ≤ τ}` both masses are prior
masses, hence the target odds equal the prior-volume ratio. -/
theorem huber_odds_eq_prior_ratio {P₀ : Measure Ω} (τ κ : ℝ) {L : Ω → ℝ}
    {B_plat B_spike : Set Ω} (hplatm : MeasurableSet B_plat)
    (hspikem : MeasurableSet B_spike)
    (hplat : ∀ θ ∈ B_plat, L θ ≤ τ) (hspike : ∀ θ ∈ B_spike, L θ ≤ τ) :
    satZOn P₀ (fun θ => huberSatPot τ κ 0 (L θ)) B_plat * P₀ B_spike
      = satZOn P₀ (fun θ => huberSatPot τ κ 0 (L θ)) B_spike * P₀ B_plat := by
  rw [satZOn_eq_measure_of_eq_zero hplatm (fun θ hθ => huberSatPot_eq_zero_of_le (hplat θ hθ)),
    satZOn_eq_measure_of_eq_zero hspikem
      (fun θ hθ => huberSatPot_eq_zero_of_le (hspike θ hθ))]
  exact mul_comm _ _

end Target

/-! ## §5. The chain rule -/

section Gradient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The chain rule `∇Φ = (κ ψ'(L − τ) + α) ∇L` for a general Frechet derivative. -/
theorem hasFDerivAt_satPot {ψ : ℝ → ℝ} {ψ' τ κ α : ℝ} {L : E → ℝ} {L' : E →L[ℝ] ℝ}
    {θ : E} (hL : HasFDerivAt L L' θ) (hψ : HasDerivAt ψ ψ' (L θ - τ)) :
    HasFDerivAt (fun y => satPot ψ τ κ α (L y)) ((κ * ψ' + α) • L') θ := by
  have hg : HasFDerivAt (fun y => L y - τ) L' θ := hL.sub_const τ
  have hcomp : HasFDerivAt (fun y => ψ (L y - τ)) (ψ' • L') θ :=
    hψ.comp_hasFDerivAt θ hg
  have hsum := (hcomp.const_mul κ).add (hL.const_mul α)
  have hcoe : κ • (ψ' • L') + α • L' = (κ * ψ' + α) • L' := by
    rw [add_smul, smul_smul]
  rw [hcoe] at hsum
  simpa [satPot] using hsum

/-- The Huberised instance: `∇Φ = (κ max 0 (L − τ)) ∇L` at `α = 0`. -/
theorem hasFDerivAt_huberPh {τ κ : ℝ} {L : E → ℝ} {L' : E →L[ℝ] ℝ} {θ : E}
    (hL : HasFDerivAt L L' θ) :
    HasFDerivAt (fun y => huberSatPot τ κ 0 (L y))
      (((κ * max 0 (L θ - τ)) : ℝ) • L') θ := by
  simpa [huberSatPot] using
    (hasFDerivAt_satPot (ψ := huber) (ψ' := max 0 (L θ - τ)) (τ := τ) (κ := κ)
      (α := 0) (L := L) (L' := L') (θ := θ) hL (huber_hasDerivAt (L θ - τ)))

/-- The softplus instance with the sigmoid derivative. -/
theorem hasFDerivAt_softPh {δ τ κ α : ℝ} (hδ : δ ≠ 0) {L : E → ℝ} {L' : E →L[ℝ] ℝ}
    {θ : E} (hL : HasFDerivAt L L' θ) :
    HasFDerivAt (fun y => softSatPot δ τ κ α (L y))
      ((κ * (Real.exp ((L θ - τ) / δ) / (1 + Real.exp ((L θ - τ) / δ))) + α) • L') θ := by
  simpa [softSatPot] using
    (hasFDerivAt_satPot (ψ := softplus δ) (ψ' := Real.exp ((L θ - τ) / δ)
        / (1 + Real.exp ((L θ - τ) / δ))) (τ := τ) (κ := κ) (α := α)
      (L := L) (L' := L') (θ := θ) hL (softplus_hasDerivAt hδ (L θ - τ)))

/-- The gradient of the Huberised satisficing potential vanishes on the knee `{L ≤ τ}` at
`α = 0`: the confinement creates no drift inside the plateau. -/
theorem huberPh_fderiv_eq_zero_of_le {τ κ : ℝ} {L : E → ℝ} {L' : E →L[ℝ] ℝ} {θ : E}
    (hL : HasFDerivAt L L' θ) (h : L θ ≤ τ) :
    HasFDerivAt (fun y => huberSatPot τ κ 0 (L y)) (0 : E →L[ℝ] ℝ) θ := by
  have hd := hasFDerivAt_huberPh (τ := τ) (κ := κ) hL
  have hmax : max 0 (L θ - τ) = 0 := max_eq_left (by linarith)
  have hzero : (((κ * max 0 (L θ - τ)) : ℝ) • L') = (0 : E →L[ℝ] ℝ) := by
    rw [hmax, mul_zero]
    exact zero_smul ℝ L'
  rw [hzero] at hd
  exact hd

end Gradient

end BookProof.MCMC.SatisficingTarget
