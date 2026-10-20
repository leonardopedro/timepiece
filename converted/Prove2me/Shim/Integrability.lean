import Mathlib

/-!
# Shim: local integrability of power singularities

`integrableOn_ball_of_norm_le_rpow` (platform Mathlib) is absent from the pinned Mathlib.  It is
re-proved here from `integrable_fun_norm_addHaar` (polar coordinates for an additive Haar measure)
and `intervalIntegral.integrableOn_Ioo_rpow_iff`: a function bounded by `C * ‖x‖ ^ (-α)` with
`α < dim E` is integrable on every ball centred at the origin.
-/

open MeasureTheory Metric Set Module

theorem integrableOn_ball_of_norm_le_rpow {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E} [μ.IsAddHaarMeasure] {f : E → F} {α C ρ : ℝ}
    (hn : 0 < finrank ℝ E) (hα : α < finrank ℝ E)
    (hbound : ∀ᶠ x in ae μ, ‖f x‖ ≤ C * ‖x‖ ^ (-α)) (hf : AEStronglyMeasurable f μ) :
    IntegrableOn f (ball 0 ρ) μ := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos hn
  set g : ℝ → ℝ := (Iio ρ).indicator (fun y => C * y ^ (-α))
  have hg : Integrable (fun x : E => g ‖x‖) μ := by
    rw [integrable_fun_norm_addHaar]
    rcases le_or_gt ρ 0 with hρ | hρ
    · refine (integrableOn_zero (s := Ioi (0:ℝ)) (μ := volume)).congr_fun (fun y hy => ?_)
        measurableSet_Ioi
      have : y ∉ Iio ρ := by simp only [mem_Iio, not_lt]; exact hρ.trans (le_of_lt hy)
      simp [g, Set.indicator_of_notMem this]
    have h1 : IntegrableOn (fun y : ℝ => C * y ^ ((finrank ℝ E - 1 : ℕ) - α : ℝ)) (Ioo 0 ρ) := by
      refine Integrable.const_mul ?_ C
      rw [← IntegrableOn, intervalIntegral.integrableOn_Ioo_rpow_iff hρ]
      have : ((finrank ℝ E - 1 : ℕ) : ℝ) = (finrank ℝ E : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [this]; linarith
    refine (h1.integrable_indicator measurableSet_Ioo).integrableOn.congr_fun
      (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0:ℝ) < y := hy
    by_cases hyρ : y < ρ
    · have hm : y ∈ Ioo 0 ρ := ⟨hy0, hyρ⟩
      simp only [g, Set.indicator_of_mem hm, Set.indicator_of_mem (show y ∈ Iio ρ from hyρ),
        smul_eq_mul]
      rw [Real.rpow_sub hy0, Real.rpow_natCast, Real.rpow_neg hy0.le, div_eq_mul_inv]
      ring
    · have hm : y ∉ Ioo 0 ρ := fun h => hyρ h.2
      simp [g, Set.indicator_of_notMem hm, Set.indicator_of_notMem (show y ∉ Iio ρ from hyρ)]
  have hg' : Integrable (fun x : E => g ‖x‖) (μ.restrict (ball 0 ρ)) := hg.restrict
  refine hg'.mono' hf.restrict ?_
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [hbound] with x hx hxb
  have : ‖x‖ ∈ Iio ρ := by simpa using hxb
  simpa [g, Set.indicator_of_mem this] using hx
