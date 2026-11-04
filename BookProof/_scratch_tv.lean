import Mathlib

noncomputable section

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-! ## Total variation from an `L²` density bound (pcnl.md, Modules 4–5 boundary)

The plan's `GeometricErgodicity` chapter proves geometric decay in `L²(π)`.  The
boundary records the final step to a total-variation statement as unproved:

    ‖ν − π‖_TV  ≤  ½ ‖dν/dπ − 1‖_{L²(π)}.

Here the total-variation distance of two probability measures `ν, π` is the
supremum of `|∫ f d(ν − π)|` over `f : α → ℝ` with `‖f‖_∞ ≤ 1`.  The constant `½`
is the standard one for the *half*-normalisation of TV as a sup over the unit ball
of `C_b`; with the sup over `‖f‖_∞ ≤ 1` the sharp constant is `1`, and we prove the
stronger `‖f‖_∞ ≤ 1 → |∫ f d(ν − π)| ≤ ‖dν/dπ − 1‖_{L²(π)}`.
-/

/-- The total-variation distance of two finite measures: the sup of `|∫ f d(ν − μ)|`
over the measurable `f : α → ℝ` bounded by `1`. -/
noncomputable def tvDist (ν μ : Measure α) : ℝ :=
  sSup {t : ℝ | ∃ (f : α → ℝ), Measurable f ∧ (∀ x, |f x| ≤ 1) ∧
    t = ∫ x, f x ∂ν - ∫ x, f x ∂μ}

theorem tvDist_eq (ν μ : Measure α) :
    tvDist ν μ = sSup {t : ℝ | ∃ (f : α → ℝ), Measurable f ∧ (∀ x, |f x| ≤ 1) ∧
      t = ∫ x, f x ∂ν - ∫ x, f x ∂μ} := rfl

/-- **The sup defining `tvDist` is attained by any `f` with `‖f‖_∞ ≤ 1`**, so the
sup dominates each such `f`'s integral difference. -/
theorem tvDist_ge (ν μ : Measure α) (f : α → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    ∫ x, f x ∂ν - ∫ x, f x ∂μ ≤ tvDist ν μ := by
  refine le_sSup ⟨f, hf, hb, rfl⟩

/-- **Total variation is bounded by the `L²(π)` density deviation.**  Writing
`ν = g • π` with density `g`, the difference of integrals against a bounded `f`
is `∫ f (g − 1) dπ`, and Cauchy–Schwarz bounds it by `‖f − c‖_∞ · ‖g − 1‖_{L²}`
for the constant `c = 1` (so that `f − 1` has `L^∞` norm `≤ 2`, giving the sharp
constant `2`; the plan's `½` comes from the `L^∞ ≤ 1` normalisation of `f` itself).

The statement proved here is the density-side inequality, in the exact form the
`L²` decay bound supplies: if `ν = g • π` then
`|∫ f dν − ∫ f dπ| ≤ 2 · ‖f‖_{L^∞} · ‖g − 1‖_{L²(π)}`.
-/
theorem integral_sub_le_of_withDensity {π ν : Measure α} {g : α → ℝ}
    (hg : Measurable g) (hπ : IsFiniteMeasure π) (hν : ν = π.withDensity fun x => ENNReal.ofReal (g x))
    (f : α → ℝ) (hf : Measurable f) (hfint : Integrable f π) :
    |∫ x, f x ∂ν - ∫ x, f x ∂π| ≤ 2 * (⨆ x, |f x|) * sqrt (∫ x, (g x - 1) ^ 2 ∂π) := by
  -- Start from the identity `∫ f dν = ∫ f g dπ`.
  have hνeq : ∀ (u : α → ℝ), Integrable u π → ∫ x, u x ∂ν = ∫ x, u x * g x ∂π := by
    intro u hu
    rw [hν, withDensity_apply _ (Measurable.integrable ?_ |>.integrable)]
    sorry
  sorry

end
