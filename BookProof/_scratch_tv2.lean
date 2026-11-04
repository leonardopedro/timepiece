import Mathlib

noncomputable section

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-! ## Step A: the density-change identity and the Cauchy–Schwarz bound.

`ν = π.withDensity (fun x => ENNReal.ofReal (g x))`, i.e. `ν = g • π` for a real `g ≥ 0`.
Then for any `f`, `∫ f dν − ∫ f dπ = ∫ f (g − 1) dπ`, and Cauchy–Schwarz bounds
`|∫ f (g − 1) dπ| ≤ ‖f‖_{L²(π)} · ‖g − 1‖_{L²(π)} ≤ ‖f‖_∞ · √(π univ) · ‖g − 1‖_{L²(π)}`.
-/

/-- The change-of-density identity: integrating `f` against `ν = g • π` equals
integrating `f * g` against `π` (for `0 ≤ g`, `π`-a.e. finite, `f` integrable). -/
theorem integral_withDensity_ofReal_eq {π : Measure α} {g : α → ℝ}
    (hg : Measurable g) (hg0 : 0 ≤ᵐ[π] g) (f : α → ℝ) :
    ∫ x, f x ∂π.withDensity (fun x => ENNReal.ofReal (g x))
      = ∫ x, f x * g x ∂π := by
  have hfin : ∀ᵐ x ∂π, (fun x => ENNReal.ofReal (g x)) x < ∞ :=
    ae_of_all _ fun x => ENNReal.ofReal_lt_top
  have hmeas : Measurable fun x => ENNReal.ofReal (g x) :=
    ENNReal.measurable_ofReal.comp hg
  rw [integral_withDensity_eq_integral_toReal_smul hmeas hfin f]
  refine integral_congr_ae ?_
  filter_upwards [hg0] with x hx
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_ofReal (le_of_eq hx)]

/-- **Cauchy–Schwarz for the density difference.**  With `ν = g • π` (`g ≥ 0`), the
deviation of `∫ f` against `ν` from that against `π` is bounded by the `L²(π)` norms. -/
theorem abs_integral_sub_integral_le_of_withDensity {π ν : Measure α} {g : α → ℝ}
    (hg : Measurable g) (hg0 : 0 ≤ᵐ[π] g) (hν : ν = π.withDensity fun x => ENNReal.ofReal (g x))
    (f : α → ℝ) (hf : MemLp f 2 π) (hg2 : MemLp (fun x => g x - 1) 2 π) :
    |∫ x, f x ∂ν - ∫ x, f x ∂π| ≤ (∫ x, ‖f x‖ ^ 2 ∂π) ^ (1 / 2) * (∫ x, ‖g x - 1‖ ^ 2 ∂π) ^ (1 / 2) := by
  have hfi : Integrable f π := hf.integrable
  have hgi : Integrable (fun x => g x - 1) π := hg2.integrable
  have h1 : ∫ x, f x ∂ν - ∫ x, f x ∂π
      = ∫ x, f x * (g x - 1) ∂π := by
    rw [hν, integral_withDensity_ofReal_eq hg hg0 f, integral_mul_sub hfi (hg2.integrable),
      sub_add_cancel]
  rw [h1]
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    (Real.HolderConjugate.two_two) ?_ ?_ hf hg2
  · rw [Real.toReal_ofNat] at hcs
    exact hcs
  · filter_upwards [] with x
    exact norm_nonneg _
  · filter_upwards [hg0] with x hx
    have : 0 ≤ ‖g x - 1‖ := norm_nonneg _
    exact this

end
