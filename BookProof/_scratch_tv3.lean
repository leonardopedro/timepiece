import Mathlib

noncomputable section

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-! ## Step A (v2): density-change identity + Cauchy–Schwarz, exact API. -/

/-- Change of density: `∫ f d(π.withDensity (ofReal ∘ g)) = ∫ f * g dπ` for `g ≥ 0`. -/
theorem integral_withDensity_ofReal_eq {π : Measure α} {g : α → ℝ}
    (hg : Measurable g) (hg0 : 0 ≤ᵐ[π] g) (f : α → ℝ) :
    ∫ x, f x ∂π.withDensity (fun x => ENNReal.ofReal (g x))
      = ∫ x, f x * g x ∂π := by
  have hmeas : Measurable fun x => ENNReal.ofReal (g x) :=
    ENNReal.measurable_ofReal.comp hg
  have hfin : ∀ᵐ x ∂π, (fun x => ENNReal.ofReal (g x)) x < ∞ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  rw [integral_withDensity_eq_integral_toReal_smul hmeas hfin f]
  refine integral_congr_ae ?_
  filter_upwards [hg0] with x hx
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (le_of_eq hx)]

/-- **Cauchy–Schwarz / Holder(2,2) for a product of real functions.** -/
theorem abs_integral_mul_le_sqrt {π : Measure α} {f h : α → ℝ}
    (hf : MemLp f 2 π) (hh : MemLp h 2 π) :
    |∫ x, f x * h x ∂π|
      ≤ (∫ x, (f x)^2 ∂π) ^ (1 / 2) * (∫ x, (h x)^2 ∂π) ^ (1 / 2) := by
  have hfi : Integrable f π := hf.integrable
  have hhi : Integrable h π := hh.integrable
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    (Real.HolderConjugate.two_two)
    (ae_of_all _ fun _ => sq_nonneg _) (ae_of_all _ fun _ => sq_nonneg _) hf hh
  rw [Real.toReal_ofNat] at hcs
  have habs : |∫ x, f x * h x ∂π| ≤ ∫ x, |f x * h x| ∂π :=
    abs_integral_le (hfi.mul hhi)
  have hmul : ∫ x, |f x * h x| ∂π = ∫ x, |f x| * |h x| ∂π := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    rw [abs_mul]
  have hcs' := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    (Real.HolderConjugate.two_two)
    (ae_of_all _ fun x => abs_nonneg _) (ae_of_all _ fun x => abs_nonneg _)
    (memLp_of_real ...) ...
  sorry

end
