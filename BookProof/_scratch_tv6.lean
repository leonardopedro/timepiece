import Mathlib

noncomputable section

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-! ## Step A (v6): density-change identity + the sharp TV bound. -/

/-- Change of density: `∫ f d(π.withDensity (ofReal ∘ g)) = ∫ f * g dπ` for `g ≥ 0`. -/
theorem integral_withDensity_ofReal_eq {π : Measure α} {g : α → ℝ}
    (hg : Measurable g) (hg0 : 0 ≤ᵐ[π] g) (f : α → ℝ) :
    ∫ x, f x ∂π.withDensity (fun x => ENNReal.ofReal (g x))
      = ∫ x, f x * g x ∂π := by
  have hmeas : Measurable fun x => ENNReal.ofReal (g x) :=
    ENNReal.measurable_ofReal.comp hg
  have hfin : ∀ᵐ x ∂π, ENNReal.ofReal (g x) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  rw [integral_withDensity_eq_integral_toReal_smul hmeas hfin f]
  refine integral_congr_ae ?_
  filter_upwards [hg0] with x hx
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (le_of_eq hx)]

/-- **The sharp `L^∞`–Cauchy–Schwarz bound.**  With `ν = g • π` (`g ≥ 0`, `π` finite),
for any `f` with `|f| ≤ C` π-a.e. (`C ≥ 0`) and `MemLp (g−1) 2 π`:

    |∫ f dν − ∫ f dπ| ≤ C * √(π univ) * ‖g − 1‖_{L²(π)}.

The constant `1` (sharper than `pcnl.md`'s `½`) is what the `‖f‖_∞ ≤ 1` normalisation of the
total-variation sup yields; `½` is the `L¹`–`L^∞` convention. -/
theorem abs_integral_sub_integral_le_of_withDensity {π ν : Measure α} {g : α → ℝ}
    (hg : Measurable g) (hg0 : 0 ≤ᵐ[π] g) (hfin : IsFiniteMeasure π)
    (hν : ν = π.withDensity fun x => ENNReal.ofReal (g x))
    (f : α → ℝ) (hf : AEStronglyMeasurable f π) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ x ∂π, |f x| ≤ C)
    (hg2 : MemLp (fun x => g x - 1) 2 π) :
    |∫ x, f x ∂ν - ∫ x, f x ∂π|
      ≤ C * (π univ).toReal ^ (1 / 2) * (∫ x, (g x - 1) ^ 2 ∂π) ^ (1 / 2) := by
  have hgi : Integrable (fun x => g x - 1) π := hg2.integrable one_le_two
  -- `f` is bounded, hence in `L²` (π finite) and integrable.
  have hfb : MemLp f 2 π :=
    (memLp_top_of_bound hf C (hC.mono fun x hx => by rwa [Real.norm_eq_abs])).mono_exponent
      one_le_two
  have hfi : Integrable f π := hfb.integrable one_le_two
  -- 1. the deviation is `∫ f (g − 1) dπ`.
  have hdev : ∫ x, f x ∂ν - ∫ x, f x ∂π = ∫ x, f x * (g x - 1) ∂π := by
    rw [hν, integral_withDensity_ofReal_eq hg hg0 f, integral_mul hfi hgi, sub_add_cancel]
  rw [hdev]
  have hmul : Integrable (fun x => f x * (g x - 1)) π := hfb.integrable_mul hg2
  -- 2. `|∫ f (g−1)| ≤ ∫ |f| |g−1|`.
  have habs : |∫ x, f x * (g x - 1) ∂π| ≤ ∫ x, |f x| * |g x - 1| ∂π := by
    refine le_trans abs_integral_le_integral_abs ?_
    refine (integral_congr_ae ?_).symm.le
    filter_upwards [] with x
    rw [abs_mul]
  -- 3. Holder(2,2) on `|f|, |g−1|`.
  have hfa : MemLp (fun x => |f x|) 2 π :=
    memLp_top_of_bound hf C (hC.mono fun x hx => by rwa [Real.norm_eq_abs])
  have hga : MemLp (fun x => |g x - 1|) 2 π := hg2.abs
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    (Real.HolderConjugate.two_two)
    (ae_of_all _ fun x => abs_nonneg _) (ae_of_all _ fun x => abs_nonneg _) hfa hga
  rw [Real.toReal_ofNat] at hcs
  -- rewrite the L² norms of `|f|, |g−1|` into plain squares.
  have hfsq : (fun x => |f x| ^ 2) = (fun x => (f x) ^ 2) := by
    funext x; rw [sq_abs]
  have hgsq : (fun x => |g x - 1| ^ 2) = (fun x => (g x - 1) ^ 2) := by
    funext x; rw [sq_abs]
  rw [hfsq, hgsq] at hcs
  refine le_trans habs (le_trans hcs ?_)
  -- 4. bound `∫ f² ≤ C² · π univ`, then take square roots.
  have hsq : ∀ᵐ x ∂π, (f x) ^ 2 ≤ C ^ 2 := hC.mono fun x hx => by
    rw [← sq_abs, ← sq_abs C]
    exact pow_le_pow_of_le_left (abs_nonneg _) hx 2
  have hbind : ∫ x, (f x) ^ 2 ∂π ≤ C ^ 2 * (π univ).toReal := by
    refine le_trans (integral_mono_ae hsq (ae_of_all _ fun _ => by positivity)) ?_
    rw [integral_const, Measure.restrict_univ, smul_eq_mul, mul_comm]
  calc (∫ x, (f x) ^ 2 ∂π) ^ (1 / 2) * (∫ x, (g x - 1) ^ 2 ∂π) ^ (1 / 2)
      ≤ (C ^ 2 * (π univ).toReal) ^ (1 / 2) * (∫ x, (g x - 1) ^ 2 ∂π) ^ (1 / 2) := by
        refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hbind (by norm_num)) ?_
        exact Real.rpow_nonneg (integral_nonneg fun x => sq_nonneg _) _
    _ = C * (π univ).toReal ^ (1 / 2) * (∫ x, (g x - 1) ^ 2 ∂π) ^ (1 / 2) := by
        rw [Real.mul_rpow (by positivity) (Real.toReal_nonneg _), Real.rpow_two,
          Real.sqrt_sq hC0]

end
