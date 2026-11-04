import Mathlib

noncomputable section

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-! ## Step A (v8): density-change identity + the sharp TV bound, correct API. -/

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
  rw [smul_eq_mul, ENNReal.toReal_ofReal hx, mul_comm]

/-- **The sharp `L^∞`–Cauchy–Schwarz bound.**  With `ν = g • π` (`g ≥ 0`, `π` finite),
for any `f` with `|f| ≤ C` π-a.e. (`C ≥ 0`) and `MemLp (g−1) 2 π`:

    |∫ f dν − ∫ f dπ| ≤ C * √(π univ) * ‖g − 1‖_{L²(π)}.

The constant `1` (sharper than `pcnl.md`'s `½`) is what the `‖f‖_∞ ≤ 1` normalisation of the
total-variation sup yields; `½` is the `L¹`–`L^∞` convention. -/
theorem abs_integral_sub_integral_le_of_withDensity {π ν : Measure α} {g : α → ℝ}
    (hg : Measurable g) (hg0 : 0 ≤ᵐ[π] g) (hfin : IsFiniteMeasure π)
    (hν : ν = π.withDensity fun x => ENNReal.ofReal (g x))
    (f : α → ℝ) (hf : AEStronglyMeasurable f π) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ x ∂π, |f x| ≤ C)
    (hg2 : MemLp (fun x => g x - 1) (2 : ENNReal) π) :
    |∫ x, f x ∂ν - ∫ x, f x ∂π|
      ≤ C * (π Set.univ).toReal ^ ((1:ℝ) / 2) * (∫ x, (g x - 1) ^ 2 ∂π) ^ ((1:ℝ) / 2) := by
  have hgi : Integrable (fun x => g x - 1) π := hg2.integrable one_le_two
  have hfbound : MemLp f ⊤ π :=
    memLp_top_of_bound hf C (hC.mono fun x hx => by rwa [Real.norm_eq_abs])
  have hfb : MemLp f (2 : ENNReal) π := hfbound.mono_exponent (by norm_num)
  have hfi : Integrable f π := hfb.integrable one_le_two
  -- 1. the deviation is `∫ f (g − 1) dπ`.
  have hdev : ∫ x, f x ∂ν - ∫ x, f x ∂π = ∫ x, f x * (g x - 1) ∂π := by
    have hpoint : ∀ x, f x * (g x - 1) = f x * g x - f x := by
      intro x; rw [mul_sub, mul_one]
    have hmul0 : Integrable (fun x => f x * (g x - 1)) π := hfb.integrable_mul hg2
    have hfg : Integrable (fun x => f x * g x) π := by
      have heq : (fun x => f x * g x) = (fun x => f x * (g x - 1) + f x) := by
        funext x; linarith [hpoint x]
      rw [heq]; exact hmul0.add hfi
    rw [hν, integral_withDensity_ofReal_eq hg hg0 f, integral_congr_ae (ae_of_all _ hpoint),
      integral_sub hfg hfi]
  rw [hdev]
  have hmul : Integrable (fun x => f x * (g x - 1)) π := hfb.integrable_mul hg2
  -- 2. `|∫ f (g−1)| ≤ ∫ |f| |g−1|`.
  have habs : |∫ x, f x * (g x - 1) ∂π| ≤ ∫ x, |f x| * |g x - 1| ∂π := by
    refine le_trans abs_integral_le_integral_abs ?_
    refine (integral_congr_ae ?_).symm.le
    filter_upwards [] with x
    rw [abs_mul]
  -- 3. Holder(2,2) on `|f|, |g−1|`.
  have hfa : MemLp (fun x => |f x|) (ENNReal.ofReal 2) π :=
    hfb.abs.mono_exponent (by norm_num)
  have hga : MemLp (fun x => |g x - 1|) (ENNReal.ofReal 2) π :=
    hg2.abs.mono_exponent (by norm_num)
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ fun x => abs_nonneg _) (ae_of_all _ fun x => abs_nonneg _) hfa hga
  -- rewrite the L² norms of `|f|, |g−1|` into plain squares.
  have hfsq : (fun x => |f x| ^ 2) = (fun x => (f x) ^ 2) := by
    funext x; rw [sq_abs]
  have hgsq : (fun x => |g x - 1| ^ 2) = (fun x => (g x - 1) ^ 2) := by
    funext x; rw [sq_abs]
  -- rewrite the Hölder RHS's `|·| ^ (2:ℝ)` to `· ^ 2` (`ℕ` literal) via `hfsq`/`hgsq`.
  have hcsR : (∫ a, |f a| ^ 2 ∂π) ^ ((1:ℝ) / 2) * (∫ a, |g a - 1| ^ 2 ∂π) ^ ((1:ℝ) / 2)
      ≤ (∫ a, (f a) ^ 2 ∂π) ^ ((1:ℝ) / 2) * (∫ a, (g a - 1) ^ 2 ∂π) ^ ((1:ℝ) / 2) := by
    rw [integral_congr_ae (ae_of_all _ fun a => congrFun hfsq a),
        integral_congr_ae (ae_of_all _ fun a => congrFun hgsq a)]
  have hcs' : ∫ a, |f a| * |g a - 1| ∂π
      ≤ (∫ a, (f a) ^ 2 ∂π) ^ ((1:ℝ) / 2) * (∫ a, (g a - 1) ^ 2 ∂π) ^ ((1:ℝ) / 2) := by
    simp only [Real.rpow_two] at hcs hcsR
    exact le_trans hcs hcsR
  refine le_trans habs (le_trans hcs' ?_)
  -- 4. bound `∫ f² ≤ C² · π univ`, then take square roots.
  have hsq : ∀ᵐ x ∂π, (f x) ^ 2 ≤ C ^ 2 := hC.mono fun x hx => by
    exact sq_le_sq.mpr (le_trans hx (le_abs_self C))
  have hcsq2 : Integrable (fun x => (f x) ^ 2) π := by
    have habsf : Integrable (fun x => |f x| ^ 2) π := hfb.integrable_norm_pow'
    have heq : (fun x => (f x) ^ 2) = fun x => |f x| ^ 2 := by
      funext x; rw [sq_abs]
    rwa [heq]
  have hconst2 : Integrable (fun x => C ^ 2) π := integrable_const _
  have hbind : ∫ x, (f x) ^ 2 ∂π ≤ C ^ 2 * (π Set.univ).toReal := by
    refine le_trans (integral_mono_ae hcsq2 hconst2 hsq) ?_
    rw [integral_const, smul_eq_mul, Measure.real_def]
    exact le_of_eq (mul_comm _ _)
  -- `C²` under the square root recovers `C` (for `C ≥ 0`).
  have hroot : (C ^ 2 : ℝ) ^ ((1:ℝ) / 2) = C := by
    rw [← Real.rpow_two, ← Real.rpow_mul hC0]
    simp
  have hsqle : (∫ x, (f x) ^ 2 ∂π) ^ ((1:ℝ) / 2)
      ≤ C * (π Set.univ).toReal ^ ((1:ℝ) / 2) := by
    refine le_trans (Real.rpow_le_rpow (by positivity) hbind (by norm_num)) ?_
    rw [Real.mul_rpow (by positivity) ENNReal.toReal_nonneg, hroot]
  have hnn : 0 ≤ (∫ x, (g x - 1) ^ 2 ∂π) := integral_nonneg fun x => by positivity
  exact mul_le_mul_of_nonneg_right hsqle (Real.rpow_nonneg hnn _)

end
