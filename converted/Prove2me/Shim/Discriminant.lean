/-
Conversion shim: the modular discriminant `Δ`, which the platform Mathlib provides as
`ModularForm.discriminant : ℍ → ℂ` and `CuspForm.discriminant : CuspForm 𝒮ℒ 12` (with
`⇑CuspForm.discriminant = ModularForm.discriminant` definitionally), and which the pinned Mathlib
lacks.

Here `Δ` is built from the normalised level-one Eisenstein series of the pinned Mathlib,
`E₄ = 1 + 240 ∑ σ₃(n) qⁿ` and `E₆ = 1 - 504 ∑ σ₅(n) qⁿ`, as the classical
`Δ = (E₄³ - E₆²) / 1728 = q - 24 q² + ⋯`.  This is the same function as `η²⁴` (Jacobi's product
formula), which is how the platform documents it; that identity is not needed by the converted
solutions and is not proved here.  Everything in this file is proved (no `sorry`).
-/
import Mathlib

open UpperHalfPlane hiding I
open ModularForm ModularFormClass MatrixGroups Complex Filter Topology
open scoped Real CongruenceSubgroup ArithmeticFunction.sigma

namespace Prove2me.Shim.Discriminant

local notation "𝕢" => Function.Periodic.qParam

/-- A level-one modular form tends to its value at `i∞`. -/
lemma tendsto_valueAtInfty {k : ℤ} (f : ModularForm Γ(1) k) :
    Tendsto f atImInfty (𝓝 (valueAtInfty f)) := by
  have h := exp_decay_sub_atImInfty f one_pos one_mem_strictPeriods_SL2Z
  have h0 : Tendsto (fun τ : ℍ ↦ Real.exp (-2 * π * τ.im / 1)) atImInfty (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    simp only [div_one]
    exact tendsto_comap.const_mul_atTop_of_neg (by linarith [Real.pi_pos])
  simpa using (h.trans_tendsto h0).add_const (valueAtInfty f)

lemma sigma_le_pow (k n : ℕ) : σ k n ≤ n ^ (k + 1) := by
  rw [ArithmeticFunction.sigma_apply, pow_succ, mul_comm]
  calc ∑ d ∈ n.divisors, d ^ k ≤ ∑ d ∈ n.divisors, n ^ k :=
        Finset.sum_le_sum fun d hd => Nat.pow_le_pow_left (Nat.divisor_le hd) k
    _ = n.divisors.card * n ^ k := by simp
    _ ≤ n * n ^ k := Nat.mul_le_mul_right _ (Nat.card_divisors_le_self n)

lemma summable_sigma_mul {k : ℕ} (z : ℍ) :
    Summable fun n : ℕ ↦ (σ k n : ℂ) * cexp (2 * π * I * z) ^ n := by
  refine Summable.of_norm_bounded ((summable_pow_mul_cexp (k + 1) 1 z).norm) fun n => ?_
  rw [norm_mul, norm_mul]
  gcongr
  · simp only [Complex.norm_natCast, norm_pow]
    exact_mod_cast sigma_le_pow k n
  · simp

/-- The `q`-expansion of `E k` as a `HasSum` statement. -/
lemma E_hasSum {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (if m = 0 then (1 : ℂ) else -(2 * k / bernoulli k) * σ (k - 1) m) •
      𝕢 1 τ ^ m) (E hk τ) := by
  rw [EisensteinSeries.q_expansion_bernoulli hk hk2 τ]
  have hq : 𝕢 1 τ = cexp (2 * π * I * τ) := by
    simp [Function.Periodic.qParam]
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, if_pos, pow_zero, smul_eq_mul, mul_one,
    Nat.add_one_ne_zero, if_false, hq]
  have : ∑' n : ℕ+, (σ (k - 1) n : ℂ) * cexp (2 * π * I * τ) ^ ((n : ℕ) : ℤ) =
      ∑' n : ℕ, (σ (k - 1) (n + 1) : ℂ) * cexp (2 * π * I * τ) ^ (n + 1) := by
    simp only [zpow_natCast]
    exact tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (σ (k - 1) n : ℂ) * cexp (2 * π * I * τ) ^ n)
  rw [this]
  have hs' := ((summable_nat_add_iff 1).mpr (summable_sigma_mul (k := k - 1) τ)).hasSum.mul_left
    (-(2 * k / bernoulli k : ℂ))
  convert hs' using 1
  · ext n; ring
  · ring

/-- The normalised Eisenstein series take the value `1` at `i∞`. -/
lemma E_valueAtInfty {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) : valueAtInfty (E hk) = 1 := by
  have := qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL2Z (E_hasSum hk hk2) 0
  rw [qExpansion_coeff_zero (E hk) one_pos one_mem_strictPeriods_SL2Z] at this
  simpa using this.symm

/-- The normalised Eisenstein series of weight 4, `1 + 240 ∑ σ₃(n) qⁿ`. -/
noncomputable def E4 : ModularForm Γ(1) 4 := E (k := 4) (by norm_num)

/-- The normalised Eisenstein series of weight 6, `1 - 504 ∑ σ₅(n) qⁿ`. -/
noncomputable def E6 : ModularForm Γ(1) 6 := E (k := 6) (by norm_num)

/-- `Δ = (E₄³ - E₆²) / 1728` as a level-one modular form of weight 12. -/
noncomputable def discriminantMF : ModularForm Γ(1) 12 :=
  (1 / 1728 : ℂ) • (mcast (by norm_num) ((E4.mul E4).mul E4) - mcast (by norm_num) (E6.mul E6))

lemma discriminantMF_apply (z : ℍ) : discriminantMF z = (E4 z ^ 3 - E6 z ^ 2) / 1728 := by
  have h1 : (mcast (by norm_num : (4:ℤ) + 4 + 4 = 12) ((E4.mul E4).mul E4)) z = E4 z ^ 3 := by
    change ((E4.mul E4).mul E4) z = _
    simp only [ModularForm.coe_mul, Pi.mul_apply]; ring
  have h2 : (mcast (by norm_num : (6:ℤ) + 6 = 12) (E6.mul E6)) z = E6 z ^ 2 := by
    change (E6.mul E6) z = _
    simp only [ModularForm.coe_mul, Pi.mul_apply]; ring
  rw [discriminantMF, IsGLPos.smul_apply, ModularForm.sub_apply, h1, h2, smul_eq_mul]
  ring

lemma discriminantMF_isZeroAtImInfty : IsZeroAtImInfty discriminantMF := by
  have h4 := tendsto_valueAtInfty E4
  have h6 := tendsto_valueAtInfty E6
  rw [E4, E_valueAtInfty _ (by decide)] at h4
  rw [E6, E_valueAtInfty _ (by decide)] at h6
  have := ((h4.pow 3).sub (h6.pow 2)).div_const 1728
  norm_num at this
  change Tendsto _ _ _
  convert this using 1
  funext z
  rw [discriminantMF_apply, E4, E6]

lemma mem_Gamma_one (g : SL(2, ℤ)) : g ∈ Γ(1) := by simp [CongruenceSubgroup.Gamma_one_top]

end Prove2me.Shim.Discriminant

open Prove2me.Shim.Discriminant

/-- The modular discriminant `Δ = (E₄³ - E₆²) / 1728 = q - 24 q² + ⋯` (`= η²⁴`). -/
noncomputable def ModularForm.discriminant : ℍ → ℂ := discriminantMF

lemma ModularForm.discriminant_slash_SL2Z (γ : SL(2, ℤ)) :
    ModularForm.discriminant ∣[(12:ℤ)] γ = ModularForm.discriminant :=
  discriminantMF.slash_action_eq' _ ⟨γ, mem_Gamma_one γ, rfl⟩

/-- The modular discriminant as a cusp form of weight 12 and level one. -/
noncomputable def CuspForm.discriminant : CuspForm 𝒮ℒ 12 where
  toFun := ModularForm.discriminant
  slash_action_eq' γ hγ := by
    obtain ⟨g, rfl⟩ := hγ
    exact discriminantMF.slash_action_eq' _ ⟨g, mem_Gamma_one g, rfl⟩
  holo' := discriminantMF.holo'
  zero_at_cusps' hc := by
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [ModularForm.discriminant_slash_SL2Z]
    exact discriminantMF_isZeroAtImInfty

lemma CuspForm.coe_discriminant : ⇑CuspForm.discriminant = ModularForm.discriminant := rfl

/-- `1` is a strict period of the image of `SL(2, ℤ)` in `GL(2, ℝ)`. -/
lemma one_mem_strictPeriods_SL : (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.T]
