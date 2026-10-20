/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 483b1965-77dd-4750-8055-ad9f14b2c9dc
* original name       : `RamanujanPetersson.L_functional_equation`
* title               : Analytic continuation and functional equation of $L(s,\tau)$
* statement author    : Lucas
* solution author     : fizzyinc3 (submission 760c5996-1d29-4aeb-84bb-b0bb4bc7b1bb,
                        accepted 2026-10-17T18:00:41.272841+00:00)
* source              : Wikipedia, "Ramanujan–Petersson conjecture", https://en.wikipedia.org/w/index.php?title=Ramanujan%E2%80%93Petersson_conjecture&oldid=1369029052 (PDF snapshot supplied by the proposer, 9 pp.), section "Ramanujan L-function", "the Ramanujan L-function can be defined by analytic continuation of this series … satisfies a functional equation" (displayed $\Gamma(s)L(s,\tau)/(2\pi)^s=\Gamma(12-s)L(12-s,\tau)/(2\pi)^{12-s}$)
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/analytic-nt/RamanujanPetersson.L_functional_equation.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/RamanujanPetersson_L_functional_equation.diff`.
-/
import Definitions.Def_RamanujanPetersson_tau
import Mathlib

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups Complex MeasureTheory
open scoped Real

namespace RPL2

local notation "𝕢" => Function.Periodic.qParam

noncomputable abbrev D : CuspForm 𝒮ℒ 12 := CuspForm.discriminant

noncomputable def g {t : ℝ} (ht : 0 < t) (u : ℝ) : ℂ := D ⟨u + t * Complex.I, by simpa using ht⟩

lemma g_cont {t : ℝ} (ht : 0 < t) : Continuous (g ht) := by
  unfold g
  fun_prop

lemma coeff_eq (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (qExpansion 1 ModularForm.discriminant).coeff n =
      ∫ u in (0:ℝ)..1, 1 / 𝕢 1 (u + t * Complex.I) ^ n * g ht u := by
  have := ModularFormClass.qExpansion_coeff_eq_intervalIntegral (Γ := 𝒮ℒ) (k := 12) (f := D)
    one_pos one_mem_strictPeriods_SL n ht
  rw [show (⇑D : ℍ → ℂ) = ModularForm.discriminant from rfl] at this
  rw [this]
  simp only [g, one_div, inv_one, one_mul, Complex.ofReal_one]
  rfl

lemma kernel (n : ℕ) (t u : ℝ) :
    1 / 𝕢 1 (u + t * Complex.I) ^ n = Real.exp (2 * π * n * t) *
      fourier (-(n : ℤ)) (u : AddCircle ((1:ℝ) - 0)) := by
  rw [fourier_coe_apply, Function.Periodic.qParam, ← Complex.exp_nat_mul, one_div, ← Complex.exp_neg,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

lemma coeff_fourier (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (qExpansion 1 ModularForm.discriminant).coeff n =
      Real.exp (2 * π * n * t) * fourierCoeffOn zero_lt_one (g ht) n := by
  rw [coeff_eq n ht, fourierCoeffOn_eq_integral]
  simp_rw [kernel n t]
  simp only [sub_zero, ne_eq, one_ne_zero, not_false_eq_true, div_self, one_smul, smul_eq_mul]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext u
  ring


lemma exists_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ {t : ℝ} (ht : 0 < t) (u : ℝ), ‖g ht u‖ ≤ C / t ^ 6 := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound (Γ := 𝒮ℒ) D
  refine ⟨max C 0, le_max_right _ _, fun {t} ht u => ?_⟩
  have h := hC ⟨u + t * Complex.I, by simpa using ht⟩
  have him : (⟨u + t * Complex.I, by simpa using ht⟩ : ℍ).im = t := by simp [UpperHalfPlane.im]
  rw [him, show ((12 : ℤ) : ℝ) / 2 = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
  exact h.trans (by gcongr; exact le_max_left _ _)

lemma l2_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ {t : ℝ}, 0 < t → ∀ N : ℕ,
    ∑ m ∈ Finset.range (N + 1),
      ‖(qExpansion 1 ModularForm.discriminant).coeff m‖ ^ 2 * Real.exp (-(4 * π * m * t))
      ≤ C ^ 2 / t ^ 12 := by
  obtain ⟨C, hC0, hC⟩ := exists_bound
  refine ⟨C, hC0, fun {t} ht N => ?_⟩
  have hmem : MemLp (g ht) 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    MemLp.of_bound (g_cont ht).aestronglyMeasurable (C / t ^ 6) (ae_of_all _ (hC ht))
  have hs := hasSum_sq_fourierCoeffOn zero_lt_one hmem
  have hint : ∫ x in (0:ℝ)..1, ‖g ht x‖ ^ 2 ≤ (C / t ^ 6) ^ 2 := by
    have := intervalIntegral.integral_mono_on (a := 0) (b := 1) zero_le_one
      (f := fun x => ‖g ht x‖ ^ 2) (g := fun _ => (C / t ^ 6) ^ 2)
      (((g_cont ht).norm.pow 2).intervalIntegrable (μ := volume) 0 1)
      (continuous_const.intervalIntegrable (μ := volume) 0 1)
      (fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hC ht x) 2)
    simpa using this
  have hle := sum_le_hasSum ((Finset.range (N + 1)).map Nat.castEmbedding)
    (fun i _ => sq_nonneg _) hs
  rw [Finset.sum_map] at hle
  calc _ = ∑ m ∈ Finset.range (N + 1), ‖fourierCoeffOn zero_lt_one (g ht) (Nat.castEmbedding m)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [coeff_fourier m ht, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
          ← Real.exp_nat_mul]
        rw [mul_comm, ← mul_assoc, ← Real.exp_add]
        simp only [Nat.castEmbedding_apply]
        have : -(4 * π * m * t) + ((2:ℕ):ℝ) * (2 * π * m * t) = 0 := by push_cast; ring
        rw [this, Real.exp_zero, one_mul]
    _ ≤ _ := hle
    _ ≤ (C / t ^ 6) ^ 2 := by simpa using hint
    _ = C ^ 2 / t ^ 12 := by rw [div_pow, ← pow_mul]


lemma sq_sum_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
    ∑ m ∈ Finset.range (N + 1), ‖(qExpansion 1 ModularForm.discriminant).coeff m‖ ^ 2
      ≤ K * (N : ℝ) ^ 12 := by
  obtain ⟨C, hC0, hC⟩ := l2_bound
  refine ⟨Real.exp (4 * π) * C ^ 2, by positivity, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : (0 : ℝ) < 1 / N := by positivity
  have h := hC ht N
  have key : ∀ m ∈ Finset.range (N + 1),
      ‖(qExpansion 1 ModularForm.discriminant).coeff m‖ ^ 2 ≤ Real.exp (4 * π) *
        (‖(qExpansion 1 ModularForm.discriminant).coeff m‖ ^ 2 *
          Real.exp (-(4 * π * m * (1 / N)))) := by
    intro m hm
    have hmN : (m : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [mul_left_comm, ← Real.exp_add]
    refine le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_exp ?_)
    have : (m : ℝ) * (1 / N) ≤ 1 := by rw [mul_one_div]; exact (div_le_one hNpos).mpr hmN
    nlinarith [Real.pi_pos]
  calc _ ≤ ∑ m ∈ Finset.range (N + 1), Real.exp (4 * π) *
        (‖(qExpansion 1 ModularForm.discriminant).coeff m‖ ^ 2 *
          Real.exp (-(4 * π * m * (1 / N)))) := Finset.sum_le_sum key
    _ = Real.exp (4 * π) * ∑ m ∈ Finset.range (N + 1),
        (‖(qExpansion 1 ModularForm.discriminant).coeff m‖ ^ 2 *
          Real.exp (-(4 * π * m * (1 / N)))) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (4 * π) * (C ^ 2 / (1 / N) ^ 12) := by gcongr
    _ = _ := by field_simp

lemma abs_sum_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
    ∑ k ∈ Finset.Icc 1 N, ‖(qExpansion 1 ModularForm.discriminant).coeff k‖
      ≤ K * (N : ℝ) ^ ((13 : ℝ) / 2) := by
  obtain ⟨K, hK0, hK⟩ := sq_sum_bound
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set a := fun k : ℕ => ‖(qExpansion 1 ModularForm.discriminant).coeff k‖
  have hsub : Finset.Icc 1 N ⊆ Finset.range (N + 1) := by
    intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 N) (fun _ => (1 : ℝ)) a
  simp only [one_mul, one_pow, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one,
    add_tsub_cancel_right] at hcs
  have h2 : ∑ k ∈ Finset.Icc 1 N, a k ^ 2 ≤ K * (N : ℝ) ^ 12 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans (hK N hN)
  have hS0 : 0 ≤ ∑ k ∈ Finset.Icc 1 N, a k := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hR0 : 0 ≤ Real.sqrt K * (N : ℝ) ^ ((13 : ℝ) / 2) := by positivity
  refine (pow_le_pow_iff_left₀ hS0 hR0 two_ne_zero).mp ?_
  calc _ ≤ (N : ℝ) * ∑ k ∈ Finset.Icc 1 N, a k ^ 2 := hcs
    _ ≤ N * (K * (N : ℝ) ^ 12) := by gcongr
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt hK0, ← Real.rpow_natCast ((N : ℝ) ^ ((13 : ℝ) / 2)) 2,
        ← Real.rpow_mul hNpos.le]
      norm_num
      ring

end RPL2

namespace RPL2

lemma tau_sum_isBigO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖RamanujanPetersson.tau k‖) =O[Filter.atTop]
    fun n : ℕ => (n : ℝ) ^ ((13 : ℝ) / 2) := by
  obtain ⟨K, hK0, hK⟩ := abs_sum_bound
  refine Asymptotics.IsBigO.of_bound K ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h0 : 0 ≤ ∑ k ∈ Finset.Icc 1 n, ‖RamanujanPetersson.tau k‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (by positivity)]
  exact hK n hn

lemma Lsumm (s : ℂ) (hs : 13 / 2 < s.re) : LSeriesSummable RamanujanPetersson.tau s :=
  LSeriesSummable_of_sum_norm_bigO tau_sum_isBigO (by norm_num) (by exact_mod_cast hs)

end RPL2

open UpperHalfPlane hiding I
open ModularForm ModularFormClass MatrixGroups Complex Filter
open scoped Real

/- conversion: the original `RPFE` section relied on the platform Mathlib's `ModularForm.L`,
`ModularForm.Λ`, `weakFEPair`, `CuspForm.isStrongFEPair`, `CuspForm.hasSum_L` and
`CuspForm.differentiable_L`, none of which exist in the pinned Mathlib.  It is replaced by a
self-contained construction with the same interface (`LL`, `LL_diff`, `LL_eq_seven`, `gamma_L`,
`Λ_fe`): the strong FE pair `f = g = (t ↦ Δ(i t))` of weight `12`, its completed Mellin transform
`Lam`, and `LL s = (2π)^s Γ(s)⁻¹ Lam s`.  The solution theorem below is unchanged. -/
namespace RPFE

open Asymptotics


noncomputable def F (t : ℝ) : ℂ := ModularForm.discriminant (ofComplex (Complex.I * t))

lemma mem_upper {t : ℝ} (ht : 0 < t) : 0 < (Complex.I * (t : ℂ)).im := by simpa using ht

lemma F_apply {t : ℝ} (ht : 0 < t) :
    F t = ModularForm.discriminant ⟨Complex.I * t, mem_upper ht⟩ := by
  rw [F, ofComplex_apply_of_im_pos (mem_upper ht)]

lemma tau_zero : RamanujanPetersson.tau 0 = 0 := by
  unfold RamanujanPetersson.tau
  rw [← CuspForm.coe_discriminant, ModularFormClass.qExpansion_coeff_zero _ one_pos
    one_mem_strictPeriods_SL]
  exact UpperHalfPlane.IsZeroAtImInfty.valueAtInfty_eq_zero
    Prove2me.Shim.Discriminant.discriminantMF_isZeroAtImInfty

lemma F_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => RamanujanPetersson.tau n * ↑(Real.exp (-(2 * π * n) * t))) (F t) := by
  rw [F_apply ht]
  have h := ModularFormClass.hasSum_qExpansion (Γ := 𝒮ℒ) (k := 12) CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL ⟨Complex.I * t, mem_upper ht⟩
  rw [CuspForm.coe_discriminant] at h
  convert h using 1
  funext n
  rw [smul_eq_mul, RamanujanPetersson.tau]
  congr 1
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul, Complex.ofReal_exp]
  congr 1
  change _ = (n : ℂ) * (2 * π * Complex.I * (Complex.I * t) / ((1 : ℝ) : ℂ))
  push_cast
  ring_nf
  rw [I_sq]; ring

lemma disc_S (z : ℍ) :
    ModularForm.discriminant (.mk _ z.im_inv_neg_coe_pos) = (z : ℂ) ^ 12 * ModularForm.discriminant z := by
  have h := congrFun (ModularForm.discriminant_slash_SL2Z ModularGroup.S) z
  rw [SlashInvariantForm.slash_S_apply] at h
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  rw [← h, mul_comm, mul_assoc, ← zpow_natCast, ← zpow_add₀ hz]
  simp

lemma F_feq (x : ℝ) (hx : x ∈ Set.Ioi 0) :
    F (1 / x) = ((1 : ℂ) * ↑(x ^ (12 : ℝ))) • F x := by
  have hx' : (0 : ℝ) < x := hx
  rw [F_apply (by positivity), F_apply hx', smul_eq_mul, one_mul]
  have : (⟨Complex.I * ((1 / x : ℝ) : ℂ), mem_upper (by positivity)⟩ : ℍ) =
      .mk _ (⟨Complex.I * x, mem_upper hx'⟩ : ℍ).im_inv_neg_coe_pos := by
    ext
    change Complex.I * ((1 / x : ℝ) : ℂ) = (-(Complex.I * (x : ℂ)))⁻¹
    have : (x : ℂ) ≠ 0 := by exact_mod_cast hx'.ne'
    push_cast
    field_simp
    rw [I_sq]
  rw [this, disc_S]
  congr 1
  change (Complex.I * (x : ℂ)) ^ 12 = _
  rw [mul_pow, show (12 : ℕ) = 2 * 6 from rfl, pow_mul, I_sq]
  rw [show ((x : ℝ) ^ (12 : ℝ)) = x ^ (12 : ℕ) by norm_cast]
  push_cast; ring

lemma F_contOn : ContinuousOn F (Set.Ioi 0) := by
  have hd := (UpperHalfPlane.mdifferentiable_iff.mp
    (ModularFormClass.holo CuspForm.discriminant)).continuousOn
  intro t ht
  have ht' : (0 : ℝ) < t := ht
  have h1 : ContinuousAt (⇑CuspForm.discriminant ∘ ofComplex) (Complex.I * t) :=
    hd.continuousAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (mem_upper ht'))
  have h2 : ContinuousAt (fun s : ℝ => Complex.I * (s : ℂ)) t := by fun_prop
  exact (ContinuousAt.comp (f := fun s : ℝ => Complex.I * (s : ℂ)) (x := t) h1 h2).continuousWithinAt

lemma F_top (r : ℝ) : (fun x => F x - 0) =O[atTop] fun x => x ^ r := by
  have h := CuspFormClass.exp_decay_atImInfty (Γ := 𝒮ℒ) (k := 12) CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL
  have ht : Tendsto (fun t : ℝ => ofComplex (Complex.I * t)) atTop atImInfty := by
    rw [UpperHalfPlane.atImInfty, tendsto_comap_iff]
    refine tendsto_id.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [Function.comp, ofComplex_apply_of_im_pos (mem_upper ht)]
  have h2 := h.comp_tendsto ht
  simp only [sub_zero]
  refine (h2.congr' (Eventually.of_forall fun t => rfl) ?_).trans
    (isLittleO_exp_neg_mul_rpow_atTop (a := 2 * π) (by positivity) r).isBigO
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [Function.comp, ofComplex_apply_of_im_pos (mem_upper ht)]


noncomputable def P : StrongFEPair ℂ where
  f := F
  g := F
  k := 12
  ε := 1
  f₀ := 0
  g₀ := 0
  hf_int := F_contOn.locallyIntegrableOn measurableSet_Ioi
  hg_int := F_contOn.locallyIntegrableOn measurableSet_Ioi
  hk := by norm_num
  hε := one_ne_zero
  h_feq := F_feq
  hf_top := F_top
  hg_top := F_top
  hf₀ := rfl
  hg₀ := rfl

noncomputable def Lam (s : ℂ) : ℂ := P.Λ s

lemma Λ_fe (s : ℂ) : Lam (12 - s) = Lam s := by
  have h := P.functional_equation s
  simpa [Lam, P] using h

noncomputable def LL (s : ℂ) : ℂ := (2 * (π : ℂ)) ^ s * (1 / Complex.Gamma s) * Lam s

lemma LL_diff : Differentiable ℂ LL := by
  have h2 : Differentiable ℂ fun s : ℂ => (2 * (π : ℂ)) ^ s := by
    intro s
    refine (differentiableAt_id.const_cpow ?_)
    left; exact mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hL : Differentiable ℂ Lam := P.differentiable_Λ
  convert (h2.mul Complex.differentiable_one_div_Gamma).mul hL using 1
  funext s
  simp [LL]

lemma gamma_L (s : ℂ) (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) :
    Complex.Gamma s * LL s / (2 * (π : ℂ)) ^ s = Lam s := by
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have hp : (2 * (π : ℂ)) ^ s ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]; left; exact mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  rw [LL]
  field_simp

lemma mellin_F (s : ℂ) (hs : 7 < s.re) :
    HasSum (fun n : ℕ => Complex.Gamma s * RamanujanPetersson.tau n / ((2 * π * n : ℝ) : ℂ) ^ s)
      (Lam s) := by
  have hΛ : Lam s = mellin F s := by
    rw [Lam, StrongFEPair.Λ_eq]; rfl
  rw [hΛ]
  refine hasSum_mellin (p := fun n : ℕ => 2 * π * n) ?_ (by linarith) (fun t ht => F_hasSum ht) ?_
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · left; exact tau_zero
    · right; positivity
  · have hsum := RPL2.Lsumm (s.re : ℂ) (by simp; linarith)
    rw [LSeriesSummable] at hsum
    have := (hsum.norm.mul_left ((2 * π) ^ (-s.re)))
    refine this.congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [tau_zero]
    · rw [LSeries.norm_term_eq]
      simp only [hn.ne', if_false, Complex.ofReal_re]
      rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 2 * π) (Nat.cast_nonneg n),
        Real.rpow_neg (by positivity : (0:ℝ) ≤ 2 * π)]
      field_simp

lemma LL_eq_seven (s : ℂ) (hs : 7 < s.re) :
    LL s = LSeries RamanujanPetersson.tau s := by
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hp : (2 * (π : ℂ)) ^ s ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]; left; exact mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  rw [LL, (mellin_F s hs).tsum_eq.symm, LSeries, ← tsum_mul_left]
  congr 1
  funext n
  rw [LSeries.term_def]
  split_ifs with hn
  · subst hn; simp [tau_zero]
  · rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
    push_cast
    field_simp

end RPFE

open UpperHalfPlane Filter Asymptotics MatrixGroups
open scoped Real

open RamanujanPetersson in
theorem _root_.Prove2me.Solution.RamanujanPetersson_L_functional_equation :
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      (∀ s : ℂ, 13 / 2 < s.re → L s = LSeries tau s) ∧
      ∀ s : ℂ, (∀ n : ℕ, s ≠ -(n : ℂ)) → (∀ n : ℕ, 12 - s ≠ -(n : ℂ)) →
        Complex.Gamma s * L s / (2 * (π : ℂ)) ^ s =
          Complex.Gamma (12 - s) * L (12 - s) / (2 * (π : ℂ)) ^ (12 - s) := by
  refine ⟨RPFE.LL, RPFE.LL_diff, ?_, ?_⟩
  · have habs : LSeries.abscissaOfAbsConv tau ≤ ((13 / 2 : ℝ) : EReal) :=
      LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
        RPL2.Lsumm y (by simpa using hy)
    have hU : AnalyticOnNhd ℂ (LSeries tau) {s : ℂ | 13 / 2 < s.re} :=
      (LSeries_analyticOnNhd tau).mono fun s hs =>
        lt_of_le_of_lt habs (by exact_mod_cast (show (13 / 2 : ℝ) < s.re from hs))
    have hL : AnalyticOnNhd ℂ RPFE.LL {s : ℂ | 13 / 2 < s.re} :=
      fun s _ => RPFE.LL_diff.analyticAt s
    have heq := hL.eqOn_of_preconnected_of_eventuallyEq hU
      (convex_halfSpace_re_gt (13 / 2 : ℝ)).isPreconnected (z₀ := 8)
      (by show (13 / 2 : ℝ) < (8 : ℂ).re; norm_num) ?_
    · exact fun s hs => heq hs
    · filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (7 : ℝ) < (8 : ℂ).re by norm_num)] with s hs
      exact RPFE.LL_eq_seven s hs
  · intro s h1 h2
    rw [RPFE.gamma_L s h1, RPFE.gamma_L _ h2, RPFE.Λ_fe]

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open UpperHalfPlane Filter Asymptotics MatrixGroups
open scoped Real

namespace RamanujanPetersson

theorem L_functional_equation :
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      (∀ s : ℂ, 13 / 2 < s.re → L s = LSeries tau s) ∧
      ∀ s : ℂ, (∀ n : ℕ, s ≠ -(n : ℂ)) → (∀ n : ℕ, 12 - s ≠ -(n : ℂ)) →
        Complex.Gamma s * L s / (2 * (π : ℂ)) ^ s =
          Complex.Gamma (12 - s) * L (12 - s) / (2 * (π : ℂ)) ^ (12 - s) := by
  first
  | exact _root_.Prove2me.Solution.RamanujanPetersson_L_functional_equation
  | (apply _root_.Prove2me.Solution.RamanujanPetersson_L_functional_equation <;> assumption)

end RamanujanPetersson


end Prove2meStatement
