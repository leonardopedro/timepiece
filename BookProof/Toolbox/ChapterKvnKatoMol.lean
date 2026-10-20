import Mathlib
import BookProof.Toolbox.ChapterKvnKatoCalc

/-!
# Mollifiers and the Schur test for the Kato argument for `N = H_G² + E`

* the scaled mollifiers `ρ_s(z) = sᵈ ρ₀(s z)`, their smoothness, support, reality, the scaling
  of their derivatives, and the `L²` convergence of the mollifications `kint u (kz ρ_s) → u`;
* the **Schur test**: an integral operator whose kernel is dominated by a translation-invariant
  integrable weight is bounded on `L²`.
-/

namespace BookProof.KvnKato

open MeasureTheory Filter Topology
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegEnergy
open BookProof.ConvolutionCalc BookProof.DegKatoEsa BookProof.MollifierL2
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The Schur test -/

/-- **The Schur test.**  If `‖k x y‖ ≤ W (x − y)` with `∫ W ≤ A`, then the integral operator
with kernel `k` maps `L²` to `L²` with norm at most `A`. -/
theorem schur_L2 {k : Vd d → Vd d → ℂ} {W : Vd d → ℝ}
    (hWm : Measurable W) {A : ℝ≥0∞} (hAt : A ≠ ⊤) (hWA : ∫⁻ w, ENNReal.ofReal (W w) ≤ A)
    (hkW : ∀ x y, ‖k x y‖ ≤ W (x - y)) {f : Vd d → ℂ}
    (hf : MemLp f 2 (volume : Measure (Vd d))) :
    eLpNorm (fun x => ∫ y, f y * k x y) 2 volume ≤ A * eLpNorm f 2 volume := by
  set w : Vd d → Vd d → ℝ≥0∞ := fun x y => ENNReal.ofReal (W (x - y)) with hw
  have hwm : ∀ x, AEMeasurable (w x) (volume : Measure (Vd d)) := fun x =>
    (ENNReal.measurable_ofReal.comp (hWm.comp (measurable_const.sub measurable_id))).aemeasurable
  have hfm : AEMeasurable (fun y => ‖f y‖ₑ) (volume : Measure (Vd d)) := hf.1.enorm
  have hwint : ∀ x, ∫⁻ y, w x y = ∫⁻ y, ENNReal.ofReal (W y) := fun x =>
    lintegral_sub_left_eq_self (fun y => ENNReal.ofReal (W y)) x
  have hwint' : ∀ y, ∫⁻ x, w x y = ∫⁻ x, ENNReal.ofReal (W x) := fun y =>
    lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (W x)) y
  -- pointwise Cauchy–Schwarz
  have hpt : ∀ x, ‖∫ y, f y * k x y‖ₑ ^ (2:ℝ) ≤ A * ∫⁻ y, w x y * ‖f y‖ₑ ^ (2:ℝ) := by
    intro x
    have h1 : ‖∫ y, f y * k x y‖ₑ ≤ ∫⁻ y, w x y * ‖f y‖ₑ := by
      refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
      rw [enorm_mul, mul_comm]
      gcongr
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hkW x y)
    have hA : AEMeasurable (fun y => (w x y) ^ ((1:ℝ)/2)) (volume : Measure (Vd d)) :=
      (hwm x).pow_const _
    have hB : AEMeasurable (fun y => (w x y) ^ ((1:ℝ)/2) * ‖f y‖ₑ)
        (volume : Measure (Vd d)) := hA.mul hfm
    have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure (Vd d)) (p := 2) (q := 2)
      (by constructor <;> norm_num) hA hB
    have e1 : ∀ y, ((fun y => (w x y) ^ ((1:ℝ)/2)) * fun y => (w x y) ^ ((1:ℝ)/2) * ‖f y‖ₑ) y
        = w x y * ‖f y‖ₑ := by
      intro y
      simp only [Pi.mul_apply]
      rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num
    have e2 : ∀ y, ((w x y) ^ ((1:ℝ)/2)) ^ (2:ℝ) = w x y := by
      intro y; rw [← ENNReal.rpow_mul]; norm_num
    have e3 : ∀ y, ((w x y) ^ ((1:ℝ)/2) * ‖f y‖ₑ) ^ (2:ℝ) = w x y * ‖f y‖ₑ ^ (2:ℝ) := by
      intro y
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
      norm_num
    simp only [e1, e2, e3, hwint x] at hCS
    calc ‖∫ y, f y * k x y‖ₑ ^ (2:ℝ)
        ≤ ((∫⁻ y, ENNReal.ofReal (W y)) ^ ((1:ℝ)/2)
            * (∫⁻ y, w x y * ‖f y‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) ^ (2:ℝ) :=
          ENNReal.rpow_le_rpow (h1.trans hCS) (by norm_num)
      _ = (∫⁻ y, ENNReal.ofReal (W y)) * ∫⁻ y, w x y * ‖f y‖ₑ ^ (2:ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul]
          norm_num
      _ ≤ A * ∫⁻ y, w x y * ‖f y‖ₑ ^ (2:ℝ) := by gcongr
  have hmeas : AEMeasurable (Function.uncurry fun x y => w x y * ‖f y‖ₑ ^ (2:ℝ))
      ((volume : Measure (Vd d)).prod volume) := by
    have h1 : Measurable (Function.uncurry w) :=
      ENNReal.measurable_ofReal.comp (hWm.comp (measurable_fst.sub measurable_snd))
    exact h1.aemeasurable.mul (hfm.pow_const _).comp_snd
  have key : ∫⁻ x, ‖∫ y, f y * k x y‖ₑ ^ (2:ℝ)
      ≤ A ^ (2:ℝ) * ∫⁻ y, ‖f y‖ₑ ^ (2:ℝ) := by
    calc ∫⁻ x, ‖∫ y, f y * k x y‖ₑ ^ (2:ℝ)
        ≤ ∫⁻ x, A * ∫⁻ y, w x y * ‖f y‖ₑ ^ (2:ℝ) := lintegral_mono hpt
      _ = A * ∫⁻ x, ∫⁻ y, w x y * ‖f y‖ₑ ^ (2:ℝ) := by
          rw [lintegral_const_mul' _ _ hAt]
      _ = A * ∫⁻ y, ∫⁻ x, w x y * ‖f y‖ₑ ^ (2:ℝ) := by rw [lintegral_lintegral_swap hmeas]
      _ = A * ∫⁻ y, (∫⁻ x, ENNReal.ofReal (W x)) * ‖f y‖ₑ ^ (2:ℝ) := by
          congr 1
          refine lintegral_congr fun y => ?_
          have hm : Measurable (fun x => w x y) :=
            ENNReal.measurable_ofReal.comp (hWm.comp (measurable_id.sub measurable_const))
          rw [lintegral_mul_const _ hm, hwint' y]
      _ ≤ A * ∫⁻ y, A * ‖f y‖ₑ ^ (2:ℝ) := by gcongr
      _ = A ^ (2:ℝ) * ∫⁻ y, ‖f y‖ₑ ^ (2:ℝ) := by
          rw [lintegral_const_mul' _ _ hAt, ← mul_assoc, ENNReal.rpow_two, sq]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : ((2 : ℝ≥0∞).toReal) = (2:ℝ) := by norm_num
  rw [h2]
  calc (∫⁻ x, ‖∫ y, f y * k x y‖ₑ ^ (2:ℝ)) ^ (1 / (2:ℝ))
      ≤ (A ^ (2:ℝ) * ∫⁻ y, ‖f y‖ₑ ^ (2:ℝ)) ^ (1 / (2:ℝ)) :=
        ENNReal.rpow_le_rpow key (by norm_num)
    _ = A * (∫⁻ y, ‖f y‖ₑ ^ (2:ℝ)) ^ (1 / (2:ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num

/-! ## 2. The scaled mollifiers -/

/-- The base bump: a smooth probability density supported in the ball of radius `1/2`. -/
def rho0 (d : ℕ) : Vd d → ℝ := mol d 1

theorem rho0_supp {z : Vd d} (h : rho0 d z ≠ 0) : ‖z‖ < 1 / 2 := by
  have := norm_lt_of_mol_ne_zero (d := d) (n := 1) h
  norm_num at this ⊢
  exact this

theorem contDiff_rho0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rho0 d) := contDiff_mol 1

theorem hasCompactSupport_rho0 : HasCompactSupport (rho0 d) := hasCompactSupport_mol 1

/-- The scaled mollifier `ρ_s(z) = sᵈ ρ₀(s z)` (real-valued). -/
def rhoR (s : ℝ) (z : Vd d) : ℝ := s ^ d * rho0 d (s • z)

/-- The scaled mollifier as a complex function. -/
def rhoS (s : ℝ) : Vd d → ℂ := cx (rhoR s)

theorem contDiff_rhoR (s : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rhoR (d := d) s) :=
  contDiff_const.mul (contDiff_rho0.comp (contDiff_id.const_smul s))

theorem contDiff_rhoS (s : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rhoS (d := d) s) :=
  contDiff_cx (contDiff_rhoR s)

theorem rhoR_nonneg {s : ℝ} (hs : 0 ≤ s) (z : Vd d) : 0 ≤ rhoR s z :=
  mul_nonneg (pow_nonneg hs d) (mol_nonneg 1 _)

theorem rhoR_supp {s : ℝ} (hs : 0 < s) {z : Vd d} (h : rhoR s z ≠ 0) : ‖z‖ < 1 / (2 * s) := by
  have h1 : rho0 d (s • z) ≠ 0 := fun h0 => h (by simp [rhoR, h0])
  have h2 := rho0_supp h1
  rw [norm_smul, Real.norm_of_nonneg hs.le] at h2
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

theorem rhoS_eq_zero {s : ℝ} (hs : 1 ≤ s) {z : Vd d} (hz : 1 / 2 < ‖z‖) : rhoS s z = 0 := by
  by_contra h
  have h1 : rhoR s z ≠ 0 := fun h0 => h (by simp [rhoS, cx, h0])
  have h2 := rhoR_supp (by linarith) h1
  have h3 : 1 / (2 * s) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith

theorem rhoS_real (s : ℝ) (z : Vd d) : (starRingEnd ℂ) (rhoS s z) = rhoS s z := by
  simp [rhoS, cx]

theorem finrank_Vd : Module.finrank ℝ (Vd d) = d := finrank_euclideanSpace_fin

theorem integral_rhoR {s : ℝ} (hs : 0 < s) : ∫ z, rhoR (d := d) s z = 1 := by
  simp only [rhoR]
  rw [integral_const_mul, Measure.integral_comp_smul, finrank_Vd, rho0, integral_mol,
    smul_eq_mul, mul_one, abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity)]

theorem lintegral_rhoR {s : ℝ} (hs : 0 < s) : ∫⁻ z, ENNReal.ofReal (rhoR (d := d) s z) = 1 := by
  have hint : Integrable (rhoR (d := d) s) (volume : Measure (Vd d)) := by
    refine (contDiff_rhoR s).continuous.integrable_of_hasCompactSupport ?_
    exact (hasCompactSupport_rho0.comp_smul hs.ne').mul_left
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun z => rhoR_nonneg hs.le z), integral_rhoR hs]
  simp

/-! ## 3. Derivatives of the scaled mollifiers -/

theorem dc_comp_smul {g : Vd d → ℂ} (hg : Differentiable ℝ g) (s : ℝ) (z : Vd d) (j : Fin d) :
    dcoord j (fun z => g (s • z)) z = (s : ℂ) * dcoord j g (s • z) := by
  have h : HasFDerivAt (fun z => g (s • z)) ((fderiv ℝ g (s • z)).comp (s • ContinuousLinearMap.id ℝ (Vd d))) z :=
    (hg (s • z)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_smul s)
  simp only [dcoord]
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, Complex.real_smul]

theorem rhoS_eq (s : ℝ) : rhoS (d := d) s = fun z => ((s ^ d : ℝ) : ℂ) * cx (rho0 d) (s • z) := by
  funext z
  simp [rhoS, rhoR, cx]

theorem dcoord_rhoS (s : ℝ) (j : Fin d) (z : Vd d) :
    dcoord j (rhoS s) z = ((s ^ d * s : ℝ) : ℂ) * dcoord j (cx (rho0 d)) (s • z) := by
  have hg : Differentiable ℝ (cx (rho0 d)) :=
    (contDiff_cx contDiff_rho0).differentiable (by simp)
  have hd : DifferentiableAt ℝ (fun z => cx (rho0 d) (s • z)) z :=
    (hg.comp (differentiable_id.const_smul s)) z
  rw [rhoS_eq, dc_const_mul _ hd, dc_comp_smul hg]
  push_cast
  ring

theorem dcoord_rhoS_fun (s : ℝ) (j : Fin d) :
    dcoord j (rhoS s) = fun z => ((s ^ d * s : ℝ) : ℂ) * dcoord j (cx (rho0 d)) (s • z) := by
  funext z; exact dcoord_rhoS s j z

theorem dcoord_dcoord_rhoS (s : ℝ) (i j : Fin d) (z : Vd d) :
    dcoord i (dcoord j (rhoS s)) z
      = ((s ^ d * s * s : ℝ) : ℂ) * dcoord i (dcoord j (cx (rho0 d))) (s • z) := by
  have hg : Differentiable ℝ (dcoord j (cx (rho0 d))) :=
    (contDiff_dcoord (contDiff_cx contDiff_rho0) j).differentiable (by simp)
  have hd : DifferentiableAt ℝ (fun z => dcoord j (cx (rho0 d)) (s • z)) z :=
    (hg.comp (differentiable_id.const_smul s)) z
  rw [dcoord_rhoS_fun, dc_const_mul _ hd, dc_comp_smul hg]
  push_cast
  ring

/-- Uniform bounds on the base bump and its first two derivatives. -/
theorem exists_rho0_bounds : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : Vd d, ‖cx (rho0 d) z‖ ≤ M ∧
    (∀ j, ‖dcoord j (cx (rho0 d)) z‖ ≤ M) ∧
    (∀ i j, ‖dcoord i (dcoord j (cx (rho0 d))) z‖ ≤ M) := by
  have hs := contDiff_cx (contDiff_rho0 (d := d))
  have hc := hasCompactSupport_cx (hasCompactSupport_rho0 (d := d))
  obtain ⟨M0, hM0⟩ := hs.continuous.bounded_above_of_compact_support hc
  have h1 : ∀ j : Fin d, ∃ M, ∀ z, ‖dcoord j (cx (rho0 d)) z‖ ≤ M := fun j =>
    (contDiff_dcoord hs j).continuous.bounded_above_of_compact_support
      (hasCompactSupport_dcoord hc j)
  have h2 : ∀ i j : Fin d, ∃ M, ∀ z, ‖dcoord i (dcoord j (cx (rho0 d))) z‖ ≤ M := fun i j =>
    (contDiff_dcoord (contDiff_dcoord hs j) i).continuous.bounded_above_of_compact_support
      (hasCompactSupport_dcoord (hasCompactSupport_dcoord hc j) i)
  choose M1 hM1 using h1
  choose M2 hM2 using h2
  refine ⟨|M0| + ∑ j, |M1 j| + ∑ i, ∑ j, |M2 i j|, by positivity, fun z => ⟨?_, ?_, ?_⟩⟩
  · have := hM0 z
    have : 0 ≤ ∑ j, |M1 j| := by positivity
    have : 0 ≤ ∑ i, ∑ j, |M2 i j| := by positivity
    linarith [le_abs_self M0]
  · intro j
    have h := hM1 j z
    have : |M1 j| ≤ ∑ j, |M1 j| :=
      Finset.single_le_sum (f := fun j => |M1 j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have : 0 ≤ ∑ i, ∑ j, |M2 i j| := by positivity
    linarith [le_abs_self (M1 j), abs_nonneg M0]
  · intro i j
    have h := hM2 i j z
    have e1 : |M2 i j| ≤ ∑ j, |M2 i j| :=
      Finset.single_le_sum (f := fun j => |M2 i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have e2 : ∑ j, |M2 i j| ≤ ∑ i, ∑ j, |M2 i j| :=
      Finset.single_le_sum (f := fun i => ∑ j, |M2 i j|) (fun _ _ => by positivity)
        (Finset.mem_univ i)
    have : 0 ≤ ∑ j, |M1 j| := by positivity
    linarith [le_abs_self (M2 i j), abs_nonneg M0]

/-! ## 4. Convergence of the mollifications -/

/-- The mollification, minus the function, as an average of translates. -/
theorem integral_smul_sub_eq_kint {ρ : Vd d → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρ1 : ∫ y, ρ y = 1) {f : Vd d → ℂ} (hf : LocallyIntegrable f (volume : Measure (Vd d)))
    (x : Vd d) :
    ∫ y, ρ y • (f (x - y) - f x) = kint f (kz (cx ρ)) x - f x := by
  have hρC : Continuous (cx ρ) := Complex.continuous_ofReal.comp hρ
  have hρCc : HasCompactSupport (cx ρ) := hasCompactSupport_cx hρc
  have hex : ConvolutionExistsAt f (cx ρ) x (ContinuousLinearMap.mul ℝ ℂ) volume :=
    hρCc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ) hf hρC x
  have hsw : Integrable (fun t => f (x - t) * cx ρ t) (volume : Measure (Vd d)) :=
    hex.integrable_swap
  have hcnv : kint f (kz (cx ρ)) x = ∫ t, f (x - t) * cx ρ t := by
    have : kint f (kz (cx ρ)) x = cnv f (cx ρ) x := rfl
    rw [this, cnv, convolution_eq_swap]
    rfl
  have hint2 : Integrable (fun t => cx ρ t * f x) (volume : Measure (Vd d)) :=
    (hρC.integrable_of_hasCompactSupport hρCc).mul_const _
  have hpt : ∀ y, ρ y • (f (x - y) - f x) = f (x - y) * cx ρ y - cx ρ y * f x := by
    intro y
    simp only [cx, Complex.real_smul]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub hsw hint2,
    integral_mul_const, hcnv]
  have h1 : ∫ t, cx ρ t = 1 := by
    simp only [cx]
    rw [integral_complex_ofReal, hρ1]
    simp
  rw [h1, one_mul]

/-- The mollifier scale at step `n`. -/
def sN (n : ℕ) : ℝ := (n : ℝ) + 2

theorem sN_pos (n : ℕ) : 0 < sN n := by unfold sN; positivity

theorem one_le_sN (n : ℕ) : 1 ≤ sN n := by unfold sN; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]

/-- **The mollifications converge in `L²`.** -/
theorem tendsto_kint_rhoS {u : Vd d → ℂ} (hu : StronglyMeasurable u)
    (hu2 : MemLp u 2 (volume : Measure (Vd d))) :
    Tendsto (fun n => eLpNorm (fun x => kint u (kz (rhoS (sN n))) x - u x) 2 volume) atTop
      (𝓝 0) := by
  have hloc : LocallyIntegrable u (volume : Measure (Vd d)) := hu2.locallyIntegrable one_le_two
  have hr : Tendsto (fun n : ℕ => 1 / (2 * sN n)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 2)) atTop atTop :=
      h.const_mul_atTop (by norm_num)
    refine h2.inv_tendsto_atTop.congr fun n => ?_
    simp only [Pi.inv_apply, sN, one_div]
  have h := tendsto_mollify_L2 (μ := (volume : Measure (Vd d))) (l := atTop) u hu hu2
    (fun n => rhoR (sN n)) (fun n : ℕ => 1 / (2 * sN n)) (fun n z => rhoR_nonneg (sN_pos n).le z)
    (fun n => (contDiff_rhoR (sN n)).continuous.measurable) (fun n => lintegral_rhoR (sN_pos n))
    (fun n z hz => rhoR_supp (sN_pos n) hz) hr
  refine h.congr fun n => ?_
  congr 1
  funext x
  exact integral_smul_sub_eq_kint (contDiff_rhoR _).continuous
    ((hasCompactSupport_rho0.comp_smul (sN_pos n).ne').mul_left) (integral_rhoR (sN_pos n)) hloc x

end

end BookProof.KvnKato
