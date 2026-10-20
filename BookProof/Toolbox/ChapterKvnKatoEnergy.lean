import Mathlib
import BookProof.Toolbox.ChapterKvnKatoCalc

/-!
# The energy inequality for the mollified deficiency equation

If `v`, `w₁` are smooth and `w₂` continuous with `A v − z v = −2 X w₁ + w₂` pointwise
(`A = −X² + E`, `E ≥ 1` real, `Re z = 0`), then for every real compactly supported smooth
cut-off `χ`

`‖χ v‖² ≤ (‖(G·∇χ) v‖ + ‖χ w₁‖)² + 4 ‖(G·∇χ) v‖ ‖χ w₁‖ + ‖χ v‖ ‖χ w₂‖`.

The proof tests the equation against `χ² v̄`, integrates by parts once (the antisymmetry of
`X`) and applies Cauchy–Schwarz.
-/

namespace BookProof.KvnKato

open MeasureTheory Filter Topology
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegEnergy
open BookProof.ConvolutionCalc BookProof.DegKatoEsa

noncomputable section

variable {d : ℕ}

/-! ## 1. `L²` norms as integrals -/

/-- The `L²` norm of a function, as a real number. -/
def l2n (f : Vd d → ℂ) : ℝ := Real.sqrt (∫ x, ‖f x‖ ^ 2)

theorem l2n_nonneg (f : Vd d → ℂ) : 0 ≤ l2n f := Real.sqrt_nonneg _

theorem l2n_eq_norm_toLp {f : Vd d → ℂ} (hf : MemLp f 2 (volume : Measure (Vd d))) :
    l2n f = ‖hf.toLp f‖ := by
  rw [l2n, ← norm_toLp_sq hf, Real.sqrt_sq (norm_nonneg _)]

theorem l2n_sq {f : Vd d → ℂ} (hf : MemLp f 2 (volume : Measure (Vd d))) :
    l2n f ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [l2n_eq_norm_toLp hf, norm_toLp_sq hf]

/-- **Cauchy–Schwarz** for integrals. -/
theorem norm_integral_conj_mul_le {f g : Vd d → ℂ} (hf : MemLp f 2 (volume : Measure (Vd d)))
    (hg : MemLp g 2 (volume : Measure (Vd d))) :
    ‖∫ x, (starRingEnd ℂ) (f x) * g x‖ ≤ l2n f * l2n g := by
  rw [← inner_toLp hf hg, l2n_eq_norm_toLp hf, l2n_eq_norm_toLp hg]
  exact norm_inner_le_norm _ _

theorem memLp_of_cc' {f : Vd d → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    MemLp f 2 (volume : Measure (Vd d)) := hf.memLp_of_hasCompactSupport hfc

/-! ## 2. The energy identity -/

variable (S : KvnData d)

theorem Df_mul {f g : Vd d → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : Vd d) :
    Df S (fun y => f y * g y) x = Df S f x * g x + f x * Df S g x := by
  have h := Xf_mul S hf hg x
  rw [Xf_eq, Xf_eq] at h
  linear_combination h

theorem Df_cx_real {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (x : Vd d) :
    (starRingEnd ℂ) (Df S (cx χ) x) = Df S (cx χ) x := by
  rw [← Df_conj S (contDiff_cx hχ)]
  congr 1
  funext y
  simp [cx]

theorem hasCompactSupport_Df {f : Vd d → ℂ} (hfc : HasCompactSupport f) :
    HasCompactSupport (Df S f) :=
  hasCompactSupport_finsetSum _ fun i _ => (hasCompactSupport_dcoord hfc i).mul_left

theorem cx_real (χ : Vd d → ℝ) (x : Vd d) : (starRingEnd ℂ) (cx χ x) = cx χ x := by simp [cx]

/-- `X (χ² v̄) = 2 χ (G·∇χ) v̄ + χ² X v̄`. -/
theorem Xf_test {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) {v : Vd d → ℂ}
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (x : Vd d) :
    Xf S (fun y => cx χ y ^ 2 * (starRingEnd ℂ) (v y)) x
      = 2 * cx χ x * Df S (cx χ) x * (starRingEnd ℂ) (v x)
        + cx χ x ^ 2 * (starRingEnd ℂ) (Xf S v x) := by
  have hc : Differentiable ℝ (cx χ) := (contDiff_cx hχ).differentiable (by simp)
  have hc2 : Differentiable ℝ (fun y => cx χ y ^ 2) := hc.pow 2
  have hvc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (starRingEnd ℂ) (v y)) :=
    (Complex.conjCLE.contDiff).comp hv
  rw [Xf_mul S hc2 (hvc.differentiable (by simp)), Xf_conj S hv]
  have hsq : Df S (fun y => cx χ y ^ 2) x = 2 * cx χ x * Df S (cx χ) x := by
    have e : (fun y => cx χ y ^ 2) = fun y => cx χ y * cx χ y := by funext y; ring
    rw [e, Df_mul S hc hc]
    ring
  rw [hsq]

set_option maxHeartbeats 1000000 in
-- many integrability side conditions
/-- **The energy identity**: the mollified equation tested against `χ² v̄`, after one
integration by parts. -/
theorem energy_identity {E : Vd d → ℂ} (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E) {z : ℂ}
    {v w1 w2 : Vd d → ℂ} (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (hw1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w1) (hw2 : Continuous w2)
    (hid : ∀ x, Af S E v x - z * v x = -2 * Xf S w1 x + w2 x)
    {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ) :
    2 * (∫ x, (starRingEnd ℂ) (Df S (cx χ) x * v x) * (cx χ x * Xf S v x))
      + (∫ x, (starRingEnd ℂ) (cx χ x * Xf S v x) * (cx χ x * Xf S v x))
      + (∫ x, E x * ((starRingEnd ℂ) (cx χ x * v x) * (cx χ x * v x)))
      - z * (∫ x, (starRingEnd ℂ) (cx χ x * v x) * (cx χ x * v x))
    = 4 * (∫ x, (starRingEnd ℂ) (Df S (cx χ) x * v x) * (cx χ x * w1 x))
      + 2 * (∫ x, (starRingEnd ℂ) (cx χ x * Xf S v x) * (cx χ x * w1 x))
      + (∫ x, (starRingEnd ℂ) (cx χ x * v x) * (cx χ x * w2 x)) := by
  -- continuity and compact support
  have hcx := contDiff_cx hχ
  have hcxc : HasCompactSupport (cx χ) := hasCompactSupport_cx hχc
  have cC : Continuous (cx χ) := hcx.continuous
  have cD : Continuous (Df S (cx χ)) := (contDiff_Df S hcx).continuous
  have cv : Continuous v := hv.continuous
  have cXv : Continuous (Xf S v) := (contDiff_Xf S hv).continuous
  have cXXv : Continuous (Xf S (Xf S v)) := (contDiff_Xf S (contDiff_Xf S hv)).continuous
  have cw1 : Continuous w1 := hw1.continuous
  have cXw1 : Continuous (Xf S w1) := (contDiff_Xf S hw1).continuous
  have cE : Continuous E := hE.continuous
  have cconj : Continuous (starRingEnd ℂ : ℂ → ℂ) := Complex.continuous_conj
  set f0 : Vd d → ℂ := fun y => cx χ y ^ 2 * (starRingEnd ℂ) (v y) with hf0
  have hf0s : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f0 :=
    (hcx.pow 2).mul ((Complex.conjCLE.contDiff).comp hv)
  have hf0c : HasCompactSupport f0 := by
    have : f0 = fun y => cx χ y * (cx χ y * (starRingEnd ℂ) (v y)) := by funext y; simp [hf0]; ring
    rw [this]; exact hcxc.mul_right
  have cf0 : Continuous f0 := hf0s.continuous
  have cXf0 : Continuous (Xf S f0) := (contDiff_Xf S hf0s).continuous
  have hXf0c : HasCompactSupport (Xf S f0) := hasCompactSupport_Xf S hf0c
  have hXf0 : ∀ x, Xf S f0 x = 2 * cx χ x * Df S (cx χ) x * (starRingEnd ℂ) (v x)
      + cx χ x ^ 2 * (starRingEnd ℂ) (Xf S v x) := Xf_test S hχ hv
  have hcr := cx_real χ
  have hDr := Df_cx_real S hχ
  -- the integrability of the pieces
  have i1 : Integrable (fun x => f0 x * -Xf S (Xf S v) x) volume :=
    integrable_of_cc (cf0.mul cXXv.neg) hf0c.mul_right
  have i2 : Integrable (fun x => E x * (f0 x * v x)) volume :=
    integrable_of_cc (cE.mul (cf0.mul cv)) hf0c.mul_right.mul_left
  have i3 : Integrable (fun x => z * (f0 x * v x)) volume :=
    integrable_of_cc (continuous_const.mul (cf0.mul cv)) hf0c.mul_right.mul_left
  have i4 : Integrable (fun x => -2 * (f0 x * Xf S w1 x)) volume :=
    integrable_of_cc (continuous_const.mul (cf0.mul cXw1)) hf0c.mul_right.mul_left
  have i5 : Integrable (fun x => f0 x * w2 x) volume :=
    integrable_of_cc (cf0.mul hw2) hf0c.mul_right
  have iA : Integrable (fun x => 2 * ((starRingEnd ℂ) (Df S (cx χ) x * v x)
      * (cx χ x * Xf S v x))) volume :=
    integrable_of_cc (continuous_const.mul ((cconj.comp (cD.mul cv)).mul (cC.mul cXv)))
      hcxc.mul_right.mul_left.mul_left
  have iB : Integrable (fun x => (starRingEnd ℂ) (cx χ x * Xf S v x)
      * (cx χ x * Xf S v x)) volume :=
    integrable_of_cc ((cconj.comp (cC.mul cXv)).mul (cC.mul cXv)) hcxc.mul_right.mul_left
  have iC : Integrable (fun x => 2 * ((starRingEnd ℂ) (Df S (cx χ) x * v x)
      * (cx χ x * w1 x))) volume :=
    integrable_of_cc (continuous_const.mul ((cconj.comp (cD.mul cv)).mul (cC.mul cw1)))
      hcxc.mul_right.mul_left.mul_left
  have iD : Integrable (fun x => (starRingEnd ℂ) (cx χ x * Xf S v x)
      * (cx χ x * w1 x)) volume :=
    integrable_of_cc ((cconj.comp (cC.mul cXv)).mul (cC.mul cw1)) hcxc.mul_right.mul_left
  -- the left side
  have hL : ∫ x, f0 x * (Af S E v x - z * v x)
      = (∫ x, f0 x * -Xf S (Xf S v) x) + (∫ x, E x * (f0 x * v x))
        - ∫ x, z * (f0 x * v x) := by
    have i12 : Integrable (fun x => f0 x * -Xf S (Xf S v) x + E x * (f0 x * v x)) volume :=
      i1.add i2
    rw [← integral_add i1 i2, ← integral_sub i12 i3]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Af]
    ring
  have hL1 : ∫ x, f0 x * -Xf S (Xf S v) x
      = 2 * (∫ x, (starRingEnd ℂ) (Df S (cx χ) x * v x) * (cx χ x * Xf S v x))
        + ∫ x, (starRingEnd ℂ) (cx χ x * Xf S v x) * (cx χ x * Xf S v x) := by
    have h := integral_mul_Xf S hf0s hf0c (contDiff_Xf S hv)
    have e : ∫ x, f0 x * -Xf S (Xf S v) x = -∫ x, f0 x * Xf S (Xf S v) x := by
      rw [← integral_neg]; congr 1; funext x; ring
    rw [e, h, neg_neg, ← integral_const_mul, ← integral_add iA iB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hXf0, map_mul, hcr, hDr]
    ring
  have hL2 : ∫ x, E x * (f0 x * v x)
      = ∫ x, E x * ((starRingEnd ℂ) (cx χ x * v x) * (cx χ x * v x)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf0, map_mul, hcr]
    ring
  have hL3 : ∫ x, z * (f0 x * v x)
      = z * ∫ x, (starRingEnd ℂ) (cx χ x * v x) * (cx χ x * v x) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf0, map_mul, hcr]
    ring
  -- the right side
  have hR : ∫ x, f0 x * (-2 * Xf S w1 x + w2 x)
      = (∫ x, -2 * (f0 x * Xf S w1 x)) + ∫ x, f0 x * w2 x := by
    rw [← integral_add i4 i5]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hR1 : ∫ x, -2 * (f0 x * Xf S w1 x)
      = 4 * (∫ x, (starRingEnd ℂ) (Df S (cx χ) x * v x) * (cx χ x * w1 x))
        + 2 * ∫ x, (starRingEnd ℂ) (cx χ x * Xf S v x) * (cx χ x * w1 x) := by
    rw [integral_const_mul, integral_mul_Xf S hf0s hf0c hw1]
    have e : ∫ x, Xf S f0 x * w1 x
        = 2 * (∫ x, (starRingEnd ℂ) (Df S (cx χ) x * v x) * (cx χ x * w1 x))
          + ∫ x, (starRingEnd ℂ) (cx χ x * Xf S v x) * (cx χ x * w1 x) := by
      rw [← integral_const_mul, ← integral_add iC iD]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hXf0, map_mul, hcr, hDr]
      ring
    rw [e]
    ring
  have hR2 : ∫ x, f0 x * w2 x = ∫ x, (starRingEnd ℂ) (cx χ x * v x) * (cx χ x * w2 x) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf0, map_mul, hcr]
    ring
  have hmain : ∫ x, f0 x * (Af S E v x - z * v x) = ∫ x, f0 x * (-2 * Xf S w1 x + w2 x) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hid x]
  rw [hL, hL1, hL2, hL3, hR, hR1, hR2] at hmain
  linear_combination hmain

theorem integral_conj_mul_self {f : Vd d → ℂ} :
    ∫ x, (starRingEnd ℂ) (f x) * f x = ((∫ x, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [Complex.conj_mul']
  norm_cast

/-- **The energy inequality.** -/
theorem energy_ineq {E : Vd d → ℂ} (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E)
    (hE1 : ∀ x, 1 ≤ (E x).re) {z : ℂ} (hz : z.re = 0)
    {v w1 w2 : Vd d → ℂ} (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (hw1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w1) (hw2 : Continuous w2)
    (hid : ∀ x, Af S E v x - z * v x = -2 * Xf S w1 x + w2 x)
    {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ) :
    l2n (fun x => cx χ x * v x) ^ 2
      ≤ (l2n (fun x => Df S (cx χ) x * v x) + l2n (fun x => cx χ x * w1 x)) ^ 2
        + 4 * l2n (fun x => Df S (cx χ) x * v x) * l2n (fun x => cx χ x * w1 x)
        + l2n (fun x => cx χ x * v x) * l2n (fun x => cx χ x * w2 x) := by
  have h := energy_identity S hE hv hw1 hw2 hid hχ hχc
  have hcx := contDiff_cx hχ
  have hcxc : HasCompactSupport (cx χ) := hasCompactSupport_cx hχc
  have cC : Continuous (cx χ) := hcx.continuous
  have cD : Continuous (Df S (cx χ)) := (contDiff_Df S hcx).continuous
  have cv : Continuous v := hv.continuous
  have cXv : Continuous (Xf S v) := (contDiff_Xf S hv).continuous
  set Q : Vd d → ℂ := fun x => Df S (cx χ) x * v x with hQ
  set P : Vd d → ℂ := fun x => cx χ x * Xf S v x with hP
  set V : Vd d → ℂ := fun x => cx χ x * v x with hV
  set W1 : Vd d → ℂ := fun x => cx χ x * w1 x with hW1
  set W2 : Vd d → ℂ := fun x => cx χ x * w2 x with hW2
  have mQ : MemLp Q 2 volume :=
    memLp_of_cc' (cD.mul cv) (hasCompactSupport_Df S hcxc).mul_right
  have mP : MemLp P 2 volume := memLp_of_cc' (cC.mul cXv) hcxc.mul_right
  have mV : MemLp V 2 volume := memLp_of_cc' (cC.mul cv) hcxc.mul_right
  have mW1 : MemLp W1 2 volume := memLp_of_cc' (cC.mul hw1.continuous) hcxc.mul_right
  have mW2 : MemLp W2 2 volume := memLp_of_cc' (cC.mul hw2) hcxc.mul_right
  have hI2 : ∫ x, (starRingEnd ℂ) (P x) * P x = ((l2n P ^ 2 : ℝ) : ℂ) := by
    rw [integral_conj_mul_self, l2n_sq mP]
  have hI4 : ∫ x, (starRingEnd ℂ) (V x) * V x = ((l2n V ^ 2 : ℝ) : ℂ) := by
    rw [integral_conj_mul_self, l2n_sq mV]
  -- the potential term dominates the mass
  have hI3 : l2n V ^ 2 ≤ (∫ x, E x * ((starRingEnd ℂ) (V x) * V x)).re := by
    have hint : Integrable (fun x => E x * ((starRingEnd ℂ) (V x) * V x)) volume :=
      integrable_of_cc (hE.continuous.mul ((Complex.continuous_conj.comp (cC.mul cv)).mul
        (cC.mul cv))) hcxc.mul_right.mul_left.mul_left
    have hre : (∫ x, E x * ((starRingEnd ℂ) (V x) * V x)).re
        = ∫ x, (E x * ((starRingEnd ℂ) (V x) * V x)).re := (integral_re hint).symm
    rw [hre, l2n_sq mV]
    have hpt : ∀ x, (E x * ((starRingEnd ℂ) (V x) * V x)).re = (E x).re * ‖V x‖ ^ 2 := by
      intro x
      rw [Complex.conj_mul']
      norm_cast
      rw [Complex.re_mul_ofReal]
    simp only [hpt]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) ?_
      (Filter.Eventually.of_forall fun x => ?_)
    · refine Continuous.integrable_of_hasCompactSupport
        ((Complex.continuous_re.comp hE.continuous).mul ((cC.mul cv).norm.pow 2)) ?_
      have hVc : HasCompactSupport V := hcxc.mul_right
      have hV2 : HasCompactSupport (fun x => ‖V x‖ ^ 2) :=
        hVc.comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)
      exact hV2.mul_left
    · simp only
      nlinarith [hE1 x, sq_nonneg ‖V x‖]
  have c1 : ‖∫ x, (starRingEnd ℂ) (Df S (cx χ) x * v x) * (cx χ x * Xf S v x)‖
      ≤ l2n Q * l2n P := norm_integral_conj_mul_le mQ mP
  have c2 : ‖∫ x, (starRingEnd ℂ) (Df S (cx χ) x * v x) * (cx χ x * w1 x)‖
      ≤ l2n Q * l2n W1 := norm_integral_conj_mul_le mQ mW1
  have c3 : ‖∫ x, (starRingEnd ℂ) (cx χ x * Xf S v x) * (cx χ x * w1 x)‖
      ≤ l2n P * l2n W1 := norm_integral_conj_mul_le mP mW1
  have c4 : ‖∫ x, (starRingEnd ℂ) (cx χ x * v x) * (cx χ x * w2 x)‖
      ≤ l2n V * l2n W2 := norm_integral_conj_mul_le mV mW2
  have hI3' : l2n V ^ 2 ≤ (∫ x, E x * ((starRingEnd ℂ) (cx χ x * v x) * (cx χ x * v x))).re :=
    hI3
  have hI2' : ∫ x, (starRingEnd ℂ) (cx χ x * Xf S v x) * (cx χ x * Xf S v x)
      = ((l2n P ^ 2 : ℝ) : ℂ) := hI2
  have hI4' : ∫ x, (starRingEnd ℂ) (cx χ x * v x) * (cx χ x * v x)
      = ((l2n V ^ 2 : ℝ) : ℂ) := hI4
  rw [hI2', hI4'] at h
  generalize (∫ x, (starRingEnd ℂ) (Df S (cx χ) x * v x) * (cx χ x * Xf S v x)) = I1 at h c1
  generalize (∫ x, (starRingEnd ℂ) (Df S (cx χ) x * v x) * (cx χ x * w1 x)) = J1 at h c2
  generalize (∫ x, (starRingEnd ℂ) (cx χ x * Xf S v x) * (cx χ x * w1 x)) = J2 at h c3
  generalize (∫ x, (starRingEnd ℂ) (cx χ x * v x) * (cx χ x * w2 x)) = J3 at h c4
  generalize (∫ x, E x * ((starRingEnd ℂ) (cx χ x * v x) * (cx χ x * v x))) = I3 at h hI3'
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, hz] at hre
  norm_num at hre
  have r1 := (abs_le.mp ((Complex.abs_re_le_norm I1).trans c1)).1
  have r2 := (Complex.re_le_norm J1).trans c2
  have r3 := (Complex.re_le_norm J2).trans c3
  have r4 := (Complex.re_le_norm J3).trans c4
  have hp := l2n_nonneg P
  have hq := l2n_nonneg Q
  have hw := l2n_nonneg W1
  nlinarith [sq_nonneg (l2n P - l2n Q - l2n W1)]

end

end BookProof.KvnKato
