import Mathlib
import BookProof.ChapterConvolutionCalc

/-!
# The cut-off energy estimate for `−Δ_S + W`

Let `v` be a smooth function on `ℝᵈ` satisfying the pointwise equation

`Δ_S v = G − z v`,  `Re z = 0`,

and let `χ` be a real compactly supported smooth cut-off.  Multiplying the equation by
`χ² v̄`, integrating, and integrating by parts once in each direction of `S` gives

`∫ χ²|∇_S v|² + Re ∫ χ² v̄ G = −2 Re ∑_j ∫ χ (∂_jχ) v̄ ∂_j v`,

and Young's inequality `2ab ≤ a²/2 + 2b²` absorbs the right-hand side:

`Re ∫ χ² v̄ G ≤ 2 ∑_{j ∈ S} ∫ |∂_jχ|² |v|²`.

That is `energy_bound`, the analytic heart of the Kato-type theorem of
`BookProof/ChapterDegKatoEsa.lean`: no ellipticity in the directions outside `S` is used,
and no regularity of `G` beyond continuity.
-/

namespace BookProof.DegEnergy

open MeasureTheory
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegSchrodinger
open BookProof.ConvolutionCalc

noncomputable section

variable {d : ℕ}

/-! ## 1. Calculus preliminaries -/

/-- Conjugation commutes with the coordinate derivative. -/
theorem dcoord_conj {v : Vd d → ℂ} (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (j : Fin d)
    (x : Vd d) :
    dcoord j (fun y => (starRingEnd ℂ) (v y)) x = (starRingEnd ℂ) (dcoord j v x) := by
  have hd : HasFDerivAt v (fderiv ℝ v x) x :=
    (hv.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hc : HasFDerivAt (fun y => (starRingEnd ℂ) (v y))
      ((Complex.conjLIE.toLinearIsometry.toContinuousLinearMap).comp (fderiv ℝ v x)) x :=
    (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap.hasFDerivAt).comp x hd
  simp only [dcoord]
  rw [hc.fderiv]
  rfl

/-- Conjugation commutes with the partial Laplacian. -/
theorem lapCS_conj {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (S : Finset (Fin d)) (y : Vd d) :
    (starRingEnd ℂ) (lapCS S g y) = lapCS S (fun t => (starRingEnd ℂ) (g t)) y := by
  have hstep : ∀ j : Fin d, (starRingEnd ℂ) (dcoord j (dcoord j g) y)
      = dcoord j (dcoord j (fun t => (starRingEnd ℂ) (g t))) y := by
    intro j
    have h1 : (fun t => (starRingEnd ℂ) (dcoord j g t)) = dcoord j (fun t =>
        (starRingEnd ℂ) (g t)) := by
      funext t
      exact (dcoord_conj hg j t).symm
    rw [← dcoord_conj (contDiff_dcoord hg j) j y, h1]
  simp only [lapCS, map_sum, hstep]

/-- A continuous compactly supported function is integrable. -/
theorem integrable_of_cc {f : Vd d → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable f (volume : Measure (Vd d)) := hf.integrable_of_hasCompactSupport hc

/-- **Integration by parts** in the `j`-th coordinate: the compactly supported smooth factor
carries the boundary terms. -/
theorem integral_dcoord_mul {f g : Vd d → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (j : Fin d) :
    ∫ x, f x * dcoord j g x = -∫ x, dcoord j f x * g x := by
  have hfcont : Continuous f := hf.continuous
  have hgcont : Continuous g := hg.continuous
  have hdf : Continuous (dcoord j f) := (contDiff_dcoord hf j).continuous
  have hdg : Continuous (dcoord j g) := (contDiff_dcoord hg j).continuous
  have hdfc : HasCompactSupport (dcoord j f) := hasCompactSupport_dcoord hfc j
  have h1 : Integrable (fun x => dcoord j f x * g x) (volume : Measure (Vd d)) :=
    integrable_of_cc (hdf.mul hgcont) (hdfc.mul_right)
  have h2 : Integrable (fun x => f x * dcoord j g x) (volume : Measure (Vd d)) :=
    integrable_of_cc (hfcont.mul hdg) (hfc.mul_right)
  have h3 : Integrable (fun x => f x * g x) (volume : Measure (Vd d)) :=
    integrable_of_cc (hfcont.mul hgcont) (hfc.mul_right)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (hf.differentiable (by simp)) (hg.differentiable (by simp))

/-! ## 2. The energy estimate -/

variable (S : Finset (Fin d))

/-- The complexified cut-off. -/
def cx (χ : Vd d → ℝ) : Vd d → ℂ := fun y => ((χ y : ℝ) : ℂ)

theorem contDiff_cx {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cx χ) :=
  Complex.ofRealCLM.contDiff.comp hχ

theorem hasCompactSupport_cx {χ : Vd d → ℝ} (hχc : HasCompactSupport χ) :
    HasCompactSupport (cx χ) := by
  refine hχc.mono ?_
  intro x hx
  simp only [Function.mem_support, cx, ne_eq, Complex.ofReal_eq_zero] at hx ⊢
  exact hx

theorem norm_cx (χ : Vd d → ℝ) (x : Vd d) : ‖cx χ x‖ = |χ x| := by
  simp [cx]

/-- The partial Laplacian of a real-valued function is real. -/
theorem lapCS_cx_conj {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (S : Finset (Fin d)) (y : Vd d) :
    (starRingEnd ℂ) (lapCS S (cx χ) y) = lapCS S (cx χ) y := by
  rw [lapCS_conj (contDiff_cx hχ) S y]
  congr 1
  funext t
  simp [cx]


/-- The `L²` mass of `v` against the cut-off, as a real number. -/
theorem integral_cx_sq_mul_normSq {χ : Vd d → ℝ} (v : Vd d → ℂ) :
    ∀ x : Vd d, cx χ x ^ 2 * (starRingEnd ℂ) (v x) * v x
      = (((χ x) ^ 2 * ‖v x‖ ^ 2 : ℝ) : ℂ) := by
  intro x
  have h : (starRingEnd ℂ) (v x) * v x = ((‖v x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']
    norm_cast
  rw [mul_assoc, h]
  simp [cx]

/-- The derivative of the square of the cut-off. -/
theorem dcoord_cx_sq {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (j : Fin d)
    (x : Vd d) : dcoord j (fun y => cx χ y ^ 2) x = 2 * cx χ x * dcoord j (cx χ) x := by
  have h : (fun y => cx χ y ^ 2) = fun y => cx χ y * cx χ y := by funext y; ring
  rw [h, dcoord_mul (contDiff_cx hχ) (contDiff_cx hχ)]
  ring

set_option maxHeartbeats 1000000 in
-- the proof assembles a dozen integrability side conditions in one elaboration
/-- **The cut-off energy estimate.** -/
theorem energy_bound {z : ℂ} (hz : z.re = 0) {v G : Vd d → ℂ}
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (hG : Continuous G)
    (hid : ∀ x, lapCS S v x = G x - z * v x)
    {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ) :
    (∫ x, cx χ x ^ 2 * (starRingEnd ℂ) (v x) * G x).re
      ≤ 2 * ∑ j ∈ S, ∫ x, ‖dcoord j (cx χ) x‖ ^ 2 * ‖v x‖ ^ 2 := by
  classical
  have hcs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cx χ) := contDiff_cx hχ
  have hcc : HasCompactSupport (cx χ) := hasCompactSupport_cx hχc
  have hcxc : Continuous (cx χ) := hcs.continuous
  have hvc : Continuous v := hv.continuous
  have hconj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (starRingEnd ℂ) (v y)) :=
    Complex.conjLIE.toLinearIsometry.toContinuousLinearMap.contDiff.comp hv
  have hconjc : Continuous (fun y : Vd d => (starRingEnd ℂ) (v y)) := hconj.continuous
  have hcc2 : HasCompactSupport (fun x : Vd d => cx χ x ^ 2) := by
    refine hcc.mono ?_
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx ⊢
    intro h0
    exact hx (by rw [h0]; ring)
  set f : Vd d → ℂ := fun x => cx χ x ^ 2 * (starRingEnd ℂ) (v x) with hf
  have hfs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := (hcs.pow 2).mul hconj
  have hfc : HasCompactSupport f := hcc2.mul_right
  have hdvs : ∀ j : Fin d, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dcoord j v) :=
    fun j => contDiff_dcoord hv j
  have hdvc : ∀ j : Fin d, Continuous (dcoord j v) := fun j => (hdvs j).continuous
  have hdcs : ∀ j : Fin d, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dcoord j (cx χ)) :=
    fun j => contDiff_dcoord hcs j
  have hdcxc : ∀ j : Fin d, Continuous (dcoord j (cx χ)) := fun j => (hdcs j).continuous
  have hdcc : ∀ j : Fin d, HasCompactSupport (dcoord j (cx χ)) :=
    fun j => hasCompactSupport_dcoord hcc j
  -- the derivative of the test factor
  have hdf : ∀ (j : Fin d) (x : Vd d), dcoord j f x
      = 2 * cx χ x * dcoord j (cx χ) x * (starRingEnd ℂ) (v x)
        + cx χ x ^ 2 * (starRingEnd ℂ) (dcoord j v x) := by
    intro j x
    have h1 := congrFun (dcoord_mul (u := fun y => cx χ y ^ 2)
        (v := fun y => (starRingEnd ℂ) (v y)) (hcs.pow 2) hconj j) x
    rw [hf, h1, dcoord_cx_sq hχ j x, dcoord_conj hv j x]
    ring
  -- the two pieces of the boundary term
  set X : Fin d → ℂ := fun j => ∫ x, 2 * cx χ x * dcoord j (cx χ) x * (starRingEnd ℂ) (v x)
    * dcoord j v x with hX
  set Y : Fin d → ℂ := fun j => ∫ x, cx χ x ^ 2 * (starRingEnd ℂ) (dcoord j v x)
    * dcoord j v x with hY
  set Yr : Fin d → ℝ := fun j => ∫ x, (χ x) ^ 2 * ‖dcoord j v x‖ ^ 2 with hYr
  set Qr : Fin d → ℝ := fun j => ∫ x, ‖dcoord j (cx χ) x‖ ^ 2 * ‖v x‖ ^ 2 with hQr
  -- integrability of all the integrands in play
  have hIX : ∀ j : Fin d, Integrable (fun x => 2 * cx χ x * dcoord j (cx χ) x
      * (starRingEnd ℂ) (v x) * dcoord j v x) (volume : Measure (Vd d)) := fun j =>
    integrable_of_cc
      ((((continuous_const.mul hcxc).mul (hdcxc j)).mul hconjc).mul (hdvc j))
      (((hdcc j).mul_left).mul_right.mul_right)
  have hIY : ∀ j : Fin d, Integrable (fun x => cx χ x ^ 2 * (starRingEnd ℂ) (dcoord j v x)
      * dcoord j v x) (volume : Measure (Vd d)) := fun j =>
    integrable_of_cc
      (((hcxc.pow 2).mul ((Complex.continuous_conj).comp (hdvc j))).mul (hdvc j))
      (hcc2.mul_right.mul_right)
  have hIfd : ∀ j : Fin d, Integrable (fun x => f x * dcoord j (dcoord j v) x)
      (volume : Measure (Vd d)) := fun j =>
    integrable_of_cc (hfs.continuous.mul (contDiff_dcoord (hdvs j) j).continuous) hfc.mul_right
  have hIfG : Integrable (fun x => f x * G x) (volume : Measure (Vd d)) :=
    integrable_of_cc (hfs.continuous.mul hG) hfc.mul_right
  have hIfv : Integrable (fun x => f x * v x) (volume : Measure (Vd d)) :=
    integrable_of_cc (hfs.continuous.mul hvc) hfc.mul_right
  -- integration by parts in each direction of `S`
  have hIBPj : ∀ j : Fin d, ∫ x, f x * dcoord j (dcoord j v) x = -(X j + Y j) := by
    intro j
    rw [integral_dcoord_mul hfs hfc (hdvs j) j, hX, hY, ← integral_add (hIX j) (hIY j)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change dcoord j f x * dcoord j v x = _
    rw [hdf j x]
    ring
  -- the energy identity
  have hEnergy : ∫ x, f x * G x = z * (∫ x, f x * v x) + ∑ j ∈ S, -(X j + Y j) := by
    have hsplit : ∫ x, f x * lapCS S v x = ∑ j ∈ S, ∫ x, f x * dcoord j (dcoord j v) x := by
      rw [← MeasureTheory.integral_finset_sum S (fun j _ => hIfd j)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [lapCS, Finset.mul_sum]
    have hlhs : ∫ x, f x * lapCS S v x = (∫ x, f x * G x) - z * ∫ x, f x * v x := by
      have hpt : ∀ x, f x * lapCS S v x = f x * G x - z * (f x * v x) := by
        intro x
        rw [hid x]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_sub hIfG ((hIfv.const_mul z)), integral_const_mul]
    rw [hlhs] at hsplit
    rw [Finset.sum_congr rfl (fun j _ => (hIBPj j).symm), ← hsplit]
    ring
  -- the mass term is real
  have hreal : ∫ x, f x * v x = (((∫ x, (χ x) ^ 2 * ‖v x‖ ^ 2 : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [hf]
    exact integral_cx_sq_mul_normSq v x
  -- the gradient terms are real and non-negative
  have hYreal : ∀ j : Fin d, Y j = ((Yr j : ℝ) : ℂ) := by
    intro j
    rw [hY, hYr]
    simp only
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact integral_cx_sq_mul_normSq (dcoord j v) x
  have hYrnonneg : ∀ j : Fin d, 0 ≤ Yr j := by
    intro j
    rw [hYr]
    exact integral_nonneg fun x => by positivity
  -- Young's inequality absorbs the boundary term
  have hchi2c : HasCompactSupport (fun x : Vd d => (χ x) ^ 2) := by
    refine hχc.mono ?_
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx ⊢
    intro h0
    exact hx (by rw [h0]; ring)
  have hdc2 : ∀ j : Fin d, HasCompactSupport (fun x : Vd d => ‖dcoord j (cx χ) x‖ ^ 2) := by
    intro j
    refine (hdcc j).mono ?_
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx ⊢
    intro h0
    exact hx (by rw [h0]; simp)
  have hIYr : ∀ j : Fin d, Integrable (fun x => (χ x) ^ 2 * ‖dcoord j v x‖ ^ 2)
      (volume : Measure (Vd d)) := fun j =>
    ((hχ.continuous.pow 2).mul ((hdvc j).norm.pow 2)).integrable_of_hasCompactSupport
      hchi2c.mul_right
  have hIQr : ∀ j : Fin d, Integrable (fun x => ‖dcoord j (cx χ) x‖ ^ 2 * ‖v x‖ ^ 2)
      (volume : Measure (Vd d)) := fun j =>
    (((hdcxc j).norm.pow 2).mul (hvc.norm.pow 2)).integrable_of_hasCompactSupport
      (hdc2 j).mul_right
  have hXbound : ∀ j : Fin d, -(X j).re ≤ Yr j / 2 + 2 * Qr j := by
    intro j
    have h1 : -(X j).re ≤ ‖X j‖ := by
      have habs := Complex.abs_re_le_norm (X j)
      have := abs_le.mp habs
      linarith [this.1]
    have h2 : ‖X j‖ ≤ ∫ x, ‖2 * cx χ x * dcoord j (cx χ) x * (starRingEnd ℂ) (v x)
        * dcoord j v x‖ := by
      rw [hX]
      exact norm_integral_le_integral_norm _
    have h3 : ∫ x, ‖2 * cx χ x * dcoord j (cx χ) x * (starRingEnd ℂ) (v x) * dcoord j v x‖
        ≤ ∫ x, ((χ x) ^ 2 * ‖dcoord j v x‖ ^ 2 / 2
            + 2 * (‖dcoord j (cx χ) x‖ ^ 2 * ‖v x‖ ^ 2)) := by
      refine integral_mono ((hIX j).norm) (((hIYr j).div_const 2).add ((hIQr j).const_mul 2))
        fun x => ?_
      have hnorm : ‖2 * cx χ x * dcoord j (cx χ) x * (starRingEnd ℂ) (v x) * dcoord j v x‖
          = 2 * (|χ x| * ‖dcoord j v x‖) * (‖dcoord j (cx χ) x‖ * ‖v x‖) := by
        simp only [norm_mul, norm_cx, RCLike.norm_conj]
        norm_num
        ring
      have hsq : (χ x) ^ 2 = |χ x| ^ 2 := (sq_abs _).symm
      simp only [hnorm, hsq]
      nlinarith [sq_nonneg (|χ x| * ‖dcoord j v x‖ - 2 * (‖dcoord j (cx χ) x‖ * ‖v x‖)),
        abs_nonneg (χ x), norm_nonneg (dcoord j v x), norm_nonneg (dcoord j (cx χ) x),
        norm_nonneg (v x)]
    have h4 : ∫ x, ((χ x) ^ 2 * ‖dcoord j v x‖ ^ 2 / 2
        + 2 * (‖dcoord j (cx χ) x‖ ^ 2 * ‖v x‖ ^ 2)) = Yr j / 2 + 2 * Qr j := by
      rw [integral_add ((hIYr j).div_const 2) ((hIQr j).const_mul 2), integral_div,
        integral_const_mul]
    linarith
  -- conclusion
  have hgoal : (∫ x, f x * G x).re = -∑ j ∈ S, ((X j).re + Yr j) := by
    rw [hEnergy]
    simp only [Complex.add_re, Complex.mul_re, hreal, Complex.ofReal_re, Complex.ofReal_im, hz]
    have : (∑ j ∈ S, -(X j + Y j)).re = ∑ j ∈ S, -((X j).re + Yr j) := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hYreal j]
      simp
    rw [this, Finset.sum_neg_distrib]
    ring
  have hfinal : -∑ j ∈ S, ((X j).re + Yr j) ≤ 2 * ∑ j ∈ S, Qr j := by
    have hterm : ∀ j ∈ S, -((X j).re + Yr j) ≤ 2 * Qr j := by
      intro j _
      have := hXbound j
      have := hYrnonneg j
      linarith
    calc -∑ j ∈ S, ((X j).re + Yr j) = ∑ j ∈ S, -((X j).re + Yr j) := by
          rw [Finset.sum_neg_distrib]
      _ ≤ ∑ j ∈ S, 2 * Qr j := Finset.sum_le_sum hterm
      _ = 2 * ∑ j ∈ S, Qr j := by rw [Finset.mul_sum]
  calc (∫ x, cx χ x ^ 2 * (starRingEnd ℂ) (v x) * G x).re = (∫ x, f x * G x).re := by
        rw [hf]
    _ = -∑ j ∈ S, ((X j).re + Yr j) := hgoal
    _ ≤ 2 * ∑ j ∈ S, Qr j := hfinal

end

end BookProof.DegEnergy
