import Mathlib
import BookProof.ChapterDegKatoEsa

/-!
# Calculus for the Kato argument for `N = H_G² + E`

Pointwise rules for the coordinate derivative `dcoord`, used by the Kato-type essential
self-adjointness proof of `BookProof/ChapterKvnKatoEsa.lean`.
-/

namespace BookProof.KvnKato

open MeasureTheory Filter Topology
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegEnergy
open BookProof.ConvolutionCalc

noncomputable section

variable {d : ℕ}

/-! ## 1. Pointwise rules for `dcoord` -/

theorem dc_add {u v : Vd d → ℂ} {x : Vd d} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (j : Fin d) :
    dcoord j (fun y => u y + v y) x = dcoord j u x + dcoord j v x := by
  simp only [dcoord]
  rw [show (fun y => u y + v y) = u + v from rfl, fderiv_add hu hv]
  rfl

theorem dc_sub {u v : Vd d → ℂ} {x : Vd d} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (j : Fin d) :
    dcoord j (fun y => u y - v y) x = dcoord j u x - dcoord j v x := by
  simp only [dcoord]
  rw [show (fun y => u y - v y) = u - v from rfl, fderiv_sub hu hv]
  rfl

theorem dc_neg {u : Vd d → ℂ} {x : Vd d} (j : Fin d) :
    dcoord j (fun y => -u y) x = -dcoord j u x := by
  simp only [dcoord]
  rw [show (fun y => -u y) = -u from rfl, fderiv_neg]
  rfl

theorem dc_mul {u v : Vd d → ℂ} {x : Vd d} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (j : Fin d) :
    dcoord j (fun y => u y * v y) x = dcoord j u x * v x + u x * dcoord j v x := by
  simp only [dcoord]
  rw [show (fun y => u y * v y) = u * v from rfl, fderiv_mul hu hv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem dc_const (a : ℂ) (x : Vd d) (j : Fin d) : dcoord j (fun _ => a) x = 0 := by
  simp [dcoord]

theorem dc_const_mul (a : ℂ) {u : Vd d → ℂ} {x : Vd d} (hu : DifferentiableAt ℝ u x)
    (j : Fin d) : dcoord j (fun y => a * u y) x = a * dcoord j u x := by
  rw [dc_mul (differentiableAt_const a) hu, dc_const]
  ring

theorem dc_sum {ι : Type*} (s : Finset ι) {u : ι → Vd d → ℂ} {x : Vd d}
    (hu : ∀ i ∈ s, DifferentiableAt ℝ (u i) x) (j : Fin d) :
    dcoord j (fun y => ∑ i ∈ s, u i y) x = ∑ i ∈ s, dcoord j (u i) x := by
  simp only [dcoord]
  have h : (fun y => ∑ i ∈ s, u i y) = ∑ i ∈ s, u i := by
    funext y
    simp
  rw [h, fderiv_sum hu]
  simp

theorem dc_comp_sub (h : Vd d → ℂ) (y x : Vd d) (j : Fin d) :
    dcoord j (fun x => h (x - y)) x = dcoord j h (x - y) := by
  simp only [dcoord]
  rw [fderiv_comp_sub]

theorem dc_reflect {h : Vd d → ℂ} (x y : Vd d) (hh : DifferentiableAt ℝ h (x - y))
    (j : Fin d) : dcoord j (fun y => h (x - y)) y = -dcoord j h (x - y) := by
  have hA : HasFDerivAt (fun y : Vd d => x - y) (-(ContinuousLinearMap.id ℝ (Vd d))) y := by
    simpa using (hasFDerivAt_const (𝕜 := ℝ) x y).sub (hasFDerivAt_id y)
  have hcomp : HasFDerivAt (fun y : Vd d => h (x - y))
      ((fderiv ℝ h (x - y)).comp (-(ContinuousLinearMap.id ℝ (Vd d)))) y :=
    hh.hasFDerivAt.comp y hA
  simp only [dcoord]
  rw [hcomp.fderiv]
  simp

theorem differentiableAt_of_smooth {u : Vd d → ℂ} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (x : Vd d) : DifferentiableAt ℝ u x :=
  (hu.differentiable (by simp)).differentiableAt

/-- **Symmetry of second derivatives.** -/
theorem dcoord_dcoord_comm {u : Vd d → ℂ} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (i j : Fin d) (x : Vd d) : dcoord j (dcoord i u) x = dcoord i (dcoord j u) x := by
  have hfd : ∀ k : Fin d, dcoord k u = fun y => fderiv ℝ u y (kinDir d k) := fun k => rfl
  have hd2 : DifferentiableAt ℝ (fderiv ℝ u) x :=
    ((hu.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl).differentiable (by simp)) x
  have key : ∀ a b : Fin d, dcoord b (dcoord a u) x
      = fderiv ℝ (fderiv ℝ u) x (kinDir d b) (kinDir d a) := by
    intro a b
    rw [hfd a]
    simp only [dcoord]
    rw [fderiv_clm_apply hd2 (differentiableAt_const _)]
    simp
  rw [key, key]
  exact (hu.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)) _ _

end

end BookProof.KvnKato

namespace BookProof.KvnKato

open MeasureTheory Filter Topology
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegEnergy
open BookProof.ConvolutionCalc

noncomputable section

variable {d : ℕ}

/-! ## 2. Integral operators with smooth, short-range kernels -/

/-- The integral operator with kernel `κ`: `kint u κ x = ∫ u(y) κ(x, y) dy`. -/
def kint (u : Vd d → ℂ) (κ : Vd d → Vd d → ℂ) (x : Vd d) : ℂ := ∫ y, u y * κ x y

/-- A **short-range smooth kernel**: jointly smooth, and vanishing for `‖x − y‖ > 1/2`. -/
structure GoodKernel (κ : Vd d → Vd d → ℂ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry κ)
  supp : ∀ x y, 1 / 2 < ‖x - y‖ → κ x y = 0

/-- The partial derivative of a kernel in its first variable. -/
def dxk (j : Fin d) (κ : Vd d → Vd d → ℂ) (x y : Vd d) : ℂ := dcoord j (fun x => κ x y) x

/-- The partial derivative of a kernel in its second variable. -/
def dyk (j : Fin d) (κ : Vd d → Vd d → ℂ) (x y : Vd d) : ℂ := dcoord j (fun y => κ x y) y

theorem GoodKernel.contDiff_left {κ : Vd d → Vd d → ℂ} (h : GoodKernel κ) (y : Vd d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => κ x y) :=
  h.smooth.comp (contDiff_id.prodMk contDiff_const)

theorem GoodKernel.contDiff_right {κ : Vd d → Vd d → ℂ} (h : GoodKernel κ) (x : Vd d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => κ x y) :=
  h.smooth.comp (contDiff_const.prodMk contDiff_id)

theorem GoodKernel.continuous {κ : Vd d → Vd d → ℂ} (h : GoodKernel κ) :
    Continuous (Function.uncurry κ) := h.smooth.continuous

theorem fderiv_left_eq {κ : Vd d → Vd d → ℂ}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry κ)) (x y : Vd d) :
    fderiv ℝ (fun x => κ x y) x
      = (fderiv ℝ (Function.uncurry κ) (x, y)).comp (ContinuousLinearMap.inl ℝ (Vd d) (Vd d)) := by
  have hd : HasFDerivAt (Function.uncurry κ) (fderiv ℝ (Function.uncurry κ) (x, y)) (x, y) :=
    ((h.differentiable (by simp)) (x, y)).hasFDerivAt
  have h2 : HasFDerivAt (fun x : Vd d => (x, y)) (ContinuousLinearMap.inl ℝ (Vd d) (Vd d)) x :=
    hasFDerivAt_prodMk_left x y
  exact (hd.comp x h2).fderiv

theorem fderiv_right_eq {κ : Vd d → Vd d → ℂ}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry κ)) (x y : Vd d) :
    fderiv ℝ (fun y => κ x y) y
      = (fderiv ℝ (Function.uncurry κ) (x, y)).comp (ContinuousLinearMap.inr ℝ (Vd d) (Vd d)) := by
  have hd : HasFDerivAt (Function.uncurry κ) (fderiv ℝ (Function.uncurry κ) (x, y)) (x, y) :=
    ((h.differentiable (by simp)) (x, y)).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Vd d => (x, y)) (ContinuousLinearMap.inr ℝ (Vd d) (Vd d)) y :=
    hasFDerivAt_prodMk_right x y
  exact (hd.comp y h2).fderiv

theorem continuous_fderiv_left {κ : Vd d → Vd d → ℂ}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry κ)) :
    Continuous (fun p : Vd d × Vd d => fderiv ℝ (fun x => κ x p.2) p.1) := by
  have hc : Continuous (fun p : Vd d × Vd d => fderiv ℝ (Function.uncurry κ) p) :=
    h.continuous_fderiv (by simp)
  have heq : (fun p : Vd d × Vd d => fderiv ℝ (fun x => κ x p.2) p.1)
      = fun p => (fderiv ℝ (Function.uncurry κ) p).comp
          (ContinuousLinearMap.inl ℝ (Vd d) (Vd d)) := by
    funext p
    exact fderiv_left_eq h p.1 p.2
  rw [heq]
  exact (ContinuousLinearMap.compL ℝ (Vd d) (Vd d × Vd d) ℂ).flip
    (ContinuousLinearMap.inl ℝ (Vd d) (Vd d)) |>.continuous.comp hc

/-- A smooth function of the pair is smooth in the uncurried sense for the partial
derivative in the first variable. -/
theorem contDiff_dxk {κ : Vd d → Vd d → ℂ}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry κ)) (j : Fin d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (dxk j κ)) := by
  have heq : Function.uncurry (dxk j κ)
      = fun p => fderiv ℝ (Function.uncurry κ) p (kinDir d j, 0) := by
    funext p
    simp only [Function.uncurry, dxk, dcoord]
    rw [fderiv_left_eq h p.1 p.2]
    simp
  rw [heq]
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => fderiv ℝ (Function.uncurry κ) p) :=
    h.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl
  exact (ContinuousLinearMap.apply ℝ ℂ ((kinDir d j, 0) : Vd d × Vd d)).contDiff.comp hf

theorem contDiff_dyk {κ : Vd d → Vd d → ℂ}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry κ)) (j : Fin d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (dyk j κ)) := by
  have heq : Function.uncurry (dyk j κ)
      = fun p => fderiv ℝ (Function.uncurry κ) p (0, kinDir d j) := by
    funext p
    simp only [Function.uncurry, dyk, dcoord]
    rw [fderiv_right_eq h p.1 p.2]
    simp
  rw [heq]
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => fderiv ℝ (Function.uncurry κ) p) :=
    h.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl
  exact (ContinuousLinearMap.apply ℝ ℂ ((0, kinDir d j) : Vd d × Vd d)).contDiff.comp hf

/-- The first-variable derivative vanishes where the kernel vanishes identically. -/
theorem fderiv_left_eq_zero {κ : Vd d → Vd d → ℂ} (h : GoodKernel κ) {x y : Vd d}
    (hxy : 1 / 2 < ‖x - y‖) : fderiv ℝ (fun x => κ x y) x = 0 := by
  have hev : (fun x => κ x y) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
    have hopen : IsOpen {x' : Vd d | 1 / 2 < ‖x' - y‖} :=
      isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
    filter_upwards [hopen.mem_nhds hxy] with x' hx'
    exact h.supp x' y hx'
  rw [hev.fderiv_eq]
  simp

theorem GoodKernel.dxk {κ : Vd d → Vd d → ℂ} (h : GoodKernel κ) (j : Fin d) :
    GoodKernel (dxk j κ) where
  smooth := contDiff_dxk h.smooth j
  supp := by
    intro x y hxy
    simp only [BookProof.KvnKato.dxk, dcoord]
    rw [fderiv_left_eq_zero h hxy]
    simp

theorem fderiv_right_eq_zero {κ : Vd d → Vd d → ℂ} (h : GoodKernel κ) {x y : Vd d}
    (hxy : 1 / 2 < ‖x - y‖) : fderiv ℝ (fun y => κ x y) y = 0 := by
  have hev : (fun y => κ x y) =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    have hopen : IsOpen {y' : Vd d | 1 / 2 < ‖x - y'‖} :=
      isOpen_lt continuous_const (continuous_const.sub continuous_id).norm
    filter_upwards [hopen.mem_nhds hxy] with y' hy'
    exact h.supp x y' hy'
  rw [hev.fderiv_eq]
  simp

theorem GoodKernel.dyk {κ : Vd d → Vd d → ℂ} (h : GoodKernel κ) (j : Fin d) :
    GoodKernel (dyk j κ) where
  smooth := contDiff_dyk h.smooth j
  supp := by
    intro x y hxy
    simp only [BookProof.KvnKato.dyk, dcoord]
    rw [fderiv_right_eq_zero h hxy]
    simp

/-- The `y`-slice of a good kernel is compactly supported. -/
theorem GoodKernel.hasCompactSupport_right {κ : Vd d → Vd d → ℂ} (h : GoodKernel κ)
    (x : Vd d) : HasCompactSupport (fun y => κ x y) := by
  refine HasCompactSupport.intro (isCompact_closedBall x (1 / 2)) ?_
  intro y hy
  refine h.supp x y ?_
  simp only [Metric.mem_closedBall, not_le] at hy
  rwa [dist_comm, dist_eq_norm] at hy

theorem GoodKernel.integrable {κ : Vd d → Vd d → ℂ} (h : GoodKernel κ) {u : Vd d → ℂ}
    (hu : LocallyIntegrable u (volume : Measure (Vd d))) (x : Vd d) :
    Integrable (fun y => u y * κ x y) (volume : Measure (Vd d)) := by
  have hc : Continuous (fun y => κ x y) := (h.contDiff_right x).continuous
  have hcs := h.hasCompactSupport_right x
  have h1 := hu.integrableOn_isCompact hcs.isCompact
  have h2 : IntegrableOn (fun y => u y * κ x y) (tsupport fun y => κ x y) volume := by
    have := h1.mul_continuousOn hc.continuousOn hcs.isCompact
    simpa using this
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h2
  intro y hy
  have : κ x y ≠ 0 := by
    intro h0
    exact hy (by simp [h0])
  exact subset_tsupport _ this


/-- **Integral operators with good kernels produce smooth functions.** -/
theorem contDiff_kint {κ : Vd d → Vd d → ℂ} (h : GoodKernel κ) {u : Vd d → ℂ}
    (hu : LocallyIntegrable u (volume : Measure (Vd d))) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (kint u κ) := by
  set g : Vd d → Vd d → ℂ := fun p w => κ p (p - w) with hg
  have hgs : ∀ p, ∀ w, p ∈ (Set.univ : Set (Vd d)) → w ∉ Metric.closedBall (0 : Vd d) 1 →
      g p w = 0 := by
    intro p w _ hw
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hw
    refine h.supp p (p - w) ?_
    rw [sub_sub_cancel]
    linarith
  have hgsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry g)
      ((Set.univ : Set (Vd d)) ×ˢ Set.univ) := by
    have : Function.uncurry g = Function.uncurry κ ∘ fun q : Vd d × Vd d => (q.1, q.1 - q.2) := by
      funext q
      rfl
    rw [this]
    exact (h.smooth.comp (contDiff_fst.prodMk (contDiff_fst.sub contDiff_snd))).contDiffOn
  have hmain := contDiffOn_convolution_right_with_param_comp (μ := (volume : Measure (Vd d)))
    (ContinuousLinearMap.mul ℝ ℂ) (s := Set.univ) (v := id) contDiffOn_id isOpen_univ
    (isCompact_closedBall (0 : Vd d) 1) hgs hu hgsm
  rw [contDiffOn_univ] at hmain
  convert hmain using 1
  funext x
  simp only [kint, convolution_def, id, hg, ContinuousLinearMap.mul_apply']
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [sub_sub_cancel]

/-- The directional derivative of a differentiable function along a coordinate line. -/
theorem hasDerivAt_line (j : Fin d) {f : Vd d → ℂ} {x : Vd d} {t : ℝ}
    (hf : DifferentiableAt ℝ f (x + t • kinDir d j)) :
    HasDerivAt (fun s : ℝ => f (x + s • kinDir d j)) (dcoord j f (x + t • kinDir d j)) t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • kinDir d j) (kinDir d j) t := by
    simpa using ((hasDerivAt_id t).smul_const (kinDir d j)).const_add x
  exact hf.hasFDerivAt.comp_hasDerivAt t hl

/-- **Differentiation under the integral sign**: the coordinate derivative of `kint u κ` is
`kint u (∂ₓκ)`. -/
theorem dcoord_kint {κ : Vd d → Vd d → ℂ} (h : GoodKernel κ) {u : Vd d → ℂ}
    (hu : LocallyIntegrable u (volume : Measure (Vd d))) (j : Fin d) (x₀ : Vd d) :
    dcoord j (kint u κ) x₀ = kint u (dxk j κ) x₀ := by
  have hdj := h.dxk j
  have hcd : Continuous (Function.uncurry (dxk j κ)) := hdj.continuous
  set e : Vd d := kinDir d j
  have he : ‖e‖ ≤ 1 := by simp [e, kinDir]
  set K : Set (Vd d × Vd d) := Metric.closedBall x₀ 1 ×ˢ Metric.closedBall x₀ 2 with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hcd.continuousOn
  set M' : ℝ := max M 0
  have hu2 : IntegrableOn u (Metric.closedBall x₀ 2) volume :=
    hu.integrableOn_isCompact (isCompact_closedBall _ _)
  have hline : ∀ t : ℝ, t ∈ Metric.ball (0 : ℝ) 1 → x₀ + t • e ∈ Metric.ball x₀ 1 := by
    intro t ht
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    simp only [Metric.mem_ball, dist_self_add_left, norm_smul, Real.norm_eq_abs]
    nlinarith [norm_nonneg e, abs_nonneg t]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Vd d)))
    (F := fun t y => u y * κ (x₀ + t • e) y) (x₀ := (0 : ℝ))
    (F' := fun t y => u y * dxk j κ (x₀ + t • e) y)
    (bound := (Metric.closedBall x₀ 2).indicator (fun y => ‖u y‖ * M'))
    (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    (Filter.Eventually.of_forall fun t => (h.integrable hu _).aestronglyMeasurable)
    (h.integrable hu _) (hdj.integrable hu _).aestronglyMeasurable ?_ ?_ ?_
  · have hk : HasDerivAt (fun t : ℝ => kint u κ (x₀ + t • e)) (dcoord j (kint u κ) x₀) 0 := by
      simpa using hasDerivAt_line j (x := x₀) (t := 0)
        ((contDiff_kint h hu).differentiable (by simp) _)
    have huniq := hk.unique key.2
    rw [huniq]
    simp [kint]
  · refine Filter.Eventually.of_forall fun y t ht => ?_
    have hx := hline t ht
    by_cases hy : y ∈ Metric.closedBall x₀ 2
    · rw [Set.indicator_of_mem hy, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact (hM (x₀ + t • e, y) ⟨Metric.ball_subset_closedBall hx, hy⟩).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem hy]
      have hxy : 1 / 2 < ‖(x₀ + t • e) - y‖ := by
        simp only [Metric.mem_closedBall, not_le] at hy
        simp only [Metric.mem_ball] at hx
        have h1 : dist y x₀ ≤ dist y (x₀ + t • e) + dist (x₀ + t • e) x₀ := dist_triangle _ _ _
        have h2 : dist y (x₀ + t • e) = ‖(x₀ + t • e) - y‖ := by rw [dist_comm, dist_eq_norm]
        linarith
      show ‖u y * dxk j κ (x₀ + t • e) y‖ ≤ 0
      rw [hdj.supp _ _ hxy, mul_zero, norm_zero]
  · exact IntegrableOn.integrable_indicator
      (show IntegrableOn (fun y => ‖u y‖ * M') _ volume from hu2.norm.mul_const M')
      measurableSet_closedBall
  · refine Filter.Eventually.of_forall fun y t _ => ?_
    have hd2 : HasDerivAt (fun s : ℝ => κ (x₀ + s • e) y) (dxk j κ (x₀ + t • e) y) t :=
      hasDerivAt_line j (x := x₀) (t := t) ((h.contDiff_left y).differentiable (by simp) _)
    exact hd2.const_mul (u y)

/-! ## 3. The first-order operator `X = G·∇ + c` -/

/-- **The data of a real first-order operator** `X = ∑ᵢ Gᵢ ∂ᵢ + c` with `c = ½ div G`: then
`H = −iX` is the Koopman–von Neumann generator of the vector field `G`. -/
structure KvnData (d : ℕ) where
  /-- The vector field. -/
  G : Fin d → Vd d → ℂ
  /-- The zeroth-order term, `½ div G`. -/
  c : Vd d → ℂ
  G_smooth : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G i)
  c_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c
  G_real : ∀ i x, (starRingEnd ℂ) (G i x) = G i x
  c_real : ∀ x, (starRingEnd ℂ) (c x) = c x
  div_eq : ∀ x, ∑ i, dcoord i (G i) x = 2 * c x

variable (S : KvnData d)

/-- The operator `X f = ∑ᵢ Gᵢ ∂ᵢ f + c f` on functions. -/
def Xf (f : Vd d → ℂ) (x : Vd d) : ℂ := ∑ i, S.G i x * dcoord i f x + S.c x * f x

/-- The derivative part `G·∇f`. -/
def Df (f : Vd d → ℂ) (x : Vd d) : ℂ := ∑ i, S.G i x * dcoord i f x

theorem Xf_eq (f : Vd d → ℂ) (x : Vd d) : Xf S f x = Df S f x + S.c x * f x := rfl

theorem KvnData.G_diff (i : Fin d) : Differentiable ℝ (S.G i) :=
  (S.G_smooth i).differentiable (by simp)

theorem KvnData.c_diff : Differentiable ℝ S.c := S.c_smooth.differentiable (by simp)

theorem contDiff_Df {f : Vd d → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Df S f) :=
  ContDiff.sum fun i _ => (S.G_smooth i).mul (contDiff_dcoord hf i)

theorem contDiff_Xf {f : Vd d → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Xf S f) :=
  (contDiff_Df S hf).add (S.c_smooth.mul hf)

theorem hasCompactSupport_Xf {f : Vd d → ℂ} (hfc : HasCompactSupport f) :
    HasCompactSupport (Xf S f) := by
  have h1 : HasCompactSupport (fun x => ∑ i, S.G i x * dcoord i f x) :=
    hasCompactSupport_finsetSum _ fun i _ => (hasCompactSupport_dcoord hfc i).mul_left
  exact h1.add hfc.mul_left

/-- **Leibniz rule** `X(fg) = (G·∇f) g + f X g`. -/
theorem Xf_mul {f g : Vd d → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : Vd d) :
    Xf S (fun y => f y * g y) x = Df S f x * g x + f x * Xf S g x := by
  simp only [Xf, Df]
  simp only [dc_mul (hf x) (hg x)]
  have h1 : ∑ i, S.G i x * (dcoord i f x * g x + f x * dcoord i g x)
      = (∑ i, S.G i x * dcoord i f x) * g x + f x * ∑ i, S.G i x * dcoord i g x := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1]
  ring

/-- `X` commutes with complex conjugation (it has real coefficients). -/
theorem Xf_conj {f : Vd d → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (x : Vd d) :
    Xf S (fun y => (starRingEnd ℂ) (f y)) x = (starRingEnd ℂ) (Xf S f x) := by
  simp only [Xf, map_add, map_sum, map_mul, dcoord_conj hf, S.G_real, S.c_real]

theorem Df_conj {f : Vd d → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (x : Vd d) :
    Df S (fun y => (starRingEnd ℂ) (f y)) x = (starRingEnd ℂ) (Df S f x) := by
  simp only [Df, map_sum, map_mul, dcoord_conj hf, S.G_real]

/-- **`X` is antisymmetric**: `∫ f · X g = −∫ (X f) · g` when `f` has compact support. -/
theorem integral_mul_Xf {f g : Vd d → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ∫ x, f x * Xf S g x = -∫ x, Xf S f x * g x := by
  have hfG : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => f x * S.G i x) :=
    fun i => hf.mul (S.G_smooth i)
  have hfGc : ∀ i, HasCompactSupport (fun x => f x * S.G i x) := fun i => hfc.mul_right
  have hpt : ∀ x, f x * Xf S g x + Xf S f x * g x
      = ∑ i, ((f x * S.G i x) * dcoord i g x + dcoord i (fun x => f x * S.G i x) x * g x) := by
    intro x
    have hd : ∀ i, dcoord i (fun x => f x * S.G i x) x
        = dcoord i f x * S.G i x + f x * dcoord i (S.G i) x := fun i =>
      dc_mul (hf.differentiable (by simp) x) (S.G_diff i x) i
    simp only [hd, Xf]
    have hdiv := S.div_eq x
    have e1 : ∑ i, (f x * S.G i x * dcoord i g x
        + (dcoord i f x * S.G i x + f x * dcoord i (S.G i) x) * g x)
        = f x * ∑ i, S.G i x * dcoord i g x + (∑ i, S.G i x * dcoord i f x) * g x
          + f x * g x * ∑ i, dcoord i (S.G i) x := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, hdiv]
    ring
  have hzero : ∀ i, ∫ x, ((f x * S.G i x) * dcoord i g x
      + dcoord i (fun x => f x * S.G i x) x * g x) = 0 := by
    intro i
    have hibp := integral_dcoord_mul (hfG i) (hfGc i) hg i
    have h1 : Integrable (fun x => (f x * S.G i x) * dcoord i g x) (volume : Measure (Vd d)) :=
      integrable_of_cc ((hfG i).continuous.mul (contDiff_dcoord hg i).continuous)
        (hfGc i).mul_right
    have h2 : Integrable (fun x => dcoord i (fun x => f x * S.G i x) x * g x)
        (volume : Measure (Vd d)) :=
      integrable_of_cc ((contDiff_dcoord (hfG i) i).continuous.mul hg.continuous)
        (hasCompactSupport_dcoord (hfGc i) i).mul_right
    rw [integral_add h1 h2, hibp]
    ring
  have hA : Integrable (fun x => f x * Xf S g x) (volume : Measure (Vd d)) :=
    integrable_of_cc (hf.continuous.mul (contDiff_Xf S hg).continuous) hfc.mul_right
  have hB : Integrable (fun x => Xf S f x * g x) (volume : Measure (Vd d)) :=
    integrable_of_cc ((contDiff_Xf S hf).continuous.mul hg.continuous)
      (hasCompactSupport_Xf S hfc).mul_right
  have hsum : ∫ x, (f x * Xf S g x + Xf S f x * g x) = 0 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_finset_sum]
    · exact Finset.sum_eq_zero fun i _ => hzero i
    · intro i _
      exact (integrable_of_cc ((hfG i).continuous.mul (contDiff_dcoord hg i).continuous)
        (hfGc i).mul_right).add (integrable_of_cc
          ((contDiff_dcoord (hfG i) i).continuous.mul hg.continuous)
          (hasCompactSupport_dcoord (hfGc i) i).mul_right)
  rw [integral_add hA hB] at hsum
  linear_combination hsum


/-- Antisymmetry with the compact support on the other factor. -/
theorem integral_mul_Xf' {f g : Vd d → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g) :
    ∫ x, f x * Xf S g x = -∫ x, Xf S f x * g x := by
  have h := integral_mul_Xf S hg hgc hf
  have e1 : (fun x => f x * Xf S g x) = fun x => Xf S g x * f x := by
    funext x; ring
  have e2 : (fun x => Xf S f x * g x) = fun x => g x * Xf S f x := by
    funext x; ring
  rw [e1, e2, h]
  ring

/-! ## 4. `X` acting on kernels -/

/-- `X` acting on the first variable of a kernel. -/
def Xxk (κ : Vd d → Vd d → ℂ) (x y : Vd d) : ℂ := Xf S (fun x => κ x y) x

/-- `X` acting on the second variable of a kernel. -/
def Xyk (κ : Vd d → Vd d → ℂ) (x y : Vd d) : ℂ := Xf S (fun y => κ x y) y

theorem Xxk_eq (κ : Vd d → Vd d → ℂ) (x y : Vd d) :
    Xxk S κ x y = ∑ i, S.G i x * dxk i κ x y + S.c x * κ x y := rfl

theorem Xyk_eq (κ : Vd d → Vd d → ℂ) (x y : Vd d) :
    Xyk S κ x y = ∑ i, S.G i y * dyk i κ x y + S.c y * κ x y := rfl

theorem GoodKernel.Xxk {κ : Vd d → Vd d → ℂ} (h : GoodKernel κ) : GoodKernel (Xxk S κ) where
  smooth := by
    have heq : Function.uncurry (BookProof.KvnKato.Xxk S κ) = fun p =>
        ∑ i, S.G i p.1 * Function.uncurry (BookProof.KvnKato.dxk i κ) p + S.c p.1 * Function.uncurry κ p := by
      funext p
      rfl
    rw [heq]
    refine ContDiff.add (ContDiff.sum fun i _ => ?_) ?_
    · exact ((S.G_smooth i).comp contDiff_fst).mul (h.dxk i).smooth
    · exact (S.c_smooth.comp contDiff_fst).mul h.smooth
  supp := by
    intro x y hxy
    rw [Xxk_eq]
    simp [(h.dxk _).supp x y hxy, h.supp x y hxy]

theorem GoodKernel.Xyk {κ : Vd d → Vd d → ℂ} (h : GoodKernel κ) : GoodKernel (Xyk S κ) where
  smooth := by
    have heq : Function.uncurry (BookProof.KvnKato.Xyk S κ) = fun p =>
        ∑ i, S.G i p.2 * Function.uncurry (BookProof.KvnKato.dyk i κ) p + S.c p.2 * Function.uncurry κ p := by
      funext p
      rfl
    rw [heq]
    refine ContDiff.add (ContDiff.sum fun i _ => ?_) ?_
    · exact ((S.G_smooth i).comp contDiff_snd).mul (h.dyk i).smooth
    · exact (S.c_smooth.comp contDiff_snd).mul h.smooth
  supp := by
    intro x y hxy
    rw [Xyk_eq]
    simp [(h.dyk _).supp x y hxy, h.supp x y hxy]

theorem GoodKernel.add {κ κ' : Vd d → Vd d → ℂ} (h : GoodKernel κ) (h' : GoodKernel κ') :
    GoodKernel (κ + κ') where
  smooth := by
    have heq : Function.uncurry (κ + κ') = Function.uncurry κ + Function.uncurry κ' := by
      funext p; rfl
    rw [heq]
    exact h.smooth.add h'.smooth
  supp := by
    intro x y hxy
    simp [h.supp x y hxy, h'.supp x y hxy]

theorem kint_add {κ κ' : Vd d → Vd d → ℂ} (h : GoodKernel κ) (h' : GoodKernel κ') {u : Vd d → ℂ}
    (hu : LocallyIntegrable u (volume : Measure (Vd d))) (x : Vd d) :
    kint u (κ + κ') x = kint u κ x + kint u κ' x := by
  simp only [kint, Pi.add_apply, mul_add]
  exact integral_add (h.integrable hu x) (h'.integrable hu x)

/-- **`X` commutes with the integral operator** in the sense `X (kint u κ) = kint u (Xₓ κ)`. -/
theorem Xf_kint {κ : Vd d → Vd d → ℂ} (h : GoodKernel κ) {u : Vd d → ℂ}
    (hu : LocallyIntegrable u (volume : Measure (Vd d))) (x : Vd d) :
    Xf S (kint u κ) x = kint u (Xxk S κ) x := by
  simp only [Xf, dcoord_kint h hu]
  have hint : ∀ i, Integrable (fun y => u y * (S.G i x * dxk i κ x y)) (volume : Measure (Vd d)) :=
    fun i => by
      have := ((h.dxk i).integrable hu x).const_mul (S.G i x)
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only
      ring
  have hint2 : Integrable (fun y => u y * (S.c x * κ x y)) (volume : Measure (Vd d)) := by
    have := (h.integrable hu x).const_mul (S.c x)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  simp only [kint, Xxk_eq, mul_add, Finset.mul_sum]
  rw [integral_add (integrable_finset_sum _ fun i _ => hint i) hint2,
    integral_finset_sum _ fun i _ => hint i]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  · rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring


/-! ## 5. Mixed partial derivatives of kernels commute -/

theorem dyk_eq_fderiv {κ : Vd d → Vd d → ℂ}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry κ)) (j : Fin d) (x y : Vd d) :
    dyk j κ x y = fderiv ℝ (Function.uncurry κ) (x, y) (0, kinDir d j) := by
  simp only [dyk, dcoord]
  rw [fderiv_right_eq h x y]
  simp

theorem dxk_eq_fderiv {κ : Vd d → Vd d → ℂ}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry κ)) (j : Fin d) (x y : Vd d) :
    dxk j κ x y = fderiv ℝ (Function.uncurry κ) (x, y) (kinDir d j, 0) := by
  simp only [dxk, dcoord]
  rw [fderiv_left_eq h x y]
  simp

/-- **Mixed partial derivatives of a smooth kernel commute.** -/
theorem dxk_dyk_comm {κ : Vd d → Vd d → ℂ}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry κ)) (i j : Fin d) (x y : Vd d) :
    dxk i (dyk j κ) x y = dyk j (dxk i κ) x y := by
  set F := fderiv ℝ (Function.uncurry κ) with hF
  have hFd : Differentiable ℝ F :=
    (h.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl).differentiable (by simp)
  have e1 : dxk i (dyk j κ) x y = fderiv ℝ F (x, y) (kinDir d i, 0) (0, kinDir d j) := by
    have hfun : (fun x' => dyk j κ x' y) = fun x' => F (x', y) (0, kinDir d j) := by
      funext x'
      exact dyk_eq_fderiv h j x' y
    simp only [dxk, dcoord]
    rw [hfun]
    have hd : HasFDerivAt (fun x' : Vd d => F (x', y))
        ((fderiv ℝ F (x, y)).comp (ContinuousLinearMap.inl ℝ (Vd d) (Vd d))) x :=
      (hFd (x, y)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x y)
    have hd2 := hd.clm_apply (hasFDerivAt_const ((0, kinDir d j) : Vd d × Vd d) x)
    rw [hd2.fderiv]
    simp
  have e2 : dyk j (dxk i κ) x y = fderiv ℝ F (x, y) (0, kinDir d j) (kinDir d i, 0) := by
    have hfun : (fun y' => dxk i κ x y') = fun y' => F (x, y') (kinDir d i, 0) := by
      funext y'
      exact dxk_eq_fderiv h i x y'
    simp only [dyk, dcoord]
    rw [hfun]
    have hd : HasFDerivAt (fun y' : Vd d => F (x, y'))
        ((fderiv ℝ F (x, y)).comp (ContinuousLinearMap.inr ℝ (Vd d) (Vd d))) y :=
      (hFd (x, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)
    have hd2 := hd.clm_apply (hasFDerivAt_const ((kinDir d i, 0) : Vd d × Vd d) y)
    rw [hd2.fderiv]
    simp
  rw [e1, e2]
  exact (h.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)) _ _

theorem differentiable_left {κ : Vd d → Vd d → ℂ}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry κ)) (y : Vd d) :
    Differentiable ℝ (fun x => κ x y) :=
  (h.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)

theorem differentiable_right {κ : Vd d → Vd d → ℂ}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry κ)) (x : Vd d) :
    Differentiable ℝ (fun y => κ x y) :=
  (h.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)

/-- The algebra behind `Xxk_Xyk_comm`. -/
theorem alg_comm (a b : Fin d → ℂ) (A : Fin d → Fin d → ℂ) (Bx By : Fin d → ℂ) (cx cy k : ℂ) :
    ∑ i, a i * (∑ j, b j * A i j + cy * Bx i) + cx * (∑ j, b j * By j + cy * k)
      = ∑ j, b j * (∑ i, a i * A i j + cx * By j) + cy * (∑ i, a i * Bx i + cx * k) := by
  have h1 : ∑ i, a i * (∑ j, b j * A i j + cy * Bx i)
      = ∑ i, ∑ j, a i * b j * A i j + cy * ∑ i, a i * Bx i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · ring
  have h2 : ∑ j, b j * (∑ i, a i * A i j + cx * By j)
      = ∑ j, ∑ i, a i * b j * A i j + cx * ∑ j, b j * By j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · ring
  rw [h1, h2, Finset.sum_comm (f := fun j i => a i * b j * A i j)]
  ring

/-- **`Xₓ` and `X_y` commute** on smooth kernels. -/
theorem Xxk_Xyk_comm {κ : Vd d → Vd d → ℂ}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry κ)) (x y : Vd d) :
    Xxk S (Xyk S κ) x y = Xyk S (Xxk S κ) x y := by
  have hdy : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (dyk j κ)) :=
    fun j => contDiff_dyk h j
  have hdx : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (dxk j κ)) :=
    fun j => contDiff_dxk h j
  have e1 : ∀ i, dxk i (Xyk S κ) x y
      = ∑ j, S.G j y * dxk i (dyk j κ) x y + S.c y * dxk i κ x y := by
    intro i
    have hfun : (fun x' => Xyk S κ x' y)
        = fun x' => ∑ j, S.G j y * dyk j κ x' y + S.c y * κ x' y := by
      funext x'; rfl
    have hd1 : ∀ j, Differentiable ℝ (fun x' => dyk j κ x' y) :=
      fun j => differentiable_left (hdy j) y
    have hd0 : Differentiable ℝ (fun x' => κ x' y) := differentiable_left h y
    simp only [dxk]
    rw [hfun, dc_add (by fun_prop) (by fun_prop), dc_sum _ (fun j _ => by fun_prop)]
    simp only [dc_const_mul _ (hd1 _ x), dc_const_mul _ (hd0 x)]
  have e2 : ∀ j, dyk j (Xxk S κ) x y
      = ∑ i, S.G i x * dyk j (dxk i κ) x y + S.c x * dyk j κ x y := by
    intro j
    have hfun : (fun y' => Xxk S κ x y')
        = fun y' => ∑ i, S.G i x * dxk i κ x y' + S.c x * κ x y' := by
      funext y'; rfl
    have hd1 : ∀ i, Differentiable ℝ (fun y' => dxk i κ x y') :=
      fun i => differentiable_right (hdx i) x
    have hd0 : Differentiable ℝ (fun y' => κ x y') := differentiable_right h x
    simp only [dyk]
    rw [hfun, dc_add (by fun_prop) (by fun_prop), dc_sum _ (fun i _ => by fun_prop)]
    simp only [dc_const_mul _ (hd1 _ y), dc_const_mul _ (hd0 y)]
  rw [Xxk_eq, Xyk_eq]
  simp only [e1, e2, dxk_dyk_comm h, Xyk_eq, Xxk_eq]
  exact alg_comm (fun i => S.G i x) (fun j => S.G j y) (fun i j => dyk j (dxk i κ) x y)
    (fun i => dxk i κ x y) (fun j => dyk j κ x y) (S.c x) (S.c y) (κ x y)


theorem Xxk_add {κ κ' : Vd d → Vd d → ℂ}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry κ))
    (h' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry κ')) (x y : Vd d) :
    Xxk S (κ + κ') x y = Xxk S κ x y + Xxk S κ' x y := by
  have hd := differentiable_left h y
  have hd' := differentiable_left h' y
  simp only [Xxk_eq, dxk, Pi.add_apply]
  have e : ∀ i, dcoord i (fun x => κ x y + κ' x y) x = dcoord i (fun x => κ x y) x
      + dcoord i (fun x => κ' x y) x := fun i => dc_add (hd x) (hd' x) i
  simp only [e, mul_add, Finset.sum_add_distrib]
  ring

theorem Xyk_add {κ κ' : Vd d → Vd d → ℂ}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry κ))
    (h' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry κ')) (x y : Vd d) :
    Xyk S (κ + κ') x y = Xyk S κ x y + Xyk S κ' x y := by
  have hd := differentiable_right h x
  have hd' := differentiable_right h' x
  simp only [Xyk_eq, dyk, Pi.add_apply]
  have e : ∀ i, dcoord i (fun y => κ x y + κ' x y) y = dcoord i (fun y => κ x y) y
      + dcoord i (fun y => κ' x y) y := fun i => dc_add (hd y) (hd' y) i
  simp only [e, mul_add, Finset.sum_add_distrib]
  ring

/-! ## 6. The mollifier kernels -/

/-- The mollifier kernel `κ₀(x, y) = ρ(x − y)`. -/
def kz (ρ : Vd d → ℂ) (x y : Vd d) : ℂ := ρ (x - y)

/-- The first commutator kernel `k₁ = (Xₓ + X_y) κ₀`. -/
def k1 (ρ : Vd d → ℂ) : Vd d → Vd d → ℂ := Xxk S (kz ρ) + Xyk S (kz ρ)

/-- The second commutator kernel `k₂ = (Xₓ + X_y) k₁`. -/
def k2 (ρ : Vd d → ℂ) : Vd d → Vd d → ℂ := Xxk S (k1 S ρ) + Xyk S (k1 S ρ)

/-- The potential commutator kernel `(E(x) − E(y)) ρ(x − y)`. -/
def ek (E ρ : Vd d → ℂ) (x y : Vd d) : ℂ := (E x - E y) * ρ (x - y)

theorem goodKernel_kz {ρ : Vd d → ℂ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hρs : ∀ z, 1 / 2 < ‖z‖ → ρ z = 0) : GoodKernel (kz ρ) where
  smooth := by
    have : Function.uncurry (kz ρ) = fun p : Vd d × Vd d => ρ (p.1 - p.2) := by
      funext p; rfl
    rw [this]
    exact hρ.comp (contDiff_fst.sub contDiff_snd)
  supp := fun x y h => hρs (x - y) h

theorem goodKernel_k1 {ρ : Vd d → ℂ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hρs : ∀ z, 1 / 2 < ‖z‖ → ρ z = 0) : GoodKernel (k1 S ρ) :=
  ((goodKernel_kz hρ hρs).Xxk S).add ((goodKernel_kz hρ hρs).Xyk S)

theorem goodKernel_k2 {ρ : Vd d → ℂ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hρs : ∀ z, 1 / 2 < ‖z‖ → ρ z = 0) : GoodKernel (k2 S ρ) :=
  ((goodKernel_k1 S hρ hρs).Xxk S).add ((goodKernel_k1 S hρ hρs).Xyk S)

theorem goodKernel_ek {E ρ : Vd d → ℂ} (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hρs : ∀ z, 1 / 2 < ‖z‖ → ρ z = 0) : GoodKernel (ek E ρ) where
  smooth := by
    have : Function.uncurry (ek E ρ) = fun p : Vd d × Vd d => (E p.1 - E p.2) * ρ (p.1 - p.2) := by
      funext p; rfl
    rw [this]
    exact ((hE.comp contDiff_fst).sub (hE.comp contDiff_snd)).mul
      (hρ.comp (contDiff_fst.sub contDiff_snd))
  supp := fun x y h => by simp [ek, hρs (x - y) h]

/-- **The kernel identity** behind the mollified equation:
`(Aₓ − A_y) κ₀ = −2 Xₓ k₁ + k₂ + (E(x) − E(y)) κ₀` with `A = −X² + E`. -/
theorem kernel_identity {E ρ : Vd d → ℂ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hρs : ∀ z, 1 / 2 < ‖z‖ → ρ z = 0) (x y : Vd d) :
    (-Xxk S (Xxk S (kz ρ)) x y + E x * kz ρ x y) - (-Xyk S (Xyk S (kz ρ)) x y + E y * kz ρ x y)
      = -2 * Xxk S (k1 S ρ) x y + k2 S ρ x y + ek E ρ x y := by
  have h0 := goodKernel_kz hρ hρs
  have hX := h0.Xxk S
  have hY := h0.Xyk S
  have hcomm := Xxk_Xyk_comm S h0.smooth x y
  simp only [k2, Pi.add_apply]
  rw [k1, Xxk_add S hX.smooth hY.smooth, Xyk_add S hX.smooth hY.smooth, hcomm]
  simp only [ek, kz]
  ring


/-! ## 7. The mollified equation -/

theorem kint_congr {κ κ' : Vd d → Vd d → ℂ} {u : Vd d → ℂ} {x : Vd d}
    (h : ∀ y, κ x y = κ' x y) : kint u κ x = kint u κ' x := by
  simp only [kint, h]

/-- Linearity of `kint` in the kernel, with coefficients depending on `x`. -/
theorem kint_lin3 {κ₁ κ₂ κ₃ : Vd d → Vd d → ℂ} (h₁ : GoodKernel κ₁) (h₂ : GoodKernel κ₂)
    (h₃ : GoodKernel κ₃) {u : Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d)))
    (a₁ a₂ a₃ : ℂ) (x : Vd d) :
    kint u (fun x y => a₁ * κ₁ x y + a₂ * κ₂ x y + a₃ * κ₃ x y) x
      = a₁ * kint u κ₁ x + a₂ * kint u κ₂ x + a₃ * kint u κ₃ x := by
  have i₁ := (h₁.integrable hu x).const_mul a₁
  have i₂ := (h₂.integrable hu x).const_mul a₂
  have i₃ := (h₃.integrable hu x).const_mul a₃
  simp only [kint]
  have e : (fun y => u y * (a₁ * κ₁ x y + a₂ * κ₂ x y + a₃ * κ₃ x y))
      = fun y => a₁ * (u y * κ₁ x y) + a₂ * (u y * κ₂ x y) + a₃ * (u y * κ₃ x y) := by
    funext y; ring
  have i₁₂ : Integrable (fun y => a₁ * (u y * κ₁ x y) + a₂ * (u y * κ₂ x y)) volume :=
    i₁.add i₂
  rw [e, integral_add i₁₂ i₃, integral_add i₁ i₂, integral_const_mul,
    integral_const_mul, integral_const_mul]

/-- The operator `A = −X² + E` on functions. -/
def Af (E φ : Vd d → ℂ) (y : Vd d) : ℂ := -Xf S (Xf S φ) y + E y * φ y

theorem Af_conj {E φ : Vd d → ℂ} (hEr : ∀ y, (starRingEnd ℂ) (E y) = E y)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (y : Vd d) :
    (starRingEnd ℂ) (Af S E φ y) = Af S E (fun y => (starRingEnd ℂ) (φ y)) y := by
  have h1 : Xf S (fun y => (starRingEnd ℂ) (φ y)) = fun y => (starRingEnd ℂ) (Xf S φ y) := by
    funext y; exact Xf_conj S hφ y
  simp only [Af, map_add, map_neg, map_mul, hEr, h1, Xf_conj S (contDiff_Xf S hφ)]

/-- The kernel of `A` acting on the second variable of `κ₀`. -/
def ayk (E ρ : Vd d → ℂ) (x y : Vd d) : ℂ := -Xyk S (Xyk S (kz ρ)) x y + E y * kz ρ x y

theorem goodKernel_ayk {E ρ : Vd d → ℂ} (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hρs : ∀ z, 1 / 2 < ‖z‖ → ρ z = 0) : GoodKernel (ayk S E ρ) where
  smooth := by
    have h := (((goodKernel_kz hρ hρs).Xyk S).Xyk S).smooth
    have : Function.uncurry (ayk S E ρ) = fun p : Vd d × Vd d =>
        -Function.uncurry (Xyk S (Xyk S (kz ρ))) p + E p.2 * ρ (p.1 - p.2) := by
      funext p; rfl
    rw [this]
    exact h.neg.add ((hE.comp contDiff_snd).mul (hρ.comp (contDiff_fst.sub contDiff_snd)))
  supp := fun x y hxy => by
    simp [ayk, (((goodKernel_kz hρ hρs).Xyk S).Xyk S).supp x y hxy, kz, hρs (x - y) hxy]

/-- **The mollified deficiency equation.**  If `u` solves `(A − z̄)u = 0` weakly against
compactly supported smooth test functions (`A = −X² + E`, `X = G·∇ + ½ div G`), then its
mollification `v = kint u κ₀` satisfies, pointwise,
`A v − z v = −2 X (kint u k₁) + kint u k₂ + kint u (E(x) − E(y))κ₀`. -/
theorem mollified_identity {E : Vd d → ℂ} (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E)
    (hEr : ∀ y, (starRingEnd ℂ) (E y) = E y) {u : Vd d → ℂ}
    (hu : LocallyIntegrable u (volume : Measure (Vd d))) {z : ℂ}
    (hweak : ∀ φ : Vd d → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∫ y, (starRingEnd ℂ) (Af S E φ y) * u y = z * ∫ y, (starRingEnd ℂ) (φ y) * u y)
    {ρ : Vd d → ℂ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hρs : ∀ z, 1 / 2 < ‖z‖ → ρ z = 0) (hρr : ∀ z, (starRingEnd ℂ) (ρ z) = ρ z) (x : Vd d) :
    Af S E (kint u (kz ρ)) x - z * kint u (kz ρ) x
      = -2 * Xf S (kint u (k1 S ρ)) x + kint u (k2 S ρ) x + kint u (ek E ρ) x := by
  have h0 := goodKernel_kz hρ hρs
  have hXX := (h0.Xxk S).Xxk S
  have hAy := goodKernel_ayk S hE hρ hρs
  -- the weak equation at the test function `y ↦ ρ(x − y)`
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => kz ρ x y) := h0.contDiff_right x
  have hψc : HasCompactSupport (fun y => kz ρ x y) := h0.hasCompactSupport_right x
  have hw := hweak _ hψ hψc
  have hψr : (fun y => (starRingEnd ℂ) (kz ρ x y)) = fun y => kz ρ x y := by
    funext y; exact hρr _
  have hw' : kint u (ayk S E ρ) x = z * kint u (kz ρ) x := by
    have e1 : ∀ y, (starRingEnd ℂ) (Af S E (fun y => kz ρ x y) y) * u y
        = u y * ayk S E ρ x y := by
      intro y
      rw [Af_conj S hEr hψ, hψr]
      rw [mul_comm]
      rfl
    have e2 : ∀ y, (starRingEnd ℂ) (kz ρ x y) * u y = u y * kz ρ x y := by
      intro y; simp only [kz, hρr]; rw [mul_comm]
    simp only [e1, e2] at hw
    exact hw
  -- the left side as an integral
  have hXv : Xf S (kint u (kz ρ)) = kint u (Xxk S (kz ρ)) := by
    funext y; exact Xf_kint S h0 hu y
  have hL : Af S E (kint u (kz ρ)) x - z * kint u (kz ρ) x
      = kint u (fun x' y => (-1) * Xxk S (Xxk S (kz ρ)) x' y + E x * kz ρ x' y
          + (-1) * ayk S E ρ x' y) x := by
    rw [kint_lin3 hXX h0 hAy hu, Af, hXv, Xf_kint S (h0.Xxk S) hu, hw']
    ring
  have hR : -2 * Xf S (kint u (k1 S ρ)) x + kint u (k2 S ρ) x + kint u (ek E ρ) x
      = kint u (fun x y => (-2) * Xxk S (k1 S ρ) x y + 1 * k2 S ρ x y + 1 * ek E ρ x y) x := by
    rw [kint_lin3 ((goodKernel_k1 S hρ hρs).Xxk S) (goodKernel_k2 S hρ hρs)
      (goodKernel_ek hE hρ hρs) hu, Xf_kint S (goodKernel_k1 S hρ hρs) hu]
    ring
  rw [hL, hR]
  refine kint_congr fun y => ?_
  have hk := kernel_identity S (E := E) hρ hρs x y
  simp only [ayk]
  linear_combination hk

end

end BookProof.KvnKato
