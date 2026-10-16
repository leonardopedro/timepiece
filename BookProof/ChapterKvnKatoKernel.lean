import Mathlib
import BookProof.ChapterKvnKatoMol

/-!
# Explicit formulas for the commutator kernels of the Kato argument

For a smooth mollifier `ρ`, the commutator kernels `k₁ = (Xₓ + X_y) ρ(x − y)` and
`k₂ = (Xₓ + X_y) k₁` are written out explicitly.  The point of the formulas is the
cancellation they exhibit: every derivative of `ρ` comes multiplied by a difference
`G(x) − G(y)` of the coefficients.
-/

namespace BookProof.KvnKato

open MeasureTheory Filter Topology
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegEnergy
open BookProof.ConvolutionCalc BookProof.DegKatoEsa
open scoped ENNReal

noncomputable section

variable {d : ℕ} (S : KvnData d)

/-- **The first commutator kernel**, explicitly. -/
theorem k1_eq {ρ : Vd d → ℂ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (x y : Vd d) :
    k1 S ρ x y = ∑ i, (S.G i x - S.G i y) * dcoord i ρ (x - y)
      + (S.c x + S.c y) * ρ (x - y) := by
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by simp)
  simp only [k1, Pi.add_apply, Xxk_eq, Xyk_eq, dxk, dyk, kz, dc_comp_sub,
    dc_reflect x y (hρd (x - y))]
  have e : ∑ i, (S.G i x - S.G i y) * dcoord i ρ (x - y)
      = ∑ i, S.G i x * dcoord i ρ (x - y) + ∑ i, S.G i y * -dcoord i ρ (x - y) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  ring

theorem k2_eq (ρ : Vd d → ℂ) (x y : Vd d) :
    k2 S ρ x y = ∑ j, (S.G j x * dxk j (k1 S ρ) x y + S.G j y * dyk j (k1 S ρ) x y)
      + (S.c x + S.c y) * k1 S ρ x y := by
  simp only [k2, Pi.add_apply, Xxk_eq, Xyk_eq, Finset.sum_add_distrib]
  ring

theorem dxk_k1 {ρ : Vd d → ℂ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (j : Fin d)
    (x y : Vd d) :
    dxk j (k1 S ρ) x y = ∑ i, (dcoord j (S.G i) x * dcoord i ρ (x - y)
        + (S.G i x - S.G i y) * dcoord j (dcoord i ρ) (x - y))
      + dcoord j S.c x * ρ (x - y) + (S.c x + S.c y) * dcoord j ρ (x - y) := by
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by simp)
  have hρ1 : ∀ i, Differentiable ℝ (dcoord i ρ) := fun i =>
    (contDiff_dcoord hρ i).differentiable (by simp)
  have hG : ∀ i, Differentiable ℝ (S.G i) := S.G_diff
  have hc : Differentiable ℝ S.c := S.c_diff
  have hf : (fun x => k1 S ρ x y) = fun x => ∑ i, (S.G i x - S.G i y) * dcoord i ρ (x - y)
      + (S.c x + S.c y) * ρ (x - y) := by
    funext x; exact k1_eq S hρ x y
  have hd1 : ∀ i, DifferentiableAt ℝ (fun x => (S.G i x - S.G i y) * dcoord i ρ (x - y)) x := by
    intro i; fun_prop
  have hd2 : DifferentiableAt ℝ (fun x => (S.c x + S.c y) * ρ (x - y)) x := by fun_prop
  simp only [dxk]
  have hd0 : DifferentiableAt ℝ (fun x => ∑ i, (S.G i x - S.G i y) * dcoord i ρ (x - y)) x := by
    fun_prop
  rw [hf, dc_add hd0 hd2, dc_sum _ fun i _ => hd1 i]
  simp (disch := fun_prop) only [dc_mul, dc_sub, dc_add, dc_const, dc_comp_sub, sub_zero, add_zero]
  ring

theorem dyk_k1 {ρ : Vd d → ℂ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (j : Fin d)
    (x y : Vd d) :
    dyk j (k1 S ρ) x y = ∑ i, (-(dcoord j (S.G i) y * dcoord i ρ (x - y))
        - (S.G i x - S.G i y) * dcoord j (dcoord i ρ) (x - y))
      + dcoord j S.c y * ρ (x - y) - (S.c x + S.c y) * dcoord j ρ (x - y) := by
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by simp)
  have hρ1 : ∀ i, Differentiable ℝ (dcoord i ρ) := fun i =>
    (contDiff_dcoord hρ i).differentiable (by simp)
  have hG : ∀ i, Differentiable ℝ (S.G i) := S.G_diff
  have hc : Differentiable ℝ S.c := S.c_diff
  have hf : (fun y => k1 S ρ x y) = fun y => ∑ i, (S.G i x - S.G i y) * dcoord i ρ (x - y)
      + (S.c x + S.c y) * ρ (x - y) := by
    funext y; exact k1_eq S hρ x y
  have hd1 : ∀ i, DifferentiableAt ℝ (fun y => (S.G i x - S.G i y) * dcoord i ρ (x - y)) y := by
    intro i; fun_prop
  have hd2 : DifferentiableAt ℝ (fun y => (S.c x + S.c y) * ρ (x - y)) y := by fun_prop
  have hd0 : DifferentiableAt ℝ (fun y => ∑ i, (S.G i x - S.G i y) * dcoord i ρ (x - y)) y := by
    fun_prop
  simp only [dyk]
  rw [hf, dc_add hd0 hd2, dc_sum _ fun i _ => hd1 i]
  have hr1 : ∀ i, dcoord j (fun y => dcoord i ρ (x - y)) y = -dcoord j (dcoord i ρ) (x - y) :=
    fun i => dc_reflect x y ((hρ1 i) (x - y)) j
  have hr0 : dcoord j (fun y => ρ (x - y)) y = -dcoord j ρ (x - y) :=
    dc_reflect x y (hρd (x - y)) j
  simp (disch := fun_prop) only [dc_mul, dc_sub, dc_add, dc_const, hr1, hr0, zero_sub, zero_add]
  have e : ∑ i, (-dcoord j (S.G i) y * dcoord i ρ (x - y)
      + (S.G i x - S.G i y) * -dcoord j (dcoord i ρ) (x - y))
      = ∑ i, (-(dcoord j (S.G i) y * dcoord i ρ (x - y))
        - (S.G i x - S.G i y) * dcoord j (dcoord i ρ) (x - y)) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  ring

/-- One term of `k₂`, explicitly. -/
theorem k2_term_eq {ρ : Vd d → ℂ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (j : Fin d)
    (x y : Vd d) :
    S.G j x * dxk j (k1 S ρ) x y + S.G j y * dyk j (k1 S ρ) x y
      = ∑ i, ((S.G j x * dcoord j (S.G i) x - S.G j y * dcoord j (S.G i) y) * dcoord i ρ (x - y)
          + (S.G i x - S.G i y) * (S.G j x - S.G j y) * dcoord j (dcoord i ρ) (x - y))
        + (S.G j x * dcoord j S.c x + S.G j y * dcoord j S.c y) * ρ (x - y)
        + (S.c x + S.c y) * (S.G j x - S.G j y) * dcoord j ρ (x - y) := by
  rw [dxk_k1 S hρ, dyk_k1 S hρ]
  have e : S.G j x * ∑ i, (dcoord j (S.G i) x * dcoord i ρ (x - y)
        + (S.G i x - S.G i y) * dcoord j (dcoord i ρ) (x - y))
      + S.G j y * ∑ i, (-(dcoord j (S.G i) y * dcoord i ρ (x - y))
        - (S.G i x - S.G i y) * dcoord j (dcoord i ρ) (x - y))
      = ∑ i, ((S.G j x * dcoord j (S.G i) x - S.G j y * dcoord j (S.G i) y) * dcoord i ρ (x - y)
          + (S.G i x - S.G i y) * (S.G j x - S.G j y) * dcoord j (dcoord i ρ) (x - y)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linear_combination e

/-! ## The size of the kernels -/

/-- Derivatives of a function vanish on an open set where the function vanishes. -/
theorem dcoord_eq_zero_of_eventually {f : Vd d → ℂ} {z : Vd d} (h : f =ᶠ[𝓝 z] 0) (j : Fin d) :
    dcoord j f z = 0 := by
  simp only [dcoord]
  rw [h.fderiv_eq]
  simp

theorem rhoS_vanish {s : ℝ} (hs : 0 < s) {z : Vd d} (hz : 1 / (2 * s) < ‖z‖) :
    rhoS s z = 0 ∧ (∀ i, dcoord i (rhoS s) z = 0) ∧ (∀ i j, dcoord j (dcoord i (rhoS s)) z = 0) := by
  have hopen : IsOpen {w : Vd d | 1 / (2 * s) < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have h0 : ∀ w : Vd d, 1 / (2 * s) < ‖w‖ → rhoS s w = 0 := by
    intro w hw
    by_contra h
    have h1 : rhoR s w ≠ 0 := fun h0 => h (by simp [rhoS, cx, h0])
    linarith [rhoR_supp hs h1]
  have hev : ∀ w : Vd d, 1 / (2 * s) < ‖w‖ → rhoS (d := d) s =ᶠ[𝓝 w] 0 := fun w hw =>
    Filter.eventually_of_mem (hopen.mem_nhds hw) fun v hv => h0 v hv
  have h1 : ∀ i, ∀ w : Vd d, 1 / (2 * s) < ‖w‖ → dcoord i (rhoS s) w = 0 := fun i w hw =>
    dcoord_eq_zero_of_eventually (hev w hw) i
  refine ⟨h0 z hz, fun i => h1 i z hz, fun i j => ?_⟩
  exact dcoord_eq_zero_of_eventually
    (Filter.eventually_of_mem (hopen.mem_nhds hz) fun v hv => h1 i v hv) j

theorem rhoS_bounds {M : ℝ} (hM : ∀ z : Vd d, ‖cx (rho0 d) z‖ ≤ M ∧
    (∀ j, ‖dcoord j (cx (rho0 d)) z‖ ≤ M) ∧
    (∀ i j, ‖dcoord i (dcoord j (cx (rho0 d))) z‖ ≤ M)) {s : ℝ} (hs : 0 ≤ s) (z : Vd d) :
    ‖rhoS s z‖ ≤ M * s ^ d ∧ (∀ i, ‖dcoord i (rhoS s) z‖ ≤ M * s ^ d * s) ∧
      (∀ i j, ‖dcoord j (dcoord i (rhoS s)) z‖ ≤ M * s ^ d * s * s) := by
  have hsd : 0 ≤ s ^ d := pow_nonneg hs d
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · rw [rhoS_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hsd]
    have := (hM (s • z)).1
    nlinarith
  · rw [dcoord_rhoS, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have := (hM (s • z)).2.1 i
    have h2 : 0 ≤ s ^ d * s := by positivity
    nlinarith
  · rw [dcoord_dcoord_rhoS, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have := (hM (s • z)).2.2 j i
    have h2 : 0 ≤ s ^ d * s * s := by positivity
    nlinarith

/-- Uniform Lipschitz constants for a finite family of smooth functions on a ball. -/
theorem exists_lip_family {ι : Type*} [Fintype ι] (F : ι → Vd d → ℂ)
    (hF : ∀ a, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F a)) (R : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a, ∀ x ∈ Metric.closedBall (0 : Vd d) R,
      ∀ y ∈ Metric.closedBall (0 : Vd d) R, ‖F a x - F a y‖ ≤ L * ‖x - y‖ := by
  have h : ∀ a, ∃ K : NNReal, LipschitzOnWith K (F a) (Metric.closedBall (0 : Vd d) R) :=
    fun a => (hF a).contDiffOn.exists_lipschitzOnWith (by simp) (convex_closedBall _ _)
      (isCompact_closedBall _ _)
  choose K hK using h
  refine ⟨∑ a, (K a : ℝ), by positivity, fun a x hx y hy => ?_⟩
  have h1 := (hK a).dist_le_mul x hx y hy
  rw [dist_eq_norm, dist_eq_norm] at h1
  have h2 : (K a : ℝ) ≤ ∑ a, (K a : ℝ) :=
    Finset.single_le_sum (f := fun a => (K a : ℝ)) (fun _ _ => NNReal.coe_nonneg _)
      (Finset.mem_univ a)
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

/-- Uniform bounds for a finite family of continuous functions on a ball. -/
theorem exists_bound_family {ι : Type*} [Fintype ι] (F : ι → Vd d → ℂ)
    (hF : ∀ a, Continuous (F a)) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a, ∀ x ∈ Metric.closedBall (0 : Vd d) R, ‖F a x‖ ≤ B := by
  have h : ∀ a, ∃ B, ∀ x ∈ Metric.closedBall (0 : Vd d) R, ‖F a x‖ ≤ B :=
    fun a => (isCompact_closedBall _ _).exists_bound_of_continuousOn (hF a).continuousOn
  choose B hB using h
  refine ⟨∑ a, |B a|, by positivity, fun a x hx => ?_⟩
  have h2 : |B a| ≤ ∑ a, |B a| :=
    Finset.single_le_sum (f := fun a => |B a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  exact (hB a x hx).trans ((le_abs_self _).trans h2)

/-- A finite sum of terms bounded by `b` is bounded by `d b`. -/
theorem norm_sum_fin_le {f : Fin d → ℂ} {b : ℝ} (h : ∀ i, ‖f i‖ ≤ b) :
    ‖∑ i, f i‖ ≤ d * b := by
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => h i).trans ?_
  simp

theorem norm_mul_le_of {a b : ℂ} {A B : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) : ‖a * b‖ ≤ A * B := by
  rw [norm_mul]
  exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)

/-- **Pointwise bound on `k₁`.** -/
theorem k1_bound_pt {ρ : Vd d → ℂ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) {x y : Vd d}
    {L M s : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hs : 0 ≤ s) (hrs : ‖x - y‖ * s ≤ 1)
    (hG : ∀ i, ‖S.G i x - S.G i y‖ ≤ L * ‖x - y‖) (hc : ‖S.c x + S.c y‖ ≤ L)
    (hP : ‖ρ (x - y)‖ ≤ M * s ^ d) (hPi : ∀ i, ‖dcoord i ρ (x - y)‖ ≤ M * s ^ d * s) :
    ‖k1 S ρ x y‖ ≤ (d + 1) * L * M * s ^ d := by
  have hsd : 0 ≤ s ^ d := pow_nonneg hs d
  rw [k1_eq S hρ]
  have h1 : ∀ i, ‖(S.G i x - S.G i y) * dcoord i ρ (x - y)‖ ≤ L * M * s ^ d := by
    intro i
    refine (norm_mul_le_of (hG i) (hPi i)).trans ?_
    have : L * ‖x - y‖ * (M * s ^ d * s) = L * M * s ^ d * (‖x - y‖ * s) := by ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) hrs
  have h2 := norm_sum_fin_le h1
  have h3 := norm_mul_le_of hc hP
  refine (norm_add_le _ _).trans ?_
  nlinarith

/-- **Pointwise bound on `k₂`.** -/
theorem k2_bound_pt {ρ : Vd d → ℂ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) {x y : Vd d}
    {L M s : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hs : 0 ≤ s) (hrs : ‖x - y‖ * s ≤ 1)
    (hG : ∀ i, ‖S.G i x - S.G i y‖ ≤ L * ‖x - y‖) (hc : ‖S.c x + S.c y‖ ≤ L)
    (hF : ∀ i j, ‖S.G j x * dcoord j (S.G i) x - S.G j y * dcoord j (S.G i) y‖ ≤ L * ‖x - y‖)
    (hH : ∀ j, ‖S.G j x * dcoord j S.c x + S.G j y * dcoord j S.c y‖ ≤ L)
    (hP : ‖ρ (x - y)‖ ≤ M * s ^ d) (hPi : ∀ i, ‖dcoord i ρ (x - y)‖ ≤ M * s ^ d * s)
    (hPij : ∀ i j, ‖dcoord j (dcoord i ρ) (x - y)‖ ≤ M * s ^ d * s * s) :
    ‖k2 S ρ x y‖ ≤ (d + 1) * (d + 1) * (L + L * L) * M * s ^ d := by
  have hsd : 0 ≤ s ^ d := pow_nonneg hs d
  have hr : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hT : ∀ j, ‖S.G j x * dxk j (k1 S ρ) x y + S.G j y * dyk j (k1 S ρ) x y‖
      ≤ (d + 1) * (L + L * L) * M * s ^ d := by
    intro j
    rw [k2_term_eq S hρ j]
    have h1 : ∀ i, ‖(S.G j x * dcoord j (S.G i) x - S.G j y * dcoord j (S.G i) y)
        * dcoord i ρ (x - y) + (S.G i x - S.G i y) * (S.G j x - S.G j y)
        * dcoord j (dcoord i ρ) (x - y)‖ ≤ (L + L * L) * M * s ^ d := by
      intro i
      have a1 := norm_mul_le_of (hF i j) (hPi i)
      have a2 := norm_mul_le_of (norm_mul_le_of (hG i) (hG j)) (hPij i j)
      have e1 : L * ‖x - y‖ * (M * s ^ d * s) = L * M * s ^ d * (‖x - y‖ * s) := by ring
      have e2 : L * ‖x - y‖ * (L * ‖x - y‖) * (M * s ^ d * s * s)
          = L * L * M * s ^ d * ((‖x - y‖ * s) * (‖x - y‖ * s)) := by ring
      rw [e1] at a1
      rw [e2] at a2
      have b1 : L * M * s ^ d * (‖x - y‖ * s) ≤ L * M * s ^ d :=
        mul_le_of_le_one_right (by positivity) hrs
      have b2 : L * L * M * s ^ d * ((‖x - y‖ * s) * (‖x - y‖ * s)) ≤ L * L * M * s ^ d :=
        mul_le_of_le_one_right (by positivity) (mul_le_one₀ hrs (by positivity) hrs)
      refine (norm_add_le _ _).trans ?_
      nlinarith
    have h2 := norm_sum_fin_le h1
    have h3 := norm_mul_le_of (hH j) hP
    have h4 := norm_mul_le_of (norm_mul_le_of hc (hG j)) (hPi j)
    have e4 : L * (L * ‖x - y‖) * (M * s ^ d * s) = L * L * M * s ^ d * (‖x - y‖ * s) := by ring
    rw [e4] at h4
    have b4 : L * L * M * s ^ d * (‖x - y‖ * s) ≤ L * L * M * s ^ d :=
      mul_le_of_le_one_right (by positivity) hrs
    refine (norm_add₃_le).trans ?_
    have : 0 ≤ (L + L * L) * M * s ^ d := by positivity
    nlinarith
  rw [k2_eq]
  have h5 := norm_sum_fin_le hT
  have h6 := norm_mul_le_of hc (k1_bound_pt S hρ hL hM hs hrs hG hc hP hPi)
  refine (norm_add_le _ _).trans ?_
  have : 0 ≤ (L + L * L) * M * s ^ d := by positivity
  have : 0 ≤ L * L * M * s ^ d := by positivity
  nlinarith

/-- **The kernels of the scaled mollifier are of size `sᵈ` on a ball of radius `1/(2s)`**
(and the potential commutator kernel of size `sᵈ⁻¹`), uniformly for `x` in a ball. -/
theorem exists_kernel_bounds {E : Vd d → ℂ} (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E)
    (R : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 ≤ s → ∀ x ∈ Metric.closedBall (0 : Vd d) R, ∀ y,
      ‖k1 S (rhoS s) x y‖ ≤ (Metric.closedBall (0 : Vd d) (1 / (2 * s))).indicator
          (fun _ => C * s ^ d) (x - y) ∧
      ‖k2 S (rhoS s) x y‖ ≤ (Metric.closedBall (0 : Vd d) (1 / (2 * s))).indicator
          (fun _ => C * s ^ d) (x - y) ∧
      ‖ek E (rhoS s) x y‖ ≤ (Metric.closedBall (0 : Vd d) (1 / (2 * s))).indicator
          (fun _ => C * s ^ d / s) (x - y) := by
  obtain ⟨M, hM0, hM⟩ := exists_rho0_bounds (d := d)
  obtain ⟨L1, hL1, hlip1⟩ := exists_lip_family (fun i => S.G i) S.G_smooth (R + 1)
  obtain ⟨L2, hL2, hlip2⟩ := exists_lip_family
    (fun ij : Fin d × Fin d => fun x => S.G ij.2 x * dcoord ij.2 (S.G ij.1) x)
    (fun ij => (S.G_smooth ij.2).mul (contDiff_dcoord (S.G_smooth ij.1) ij.2)) (R + 1)
  obtain ⟨L3, hL3, hlip3⟩ := exists_lip_family (fun _ : Unit => E) (fun _ => hE) (R + 1)
  obtain ⟨B1, hB1, hb1⟩ := exists_bound_family (fun _ : Unit => S.c)
    (fun _ => S.c_smooth.continuous) (R + 1)
  obtain ⟨B2, hB2, hb2⟩ := exists_bound_family
    (fun j : Fin d => fun x => S.G j x * dcoord j S.c x)
    (fun j => ((S.G_smooth j).mul (contDiff_dcoord S.c_smooth j)).continuous) (R + 1)
  set L : ℝ := L1 + L2 + L3 + 2 * B1 + 2 * B2 with hLdef
  have hL : 0 ≤ L := by positivity
  refine ⟨(d + 1) * (d + 1) * (L + L * L) * M, by positivity, fun s hs x hx y => ?_⟩
  have hs0 : 0 < s := by linarith
  have hsd : 0 ≤ s ^ d := pow_nonneg hs0.le d
  have hρ := contDiff_rhoS (d := d) s
  by_cases hxy : ‖x - y‖ ≤ 1 / (2 * s)
  · have hmem : x - y ∈ Metric.closedBall (0 : Vd d) (1 / (2 * s)) := by
      rw [mem_closedBall_zero_iff]; exact hxy
    simp only [Set.indicator_of_mem hmem]
    have hhalf : 1 / (2 * s) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hx' : x ∈ Metric.closedBall (0 : Vd d) (R + 1) := by
      rw [mem_closedBall_zero_iff] at hx ⊢; linarith
    have hy' : y ∈ Metric.closedBall (0 : Vd d) (R + 1) := by
      rw [mem_closedBall_zero_iff] at hx ⊢
      have : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by simpa using norm_sub_le x (x - y)
      linarith
    have hrs : ‖x - y‖ * s ≤ 1 := by
      have : ‖x - y‖ * s ≤ 1 / (2 * s) * s := mul_le_mul_of_nonneg_right hxy hs0.le
      have e : 1 / (2 * s) * s = 1 / 2 := by field_simp
      linarith
    have hr0 : 0 ≤ ‖x - y‖ := norm_nonneg _
    have hLle1 : L1 ≤ L := by rw [hLdef]; linarith
    have hLle2 : L2 ≤ L := by rw [hLdef]; linarith
    have hLle3 : L3 ≤ L := by rw [hLdef]; linarith
    have hG : ∀ i, ‖S.G i x - S.G i y‖ ≤ L * ‖x - y‖ := fun i =>
      (hlip1 i x hx' y hy').trans (mul_le_mul_of_nonneg_right hLle1 hr0)
    have hF : ∀ i j, ‖S.G j x * dcoord j (S.G i) x - S.G j y * dcoord j (S.G i) y‖
        ≤ L * ‖x - y‖ := fun i j =>
      (hlip2 (i, j) x hx' y hy').trans (mul_le_mul_of_nonneg_right hLle2 hr0)
    have hEl : ‖E x - E y‖ ≤ L * ‖x - y‖ :=
      (hlip3 () x hx' y hy').trans (mul_le_mul_of_nonneg_right hLle3 hr0)
    have hc : ‖S.c x + S.c y‖ ≤ L := by
      refine (norm_add_le _ _).trans ?_
      have := hb1 () x hx'
      have := hb1 () y hy'
      rw [hLdef]; linarith
    have hH : ∀ j, ‖S.G j x * dcoord j S.c x + S.G j y * dcoord j S.c y‖ ≤ L := by
      intro j
      refine (norm_add_le _ _).trans ?_
      have := hb2 j x hx'
      have := hb2 j y hy'
      rw [hLdef]; linarith
    obtain ⟨hP, hPi, hPij⟩ := rhoS_bounds hM hs0.le (x - y)
    have hk1 := k1_bound_pt S hρ hL hM0 hs0.le hrs hG hc hP hPi
    have hk2 := k2_bound_pt S hρ hL hM0 hs0.le hrs hG hc hF hH hP hPi hPij
    have hd1 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hA : (1 : ℝ) ≤ d + 1 := by linarith
    have hLL : L ≤ L + L * L := by nlinarith
    have hDL : (d + 1 : ℝ) * L ≤ (d + 1) * (d + 1) * (L + L * L) := by
      calc (d + 1 : ℝ) * L = (d + 1) * L * 1 := by ring
        _ ≤ (d + 1) * L * (d + 1) := mul_le_mul_of_nonneg_left hA (by positivity)
        _ = (d + 1) * (d + 1) * L := by ring
        _ ≤ (d + 1) * (d + 1) * (L + L * L) := mul_le_mul_of_nonneg_left hLL (by positivity)
    have hDL' : L ≤ (d + 1) * (d + 1) * (L + L * L) := by
      calc L = 1 * L := by ring
        _ ≤ (d + 1) * L := mul_le_mul_of_nonneg_right hA hL
        _ ≤ _ := hDL
    refine ⟨?_, hk2, ?_⟩
    · refine hk1.trans ?_
      have h2 : 0 ≤ M * s ^ d := by positivity
      have := mul_le_mul_of_nonneg_right hDL h2
      linarith
    · simp only [ek]
      refine (norm_mul_le_of hEl hP).trans ?_
      have h3 : L * ‖x - y‖ * (M * s ^ d) ≤ L * M * s ^ d / s := by
        rw [le_div_iff₀ hs0]
        have : L * ‖x - y‖ * (M * s ^ d) * s = L * M * s ^ d * (‖x - y‖ * s) := by ring
        rw [this]
        exact mul_le_of_le_one_right (by positivity) hrs
      refine h3.trans ?_
      rw [div_le_div_iff_of_pos_right hs0]
      have h2 : 0 ≤ M * s ^ d := by positivity
      have := mul_le_mul_of_nonneg_right hDL' h2
      linarith
  · have hnot : x - y ∉ Metric.closedBall (0 : Vd d) (1 / (2 * s)) := by
      rw [mem_closedBall_zero_iff]; exact hxy
    simp only [Set.indicator_of_notMem hnot]
    obtain ⟨h0, h1, h2⟩ := rhoS_vanish hs0 (lt_of_not_ge hxy)
    refine ⟨?_, ?_, ?_⟩
    · rw [k1_eq S hρ]; simp [h0, h1]
    · rw [k2_eq, k1_eq S hρ]; simp [k2_term_eq S hρ, h0, h1, h2]
    · simp [ek, h0]

end

end BookProof.KvnKato
