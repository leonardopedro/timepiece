import Mathlib
import BookProof.ChapterDegSchrodingerCore

/-!
# Mollification as a convolution: smoothness and derivatives

The Kato-type theorem of `BookProof/ChapterDegKatoEsa.lean` mollifies an `L²` deficiency
vector.  This module records the two calculus facts that the mollification needs:

* `contDiff_cnv` — the convolution of a locally integrable function with a compactly
  supported smooth function is smooth;
* `dcoord_cnv`, `lapCS_cnv` — every derivative falls on the smooth factor.

The convolution is written `cnv u ρ x = ∫ u y * ρ (x − y)`, i.e. Mathlib's
`convolution u ρ (ContinuousLinearMap.mul ℝ ℂ) volume`, so that `cnv u ρ x` is literally the
pairing of `u` with the test function `y ↦ ρ (x − y)`.
-/

namespace BookProof.ConvolutionCalc

open MeasureTheory
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegSchrodinger

noncomputable section

variable {d : ℕ}

/-- The convolution `cnv u ρ x = ∫ u y · ρ (x − y)`: the pairing of `u` with the translated
test function `y ↦ ρ (x − y)`. -/
def cnv (u ρ : Vd d → ℂ) : Vd d → ℂ :=
  convolution u ρ (ContinuousLinearMap.mul ℝ ℂ) volume

theorem cnv_apply (u ρ : Vd d → ℂ) (x : Vd d) : cnv u ρ x = ∫ y, u y * ρ (x - y) := rfl

/-- The convolution of a locally integrable function with a compactly supported smooth
function is smooth. -/
theorem contDiff_cnv {u ρ : Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d)))
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hc : HasCompactSupport ρ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cnv u ρ) :=
  hc.contDiff_convolution_right _ hu hρ

/-- A directional derivative of a compactly supported smooth function has compact support. -/
theorem hasCompactSupport_dcoord {ρ : Vd d → ℂ}
    (hc : HasCompactSupport ρ) (j : Fin d) : HasCompactSupport (dcoord j ρ) := by
  refine (hc.fderiv ℝ).mono ?_
  intro x hx
  simp only [Function.mem_support, dcoord] at hx ⊢
  intro h
  exact hx (by rw [h]; simp)

/-- A finite sum of compactly supported functions has compact support. -/
theorem hasCompactSupport_finsetSum {ι : Type*} (s : Finset ι) {f : ι → Vd d → ℂ}
    (h : ∀ i ∈ s, HasCompactSupport (f i)) : HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (HasCompactSupport.zero : HasCompactSupport (fun _ : Vd d => (0 : ℂ)))
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (h i (by simp)).add (ih fun j hj => h j (by simp [hj]))

/-- **Derivatives fall on the smooth factor.** -/
theorem dcoord_cnv {u ρ : Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d)))
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hc : HasCompactSupport ρ) (j : Fin d) :
    dcoord j (cnv u ρ) = cnv u (dcoord j ρ) := by
  funext x
  have h1 : HasFDerivAt (cnv u ρ)
      ((convolution u (fderiv ℝ ρ) ((ContinuousLinearMap.mul ℝ ℂ).precompR (Vd d)) volume) x) x :=
    hc.hasFDerivAt_convolution_right _ hu (hρ.of_le (by exact_mod_cast le_top)) x
  simp only [dcoord]
  rw [h1.fderiv]
  exact convolution_precompR_apply _ hu (hc.fderiv ℝ) (hρ.continuous_fderiv (by simp)) x _

/-- The convolution integrand is integrable. -/
theorem integrable_cnv_integrand {u g : Vd d → ℂ}
    (hu : LocallyIntegrable u (volume : Measure (Vd d))) (hg : Continuous g)
    (hgc : HasCompactSupport g) (x : Vd d) :
    Integrable (fun y => u y * g (x - y)) (volume : Measure (Vd d)) :=
  hgc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ) hu hg x

/-- The convolution is additive in the smooth factor. -/
theorem cnv_finset_sum {ι : Type*} (s : Finset ι) {u : Vd d → ℂ} {g : ι → Vd d → ℂ}
    (hu : LocallyIntegrable u (volume : Measure (Vd d)))
    (hg : ∀ i ∈ s, Continuous (g i)) (hgc : ∀ i ∈ s, HasCompactSupport (g i)) (x : Vd d) :
    cnv u (fun y => ∑ i ∈ s, g i y) x = ∑ i ∈ s, cnv u (g i) x := by
  classical
  have hint : ∀ i ∈ s, Integrable (fun y => u y * g i (x - y)) (volume : Measure (Vd d)) := by
    intro i hi
    exact (hgc i hi).convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ) hu (hg i hi) x
  simp only [cnv_apply]
  rw [← MeasureTheory.integral_finset_sum s hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [Finset.mul_sum]

/-- **The partial Laplacian falls on the smooth factor.** -/
theorem lapCS_cnv {u ρ : Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d)))
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hc : HasCompactSupport ρ)
    (S : Finset (Fin d)) (x : Vd d) :
    lapCS S (cnv u ρ) x = cnv u (lapCS S ρ) x := by
  have hd : ∀ j : Fin d, dcoord j (dcoord j (cnv u ρ)) = cnv u (dcoord j (dcoord j ρ)) := by
    intro j
    rw [dcoord_cnv hu hρ hc j,
      dcoord_cnv hu (contDiff_dcoord hρ j) (hasCompactSupport_dcoord hc j) j]
  have hsum := cnv_finset_sum (u := u) (g := fun j => dcoord j (dcoord j ρ)) S hu
    (fun j _ => (contDiff_dcoord (contDiff_dcoord hρ j) j).continuous)
    (fun j _ => hasCompactSupport_dcoord (hasCompactSupport_dcoord hc j) j) x
  have hlap : (lapCS S ρ) = fun y => ∑ i ∈ S, dcoord i (dcoord i ρ) y := rfl
  simp only [lapCS]
  rw [hlap, hsum]
  exact Finset.sum_congr rfl fun j _ => congrFun (hd j) x

/-! ## Reflected test functions -/

/-- Differentiating the reflected function `y ↦ g (x − y)` flips the sign. -/
theorem dcoord_reflect {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (x : Vd d)
    (j : Fin d) : dcoord j (fun y => g (x - y)) = fun y => -(dcoord j g (x - y)) := by
  funext y
  have hA : HasFDerivAt (fun y : Vd d => x - y) (-(ContinuousLinearMap.id ℝ (Vd d))) y := by
    simpa using (hasFDerivAt_const (𝕜 := ℝ) x y).sub (hasFDerivAt_id y)
  have hgd : HasFDerivAt g (fderiv ℝ g (x - y)) (x - y) :=
    (hg.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp : HasFDerivAt (fun y : Vd d => g (x - y))
      ((fderiv ℝ g (x - y)).comp (-(ContinuousLinearMap.id ℝ (Vd d)))) y := hgd.comp y hA
  simp only [dcoord]
  rw [hcomp.fderiv]
  simp

/-- The partial Laplacian commutes with reflection. -/
theorem lapCS_reflect {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (x : Vd d)
    (S : Finset (Fin d)) (y : Vd d) :
    lapCS S (fun y => g (x - y)) y = lapCS S g (x - y) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : dcoord j (fun y => g (x - y)) = fun y => (-(dcoord j g)) (x - y) := by
    rw [dcoord_reflect hg x j]
    funext w
    simp
  have h2 : dcoord j (fun y => (-(dcoord j g)) (x - y))
      = fun y => -(dcoord j (-(dcoord j g)) (x - y)) :=
    dcoord_reflect ((contDiff_dcoord hg j).neg) x j
  rw [h1, h2]
  have h3 : dcoord j (-(dcoord j g)) = -(dcoord j (dcoord j g)) := by
    funext w
    simp only [dcoord, Pi.neg_apply]
    rw [fderiv_neg]
    simp
  rw [h3]
  simp

end

end BookProof.ConvolutionCalc
