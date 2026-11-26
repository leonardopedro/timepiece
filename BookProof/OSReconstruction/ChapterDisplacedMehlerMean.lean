import Mathlib
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Chapter DisplacedMehlerMean — H6 Route A at the Gaussian reference level

Route A of H6 replaces the reference measure by a Gaussian centered at the Higgs vacuum `v`
and studies the fluctuating field `h = φ − v`.  This chapter proves the finite-dimensional
part of that replacement: the displaced Gaussian is the pushforward of the centered one by
translation, its mean is exactly `v`, and the fluctuation has mean zero and the unchanged
variance.  The density of the displaced reference is strictly positive everywhere, which is
the density-level form of "the shifted reference maintains positive overlap with the ground
state".

This is the Gaussian-reference half of the Route A acceptance item only.  It does not
conjugate the interacting Hamiltonian by a Weyl displacement, does not construct the
nested-Fock vacuum `Ω_v`, and does not address infinite-volume sector inequivalence (H5).
-/

noncomputable section

namespace BookProof.DisplacedMehlerMean

open MeasureTheory ProbabilityTheory

/-- The Gaussian centered at `v` is the centered Gaussian translated by `v`. -/
theorem displaced_reference_eq_map (v : ℝ) (σ : NNReal) :
    (gaussianReal 0 σ).map (fun x : ℝ => x + v) = gaussianReal v σ := by
  simpa using (gaussianReal_map_add_const (μ := 0) (v := σ) v)

/-- Integrating against the displaced reference equals integrating the translated observable
    against the centered reference.  This is the Route A change of variables `φ = v + h`. -/
theorem integral_displaced {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ) (σ : NNReal) (f : ℝ → E)
    (hf : AEStronglyMeasurable f (gaussianReal v σ)) :
    (∫ x, f x ∂gaussianReal v σ) = ∫ x, f (x + v) ∂gaussianReal 0 σ := by
  rw [← displaced_reference_eq_map v σ]
  have hf' : AEStronglyMeasurable f
      (Measure.map (fun x : ℝ => x + v) (gaussianReal 0 σ)) := by
    simpa [displaced_reference_eq_map v σ] using hf
  exact integral_map (by fun_prop) hf'

/-- The mean of the displaced reference is exactly the vacuum `v`. -/
theorem displaced_reference_mean (v : ℝ) (σ : NNReal) :
    (∫ x : ℝ, x ∂gaussianReal v σ) = v := by
  simp

/-- The fluctuating field `h = φ − v` has zero mean under the displaced reference. -/
theorem shifted_field_mean_zero (v : ℝ) (σ : NNReal) :
    (∫ x : ℝ, (x - v) ∂gaussianReal v σ) = 0 := by
  rw [← integral_map (by fun_prop : AEMeasurable (fun x : ℝ => x - v) (gaussianReal v σ))
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x)
        (Measure.map (fun x : ℝ => x - v) (gaussianReal v σ)))]
  rw [gaussianReal_map_sub_const]
  simp

/-- Translation does not change the variance of the fluctuation. -/
theorem shifted_field_variance (v : ℝ) (σ : NNReal) :
    Var[fun x : ℝ => x - v; gaussianReal v σ] = (σ : ℝ) := by
  rw [← displaced_reference_eq_map v σ]
  rw [variance_map (by fun_prop) (by fun_prop)]
  have hf : (fun x : ℝ => x - v) ∘ (fun x : ℝ => x + v) = fun x => x := by
    funext x
    simp [Function.comp_apply]
  rw [hf]
  simp

/-- At nonzero variance the displaced reference density is strictly positive everywhere:
    the density-level form of positive overlap with the shifted vacuum. -/
theorem displaced_pdf_pos (v x : ℝ) {σ : NNReal} (hσ : σ ≠ 0) :
    0 < gaussianPDFReal v σ x :=
  gaussianPDFReal_pos v σ x hσ

end BookProof.DisplacedMehlerMean
