import Mathlib
import BookProof.OSReconstruction.ChapterTwoSlicePathMeasure

/-!
# Chapter ThreeSlicePathMeasure — H3's path measure, three slices

Extends `ChapterTwoSlicePathMeasure` to three transitions by nesting the path space as
`ℝ × (ℝ × ℝ)`.  The density is `K_ρ(x,z₁) K_σ(z₁,z₂) K_τ(z₂,z₃)` against the product of
Lebesgue measures, and its total mass is one by two applications of Tonelli in path order.
This establishes the recursion pattern for the general finite-slice family; the general `N`
family and the interacting weight remain open.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace BookProof.ThreeSlicePathMeasure

open MeasureTheory Filter Topology
open BookProof.MehlerTransitionDensity
open BookProof.TwoSlicePathMeasure

/-- Three-slice density on the nested path space. -/
def threeSliceDensity (ρ σ τ x : ℝ) (p : ℝ × (ℝ × ℝ)) : ENNReal :=
  ENNReal.ofReal (mehlerKernel ρ x p.1) *
    (ENNReal.ofReal (mehlerKernel σ p.1 p.2.1) *
      ENNReal.ofReal (mehlerKernel τ p.2.1 p.2.2))

/-- The three-slice path measure. -/
def threeSliceMeasure (ρ σ τ x : ℝ) : Measure (ℝ × (ℝ × ℝ)) :=
  (volume.prod (volume.prod volume)).withDensity (threeSliceDensity ρ σ τ x)

/-- Measurability of the density. -/
theorem measurable_threeSliceDensity {ρ σ τ : ℝ} (hρ : ρ ^ 2 < 1) (hσ : σ ^ 2 < 1)
    (hτ : τ ^ 2 < 1) (x : ℝ) : Measurable (threeSliceDensity ρ σ τ x) := by
  have hρd : 1 - ρ ^ 2 ≠ 0 := by linarith
  have hσd : 1 - σ ^ 2 ≠ 0 := by linarith
  have hτd : 1 - τ ^ 2 ≠ 0 := by linarith
  have c1 : Continuous (fun p : ℝ × (ℝ × ℝ) => mehlerKernel ρ x p.1) := by
    unfold mehlerKernel
    fun_prop
  have c2 : Continuous (fun p : ℝ × (ℝ × ℝ) => mehlerKernel σ p.1 p.2.1) := by
    unfold mehlerKernel
    fun_prop
  have c3 : Continuous (fun p : ℝ × (ℝ × ℝ) => mehlerKernel τ p.2.1 p.2.2) := by
    unfold mehlerKernel
    fun_prop
  exact (c1.measurable.ennreal_ofReal).mul ((c2.measurable.ennreal_ofReal).mul
    (c3.measurable.ennreal_ofReal))

/-- The three-slice path measure is a probability. -/
theorem threeSliceMeasure_univ {ρ σ τ : ℝ} (hρ : ρ ^ 2 < 1) (hσ : σ ^ 2 < 1)
    (hτ : τ ^ 2 < 1) (x : ℝ) : threeSliceMeasure ρ σ τ x Set.univ = 1 := by
  dsimp [threeSliceMeasure]
  rw [withDensity_apply _ MeasurableSet.univ]
  rw [setLIntegral_univ]
  rw [lintegral_prod (threeSliceDensity ρ σ τ x)
    (measurable_threeSliceDensity hρ hσ hτ x).aemeasurable]
  simp only [threeSliceDensity]
  have hinner : ∀ a : ℝ,
      (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (mehlerKernel ρ x a) *
        (ENNReal.ofReal (mehlerKernel σ a p.1) *
          ENNReal.ofReal (mehlerKernel τ p.1 p.2)) ∂(volume.prod volume)) =
      ENNReal.ofReal (mehlerKernel ρ x a) := by
    intro a
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [lintegral_prod]
    · simp only
      have hmid : ∀ b : ℝ,
          (∫⁻ c : ℝ, ENNReal.ofReal (mehlerKernel σ a b) *
            ENNReal.ofReal (mehlerKernel τ b c) ∂volume) =
          ENNReal.ofReal (mehlerKernel σ a b) := by
        intro b
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [mehlerKernel_lintegral hτ b]
        simp
      simp_rw [hmid]
      rw [mehlerKernel_lintegral hσ a]
      simp
    · have hσd : 1 - σ ^ 2 ≠ 0 := by linarith
      have hτd : 1 - τ ^ 2 ≠ 0 := by linarith
      have c2 : Continuous (fun p : ℝ × ℝ => mehlerKernel σ a p.1) := by
        unfold mehlerKernel
        fun_prop
      have c3 : Continuous (fun p : ℝ × ℝ => mehlerKernel τ p.1 p.2) := by
        unfold mehlerKernel
        fun_prop
      exact (c2.measurable.ennreal_ofReal.mul c3.measurable.ennreal_ofReal).aemeasurable
  simp_rw [hinner]
  rw [mehlerKernel_lintegral hρ x]

end BookProof.ThreeSlicePathMeasure
