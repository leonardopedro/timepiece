import Mathlib
import BookProof.ReflectionPositivity.ChapterMehlerTransitionDensity

/-!
# Chapter TwoSlicePathMeasure — H3's finite-slice path measure, two slices

`cftproof.md` H3 asks to assemble the one-slice kernels into a finite-slice path measure.
This module takes the first measure-valued step: the two-slice path measure on `ℝ × ℝ` with
density `K_ρ(x, z₁) · K_σ(z₁, z₂)` relative to the product of Lebesgue measures, and proves it
is a probability.  The proof uses Tonelli (`lintegral_prod`) in path order together with H1's
unit-mass theorem; no Fubini swap of integrable functions is needed because the density is
nonnegative.

The `N`-slice family, the interacting Strang weight and the `N → ∞` transfer remain open.
Axioms are `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace BookProof.TwoSlicePathMeasure

open BookProof.MehlerTransitionDensity

/-- The lintegral of the closed kernel density is one (the ENNReal form of H1's normalization). -/
theorem mehlerKernel_lintegral {ρ : ℝ} (hρ : ρ ^ 2 < 1) (x : ℝ) :
    (∫⁻ y : ℝ, ENNReal.ofReal (mehlerKernel ρ x y) ∂MeasureTheory.volume) = 1 := by
  have hdenpos : 0 < 1 - ρ ^ 2 := by linarith
  let a : ℝ := (1 - ρ ^ 2)⁻¹
  have ha : 0 < a := inv_pos.mpr hdenpos
  have hInt0 : MeasureTheory.Integrable (fun y : ℝ => Real.exp (-a * y ^ 2)) :=
    integrable_exp_neg_mul_sq ha
  have hInt1 : MeasureTheory.Integrable (fun y : ℝ => Real.exp (-a * (y - ρ * x) ^ 2)) := by
    simpa [a] using hInt0.comp_sub_right (ρ * x)
  have hEq : mehlerKernel ρ x =
      fun y : ℝ => (Real.sqrt (Real.pi * (1 - ρ ^ 2)))⁻¹ *
        Real.exp (-a * (y - ρ * x) ^ 2) := by
    funext y
    dsimp [mehlerKernel]
    congr 2
    dsimp [a]
    field_simp [ne_of_gt hdenpos]
  have hInt : MeasureTheory.Integrable (mehlerKernel ρ x) := by
    rw [hEq]
    exact hInt1.const_mul _
  have hnn : 0 ≤ᵐ[MeasureTheory.volume] mehlerKernel ρ x :=
    Filter.Eventually.of_forall (fun y => le_of_lt (mehlerKernel_pos hρ x y))
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn]
  rw [mehlerKernel_integral hρ x]
  norm_num

/-- The two-slice density and its measure. -/
def twoSliceDensity (ρ σ x : ℝ) : ℝ × ℝ → ENNReal := fun p =>
  ENNReal.ofReal (mehlerKernel ρ x p.1) * ENNReal.ofReal (mehlerKernel σ p.1 p.2)

def twoSliceMeasure (ρ σ x : ℝ) : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.prod MeasureTheory.volume).withDensity (twoSliceDensity ρ σ x)

/-- The two-slice density is measurable. -/
theorem measurable_twoSliceDensity {ρ σ : ℝ} (hρ : ρ ^ 2 < 1) (hσ : σ ^ 2 < 1) (x : ℝ) :
    Measurable (twoSliceDensity ρ σ x) := by
  have hρden : 1 - ρ ^ 2 ≠ 0 := by linarith
  have hσden : 1 - σ ^ 2 ≠ 0 := by linarith
  have hc₁ : Continuous (fun p : ℝ × ℝ => mehlerKernel ρ x p.1) := by
    unfold mehlerKernel
    fun_prop
  have hc₂ : Continuous (fun p : ℝ × ℝ => mehlerKernel σ p.1 p.2) := by
    unfold mehlerKernel
    fun_prop
  exact (hc₁.measurable.ennreal_ofReal).mul (hc₂.measurable.ennreal_ofReal)

/-- The two-slice path measure is a probability. -/
theorem twoSliceMeasure_univ {ρ σ : ℝ} (hρ : ρ ^ 2 < 1) (hσ : σ ^ 2 < 1) (x : ℝ) :
    twoSliceMeasure ρ σ x Set.univ = 1 := by
  dsimp [twoSliceMeasure]
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  rw [MeasureTheory.setLIntegral_univ]
  rw [MeasureTheory.lintegral_prod (twoSliceDensity ρ σ x)
    (measurable_twoSliceDensity hρ hσ x).aemeasurable]
  simp only [twoSliceDensity]
  have hinner : ∀ p₁ : ℝ,
      (∫⁻ p₂ : ℝ, ENNReal.ofReal (mehlerKernel ρ x p₁) *
        ENNReal.ofReal (mehlerKernel σ p₁ p₂) ∂MeasureTheory.volume) =
      ENNReal.ofReal (mehlerKernel ρ x p₁) := by
    intro p₁
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [mehlerKernel_lintegral hσ p₁]
    simp
  simp_rw [hinner]
  rw [mehlerKernel_lintegral hρ x]

end BookProof.TwoSlicePathMeasure
