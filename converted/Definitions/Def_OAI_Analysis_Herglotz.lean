/-
prove2.me platform library module `Definitions.Def_OAI_Analysis_Herglotz`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Analysis_Herglotz.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Analysis/Herglotz.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntropyPhotonNumber mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Prove2me.Shim.Poisson  -- conversion shim (platform Mathlib API)
import Prove2me.Shim.Harmonic

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal

namespace EntropyPhotonNumber.Herglotz

section Density
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def densityMeasure (f : C(X, ℝ)) : FiniteMeasure X :=
  ⟨μ.withDensity (fun x => ENNReal.ofReal (f x)),
    isFiniteMeasure_withDensity
      (f.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace f)).lintegral_lt_top.ne⟩

end Density

section WeakIntegral
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X]

end WeakIntegral

abbrev Angle := Icc (0 : ℝ) (2 * Real.pi)

local instance instMeasureSpaceElemRealAngle : MeasureSpace Angle := Measure.Subtype.measureSpace

instance : IsFiniteMeasure (volume : Measure Angle) := by
  constructor
  rw [show (volume : Measure Angle) = Measure.comap Subtype.val volume from rfl,
    Measure.comap_apply _ Subtype.val_injective
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' _
      MeasurableSet.univ]
  simpa only [image_univ, Subtype.range_coe_subtype, setOf_mem_eq] using
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi))).measure_lt_top

def RadialDensity (v : ℂ → ℝ) (R : ℝ)
    (hv : ContinuousOn v (ball 0 1)) (hR : R ∈ Ioo 0 1) : C(Angle, ℝ) where
  toFun θ := (2 * Real.pi)⁻¹ * v (circleMap 0 R θ)
  continuous_toFun := by
    apply continuous_const.mul
    apply hv.comp_continuous ((continuous_circleMap 0 R).comp continuous_subtype_val)
    intro θ
    simp only [Function.comp_apply, mem_ball, dist_zero_right, norm_circleMap_zero,
      abs_of_pos hR.1]
    exact hR.2

def radialMeasure (v : ℂ → ℝ) (R : ℝ)
    (hv : ContinuousOn v (ball 0 1)) (hR : R ∈ Ioo 0 1) : FiniteMeasure Angle :=
  densityMeasure volume (RadialDensity v R hv hR)

def radialKernel (w : ℂ) (R : ℝ) (hR : ‖w‖ < R) : C(Angle, ℝ) where
  toFun θ := (herglotzRieszKernel 0 w (circleMap 0 R θ)).re
  continuous_toFun := by
    have hn (θ : Angle) : circleMap 0 R θ - w ≠ 0 := by
      intro h
      have he := congrArg norm (sub_eq_zero.mp h)
      simp only [norm_circleMap_zero, abs_of_pos (lt_of_le_of_lt (norm_nonneg w) hR)] at he
      linarith
    simp only [herglotzRieszKernel, sub_zero]
    apply Complex.continuous_re.comp
    exact (continuous_circleMap 0 R |>.comp continuous_subtype_val |>.add continuous_const).div
      (continuous_circleMap 0 R |>.comp continuous_subtype_val |>.sub continuous_const) hn

def approachRadius (n : ℕ) : ℝ := 1 - ((n : ℝ) + 2)⁻¹

theorem approachRadius_mem (n : ℕ) : approachRadius n ∈ Ioo 0 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 < (n : ℝ) + 2 := by linarith
  have hi := (inv_lt_one₀ hp).mpr (by linarith)
  have hi' := inv_pos.mpr hp
  exact ⟨by dsimp [approachRadius]; linarith, by dsimp [approachRadius]; linarith⟩

def clippedRadius (w : ℂ) (hw : ‖w‖ < 1) (R : ℝ) : Ioi ‖w‖ :=
  ⟨max ((‖w‖ + 1) / 2) R,
    show ‖w‖ < max ((‖w‖ + 1) / 2) R from
      lt_of_lt_of_le (show ‖w‖ < (‖w‖ + 1) / 2 by linarith) (le_max_left _ _)⟩

def clippedKernel (w : ℂ) (hw : ‖w‖ < 1) (R : ℝ) : C(Angle, ℝ) :=
  radialKernel w (clippedRadius w hw R) (clippedRadius w hw R).property

def radialSequence (v : ℂ → ℝ) (hv : HarmonicOnNhd v (ball 0 1))
    (n : ℕ) : FiniteMeasure Angle :=
  radialMeasure v (approachRadius n) hv.continuousOn (approachRadius_mem n)

def diskKernel (w : ℂ) (hw : ‖w‖ < 1) : C(Angle, ℂ) where
  toFun θ := herglotzRieszKernel 0 w (circleMap 0 1 θ)
  continuous_toFun := by
    have hn (θ : Angle) : circleMap 0 1 θ - w ≠ 0 := by
      intro h
      have he := congrArg norm (sub_eq_zero.mp h)
      simp only [norm_circleMap_zero, abs_one] at he
      linarith
    simp only [herglotzRieszKernel, sub_zero]
    exact (continuous_circleMap 0 1 |>.comp continuous_subtype_val |>.add continuous_const).div
      (continuous_circleMap 0 1 |>.comp continuous_subtype_val |>.sub continuous_const) hn

def diskIntegral (μ : FiniteMeasure Angle) (w : ℂ) : ℂ :=
  ∫ θ : Angle, herglotzRieszKernel 0 w (circleMap 0 1 θ) ∂(μ : Measure Angle)

def toDisk (s : ℂ) : ℂ := (s - I) / (s + I)
def toHalfPlane (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

def boundaryParameter (θ : Angle) : ℝ :=
  (1 - (circleMap 0 1 θ).re + max 0 (circleMap 0 1 θ).im) /
    (2 * (1 + max 0 (circleMap 0 1 θ).im))

def boundaryWeight (θ : Angle) : ℝ :=
  (1 + max 0 (circleMap 0 1 θ).im)⁻¹

theorem boundaryParameter_mem (θ : Angle) : boundaryParameter θ ∈ Icc 0 1 := by
  have hr : |(circleMap 0 1 θ).re| ≤ 1 := by
    simpa only [norm_circleMap_zero, abs_one] using Complex.abs_re_le_norm (circleMap 0 1 θ)
  have hm : 0 ≤ max 0 (circleMap 0 1 θ).im := le_max_left _ _
  have hd : 0 < 2 * (1 + max 0 (circleMap 0 1 θ).im) := by positivity
  rw [abs_le] at hr
  constructor
  · exact div_nonneg (by linarith) hd.le
  · rw [boundaryParameter, div_le_one hd]
    linarith

theorem continuous_boundaryParameter : Continuous boundaryParameter := by
  unfold boundaryParameter
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro θ
  positivity

theorem continuous_boundaryWeight : Continuous boundaryWeight := by
  unfold boundaryWeight
  apply Continuous.inv₀ (by fun_prop)
  intro θ
  positivity

def compactKernel (t w : ℝ) (s : ℂ) : ℂ := (w : ℂ) / (1 + (s - 1) * t)

def compactIntegral (μ : FiniteMeasure Angle) (s : ℂ) : ℂ :=
  ∫ θ : Angle, compactKernel (boundaryParameter θ) (boundaryWeight θ) s ∂(μ : Measure Angle)

theorem real_compactDen_pos {t : ℝ} (ht : t ∈ Icc 0 1) {x : ℝ} (hx : 0 < x) :
    0 < 1 + (x - 1) * t := by
  by_cases h : t = 0
  · simp [h]
  · have hp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    nlinarith [mul_pos hx hp, ht.2]

def realResolvent (x : ℝ) (hx : 0 < x) : C(Angle, ℝ) where
  toFun θ := (1 + (x - 1) * boundaryParameter θ)⁻¹
  continuous_toFun :=
    (continuous_const.add (continuous_const.mul continuous_boundaryParameter)).inv₀
      (fun θ => (real_compactDen_pos (boundaryParameter_mem θ) hx).ne')

def resolventDensity (A : ℝ) (hA : 0 < A) : C(Angle, ℝ) where
  toFun θ := A * boundaryWeight θ / (1 + A * boundaryParameter θ)
  continuous_toFun :=
    (continuous_const.mul continuous_boundaryWeight).div
      (continuous_const.add (continuous_const.mul continuous_boundaryParameter))
      (fun θ => by nlinarith [(boundaryParameter_mem θ).1])

def resolventMeasure (μ : FiniteMeasure Angle) (A : ℝ) (hA : 0 < A) : FiniteMeasure Angle :=
  densityMeasure (μ : Measure Angle) (resolventDensity A hA)

end EntropyPhotonNumber.Herglotz

end

end

end OAI
