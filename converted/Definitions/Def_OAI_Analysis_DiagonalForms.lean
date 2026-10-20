/-
prove2.me platform library module `Definitions.Def_OAI_Analysis_DiagonalForms`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Analysis_DiagonalForms.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiagonalForms.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace DiagonalForms.System
def logMean (X Y : ℝ) : ℝ := if X = Y then X else (Y-X) / (Real.log Y-Real.log X)
end DiagonalForms.System

namespace QuantumCalculus
theorem integral_exp_affine_log {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ s in (0 : ℝ)..1, Real.exp ((1-s)*Real.log p+s*Real.log q)) =
      DiagonalForms.System.logMean p q := by
  by_cases he : p = q
  · subst q
    have hh (s : ℝ) : (1-s)*Real.log p+s*Real.log p = Real.log p := by ring
    simp_rw [hh, Real.exp_log hp]
    simp [DiagonalForms.System.logMean]
  · have hd : Real.log q - Real.log p ≠ 0 := by
      intro h
      exact he ((Real.log_injOn_pos hp hq) (sub_eq_zero.mp h).symm)
    conv_lhs => arg 1; ext s
                rw [show (1-s)*Real.log p+s*Real.log q =
                  (Real.log q-Real.log p)*s+Real.log p by ring]
    rw [intervalIntegral.integral_comp_mul_add _ hd]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel, integral_exp,
      Real.exp_log hp, Real.exp_log hq]
    simp [DiagonalForms.System.logMean, he, div_eq_mul_inv, mul_comm]
end QuantumCalculus

namespace DiagonalForms.System
@[simp] theorem logMean_self (p : ℝ) : logMean p p = p := by simp [logMean]
theorem logMean_symm (p q : ℝ) : logMean p q = logMean q p := by
  by_cases he : p = q
  · subst q; rfl
  · rw [logMean, ite_eq_right he, logMean, ite_eq_right (Ne.symm he)]
    rw [show p-q = -(q-p) by ring, show Real.log p-Real.log q = -(Real.log q-Real.log p) by ring]
    simp only [neg_div_neg_eq]
theorem logMean_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : 0 < logMean p q := by
  rcases lt_trichotomy p q with h | h | h
  · rw [logMean, ite_eq_right h.ne]
    exact div_pos (sub_pos.mpr h) (sub_pos.mpr (Real.strictMonoOn_log hp hq h))
  · simp [h, hq]
  · rw [logMean_symm, logMean, ite_eq_right h.ne]
    exact div_pos (sub_pos.mpr h) (sub_pos.mpr (Real.strictMonoOn_log hq hp h))
theorem logMean_le_arithmetic {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : logMean p q ≤ (p+q)/2 := by
  rw [← QuantumCalculus.integral_exp_affine_log hp hq]
  calc
    _ ≤ ∫ s in (0:ℝ)..1, ((1-s)*p+s*q) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · exact Continuous.intervalIntegrable (by fun_prop) _ _
      · exact Continuous.intervalIntegrable (by fun_prop) _ _
      intro s hs
      have hh := convexOn_exp.2 (Set.mem_univ (Real.log p)) (Set.mem_univ (Real.log q))
        (sub_nonneg.mpr hs.2) hs.1 (by ring : (1-s)+s=1)
      simpa only [smul_eq_mul, Real.exp_log hp, Real.exp_log hq] using hh
    _ = (p+q)/2 := by
      rw [intervalIntegral.integral_add (by exact Continuous.intervalIntegrable (by fun_prop) _ _) (by exact Continuous.intervalIntegrable (by fun_prop) _ _),
        intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_sub (by exact Continuous.intervalIntegrable (by fun_prop) _ _) (by exact Continuous.intervalIntegrable (by fun_prop) _ _)]
      simp
      ring
end DiagonalForms.System

namespace DiagonalForms.System
open EntropyPhotonNumber

theorem logMean_exp_mul_f (u v : ℝ) :
    logMean (Real.exp u) (Real.exp v)*f ((u-v)/2)=Real.exp ((u+v)/2) := by
  by_cases he : u=v
  · subst v
    simp
  · have he' : Real.exp u ≠ Real.exp v := fun h => he (Real.exp_injective h)
    have hx : (u-v)/2 ≠ 0 := div_ne_zero (sub_ne_zero.mpr he) (by norm_num)
    have hd : v-u ≠ 0 := sub_ne_zero.mpr (Ne.symm he)
    have hu : Real.exp u=Real.exp ((u+v)/2)*Real.exp ((u-v)/2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hv : Real.exp v=Real.exp ((u+v)/2)*Real.exp (-((u-v)/2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [logMean, ite_eq_right he', Real.log_exp, Real.log_exp, f_of_ne_zero hx,
      hu, hv, Real.sinh_eq]
    have hsh : Real.exp ((u-v)/2)-Real.exp (-((u-v)/2)) ≠ 0 := by
      intro hh
      have hh' := Real.exp_injective (sub_eq_zero.mp hh)
      apply hx
      linarith
    field_simp
    ring

theorem logMean_mul_f {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    logMean p q*f ((Real.log p-Real.log q)/2)=Real.exp ((Real.log p+Real.log q)/2) := by
  simpa only [Real.exp_log hp, Real.exp_log hq] using logMean_exp_mul_f (Real.log p) (Real.log q)

theorem logMean_product {a b c d : ℝ} (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) :
    logMean (a*c) (b*d)=logMean a b*fourWeightTarget (logMean c d)
      ((Real.log a-Real.log b)/2) ((Real.log c-Real.log d)/2) := by
  have hh :
      (logMean a b*f ((Real.log a-Real.log b)/2))*(logMean c d*f ((Real.log c-Real.log d)/2))=
      logMean (a*c) (b*d)*f (((Real.log a-Real.log b)/2)+((Real.log c-Real.log d)/2)) := by
    rw [logMean_mul_f ha hb, logMean_mul_f hc hd, ← Real.exp_add]
    rw [show ((Real.log a-Real.log b)/2)+((Real.log c-Real.log d)/2) =
      (Real.log (a*c)-Real.log (b*d))/2 by rw [Real.log_mul ha.ne' hc.ne', Real.log_mul hb.ne' hd.ne']; ring,
      logMean_mul_f (mul_pos ha hc) (mul_pos hb hd)]
    congr 1
    rw [Real.log_mul ha.ne' hc.ne', Real.log_mul hb.ne' hd.ne']
    ring
  unfold fourWeightTarget
  have hf := (f_pos (((Real.log a-Real.log b)/2)+((Real.log c-Real.log d)/2))).ne'
  rw [← mul_div_assoc]
  apply (eq_div_iff hf).mpr
  nlinarith [hh]

theorem logMean_scale {p q : ℝ} (hp : 0<p) (hq : 0<q) {c : ℝ} (hc : 0<c) :
    logMean (c*p) (c*q)=c*logMean p q := by
  by_cases he : p=q
  · subst q; simp
  · have he' : c*p ≠ c*q := fun h => he (mul_left_cancel₀ hc.ne' h)
    rw [logMean, ite_eq_right he', Real.log_mul hc.ne' hq.ne', Real.log_mul hc.ne' hp.ne',
      logMean, ite_eq_right he]
    ring

theorem logMean_mono {p q a b : ℝ} (hp : 0<p) (hq : 0<q) (hpa : p≤a) (hqb : q≤b) :
    logMean p q≤logMean a b := by
  rw [← QuantumCalculus.integral_exp_affine_log hp hq,
    ← QuantumCalculus.integral_exp_affine_log (hp.trans_le hpa) (hq.trans_le hqb)]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro s hs
  apply Real.exp_le_exp.mpr
  exact add_le_add (mul_le_mul_of_nonneg_left (Real.log_le_log hp hpa) (sub_nonneg.mpr hs.2))
    (mul_le_mul_of_nonneg_left (Real.log_le_log hq hqb) hs.1)

end DiagonalForms.System

end

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
open Filter Topology

namespace DiagonalForms

structure System (P I J : Type*) where
  sourceParam : I → P
  targetParam : J → P
  tests : Submodule ℂ (I → ℂ)
  map : tests →ₗ[ℂ] (J → ℂ)
  mass_summable : ∀ z : tests, Summable (fun i => Complex.normSq (z.val i))
  finite_values : ∀ z : tests, ∃ s : Finset P, ∀ i, z.val i ≠ 0 → sourceParam i ∈ s
  multiplier_mem : ∀ (z : tests) (w : P → ℂ), (fun i => w (sourceParam i) * z.val i) ∈ tests

namespace System

variable {P I J : Type*} (D : System P I J)

def sourceForm (w : P → ℝ) (z : D.tests) : ℝ :=
  ∑' i, w (D.sourceParam i) * Complex.normSq (z.val i)

def Comparison (w : P → ℝ) : Prop :=
  ∀ (z : D.tests) (s : Finset J),
    ∑ j ∈ s, w (D.targetParam j) * Complex.normSq (D.map z j) ≤ D.sourceForm w z

def multiplier (w : P → ℝ) (z : D.tests) : D.tests :=
  ⟨fun i => (w (D.sourceParam i) : ℂ) * z.val i, D.multiplier_mem z (fun p => (w p : ℂ))⟩

@[simp] theorem multiplier_apply (w : P → ℝ) (z : D.tests) (i : I) :
    (D.multiplier w z).val i = (w (D.sourceParam i) : ℂ) * z.val i := rfl

def parallel (x y : ℝ) : ℝ := x * y / (x + y)

end System

end DiagonalForms

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

section CompactIntegral
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (k₀ : K)

def compactApprox (n : ℕ) : SimpleFunc K K :=
  SimpleFunc.approxOn id measurable_id Set.univ k₀ (Set.mem_univ _) n

end CompactIntegral
end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
abbrev UnitInterval := Set.Icc (0 : ℝ) 1

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (k₀ : K)

def resolventWeight (c : ℝ) (r : K → ℝ) (q : ℝ) : ℝ :=
  q⁻¹ + c + ∫ k, (1+(q-1)*r k)⁻¹ ∂μ

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]

end DiagonalForms.System

namespace DiagonalForms.System
open Function
variable {P I J : Type*} (D : DiagonalForms.System P I J)

def fiveQuadratic (v₀ v₁ v₂ v₃ v₄ : ℝ) (ξ φ : ℂ) : ℝ :=
  v₀*Complex.normSq (ξ-φ) + v₁*Complex.normSq (ξ+φ) +
  v₂*Complex.normSq (ξ+φ) + v₃*Complex.normSq (ξ-φ) + v₄*Complex.normSq φ

end DiagonalForms.System

end

end

end OAI
