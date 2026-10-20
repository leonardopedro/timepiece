/-
prove2.me platform library module `Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_InformationTheory_PhotonNumber_SpectralLog.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/SpectralLog.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

noncomputable section

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

namespace SquareAnalysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I : Type*}

abbrev H (I : Type*) := lp (fun _ : I => ℂ) 2

def vector (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2)) (x : E) : H I :=
  ⟨fun i => f i x, (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
    (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs x)⟩

@[simp] theorem vector_apply (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    (x : E) (i : I) : vector f hs x i = f i x := rfl

theorem hasSum_square (x : H I) : HasSum (fun i => ‖x i‖^2) (‖x‖^2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (lp.hasSum_norm (p := 2) (by norm_num) x)

theorem vector_norm_sq (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    (x : E) : ‖vector f hs x‖^2 = ∑' i, ‖f i x‖^2 :=
  (hasSum_square (vector f hs x)).tsum_eq.symm

def linearMap (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2)) :
    E →ₗ[ℂ] H I where
  toFun := vector f hs
  map_add' := fun x y => by apply lp.ext; funext i; exact map_add (f i) x y
  map_smul' := fun c x => by apply lp.ext; funext i; exact map_smul (f i) c x

theorem vector_norm_le (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖f i x‖^2) ≤ C*‖x‖^2) (x : E) :
    ‖vector f hs x‖ ≤ Real.sqrt C*‖x‖ := by
  have hh := hb x
  rw [← vector_norm_sq f hs x] at hh
  have he := Real.sq_sqrt hC
  have hp := mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg x)
  nlinarith [sq_nonneg (‖vector f hs x‖-Real.sqrt C*‖x‖)]

def continuousMap (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖f i x‖^2) ≤ C*‖x‖^2) : E →L[ℂ] H I :=
  (linearMap f hs).mkContinuous (Real.sqrt C) (vector_norm_le f hs hC hb)

@[simp] theorem continuousMap_apply (f : I → E →ₗ[ℂ] ℂ)
    (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖f i x‖^2) ≤ C*‖x‖^2) (x : E) :
    continuousMap f hs C hC hb x = vector f hs x := rfl

variable [CompleteSpace E]

def gram (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖f i x‖^2) ≤ C*‖x‖^2) : E →L[ℂ] E :=
  (continuousMap f hs C hC hb).adjoint ∘L continuousMap f hs C hC hb

end SquareAnalysis

namespace QuantumTrace
open scoped ComplexConjugate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

def logCoordinates (b : HilbertBasis J ℂ E) (c : J → ℝ) (V : E →L[ℂ] E) (j : J) : E →ₗ[ℂ] ℂ :=
  (Real.sqrt (c j):ℂ) • ((innerSL ℂ (b j)).toLinearMap.comp V.toLinearMap)

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace Annihilation

structure SpectralLogData (n : ℕ) (ρ : State n) where
  J : Type
  basis : HilbertBasis J ℂ (Fock n)
  probability : J → ℝ
  probability_pos : ∀ j, 0 < probability j
  probability_sum : HasSum probability 1
  eigen : ∀ j, ρ.op (basis j)=(probability j:ℂ) • basis j
  spectralColumns : J → Fock n
  spectralColumns_summable : Summable (fun j => ‖spectralColumns j‖^2)
  spectralColumns_inverse : ∀ j, inverseWeight 3 (spectralColumns j)=
    CrossEnsemble.eigenEnsemble basis probability j
  logSandwich : Fock n →L[ℂ] Fock n
  logSandwich_symmetric : logSandwich.IsSymmetric
  logSandwich_parseval : ∀ y, HasSum
    (fun j => -Real.log (probability j)*‖inner ℂ (basis j) (inverseWeight 2 y)‖^2)
    (inner ℂ y (logSandwich y)).re
  logSandwich_preimage : ∀ j, logSandwich (inverseWeight 1 (spectralColumns j))=
    ((-Real.log (probability j):ℝ):ℂ) • inverseWeight 5 (spectralColumns j)

namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n}

def toSpectralLogData (G : GibbsData n k ρ) (hk : 0<k) : SpectralLogData n ρ where
  J := G.J
  basis := G.basis
  probability := G.probability
  probability_pos := G.probability_pos
  probability_sum := G.probability_sum
  eigen := G.eigen
  spectralColumns := G.spectralColumns
  spectralColumns_summable := G.spectralColumns_summable
  spectralColumns_inverse := G.spectralColumns_inverse
  logSandwich := G.logSandwich
  logSandwich_symmetric := G.logSandwich_symmetric hk
  logSandwich_parseval := G.logSandwich_parseval hk
  logSandwich_preimage := fun j => G.logSandwich_preimage hk j _ (G.spectralColumns_inverse j)
end GibbsData
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

def logCoefficient (j : G.J) : ℝ := -Real.log (G.probability j)
theorem logCoefficient_nonneg (j : G.J) : 0 ≤ G.logCoefficient j := by
  apply neg_nonneg.mpr
  apply Real.log_nonpos (G.probability_pos j).le
  exact G.probability_sum.tsum_eq ▸ G.probability_sum.summable.le_tsum j (fun i _ => (G.probability_pos i).le)
theorem spectralColumns_normalized :
    HasSum (fun r => ‖inverseWeight 3 (G.spectralColumns r)‖^2) 1 := by
  simpa only [G.spectralColumns_inverse,
    CrossEnsemble.eigenEnsemble_norm G.basis G.probability (fun r => (G.probability_pos r).le)]
    using G.probability_sum

end SpectralLogData
end EntropyPhotonNumber

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

def annihilationMatrix (j : Fin n) (a : G.J × G.J) : ℂ :=
  loweringEntry G.basis G.probability G.spectralColumns j a.1 a.2

def annihilationMean (j : Fin n) : ℂ := diagonalMean G.probability (G.annihilationMatrix j)

def centeredMatrix (j : Fin n) (a : G.J × G.J) : ℂ :=
  centeredEntry G.basis G.probability G.spectralColumns j (G.annihilationMean j) a.1 a.2

theorem centeredMatrix_six_sums (j : Fin n) :
    Summable (fun a : G.J × G.J => G.probability a.2*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.probability a.1*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.logCoefficient a.1*G.probability a.2*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.logCoefficient a.2*G.probability a.2*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.logCoefficient a.1*G.probability a.1*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.logCoefficient a.2*G.probability a.1*‖G.centeredMatrix j a‖^2) :=
  centered_six_sums G.basis G.probability G.probability_pos G.probability_sum.summable
    G.spectralColumns G.spectralColumns_summable G.spectralColumns_inverse
    G.logSandwich (G.logSandwich_symmetric) G.logCoefficient G.logCoefficient_nonneg
    (G.logSandwich_parseval)
    G.logSandwich_preimage j (G.annihilationMean j)

theorem centeredMatrix_defect_summable (t : ℝ) (j : Fin n) :
    Summable (fun a : G.J × G.J =>
      (1-frequency t (G.probability a.1) (G.probability a.2))*
      defectCoefficient t (G.probability a.1) (G.probability a.2)*‖G.centeredMatrix j a‖^2) := by
  rcases G.centeredMatrix_six_sums j with ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
  exact defect_series_summable t G.probability G.logCoefficient (fun _ => rfl)
    (G.centeredMatrix j) h₁ h₂ h₃ h₄ h₅ h₆

def defect (t : ℝ) (ht : 0<t) (j : Fin n) :
    centeredSpace t ht G.probability G.probability_pos G.probability_sum.summable →L[ℂ] ℂ :=
  (defectFunctional t ht G.probability G.probability_pos (G.centeredMatrix j)
    (G.centeredMatrix_defect_summable t j)).comp
    (centeredSpace t ht G.probability G.probability_pos G.probability_sum.summable).subtypeL

def centeredEnergy : ℝ := ∑ j, ∑' r,
  ‖centeredLadder j (G.annihilationMean j) false (G.spectralColumns r)‖^2

end EntropyPhotonNumber.SpectralLogData

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation
variable {n : ℕ} {J : Type} {ρ : State n}

end

def numberBasis (n : ℕ) : HilbertBasis (NumberIndex n) ℂ (Fock n) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

@[simp] theorem numberBasis_apply (n : ℕ) (k : NumberIndex n) :
    numberBasis n k = numberKet k := by
  classical
  exact ((numberBasis n).repr_symm_single k).symm

end EntropyPhotonNumber

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I : Type*}

def diagonalVector (b : HilbertBasis I ℂ E) (p : I → ℝ) (i : I) : E :=
  (Real.sqrt (p i) : ℂ) • b i

omit [CompleteSpace E] in
@[simp] theorem diagonalVector_norm_sq (b : HilbertBasis I ℂ E) (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (i : I) : ‖diagonalVector b p i‖^2 = p i := by
  simp [diagonalVector, norm_smul, b.orthonormal.norm_eq_one, Real.sq_sqrt (hp i)]

theorem diagonalVector_eigen (b : HilbertBasis I ℂ E) (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : Summable p) (i : I) :
    operator (diagonalVector b p) (b i) = (p i : ℂ) • b i := by
  classical
  have hv : Summable (fun j => ‖diagonalVector b p j‖^2) := by
    simpa only [diagonalVector_norm_sq b p hp] using hs
  have he (j : I) : InnerProductSpace.rankOne ℂ (diagonalVector b p j)
      (diagonalVector b p j) (b i) = if j=i then (p i : ℂ) • b i else 0 := by
    simp only [InnerProductSpace.rankOne_apply, diagonalVector, inner_smul_left,
      orthonormal_iff_ite.mp b.orthonormal]
    split_ifs with h
    · subst j
      have hsq : (Real.sqrt (p i) : ℂ) * (Real.sqrt (p i) : ℂ) = (p i : ℂ) := by
        norm_cast
        exact Real.mul_self_sqrt (hp i)
      simp only [Complex.conj_ofReal, mul_one, smul_smul, hsq]
    · simp only [mul_zero, zero_smul]
  have hh := ((ContinuousLinearMap.apply ℂ E (b i)).hasSum (hasSum_rankOne hv))
  simpa only [ContinuousLinearMap.apply_apply, he, tsum_ite_eq] using hh.tsum_eq.symm

end TraceEnsemble

namespace EntropyPhotonNumber
open QuantumTrace TraceEnsemble

def diagonalState {n : ℕ} (p : NumberIndex n → ℝ) (hp : ∀ k, 0 ≤ p k) (hs : HasSum p 1) : State n where
  op := TraceEnsemble.operator (diagonalVector (numberBasis n) p)
  positive := TraceEnsemble.positive (by simpa only [diagonalVector_norm_sq _ p hp] using hs.summable)
  trace_one := by
    simpa only [numberBasis_apply, entry] using TraceEnsemble.trace
      (by simpa only [diagonalVector_norm_sq _ p hp] using hs :
        HasSum (fun k => ‖diagonalVector (numberBasis n) p k‖^2) 1) (numberBasis n)

@[simp] theorem diagonalState_eigen {n : ℕ} (p : NumberIndex n → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hs : HasSum p 1) (k : NumberIndex n) :
    (diagonalState p hp hs).op (numberBasis n k) = (p k : ℂ) • numberBasis n k :=
  diagonalVector_eigen _ _ hp hs.summable k

@[simp] theorem diagonalState_diagonal {n : ℕ} (p : NumberIndex n → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hs : HasSum p 1) (k : NumberIndex n) :
    (entry (diagonalState p hp hs).op k k).re = p k := by
  rw [entry, ← numberBasis_apply n k, diagonalState_eigen, inner_smul_right,
    orthonormal_iff_ite.mp (numberBasis n).orthonormal k k, ite_eq_left rfl, mul_one, Complex.ofReal_re]

def thermalState (n : ℕ) (r : ℝ) (hr : 0 < r) : State n :=
  diagonalState (thermalWeight n r) (fun k => (thermalWeight_pos n hr k).le)
    (hasSum_thermalWeight n hr)

@[simp] theorem thermalState_diagonal (n : ℕ) (r : ℝ) (hr : 0 < r) (k : NumberIndex n) :
    (entry (thermalState n r hr).op k k).re = thermalWeight n r k :=
  diagonalState_diagonal _ _ _ _

def mixture {n : ℕ} (t : ℝ) (ht : t ∈ Set.Icc 0 1) (ρ σ : State n) : State n where
  op := (t : ℂ) • ρ.op + ((1-t : ℝ) : ℂ) • σ.op
  positive := by
    have h₁ := ρ.positive.smul_of_nonneg (c := (t : ℂ)) (by exact_mod_cast ht.1)
    have h₂ := σ.positive.smul_of_nonneg (c := ((1-t : ℝ) : ℂ)) (by exact_mod_cast (sub_nonneg.mpr ht.2))
    exact h₁.add h₂
  trace_one := by
    convert (ρ.trace_one.mul_left t).add (σ.trace_one.mul_left (1-t)) using 1
    · funext k
      simp only [entry, add_apply, smul_apply,
        inner_add_right, inner_smul_right, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    · ring

end EntropyPhotonNumber

namespace QuantumTrace

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

def regularNegLog (T : E →L[ℂ] E) (ε : ℝ) : E →L[ℂ] E :=
  Real.log (1+ε) • 1 - CFC.log (T + ε • 1)

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I : Type*}

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace

def vectorEnergy {n : ℕ} (x : Fock n) : ℝ :=
  ∑' k, (totalNumber k : ℝ)*‖inner ℂ (numberBasis n k) x‖^2

def FiniteVectorEnergy {n : ℕ} (x : Fock n) : Prop :=
  Summable (fun k => (totalNumber k : ℝ)*‖inner ℂ (numberBasis n k) x‖^2)

end

open QuantumTrace Annihilation
variable {n : ℕ}

end EntropyPhotonNumber

end

end OAI
