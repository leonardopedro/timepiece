/-
prove2.me platform library module `Definitions.Def_OAI_InformationTheory_PhotonNumber_Duality`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_InformationTheory_PhotonNumber_Duality.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Duality.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Contraction
import Definitions.Def_OAI_InformationTheory_PhotonNumber_FiniteVariation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_PhysicalMinimum

namespace OAI

noncomputable section

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation BeamLadder TensorLp ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
end EntropyPhotonNumber.SpectralLogData

section
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace TensorLp
open EntropyPhotonNumber
variable {A B I J : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp KrausBounded BeamLadder Annihilation
variable {n : ℕ}

namespace WeightedColumns
variable {ρ σ τ : State n}

end WeightedColumns
end EntropyPhotonNumber

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def scalarTarget (q : (E →L[ℂ] E) →ₗ[ℂ] ℂ) :
    (E →L[ℂ] E) →ₗ[ℂ] (Unit → ℂ) where
  toFun Z _ := q Z
  map_add' X Y := by ext; exact map_add q X Y
  map_smul' c X := by ext; exact q.map_smul c X

def scalarDiagram (S : Space E) (q : (E →L[ℂ] E) →ₗ[ℂ] ℂ) :
    DiagonalForms.System (Option Param) (S.I × S.I) Unit :=
  CenteredTests.system S.basis S.p S.pos S.sum.summable (h S.r) (h_pos S.rpos)
    (fun ij => some (S.pparam ij)) (some (⟨S.r,S.rpos⟩,0))
    (fun j => by simp [Space.pparam, Space.param, frequency])
    (fun _ => none) (scalarTarget q)

def scalarWeight (w : Param → ℝ) : Option Param → ℝ
  | none => 1
  | some p => w p

end ThermalSpectral

end

open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology Complex MeasureTheory

namespace EnsembleL2
open scoped BigOperators ComplexConjugate
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def meanLM (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) :
    (E →L[ℂ] E) →ₗ[ℂ] ℂ where
  toFun := mean v
  map_add' Z Y := by
    unfold mean
    simp only [add_apply, inner_add_right]
    exact (mean_hasSum v hv Z).summable.tsum_add (mean_hasSum v hv Y).summable
  map_smul' c Z := by
    simp only [mean, smul_apply, inner_smul_right, tsum_mul_left, smul_eq_mul, RingHom.id_apply]
def mixtureFunctional (v : I → E) (w : J → E)
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    (t : ℝ) : (E →L[ℂ] E) →ₗ[ℂ] ℂ :=
  (Real.sqrt (t*(1-t)) : ℂ) • (meanLM v hv-meanLM w hw)

end EnsembleL2

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalSpectral

namespace ThermalDual

variable {I J : Type*} [Fintype I] [Fintype J]

end ThermalDual

namespace ThermalSpectral
open EntropyPhotonNumber ThermalMetric
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalSpectral

namespace ThermalDual

section
open EntropyPhotonNumber ThermalMetric ThermalSpectral
open scoped BigOperators
variable {E I J K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Fintype K]

end

section
variable {I J : Type*} [Fintype I] [Fintype J]

end

open scoped ComplexConjugate

end ThermalDual

end

end OAI
