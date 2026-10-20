/-
prove2.me platform library module `Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_InformationTheory_PhotonNumber_Generator.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Generator.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

namespace PhysicalGenerator
open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I : Type*}

def lowerCoefficient (j : Fin n) (k : NumberIndex n) : ℂ := Real.sqrt ((k j:ℝ)+1)
def raiseCoefficient (j : Fin n) (k : NumberIndex n) : ℂ :=
  if k j=0 then 0 else Real.sqrt (k j:ℝ)
def modeCoefficient (j : Fin n) (u : Bool) (k : NumberIndex n) : ℂ :=
  (k j:ℂ)+(if u then 1 else 0)

def lowerFamily (j : Fin n) (x : I → Fock n) := fun i => sandwich 0 3 (by omega) j (x i)
def raiseFamily (j : Fin n) (x : I → Fock n) := fun i => creationSandwich 0 3 (by omega) j (x i)
def modeFamily (j : Fin n) (u : Bool) (x : I → Fock n) := fun i => inverseWeight 2 (modeBound j u (x i))
def baseFamily (x : I → Fock n) := fun i => inverseWeight 3 (x i)

def dissipator (j : Fin n) (u : Bool) (x : I → Fock n) : Fock n →L[ℂ] Fock n :=
  CrossEnsemble.operator (if u then raiseFamily j x else lowerFamily j x)
      (if u then raiseFamily j x else lowerFamily j x)-
    (2:ℂ)⁻¹ • (CrossEnsemble.operator (modeFamily j u x) (baseFamily x)+
      CrossEnsemble.operator (baseFamily x) (modeFamily j u x))
def generator (r : ℝ) (x : I → Fock n) : Fock n →L[ℂ] Fock n :=
  ∑ j, (((r+1:ℝ):ℂ) • dissipator j false x+(r:ℂ) • dissipator j true x)

end PhysicalGenerator

namespace QuantumTrace
end QuantumTrace

namespace PhysicalGenerator

section
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ} {I : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I J K : Type*}

end PhysicalGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder

structure WeightedColumns {n : ℕ} (ρ : State n) where
  Index : Type
  vector : Index → Fock n
  summable : Summable (fun i => ‖vector i‖^2)
  normalized : HasSum (fun i => ‖inverseWeight 3 (vector i)‖^2) 1
  density : TraceEnsemble.operator (fun i => inverseWeight 3 (vector i))=ρ.op

namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

def slice (η : ℝ) (hη : η ∈ Set.Icc 0 1) (B : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  weightedConditional η hη (fun i => inverseWeight 1 (X.vector i)) B

def sliceRight (η : ℝ) (hη : η ∈ Set.Icc 0 1) (B : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  weightedConditionalRight η hη (fun i => inverseWeight 1 (X.vector i)) B

end WeightedColumns

end EntropyPhotonNumber

namespace PhysicalGenerator
open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I J K : Type*}

def weakOperator (r : ℝ) (j : Fin n) (x : I → Fock n) : Fock n →L[ℂ] Fock n :=
  (r+1:ℂ) • CrossEnsemble.operator (baseFamily x) (lowerFamily j x)-
    (r:ℂ) • CrossEnsemble.operator (raiseFamily j x) (baseFamily x)

end PhysicalGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder TensorLp
namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

def rawSlice (η : ℝ) (hη : η ∈ Set.Icc 0 1) (Z : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  conditionalLeft (fun i => inverseWeight 3 (X.vector i)) X.normalized (conjugate η hη Z)

def rawSliceRight (η : ℝ) (hη : η ∈ Set.Icc 0 1) (Z : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  conditionalRight (fun i => inverseWeight 3 (X.vector i)) X.normalized (conjugate η hη Z)

end WeightedColumns

end EntropyPhotonNumber

namespace KrausBounded
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
end KrausBounded

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}
end BeamLadder

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder TensorLp
namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

def expectation (Z : Fock n →L[ℂ] Fock n) : ℂ :=
  CrossEnsemble.pairing (fun i => inverseWeight 3 (X.vector i))
    (fun i => inverseWeight 3 (X.vector i)) Z

def weakMean (r : ℝ) (j : Fin n) : ℂ := singleWeak r j X.vector 1

def centeredWeak (r : ℝ) (j : Fin n) (Z : Fock n →L[ℂ] Fock n) : ℂ :=
  singleWeak r j X.vector Z-X.weakMean r j*X.expectation Z

end WeightedColumns

end EntropyPhotonNumber

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

end BeamLadder

namespace EntropyPhotonNumber

namespace WeightedColumns
open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

end WeightedColumns

end EntropyPhotonNumber

end

end OAI
