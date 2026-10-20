/-
prove2.me platform library module `Definitions.Def_OAI_InformationTheory_PhotonNumber_PhysicalMinimum`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_InformationTheory_PhotonNumber_PhysicalMinimum.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/PhysicalMinimum.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open MeasureTheory NormedSpace
open Filter Asymptotics Topology
open ContinuousLinearMap

namespace TensorLp
open scoped ENNReal
variable {A B : Type*}

end TensorLp

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {J : Type*}

end BeamLadder

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ}
namespace GibbsData
variable {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end GibbsData

def WeightedColumns.canonical (ρ : State n) (hm : FiniteMoment 6 ρ) : WeightedColumns ρ where
  Index := NumberIndex n
  vector := weightedRoot 3 ρ hm
  summable := weightedRoot_summable 3 ρ hm
  normalized := by simpa only [inverse_weightedRoot] using rootColumn_norm ρ
  density := by simpa only [inverse_weightedRoot] using rootColumn_operator ρ

namespace WeightedColumns

end WeightedColumns

end

section
open QuantumTrace TensorLp

end

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} {k : ℝ} {ρ : State n}
namespace GibbsData
variable (G : GibbsData n k ρ)

end GibbsData
end

namespace Regularization
open QuantumTrace
variable {n : ℕ} (R : Regularization n)

end Regularization

open QuantumTrace Annihilation BeamLadder TensorLp
namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end EntropyPhotonNumber

namespace WeightedGenerator
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ} {I : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} {k : ℝ} {ρ : State n}
namespace GibbsData
variable (G : GibbsData n k ρ)
end GibbsData
end

namespace Regularization

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} (R : Regularization n)

end

open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} (R : Regularization n)

end Regularization

open QuantumTrace Annihilation BeamLadder TensorLp

namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end EntropyPhotonNumber

end

end OAI
