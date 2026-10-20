/-
prove2.me platform library module `Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_InformationTheory_PhotonNumber_Interpolation.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Interpolation.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

namespace EntropyPhotonNumber
open Herglotz MeasureTheory

end EntropyPhotonNumber

namespace EntropyPhotonNumber.Herglotz

end EntropyPhotonNumber.Herglotz

namespace EntropyPhotonNumber
open MeasureTheory Herglotz

def resolventB (μ : FiniteMeasure Angle) (s : ℂ) : ℂ :=
  1 - (s - 1) * compactIntegral μ s

def resolventR (μ : FiniteMeasure Angle) (s : ℂ) : ℂ :=
  (s * compactIntegral μ s)⁻¹

end EntropyPhotonNumber

end

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

namespace EntropyPhotonNumber

section
open DiagonalForms.System MeasureTheory Set Filter Topology

def genericAdditionalE (D : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (∫ θ : UnitInterval, D ((1-θ.val)*s+θ.val*t))⁻¹

def interpolationQuadratic (m x y e : ℝ) (ξ φ : ℂ) : ℝ :=
  1/4*(m*f x*Real.exp x*Complex.normSq (ξ-φ)) +
  1/4*(m*f x*Real.exp (-x)*Complex.normSq (ξ+φ)) +
  1/4*(m*f y*Real.exp y*Complex.normSq (ξ+φ)) +
  1/4*(m*f y*Real.exp (-y)*Complex.normSq (ξ-φ)) +
  m*e*Complex.normSq φ

end

open DiagonalForms.System MeasureTheory Set Filter Topology Herglotz

end EntropyPhotonNumber

end

end OAI
