/-
prove2.me platform library module `Definitions.Def_OAI_InformationTheory_PhotonNumber_Minimum`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_InformationTheory_PhotonNumber_Minimum.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Minimum.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Duality

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology _root_.Complex _root_.OAI.Complex Metric
open MeasureTheory Set Filter Topology _root_.Complex _root_.OAI.Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology _root_.Complex _root_.OAI.Complex MeasureTheory

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder TensorLp ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ}

def twoPortLambda (η θ : ℝ) : Fin 2 → ℝ := ![θ*η,θ*(1-η)]

def outputReference (η θ : ℝ) (a : Fin 2 → ℝ) (d : ℝ) : ℝ :=
  θ*(η*a 0+(1-η)*a 1)+(1-θ)*d

end

section
open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp BeamLadder
open scoped ComplexConjugate
variable {n : ℕ}

end

open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp
variable {n : ℕ}
end EntropyPhotonNumber

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace EnsembleL2
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end EnsembleL2

namespace TensorLp
variable {A B I J : Type*}
end TensorLp

namespace EntropyPhotonNumber.WeightedColumns
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} {ρ σ τ : State n}

def lowerEnergy (X : WeightedColumns ρ) (j : Fin n) : ℝ :=
  ∑' i, ‖sandwich 0 3 (by omega) j (X.vector i)‖^2

end EntropyPhotonNumber.WeightedColumns

namespace EnsembleL2
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end EnsembleL2

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

end EntropyPhotonNumber.SpectralLogData

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}
end Annihilation

namespace EntropyPhotonNumber.WeightedColumns

section
open QuantumTrace Annihilation
variable {n : ℕ} {ρ : State n}

end

section
open QuantumTrace Annihilation
variable {n : ℕ}

end

section
open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} {ρ σ τ : State n}

def centeredLowerEnergy (X : WeightedColumns ρ) (r : ℝ) (j : Fin n) : ℝ :=
  X.lowerEnergy j-‖X.weakMean r j‖^2

end

open QuantumTrace
variable {n : ℕ}

end EntropyPhotonNumber.WeightedColumns

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace WeightedColumns
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

end EntropyPhotonNumber.SpectralLogData

namespace EntropyPhotonNumber
open QuantumTrace WeightedColumns
variable {n : ℕ}

end EntropyPhotonNumber

end

namespace EntropyPhotonNumber
open scoped BigOperators ComplexConjugate

section
open TensorLp KrausBounded BeamLadder
variable {n : ℕ}

namespace Regularization
open QuantumTrace
variable (R : Regularization n)

end Regularization
end

open QuantumTrace Annihilation
variable {n : ℕ} {J : Type} {ρ : State n}

namespace GibbsData
variable {k : ℝ} (G : GibbsData n k ρ)
end GibbsData

end EntropyPhotonNumber

section
open scoped BigOperators

namespace WeightedGenerator

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}
def driftPolynomial (n : ℕ) (r t : ℝ) : ℝ :=
  (r+1)*t*(t^4-(t+1)^4)+r*(t+n)*((t+2)^4-(t+1)^4)

end

end WeightedGenerator

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation
variable {n : ℕ}

theorem number_le_weight (k : NumberIndex n) : (totalNumber k:ℝ)≤numberWeight k := by
  simp only [numberWeight,totalNumber,Nat.cast_sum]; linarith

theorem number_div_weight_bound (k : NumberIndex n) : |(totalNumber k:ℝ)/numberWeight k^4|≤1 := by
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_one (pow_pos (lt_of_lt_of_le zero_lt_one (numberWeight_one_le k)) _)).mpr
  exact (number_le_weight k).trans (le_self_pow₀ (numberWeight_one_le k) (by norm_num))

def numberSandwich (n : ℕ) : Fock n →L[ℂ] Fock n :=
  diagonal (fun k => (totalNumber k:ℝ)/numberWeight k^4) 1 (by norm_num) number_div_weight_bound

end

open QuantumTrace Annihilation WeightedGenerator
variable {n : ℕ}

def fourthDriftConstant (n : ℕ) (r : ℝ) : ℝ :=
  |(-4:ℝ)|+|4*r*n+12*r-6|+|18*r*n+24*r-4|+|28*r*n+14*r-1|+|15*r*n|

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate

namespace EntropyPhotonNumber.Regularization
open QuantumTrace Annihilation
variable {n : ℕ} (R : Regularization n)

theorem attenuation_mem : 1-R.δ ∈ Set.Icc 0 1 :=
  ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩

end EntropyPhotonNumber.Regularization

namespace EntropyPhotonNumber

section
open QuantumTrace ThermalMetric

structure ThermalSetup where
  η : ℝ
  θ : ℝ
  κ : ℝ
  ε : ℝ
  d : ℝ
  r1 : ℝ
  r2 : ℝ
  hη : η ∈ Set.Ioo 0 1
  hθ : θ ∈ Set.Ioo 0 1
  hκ : κ ∈ Set.Ioo 0 1
  hε : 0<ε
  hd : 0<d
  hr1 : 0<r1
  hr2 : 0<r2
  slack_r : (1+ε)*(θ*η*r1+θ*(1-η)*r2)≤θ*(η*r1+(1-η)*r2)+(1-θ)*d
  slack_s : (1+ε)*(θ*η*(r1+1)+θ*(1-η)*(r2+1))≤θ*(η*r1+(1-η)*r2)+(1-θ)*d+1
  small_κ : κ≤ε^2/(4*(ε+2)*mixtureConstant (θ*(η*r1+(1-η)*r2)+(1-θ)*d)^2)

namespace ThermalSetup
variable (P : ThermalSetup)
def r0 : ℝ := P.θ*(P.η*P.r1+(1-P.η)*P.r2)+(1-P.θ)*P.d
def w1 : ℝ := (1-P.κ)*P.θ*P.η
def w2 : ℝ := (1-P.κ)*P.θ*(1-P.η)
theorem r0_pos : 0<P.r0 := by
  unfold r0
  exact add_pos (mul_pos P.hθ.1 (add_pos (mul_pos P.hη.1 P.hr1)
    (mul_pos (sub_pos.mpr P.hη.2) P.hr2))) (mul_pos (sub_pos.mpr P.hθ.2) P.hd)
theorem w1_pos : 0<P.w1 := mul_pos (mul_pos (sub_pos.mpr P.hκ.2) P.hθ.1) P.hη.1
theorem w2_pos : 0<P.w2 := mul_pos (mul_pos (sub_pos.mpr P.hκ.2) P.hθ.1) (sub_pos.mpr P.hη.2)
theorem η_mem : P.η ∈ Set.Icc 0 1 := ⟨P.hη.1.le,P.hη.2.le⟩
theorem θ_mem : P.θ ∈ Set.Icc 0 1 := ⟨P.hθ.1.le,P.hθ.2.le⟩
theorem κ_mem : P.κ ∈ Set.Icc 0 1 := ⟨P.hκ.1.le,P.hκ.2.le⟩
theorem δ_mem : 1-P.θ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr P.hθ.2.le,sub_le_self _ P.hθ.1.le⟩

def reg (n : ℕ) (ζ : ℝ) (hζ : 0<ζ) : Regularization n where
  η := P.η
  δ := 1-P.θ
  κ := P.κ
  hη := P.η_mem
  hδ := P.δ_mem
  hκ := P.κ_mem
  τD := thermalState n P.d P.hd
  τ0 := thermalState n P.r0 P.r0_pos
  finiteD := thermalState_finiteEnergy n P.d P.hd
  finite0 := thermalState_finiteEnergy n P.r0 P.r0_pos
  c := 1/h P.r0
  a1 := (1+P.ε)*P.w1/h P.r1
  a2 := (1+P.ε)*P.w2/h P.r2
  b1 := P.ε*P.w1
  b2 := P.ε*P.w2
  ζ := ζ
  hc := one_div_pos.mpr (h_pos P.r0_pos)
  ha1 := div_pos (mul_pos (by linarith [P.hε]) P.w1_pos) (h_pos P.hr1)
  ha2 := div_pos (mul_pos (by linarith [P.hε]) P.w2_pos) (h_pos P.hr2)
  hb1 := mul_pos P.hε P.w1_pos
  hb2 := mul_pos P.hε P.w2_pos
  hζ := hζ

def middle {n : ℕ} (ρ σ : State n) : State n := beamOutput P.η P.η_mem ρ σ
def raw {n : ℕ} (ρ σ : State n) : State n :=
  beamOutput P.θ P.θ_mem (P.middle ρ σ) (thermalState n P.d P.hd)
end ThermalSetup

namespace WeightedColumns
variable {n : ℕ} {ρ : State n}
end WeightedColumns
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
end SpectralLogData
end

open QuantumTrace ThermalMetric Annihilation
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
def defectSquared (r : ℝ) (hr : 0<r) : ℝ := ∑ j, ‖G.defect r hr j‖^2
def meanSquared : ℝ := ∑ j, ‖G.annihilationMean j‖^2
end SpectralLogData
namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)
end GibbsData
namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)

end ThermalSetup

namespace ThermalDual

end ThermalDual
namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)

end ThermalSetup
end EntropyPhotonNumber

end

end OAI
