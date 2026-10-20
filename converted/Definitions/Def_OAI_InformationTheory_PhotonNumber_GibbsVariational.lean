/-
prove2.me platform library module `Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_InformationTheory_PhotonNumber_GibbsVariational.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/GibbsVariational.lean by skeleton subtraction
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

namespace QuantumTrace

section
open scoped BigOperators
open Filter Topology

structure StochasticOverlap (I J : Type*) where
  value : I → J → ℝ
  nonneg : ∀ i j, 0 ≤ value i j
  row : ∀ i, HasSum (value i) 1
  col : ∀ j, HasSum (fun i => value i j) 1

namespace StochasticOverlap
variable {I J : Type*} (a : StochasticOverlap I J)

def transpose : StochasticOverlap J I where
  value j i := a.value i j
  nonneg j i := a.nonneg i j
  row := a.col
  col := a.row

def diagonal (p : I → ℝ) (j : J) : ℝ := ∑' i, a.value i j * p i

end StochasticOverlap
end

section
open scoped BigOperators
variable {I J : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def basisOverlap (b : HilbertBasis I ℂ E) (c : HilbertBasis J ℂ E) :
    StochasticOverlap I J where
  value i j := ‖inner ℂ (c j) (b i)‖ ^ 2
  nonneg _ _ := sq_nonneg _
  row i := by
    simpa only [b.orthonormal.norm_eq_one, one_pow] using basis_hasSum_norm_sq c (b i)
  col j := by
    simpa only [norm_inner_symm, c.orthonormal.norm_eq_one, one_pow] using
      basis_hasSum_norm_sq b (c j)

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

end

variable {J : Type*}

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace

def crossEntropy {n : ℕ} {J : Type*} (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (σ : State n) : ℝ :=
  ∑' j, (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re

end EntropyPhotonNumber

namespace QuantumTrace
variable {n : ℕ} {J : Type*} [Nonempty J]

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace
end

section
open QuantumTrace TraceEnsemble

def sliceFreeEnergy {n : ℕ} {K : Type*} (a : HilbertBasis K ℂ (Fock n)) (w : K → ℝ)
    (Φ : State n → State n) (k α β : ℝ) (ρ : State n) : ℝ :=
  k*numberMoment 4 ρ + α*(∑' j, w j*(inner ℂ (a j) ((Φ ρ).op (a j))).re) +
    β*energy ρ - entropy ρ

end

section
open QuantumTrace

end

section
open QuantumTrace TensorLp

structure KrausFlow (n : ℕ) where
  I : Type
  V : I → Fock n →L[ℂ] Fock n
  norm : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2)
  F : ℝ
  nonneg : 0 ≤ F
  energy : ∀ x, (∑' i, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (V i x)) ≤
    vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x+ENNReal.ofReal F*ENNReal.ofReal (‖x‖^2)
  map : State n → State n
  ensemble : ∀ (J : Type) (v : J → Fock n) (ρ : State n),
    HasSum (fun j => ‖v j‖^2) 1 → TraceEnsemble.operator v = ρ.op →
    TraceEnsemble.operator (fun z : I × J => V z.1 (v z.2)) = (map ρ).op
  finiteEnergy : ∀ ρ, FiniteEnergy ρ → FiniteEnergy (map ρ)

theorem composedKraus_second_ensemble {n : ℕ} {J : Type*}
    (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (ρ σ τ : State n)
    (v : J → Fock n) (hv : HasSum (fun j => ‖v j‖^2) 1)
    (he : TraceEnsemble.operator v = σ.op) :
    TraceEnsemble.operator (fun z : ((NumberIndex n × NumberIndex n) ×
      (NumberIndex n × NumberIndex n)) × J =>
      composeKraus (firstKraus θ hθ τ) (secondKraus η hη ρ) z.1 (v z.2)) =
      (beamOutput θ hθ (beamOutput η hη ρ σ) τ).op := by
  have hV := TraceEnsemble.kraus_hasSum (secondKraus_norm η hη ρ) hv
  have heV := secondKraus_ensemble η hη ρ σ v hv he
  have heU := firstKraus_ensemble θ hθ (beamOutput η hη ρ σ) τ _ hV heV
  exact (composeKraus_ensemble (firstKraus θ hθ τ) (secondKraus η hη ρ) v).trans heU

namespace Regularization
variable {n : ℕ} (R : Regularization n)

def rawOutput (ρ σ : State n) : State n :=
  beamOutput (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2, sub_le_self _ R.hδ.1⟩
    (beamOutput R.η R.hη ρ σ) R.τD

def firstFlow (σ : State n) (hσ : FiniteEnergy σ) : KrausFlow n where
  I := (NumberIndex n × NumberIndex n) × (NumberIndex n × NumberIndex n)
  V := composeKraus (firstKraus (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2, sub_le_self _ R.hδ.1⟩ R.τD)
    (firstKraus R.η R.hη σ)
  norm := composeKraus_norm _ _ (firstKraus_norm _ _ _) (firstKraus_norm _ _ _)
  F := energy R.τD+energy σ
  nonneg := add_nonneg (energy_nonneg _) (energy_nonneg _)
  energy := by
    intro x
    have hh := composeKraus_energy
      (firstKraus (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2, sub_le_self _ R.hδ.1⟩ R.τD)
      (firstKraus R.η R.hη σ) (firstKraus_norm _ _ _) (firstKraus_energy _ _ _)
      (firstKraus_energy _ _ _) x
    simpa only [energyMoment_ofReal R.finiteD, energyMoment_ofReal hσ,
      ENNReal.ofReal_add (energy_nonneg R.τD) (energy_nonneg σ)] using hh
  map := fun ρ => R.rawOutput ρ σ
  ensemble := by
    intro J v ρ hv he
    exact composedKraus_first_ensemble _ _ _ _ ρ σ R.τD v hv he
  finiteEnergy := fun _ hρ => beamOutput_finiteEnergy _ _ (beamOutput_finiteEnergy _ _ hρ hσ) R.finiteD

def secondFlow (ρ : State n) (hρ : FiniteEnergy ρ) : KrausFlow n where
  I := (NumberIndex n × NumberIndex n) × (NumberIndex n × NumberIndex n)
  V := composeKraus (firstKraus (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2, sub_le_self _ R.hδ.1⟩ R.τD)
    (secondKraus R.η R.hη ρ)
  norm := composeKraus_norm _ _ (firstKraus_norm _ _ _) (secondKraus_norm _ _ _)
  F := energy R.τD+energy ρ
  nonneg := add_nonneg (energy_nonneg _) (energy_nonneg _)
  energy := by
    intro x
    have hh := composeKraus_energy
      (firstKraus (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2, sub_le_self _ R.hδ.1⟩ R.τD)
      (secondKraus R.η R.hη ρ) (secondKraus_norm _ _ _) (firstKraus_energy _ _ _)
      (secondKraus_energy _ _ _) x
    simpa only [energyMoment_ofReal R.finiteD, energyMoment_ofReal hρ,
      ENNReal.ofReal_add (energy_nonneg R.τD) (energy_nonneg ρ)] using hh
  map := fun σ => R.rawOutput ρ σ
  ensemble := by
    intro J v σ hv he
    exact composedKraus_second_ensemble _ _ _ _ ρ σ R.τD v hv he
  finiteEnergy := fun _ hσ => beamOutput_finiteEnergy _ _ (beamOutput_finiteEnergy _ _ hρ hσ) R.finiteD

end Regularization
end

section
open QuantumTrace
namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end

open QuantumTrace TraceEnsemble

namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)
end GibbsData

def relativeEntropy {n : ℕ} {J : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (σ : State n) : ℝ := crossEntropy b p σ-entropy σ

end EntropyPhotonNumber

namespace TensorLp
variable {A B I J : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp

def powerMoment {n : ℕ} (m : ℕ) (ρ : State n) : ℝ≥0∞ :=
  matrixMoment (fun k => (1+(totalNumber k : ℝ≥0∞))^m) ρ.op

end EntropyPhotonNumber

end

end OAI
