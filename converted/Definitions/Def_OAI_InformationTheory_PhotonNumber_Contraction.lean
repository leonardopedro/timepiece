/-
prove2.me platform library module `Definitions.Def_OAI_InformationTheory_PhotonNumber_Contraction`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_InformationTheory_PhotonNumber_Contraction.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Contraction.lean by skeleton subtraction
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
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace EnsembleL2

section
open scoped BigOperators ComplexConjugate
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def secondMoment (v : I → E) (Z : E →L[ℂ] E) : ℝ := ∑' i, ‖Z (v i)‖^2

def mixture (v : I → E) (w : J → E) (t : ℝ) : I ⊕ J → E :=
  Sum.elim (fun i => (Real.sqrt t : ℂ) • v i) (fun j => (Real.sqrt (1-t) : ℂ) • w j)

end

open scoped BigOperators
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end EnsembleL2

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

def ensemble (i : S.I) : E := (Real.sqrt (S.p i) : ℂ) • S.basis i

end ThermalSpectral.Space

namespace EnsembleL2
open scoped ComplexConjugate
variable {E I J K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end EnsembleL2

namespace BKM
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
def mean (b : HilbertBasis J ℂ E) (p : J → ℝ) (Z : E →L[ℂ] E) : ℂ :=
  ∑' j, (p j : ℂ)*entry b Z j j
def center (b : HilbertBasis J ℂ E) (p : J → ℝ) (Z : E →L[ℂ] E) : E →L[ℂ] E :=
  Z-mean b p Z • ContinuousLinearMap.id ℂ E
end BKM

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace TensorLp
open KrausBounded
variable {A B I J : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp KrausBounded
open scoped BigOperators ComplexConjugate

abbrev RawIndex (n : ℕ) := (NumberIndex n × NumberIndex n) ×
  (NumberIndex n × (NumberIndex n × NumberIndex n))

def rawEnsemble {n : ℕ} (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (ik : RawIndex n) : Fock n :=
  rawJointKraus η θ hη hθ τ ik.2 (tensor (rootColumn ρ ik.1.1) (rootColumn σ ik.1.2))

def rawEnsembleEquiv (n : ℕ) : RawIndex n ≃
    (NumberIndex n × NumberIndex n) × (NumberIndex n × (NumberIndex n × NumberIndex n)) where
  toFun i := (i.2.2, (i.2.1,i.1))
  invFun i := (i.2.2,(i.2.1,i.1))
  left_inv _ := rfl
  right_inv _ := rfl

end EntropyPhotonNumber

namespace EnsembleL2
open scoped ComplexConjugate
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end EnsembleL2

namespace EntropyPhotonNumber
open TensorLp KrausBounded
open scoped BigOperators ComplexConjugate
variable {n : ℕ}

def rawFirstSlice (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (σ τ : State n) (Z : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  conditionalLeft (rootColumn σ) (rootColumn_norm σ) (rawDual η θ hη hθ τ Z)

def rawSecondSlice (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ τ : State n) (Z : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  conditionalRight (rootColumn ρ) (rootColumn_norm ρ) (rawDual η θ hη hθ τ Z)

end EntropyPhotonNumber

namespace EnsembleL2
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end EnsembleL2

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace EntropyPhotonNumber
open ThermalSpectral ThermalSpectral.Space
variable {n : ℕ}

end EntropyPhotonNumber

namespace BKM

section
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem entry_add (b : HilbertBasis J ℂ E) (Z T : E →L[ℂ] E) (i j : J) :
    entry b (Z+T) i j=entry b Z i j+entry b T i j := by simp [entry]
theorem entry_smul (b : HilbertBasis J ℂ E) (c : ℂ) (Z : E →L[ℂ] E) (i j : J) :
    entry b (c • Z) i j=c*entry b Z i j := by simp [entry]
theorem entry_norm_le (b : HilbertBasis J ℂ E) (Z : E →L[ℂ] E) (i j : J) :
    ‖entry b Z i j‖ ≤ ‖Z‖ := by
  calc
    _ ≤ ‖b i‖*‖Z (b j)‖ := norm_inner_le_norm _ _
    _ ≤ ‖b i‖*(‖Z‖*‖b j‖) := mul_le_mul_of_nonneg_left (Z.le_opNorm _) (norm_nonneg _)
    _ = ‖Z‖ := by simp [b.orthonormal.norm_eq_one]

theorem mean_summable (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p)
    (Z : E →L[ℂ] E) : Summable (fun j => (p j : ℂ)*entry b Z j j) := by
  apply (hs.mul_right ‖Z‖).of_norm_bounded
  intro j
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp j)]
  exact mul_le_mul_of_nonneg_left (entry_norm_le b Z j j) (hp j)

theorem mean_add (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p)
    (Z T : E →L[ℂ] E) : mean b p (Z+T)=mean b p Z+mean b p T := by
  simp only [mean, entry_add, mul_add]
  exact (mean_summable b p hp hs Z).tsum_add (mean_summable b p hp hs T)

theorem mean_smul (b : HilbertBasis J ℂ E) (p : J → ℝ) (c : ℂ) (Z : E →L[ℂ] E) :
    mean b p (c • Z)=c*mean b p Z := by
  simp only [mean, entry_smul, mul_left_comm (p _ : ℂ) c, tsum_mul_left]

end

section
open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def centerLM (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p) :
    (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E) where
  toFun := center b p
  map_add' Z T := by simp only [center, mean_add b p hp hs, add_smul]; abel
  map_smul' c Z := by simp [center, mean_smul, smul_sub, smul_smul]

@[simp] theorem centerLM_apply (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p)
    (Z : E →L[ℂ] E) : centerLM b p hp hs Z = center b p Z := rfl

end

open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
end BKM

namespace CenteredTests
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end CenteredTests

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

def normalize (lam : ℝ) : (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E) :=
  (Real.sqrt lam : ℂ)⁻¹ • BKM.centerLM S.basis S.p (fun j => (S.pos j).le) S.sum.summable

end ThermalSpectral.Space

namespace EntropyPhotonNumber
open TensorLp KrausBounded ThermalSpectral ThermalSpectral.Space
variable {n : ℕ}

def rawFirstSliceLM (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (σ τ : State n) : (Fock n →L[ℂ] Fock n) →ₗ[ℂ] (Fock n →L[ℂ] Fock n) where
  toFun := rawFirstSlice η θ hη hθ σ τ
  map_add' Z T := by simp only [rawFirstSlice, conditionalLeft, rawDual, dual_add]
  map_smul' c Z := by simp only [rawFirstSlice, conditionalLeft, rawDual, dual_smul, RingHom.id_apply]

def rawSecondSliceLM (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ τ : State n) : (Fock n →L[ℂ] Fock n) →ₗ[ℂ] (Fock n →L[ℂ] Fock n) where
  toFun := rawSecondSlice η θ hη hθ ρ τ
  map_add' Z T := by simp only [rawSecondSlice, conditionalRight, rawDual, dual_add]
  map_smul' c Z := by simp only [rawSecondSlice, conditionalRight, rawDual, dual_smul, RingHom.id_apply]

def normalizedSlices (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (S : Fin 2 → Space (Fock n)) (lam : Fin 2 → ℝ) :
    (i : Fin 2) → (Fock n →L[ℂ] Fock n) →ₗ[ℂ] (Fock n →L[ℂ] Fock n) :=
  ![((S 0).normalize (lam 0)).comp (rawFirstSliceLM η θ hη hθ σ τ),
    ((S 1).normalize (lam 1)).comp (rawSecondSliceLM η θ hη hθ ρ τ)]

end EntropyPhotonNumber

namespace BKM
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
def quadratic (b : HilbertBasis J ℂ E) (p : J → ℝ) (Z : E →L[ℂ] E) : ℝ :=
  ∑' ij : J × J, logMean (p ij.1) (p ij.2)*Complex.normSq (entry b Z ij.1 ij.2)
end BKM

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalSpectral

namespace EntropyPhotonNumber
open TensorLp KrausBounded ThermalSpectral ThermalSpectral.Space ThermalMetric
variable {n : ℕ}

end EntropyPhotonNumber

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

def thermalSpace (t : ℝ) (ht : 0<t) : ThermalSpectral.Space (Fock n) where
  I := G.J
  basis := G.basis
  p := G.probability
  pos := G.probability_pos
  sum := G.probability_sum
  r := t
  rpos := ht

theorem inverse_spectralColumns_operator :
    CrossEnsemble.operator (fun r => inverseWeight 3 (G.spectralColumns r))
      (fun r => inverseWeight 3 (G.spectralColumns r))=ρ.op := by
  simp only [G.spectralColumns_inverse]
  exact CrossEnsemble.eigenEnsemble_operator G.basis G.probability
    (fun r => (G.probability_pos r).le) G.probability_sum.summable ρ.op ρ.positive.isSymmetric G.eigen

def weightedColumns : WeightedColumns ρ where
  Index := G.J
  vector := G.spectralColumns
  summable := G.spectralColumns_summable
  normalized := G.spectralColumns_normalized
  density := G.inverse_spectralColumns_operator

def ambientDefect (t : ℝ) (ht : 0<t) (j : Fin n) : lp (fun _ : G.J × G.J => ℂ) 2 →L[ℂ] ℂ :=
  defectFunctional t ht G.probability G.probability_pos (G.centeredMatrix j)
    (G.centeredMatrix_defect_summable t j)

end EntropyPhotonNumber.SpectralLogData

end

end OAI
