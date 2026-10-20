/-
prove2.me platform library module `Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_InformationTheory_PhotonNumber_BeamForms.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/BeamForms.lean by skeleton subtraction
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

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

def preLowerL (j : Fin n) : JointFock n →L[ℂ] JointFock n := lowerL j ∘L (1-inverse)
def preLowerR (j : Fin n) : JointFock n →L[ℂ] JointFock n := lowerR j ∘L (1-inverse)
def preRaiseL (j : Fin n) : JointFock n →L[ℂ] JointFock n := raiseL j ∘L (1+inverse)
def preRaiseR (j : Fin n) : JointFock n →L[ℂ] JointFock n := raiseR j ∘L (1+inverse)

def quadMinusL (j : Fin n) (x y : JointFock n) (Z : JointFock n →L[ℂ] JointFock n) : ℂ :=
  inner ℂ (lowerL j (inverse x)) (Z (lowerL j (inverse y)))-
    (2:ℂ)⁻¹*(inner ℂ (inverse (inverse x)) (Z (raiseL j (preLowerL j y)))+
      inner ℂ (raiseL j (preLowerL j x)) (Z (inverse (inverse y))))
def quadMinusR (j : Fin n) (x y : JointFock n) (Z : JointFock n →L[ℂ] JointFock n) : ℂ :=
  inner ℂ (lowerR j (inverse x)) (Z (lowerR j (inverse y)))-
    (2:ℂ)⁻¹*(inner ℂ (inverse (inverse x)) (Z (raiseR j (preLowerR j y)))+
      inner ℂ (raiseR j (preLowerR j x)) (Z (inverse (inverse y))))
def quadPlusL (j : Fin n) (x y : JointFock n) (Z : JointFock n →L[ℂ] JointFock n) : ℂ :=
  inner ℂ (raiseL j (inverse x)) (Z (raiseL j (inverse y)))-
    (2:ℂ)⁻¹*(inner ℂ (inverse (inverse x)) (Z (lowerL j (preRaiseL j y)))+
      inner ℂ (lowerL j (preRaiseL j x)) (Z (inverse (inverse y))))
def quadPlusR (j : Fin n) (x y : JointFock n) (Z : JointFock n →L[ℂ] JointFock n) : ℂ :=
  inner ℂ (raiseR j (inverse x)) (Z (raiseR j (inverse y)))-
    (2:ℂ)⁻¹*(inner ℂ (inverse (inverse x)) (Z (lowerR j (preRaiseR j y)))+
      inner ℂ (lowerR j (preRaiseR j x)) (Z (inverse (inverse y))))

def crossMinus (j : Fin n) (x y : JointFock n) (T : JointFock n →L[ℂ] JointFock n) : ℂ :=
  inner ℂ (lowerL j (inverse x)) (T (lowerR j (inverse y)))+
  inner ℂ (lowerR j (inverse x)) (T (lowerL j (inverse y)))-
  (2:ℂ)⁻¹*(inner ℂ (inverse (inverse x)) (T (raiseL j (preLowerR j y)))+
    inner ℂ (inverse (inverse x)) (T (raiseR j (preLowerL j y)))+
    inner ℂ (raiseL j (preLowerR j x)) (T (inverse (inverse y)))+
    inner ℂ (raiseR j (preLowerL j x)) (T (inverse (inverse y))))

def crossPlus (j : Fin n) (x y : JointFock n) (T : JointFock n →L[ℂ] JointFock n) : ℂ :=
  inner ℂ (raiseL j (inverse x)) (T (raiseR j (inverse y)))+
  inner ℂ (raiseR j (inverse x)) (T (raiseL j (inverse y)))-
  (2:ℂ)⁻¹*(inner ℂ (inverse (inverse x)) (T (lowerL j (preRaiseR j y)))+
    inner ℂ (inverse (inverse x)) (T (lowerR j (preRaiseL j y)))+
    inner ℂ (lowerL j (preRaiseR j x)) (T (inverse (inverse y)))+
    inner ℂ (lowerR j (preRaiseL j x)) (T (inverse (inverse y))))

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

def tensorPreimage2 (x y : Fock n) : JointFock n :=
  tensor (inverseWeight 1 x) (inverseWeight 3 y)+
    tensor (inverseWeight 3 x) (inverseWeight 1 y)+
    tensor (inverseWeight 3 x) (inverseWeight 3 y)+
    (2:ℂ) • tensor (inverseWeight 2 x) (inverseWeight 2 y)-
    (2:ℂ) • tensor (inverseWeight 2 x) (inverseWeight 3 y)-
    (2:ℂ) • tensor (inverseWeight 3 x) (inverseWeight 2 y)

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

def generatorPairingL (r : ℝ) (x y : I → JointFock n)
    (Z : JointFock n →L[ℂ] JointFock n) : ℂ :=
  ∑ j, (((r+1:ℝ):ℂ)*(∑' i, quadMinusL j (x i) (y i) Z)+
    (r:ℂ)*(∑' i, quadPlusL j (x i) (y i) Z))
def generatorPairingR (r : ℝ) (x y : I → JointFock n)
    (Z : JointFock n →L[ℂ] JointFock n) : ℂ :=
  ∑ j, (((r+1:ℝ):ℂ)*(∑' i, quadMinusR j (x i) (y i) Z)+
    (r:ℂ)*(∑' i, quadPlusR j (x i) (y i) Z))

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

def singleGeneratorPairing (r : ℝ) (x : I → Fock n) (Z : Fock n →L[ℂ] Fock n) : ℂ :=
  ∑ j, (((r+1:ℝ):ℂ)*(CrossEnsemble.pairing
      (fun i => sandwich 0 3 (by omega) j (x i)) (fun i => sandwich 0 3 (by omega) j (x i)) Z-
    (2:ℂ)⁻¹*(CrossEnsemble.pairing (fun i => inverseWeight 2 (modeBound j false (x i))) (fun i => inverseWeight 3 (x i)) Z+
      CrossEnsemble.pairing (fun i => inverseWeight 3 (x i)) (fun i => inverseWeight 2 (modeBound j false (x i))) Z))+
    (r:ℂ)*(CrossEnsemble.pairing
      (fun i => creationSandwich 0 3 (by omega) j (x i)) (fun i => creationSandwich 0 3 (by omega) j (x i)) Z-
    (2:ℂ)⁻¹*(CrossEnsemble.pairing (fun i => inverseWeight 2 (modeBound j true (x i))) (fun i => inverseWeight 3 (x i)) Z+
      CrossEnsemble.pairing (fun i => inverseWeight 3 (x i)) (fun i => inverseWeight 2 (modeBound j true (x i))) Z)))

end BeamLadder

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end CrossEnsemble

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

def tensorRatio (ke : NumberIndex n × NumberIndex n) : ℝ :=
  W ke/(numberWeight ke.1*numberWeight ke.2)

def retainedRatio (ke : NumberIndex n × NumberIndex n) : ℝ := numberWeight ke.1/W ke

theorem tensorRatio_mem (ke : NumberIndex n × NumberIndex n) : tensorRatio ke ∈ Set.Icc 0 1 := by
  have h1 := numberWeight_one_le ke.1
  have h2 := numberWeight_one_le ke.2
  have hw : 0<W ke := by linarith [W_one_le ke]
  have hd : 0<numberWeight ke.1*numberWeight ke.2 := mul_pos (by linarith) (by linarith)
  refine ⟨div_nonneg hw.le hd.le, (div_le_one hd).mpr ?_⟩
  dsimp [W]
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

theorem retainedRatio_mem (ke : NumberIndex n × NumberIndex n) : retainedRatio ke ∈ Set.Icc 0 1 := by
  have hw : 0<W ke := by linarith [W_one_le ke]
  refine ⟨div_nonneg (by linarith [numberWeight_one_le ke.1]) hw.le, (div_le_one hw).mpr ?_⟩
  dsimp [W]
  linarith [numberWeight_one_le ke.2]

theorem ratioSquare_norm {a : ℝ} (ha : a ∈ Set.Icc 0 1) : ‖(a^2:ℝ) • (1:ℂ)‖≤1 := by
  simp only [norm_smul, norm_one, mul_one, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
  nlinarith [ha.1,ha.2]

def tensorRatioCLM : JointFock n →L[ℂ] JointFock n :=
  WeightedShift.pullCLM id Function.injective_id (fun ke => ((tensorRatio ke)^2:ℂ))
    1 (by norm_num) (fun ke => by simpa only [Complex.real_smul,mul_one,Complex.ofReal_pow] using ratioSquare_norm (tensorRatio_mem ke))

def retainedRatioCLM : JointFock n →L[ℂ] JointFock n :=
  WeightedShift.pullCLM id Function.injective_id (fun ke => ((retainedRatio ke)^2:ℂ))
    1 (by norm_num) (fun ke => by simpa only [Complex.real_smul,mul_one,Complex.ofReal_pow] using ratioSquare_norm (retainedRatio_mem ke))

def weightedColumn (η : ℝ) (hη : η ∈ Set.Icc 0 1) (y : Fock n) : Fock n →L[ℂ] JointFock n :=
  retainedRatioCLM ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    tensorRatioCLM ∘L tensorRight y

@[simp] theorem weightedColumn_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (x y : Fock n) :
    weightedColumn η hη y x = retainedRatioCLM (beamUnitary η hη (tensorRatioCLM (tensor x y))) := rfl

end BeamLadder

namespace EnsemblePullback

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {I : Type*}

def compression (V : E →L[ℂ] F) (Z : F →L[ℂ] F) : E →L[ℂ] E :=
  V.adjoint ∘L Z ∘L V

def pullback (V : I → E →L[ℂ] F) (Z : F →L[ℂ] F) : E →L[ℂ] E :=
  ∑' i, compression (V i) Z

end

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {I J : Type*}

end EnsemblePullback

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

def weightedConditional (η : ℝ) (hη : η ∈ Set.Icc 0 1) (y : J → Fock n)
    (B : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  EnsemblePullback.pullback (fun j => weightedColumn η hη (y j)) (liftLeft B)

def weightedSlices (η : ℝ) (hη : η ∈ Set.Icc 0 1) (y : J → Fock n)
    (x : I → Fock n) (ije : (I × J) × NumberIndex n) : Fock n :=
  slice (weightedColumn η hη (y ije.1.2) (x ije.1.1)) ije.2

end BeamLadder

namespace CrossEnsemble
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {I : Type*}
end CrossEnsemble

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

end Annihilation

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I : Type*}

end BeamLadder

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I K : Type*}

def pushedDissipator (F : (I → Fock n) → K → Fock n) (x : I → Fock n)
    (j : Fin n) (upward : Bool) : Fock n →L[ℂ] Fock n :=
  CrossEnsemble.operator (F (fun i => gain j upward (x i))) (F (fun i => gain j upward (x i)))-
    (2:ℂ)⁻¹ • (CrossEnsemble.operator (F (fun i => modeBound j upward (x i))) (F (fun i => inverseWeight 1 (x i)))+
      CrossEnsemble.operator (F (fun i => inverseWeight 1 (x i))) (F (fun i => modeBound j upward (x i))))

def pushedGenerator (F : (I → Fock n) → K → Fock n) (r : ℝ) (x : I → Fock n) : Fock n →L[ℂ] Fock n :=
  ∑ j, (((r+1:ℝ):ℂ) • pushedDissipator F x j false+(r:ℂ) • pushedDissipator F x j true)

def pushedPairing (F : (I → Fock n) → K → Fock n) (r : ℝ) (x : I → Fock n)
    (Z : Fock n →L[ℂ] Fock n) : ℂ :=
  ∑ j, (((r+1:ℝ):ℂ)*(CrossEnsemble.pairing (F (fun i => gain j false (x i))) (F (fun i => gain j false (x i))) Z-
      (2:ℂ)⁻¹*(CrossEnsemble.pairing (F (fun i => modeBound j false (x i))) (F (fun i => inverseWeight 1 (x i))) Z+
        CrossEnsemble.pairing (F (fun i => inverseWeight 1 (x i))) (F (fun i => modeBound j false (x i))) Z))+
    (r:ℂ)*(CrossEnsemble.pairing (F (fun i => gain j true (x i))) (F (fun i => gain j true (x i))) Z-
      (2:ℂ)⁻¹*(CrossEnsemble.pairing (F (fun i => modeBound j true (x i))) (F (fun i => inverseWeight 1 (x i))) Z+
        CrossEnsemble.pairing (F (fun i => inverseWeight 1 (x i))) (F (fun i => modeBound j true (x i))) Z)))

end WeightedGenerator

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

def weightedColumnRight (η : ℝ) (hη : η ∈ Set.Icc 0 1) (y : Fock n) : Fock n →L[ℂ] JointFock n :=
  retainedRatioCLM ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    tensorRatioCLM ∘L tensorLeft y

@[simp] theorem weightedColumnRight_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (x y : Fock n) :
    weightedColumnRight η hη y x = retainedRatioCLM (beamUnitary η hη (tensorRatioCLM (tensor y x))) := rfl

def weightedConditionalRight (η : ℝ) (hη : η ∈ Set.Icc 0 1) (y : J → Fock n)
    (B : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  EnsemblePullback.pullback (fun j => weightedColumnRight η hη (y j)) (liftLeft B)

def weightedSlicesRight (η : ℝ) (hη : η ∈ Set.Icc 0 1) (y : J → Fock n)
    (x : I → Fock n) (ije : (I × J) × NumberIndex n) : Fock n :=
  slice (weightedColumnRight η hη (y ije.1.2) (x ije.1.1)) ije.2

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end BeamLadder

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I : Type*}

end CrossEnsemble

end

end OAI
