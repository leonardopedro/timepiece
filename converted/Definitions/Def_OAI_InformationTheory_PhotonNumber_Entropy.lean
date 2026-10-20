/-
prove2.me platform library module `Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_InformationTheory_PhotonNumber_Entropy.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Entropy.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace Annihilation
open EntropyPhotonNumber QuantumTrace WeightedShift
open scoped ComplexConjugate
variable {n : ℕ}

def diagonal (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ k, |f k| ≤ C) :
    Fock n →L[ℂ] Fock n :=
  pullCLM id Function.injective_id (fun k => (f k:ℂ)) C hC
    (fun k => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hf k)

@[simp] theorem diagonal_apply (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k| ≤ C) (x : Fock n) (k : NumberIndex n) :
    diagonal f C hC hf x k=(f k:ℂ)*x k := rfl

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped BigOperators
variable {n : ℕ} {I : Type*}

def columnPairing (r : ℝ) (x : Fock n) (Z : Fock n →L[ℂ] Fock n) : ℝ :=
  ∑ j, ((r+1)*((inner ℂ (gain j false x) (Z (gain j false x))).re-
      ((inner ℂ (inverseWeight 1 x) (Z (modeBound j false x))).re+
       (inner ℂ (modeBound j false x) (Z (inverseWeight 1 x))).re)/2)+
    r*((inner ℂ (gain j true x) (Z (gain j true x))).re-
      ((inner ℂ (inverseWeight 1 x) (Z (modeBound j true x))).re+
       (inner ℂ (modeBound j true x) (Z (inverseWeight 1 x))).re)/2))

def drift (r : ℝ) (f : NumberIndex n → ℝ) (k : NumberIndex n) : ℝ :=
  ∑ j, ((r+1)*(k j:ℝ)*(f (down j k)-f k)+r*((k j:ℝ)+1)*(f (up j k)-f k))

def componentPairing (r : ℝ) (x : Fock n) (Z : Fock n →L[ℂ] Fock n) (j : Fin n) : ℝ :=
  (r+1)*((inner ℂ (gain j false x) (Z (gain j false x))).re-
    ((inner ℂ (inverseWeight 1 x) (Z (modeBound j false x))).re+
     (inner ℂ (modeBound j false x) (Z (inverseWeight 1 x))).re)/2)+
  r*((inner ℂ (gain j true x) (Z (gain j true x))).re-
    ((inner ℂ (inverseWeight 1 x) (Z (modeBound j true x))).re+
     (inner ℂ (modeBound j true x) (Z (inverseWeight 1 x))).re)/2)

end WeightedGenerator

namespace WeightedShift
variable {I K : Type*}
end WeightedShift

namespace EntropyPhotonNumber
open QuantumTrace WeightedShift Annihilation
variable {n : ℕ}

end EntropyPhotonNumber

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

namespace QuantumTrace

section
open Filter Topology

def numberBox (n K : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset (fun _ => Finset.range (K + 1))

open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

end

section
open ContinuousLinearMap InnerProductSpace Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

def basisProjection (b : HilbertBasis ι ℂ H) (s : Finset ι) : H →L[ℂ] H :=
  basisApprox b (ContinuousLinearMap.id ℂ H) s

omit [CompleteSpace H] in
theorem basisProjection_apply_basis (b : HilbertBasis ι ℂ H) (s : Finset ι) (j : ι)
    [Decidable (j ∈ s)] : basisProjection b s (b j) = if j ∈ s then b j else 0 := by
  simpa [basisProjection] using basisApprox_apply_basis b (ContinuousLinearMap.id ℂ H) s j

theorem basisProjection_adjoint (b : HilbertBasis ι ℂ H) (s : Finset ι) :
    adjoint (basisProjection b s) = basisProjection b s := by
  simp [basisProjection, basisApprox]

end

section
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def energySet {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H) (E : ℝ) : Set (H →L[ℂ] H) :=
  {T | T.IsPositive ∧
    HasSum (fun k => (inner ℂ (b k) (T (b k))).re) 1 ∧
    Summable (fun k => (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re) ∧
    (∑' k, (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re) ≤ E}

end

section
open ContinuousLinearMap InnerProductSpace Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

def matrixEmbed (b : HilbertBasis ι ℂ H) (s : Finset ι) (c : s → s → ℂ) : H →L[ℂ] H :=
  ∑ i, ∑ j, c i j • rankOne ℂ (b i) (b j)

end

section
open ContinuousLinearMap Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def momentSet {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H)
    (w : (Fin n → ℕ) → ℝ) (E M : ℝ) : Set (H →L[ℂ] H) :=
  {T | T ∈ energySet b E ∧
    Summable (fun k => w k * (inner ℂ (b k) (T (b k))).re) ∧
    (∑' k, w k * (inner ℂ (b k) (T (b k))).re) ≤ M}

end QuantumTrace

end

namespace EntropyPhotonNumber
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

def energy {n : ℕ} (ρ : State n) : ℝ :=
  ∑' k, (totalNumber k : ℝ) * (entry ρ.op k k).re

theorem energy_nonneg {n : ℕ} (ρ : State n) : 0 ≤ energy ρ := by
  exact tsum_nonneg (fun k => mul_nonneg (Nat.cast_nonneg _)
    (ρ.positive.re_inner_nonneg_right _))

end EntropyPhotonNumber

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal

namespace TraceEnsemble
open Filter Topology
open scoped BigOperators
variable {I A E G : Type*}
variable [NormedAddCommGroup G] [CompleteSpace G]

variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end TraceEnsemble

namespace TensorLp
variable {A B : Type*}

def tensorBilinear : H A →L[ℂ] H B →L[ℂ] H (A × B) :=
  LinearMap.mkContinuous
    { toFun := tensorLeft
      map_add' := fun x y => by
        apply ContinuousLinearMap.ext
        intro z
        apply lp.ext
        funext ab
        change (x ab.1+y ab.1)*z ab.2 = x ab.1*z ab.2 + y ab.1*z ab.2
        ring
      map_smul' := fun c x => by
        apply ContinuousLinearMap.ext
        intro z
        apply lp.ext
        funext ab
        change (c*x ab.1)*z ab.2 = c*(x ab.1*z ab.2)
        ring }
    1 (fun x => by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro y
      change ‖tensor x y‖ ≤ (1*‖x‖)*‖y‖
      rw [tensor_norm, one_mul])

@[simp] theorem tensorBilinear_apply (x : H A) (y : H B) : tensorBilinear x y = tensor x y := rfl

end TensorLp

namespace EntropyPhotonNumber

section
open Filter Topology TensorLp

end

open QuantumTrace TraceEnsemble
@[simp] theorem mixture_entry {n : ℕ} (t : ℝ) (ht : t ∈ Set.Icc 0 1) (ρ σ : State n)
    (k l : NumberIndex n) :
    entry (mixture t ht ρ σ).op k l = (t : ℂ)*entry ρ.op k l + ((1-t : ℝ) : ℂ)*entry σ.op k l := by
  simp only [mixture, entry, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_right, inner_smul_right]

end EntropyPhotonNumber

namespace QuantumTrace
open scoped ENNReal

theorem summable_finite_product (n : ℕ) (w : ℕ → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hs : Summable w) :
    Summable (fun k : Fin n → ℕ => ∏ j, w (k j)) := by
  have hh : (∑' k : Fin n → ℕ, ENNReal.ofReal (∏ j, w (k j))) < ⊤ := by
    simp only [ENNReal.ofReal_prod_of_nonneg (fun _ _ => hw _)]
    rw [tsum_finite_product n (fun k => ENNReal.ofReal (w k))]
    exact ENNReal.pow_lt_top hs.tsum_ofReal_lt_top
  have he := ENNReal.summable_toReal hh.ne
  simpa only [ENNReal.toReal_ofReal (Finset.prod_nonneg (fun _ _ => hw _))] using he

theorem one_add_sum_le_product {I : Type*} (s : Finset I) (a : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) : 1+∑ i ∈ s, a i ≤ ∏ i ∈ s, (1+a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hp : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg (fun j _ => ha j)
    have hm := mul_le_mul_of_nonneg_left ih (by linarith [ha i] : 0 ≤ 1+a i)
    nlinarith [mul_nonneg (ha i) hp]

theorem summable_shift_pow_geometric {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (m : ℕ) :
    Summable (fun k : ℕ => (1+(k : ℝ))^m*q^k) := by
  have hs := (summable_pow_mul_geometric_of_norm_lt_one m
    (show ‖q‖ < 1 by rwa [Real.norm_eq_abs, abs_of_pos hq])).comp_injective Nat.succ_injective
  convert hs.mul_left q⁻¹ using 1
  funext k
  change (1+(k : ℝ))^m*q^k = q⁻¹*((k+1 : ℕ)^m*q^(k+1))
  simp only [Nat.cast_succ, pow_succ]
  rw [add_comm (k : ℝ) 1]
  field_simp

theorem thermalWeight_moment_summable (n m : ℕ) {r : ℝ} (hr : 0 < r) :
    Summable (fun k : Fin n → ℕ => (1+∑ j, (k j : ℝ))^m * thermalWeight n r k) := by
  let q := r/(r+1)
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := (div_lt_one (by linarith : 0 < r+1)).mpr (by linarith)
  have hs := summable_finite_product n
    (fun k => (1+(k : ℝ))^m*((r+1)⁻¹*q^k))
    (fun _ => by positivity)
    (by simpa only [mul_left_comm _ (r+1)⁻¹] using
      (summable_shift_pow_geometric hq hq1 m).mul_left (r+1)⁻¹)
  apply Summable.of_nonneg_of_le (fun _ => by apply mul_nonneg _ (thermalWeight_pos n hr _).le; positivity) _ hs
  intro k
  have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1+∑ j, (k j : ℝ))
    (one_add_sum_le_product Finset.univ (fun j => (k j : ℝ)) (fun _ => Nat.cast_nonneg _)) m
  have hh := mul_le_mul_of_nonneg_right h (thermalWeight_pos n hr k).le
  simpa only [← Finset.prod_pow, thermalWeight, ← Finset.prod_mul_distrib, q] using hh

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace
theorem thermalState_finiteMoment (n m : ℕ) (r : ℝ) (hr : 0 < r) :
    FiniteMoment m (thermalState n r hr) := by
  simpa only [FiniteMoment, thermalState_diagonal, totalNumber, Nat.cast_sum] using
    thermalWeight_moment_summable n m hr

theorem finiteMoment_finiteEnergy {n m : ℕ} (hm : 1 ≤ m) {ρ : State n} (hρ : FiniteMoment m ρ) :
    FiniteEnergy ρ := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (Nat.cast_nonneg _) (ρ.positive.re_inner_nonneg_right _)) _ hρ
  intro k
  have h : (1+(totalNumber k : ℝ))^1 ≤ (1+(totalNumber k : ℝ))^m :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) (totalNumber k)]) hm
  exact mul_le_mul_of_nonneg_right (by simpa only [pow_one] using (by linarith :
    (totalNumber k : ℝ) ≤ (1+(totalNumber k : ℝ))^m)) (ρ.positive.re_inner_nonneg_right _)

theorem thermalState_finiteEnergy (n : ℕ) (r : ℝ) (hr : 0 < r) :
    FiniteEnergy (thermalState n r hr) :=
  finiteMoment_finiteEnergy le_rfl (thermalState_finiteMoment n 1 r hr)

end

open QuantumTrace Filter Topology

theorem energyMoment_ofReal {n : ℕ} {ρ : State n} (hρ : FiniteEnergy ρ) :
    energyMoment ρ = ENNReal.ofReal (energy ρ) := by
  rw [energyMoment_eq]
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun k => mul_nonneg (Nat.cast_nonneg _) (ρ.positive.re_inner_nonneg_right _)) hρ).symm

def regularizedOutput {n : ℕ} (η δ κ : ℝ) (hη : η ∈ Set.Icc 0 1)
    (hδ : δ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1) (τD τ0 ρ σ : State n) : State n :=
  mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
    (beamOutput (1-δ) ⟨sub_nonneg.mpr hδ.2, sub_le_self _ hδ.1⟩
      (beamOutput η hη ρ σ) τD) τ0

instance stateTopology (n : ℕ) : TopologicalSpace (State n) :=
  TopologicalSpace.induced State.op inferInstance

def boundedStates (n : ℕ) (E M : ℝ) : Set (State n) :=
  {ρ | FiniteEnergy ρ ∧ energy ρ ≤ E ∧ FiniteMoment 4 ρ ∧ numberMoment 4 ρ ≤ M}

def stateOfMomentSet {n : ℕ} {E M : ℝ}
    (T : momentSet (numberBasis n) (fun k => (1+(totalNumber k : ℝ))^4) E M) : State n where
  op := T.val
  positive := T.property.1.1
  trace_one := by simpa only [numberBasis_apply, entry] using T.property.1.2.1

structure Regularization (n : ℕ) where
  η : ℝ
  δ : ℝ
  κ : ℝ
  hη : η ∈ Set.Icc 0 1
  hδ : δ ∈ Set.Icc 0 1
  hκ : κ ∈ Set.Icc 0 1
  τD : State n
  τ0 : State n
  finiteD : FiniteEnergy τD
  finite0 : FiniteEnergy τ0
  c : ℝ
  a1 : ℝ
  a2 : ℝ
  b1 : ℝ
  b2 : ℝ
  ζ : ℝ
  hc : 0 < c
  ha1 : 0 < a1
  ha2 : 0 < a2
  hb1 : 0 < b1
  hb2 : 0 < b2
  hζ : 0 < ζ

namespace Regularization
variable {n : ℕ} (R : Regularization n)

def output (ρ σ : State n) : State n :=
  regularizedOutput R.η R.δ R.κ R.hη R.hδ R.hκ R.τD R.τ0 ρ σ

def objective (ρ σ : State n) : ℝ :=
  R.c*entropy (R.output ρ σ)-R.a1*entropy ρ-R.a2*entropy σ+
    (R.b1*energy ρ+R.ζ*numberMoment 4 ρ)+(R.b2*energy σ+R.ζ*numberMoment 4 σ)

def entropyConstant : ℝ :=
  R.a1*n*Real.log (2*R.a1/R.b1+1)+R.a2*n*Real.log (2*R.a2/R.b2+1)

end Regularization
end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I J : Type*}

def basisMoment (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞) (x : E) : ℝ≥0∞ :=
  ∑' i, w i*ENNReal.ofReal (‖inner ℂ (b i) x‖^2)

def basisExpectation (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞) (T : E →L[ℂ] E) : ℝ≥0∞ :=
  ∑' i, w i*ENNReal.ofReal (inner ℂ (b i) (T (b i))).re

variable [CompleteSpace E]

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace

def numberVectorMoment {n : ℕ} (x : Fock n) : ℝ≥0∞ :=
  basisMoment (numberBasis n) (fun k => (totalNumber k : ℝ≥0∞)) x

end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

def sliceMoment (b : HilbertBasis J ℂ E) (w : J → ℝ≥0∞)
    (V : I → E →L[ℂ] E) (x : E) : ℝ≥0∞ := ∑' i, basisMoment b w (V i x)

def sliceCoordinates (b : HilbertBasis J ℂ E) (w : J → ℝ)
    (V : I → E →L[ℂ] E) (S : E →L[ℂ] E) (ij : I × J) : E →ₗ[ℂ] ℂ :=
  (Real.sqrt (w ij.2) : ℂ) • ((innerSL ℂ (b ij.2)).toLinearMap.comp
    ((V ij.1).toLinearMap.comp S.toLinearMap))

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace TensorLp

def energyInverse (n : ℕ) : Fock n →L[ℂ] Fock n :=
  inversePower rootNumberWeight rootNumberWeight_one_le 1

end

open QuantumTrace

end EntropyPhotonNumber

namespace QuantumTrace

section
variable {ι J L : Type*}

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace TensorLp

theorem composedKraus_first_ensemble {n : ℕ} {J : Type*}
    (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (ρ σ τ : State n)
    (v : J → Fock n) (hv : HasSum (fun j => ‖v j‖^2) 1)
    (he : TraceEnsemble.operator v = ρ.op) :
    TraceEnsemble.operator (fun z : ((NumberIndex n × NumberIndex n) ×
      (NumberIndex n × NumberIndex n)) × J =>
      composeKraus (firstKraus θ hθ τ) (firstKraus η hη σ) z.1 (v z.2)) =
      (beamOutput θ hθ (beamOutput η hη ρ σ) τ).op := by
  have hV := TraceEnsemble.kraus_hasSum (firstKraus_norm η hη σ) hv
  have heV := firstKraus_ensemble η hη ρ σ v hv he
  have heU := firstKraus_ensemble θ hθ (beamOutput η hη ρ σ) τ _ hV heV
  exact (composeKraus_ensemble (firstKraus θ hθ τ) (firstKraus η hη σ) v).trans heU

end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {J : Type*}

end QuantumTrace

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber
open QuantumTrace TraceEnsemble

end EntropyPhotonNumber

end

end OAI
