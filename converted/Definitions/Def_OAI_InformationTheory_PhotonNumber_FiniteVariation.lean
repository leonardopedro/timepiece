/-
prove2.me platform library module `Definitions.Def_OAI_InformationTheory_PhotonNumber_FiniteVariation`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_InformationTheory_PhotonNumber_FiniteVariation.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/FiniteVariation.lean by skeleton subtraction
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

namespace OAI

noncomputable section

section
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

namespace FiniteBlock

section
variable {I J E : Type*} [Fintype I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def embedLinear (b : HilbertBasis (I ⊕ J) ℂ E) : EuclideanSpace ℂ I →ₗ[ℂ] E :=
  (EuclideanSpace.basisFun I ℂ).toBasis.constr ℂ (fun i => b (Sum.inl i))

@[simp] theorem embedLinear_basis (b : HilbertBasis (I ⊕ J) ℂ E) (i : I) :
    embedLinear b ((EuclideanSpace.basisFun I ℂ) i) = b (Sum.inl i) := by
  exact (EuclideanSpace.basisFun I ℂ).toBasis.constr_basis ℂ _ i

theorem embedLinear_orthonormal (b : HilbertBasis (I ⊕ J) ℂ E) :
    Orthonormal ℂ (embedLinear b ∘ (EuclideanSpace.basisFun I ℂ).toBasis) := by
  have he : embedLinear b ∘ (EuclideanSpace.basisFun I ℂ).toBasis = (fun i => b (Sum.inl i)) := by
    funext i
    exact embedLinear_basis b i
  rw [he]
  exact b.orthonormal.comp Sum.inl Sum.inl_injective

def embed (b : HilbertBasis (I ⊕ J) ℂ E) : EuclideanSpace ℂ I →ₗᵢ[ℂ] E :=
  (embedLinear b).isometryOfOrthonormal (v := (EuclideanSpace.basisFun I ℂ).toBasis)
    (EuclideanSpace.basisFun I ℂ).orthonormal (embedLinear_orthonormal b)

@[simp] theorem embed_basis (b : HilbertBasis (I ⊕ J) ℂ E) (i : I) :
    embed b ((EuclideanSpace.basisFun I ℂ) i) = b (Sum.inl i) := embedLinear_basis b i

theorem embed_apply (b : HilbertBasis (I ⊕ J) ℂ E) (x : EuclideanSpace ℂ I) :
    embed b x = ∑ i, x i • b (Sum.inl i) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun I ℂ).sum_repr x]
  simp only [map_sum, map_smul, embed_basis]
  rfl

variable (b : HilbertBasis (I ⊕ J) ℂ E) (c : OrthonormalBasis I ℂ (EuclideanSpace ℂ I))

def vectors : I ⊕ J → E := Sum.elim (fun i => embed b (c i)) (fun j => b (Sum.inr j))

theorem vectors_orthonormal : Orthonormal ℂ (vectors b c) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simpa only [vectors, Sum.elim_inl, (embed b).inner_map_map,
        Sum.inl.injEq] using (orthonormal_iff_ite.mp c.orthonormal i j)
    | inr j =>
      simp only [vectors, Sum.elim_inl, Sum.elim_inr, Sum.inl_ne_inr, ↓reduceIte,
        embed_apply, sum_inner, inner_smul_left, orthonormal_iff_ite.mp b.orthonormal,
        mul_zero, Finset.sum_const_zero]
  | inr i =>
    cases j with
    | inl j =>
      simp only [vectors, Sum.elim_inl, Sum.elim_inr, Sum.inr_ne_inl, ↓reduceIte,
        embed_apply, inner_sum, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal,
        mul_zero, Finset.sum_const_zero]
    | inr j => simpa only [vectors, Sum.elim_inr, Sum.inr.injEq] using
        (orthonormal_iff_ite.mp b.orthonormal (Sum.inr i) (Sum.inr j))

variable [CompleteSpace E]

def basis : HilbertBasis (I ⊕ J) ℂ E := HilbertBasis.mk (vectors_orthonormal b c) (by
  have hsub : Submodule.span ℂ (Set.range b) ≤ Submodule.span ℂ (Set.range (vectors b c)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    cases i with
    | inr j => exact Submodule.subset_span ⟨Sum.inr j,rfl⟩
    | inl i =>
      rw [← embed_basis b i, ← c.sum_repr ((EuclideanSpace.basisFun I ℂ) i), map_sum]
      apply Submodule.sum_mem
      intro j _
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl j,rfl⟩)
  exact b.dense_span.ge.trans (Submodule.topologicalClosure_mono hsub))

@[simp] theorem basis_inl (i : I) : basis b c (Sum.inl i) = embed b (c i) :=
  congrFun (HilbertBasis.coe_mk _ _) _
@[simp] theorem basis_inr (j : J) : basis b c (Sum.inr j) = b (Sum.inr j) :=
  congrFun (HilbertBasis.coe_mk _ _) _

omit [CompleteSpace E] in

def block (M : Matrix I I ℂ) : E →L[ℂ] E :=
  ∑ i, ∑ j, M i j • InnerProductSpace.rankOne ℂ (b (Sum.inl i)) (b (Sum.inl j))

variable [DecidableEq I]

end

open NormedSpace Matrix
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

def partition {J : Type*} (p : I ⊕ J → ℝ) (M : Matrix I I ℂ) (hM : M.IsHermitian) : ℝ :=
  (∑' j, p (Sum.inr j)) + ∑ i, Real.exp (hM.eigenvalues i)

def weights {J : Type*} (p : I ⊕ J → ℝ) (M : Matrix I I ℂ) (hM : M.IsHermitian) : I ⊕ J → ℝ :=
  Sum.elim (fun i => Real.exp (hM.eigenvalues i) / partition p M hM)
    (fun j => p (Sum.inr j) / partition p M hM)

theorem partition_pos {J : Type*} (p : I ⊕ J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1) (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    0 < partition p M hM := by
  classical
  have htail := hs.summable.comp_injective Sum.inr_injective
  obtain ⟨j,hj⟩ : ∃ j, p j ≠ 0 := by
    by_contra! h
    have he : p = fun _ => 0 := funext h
    have : HasSum p 0 := by rw [he]; exact hasSum_zero
    exact zero_ne_one (this.unique hs)
  unfold partition
  cases j with
  | inl i =>
    exact add_pos_of_nonneg_of_pos (tsum_nonneg (fun j => (hp (Sum.inr j)).le))
      (Finset.sum_pos' (fun j _ => (Real.exp_pos _).le) ⟨i,Finset.mem_univ _,Real.exp_pos _⟩)
  | inr j =>
    exact add_pos_of_pos_of_nonneg
      ((hp (Sum.inr j)).trans_le (htail.le_tsum j (fun i _ => (hp _).le)))
      (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))

theorem weights_pos {J : Type*} (p : I ⊕ J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1) (M : Matrix I I ℂ) (hM : M.IsHermitian) (j : I ⊕ J) :
    0 < weights p M hM j := by
  cases j with
  | inl i => exact div_pos (Real.exp_pos _) (partition_pos p hp hs M hM)
  | inr j => exact div_pos (hp _) (partition_pos p hp hs M hM)

theorem weights_hasSum {J : Type*} (p : I ⊕ J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1) (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    HasSum (weights p M hM) 1 := by
  have ht := hs.summable.comp_injective Sum.inr_injective
  have hf : HasSum (Sum.elim (fun i => Real.exp (hM.eigenvalues i)) (fun j => p (Sum.inr j)))
      ((∑ i, Real.exp (hM.eigenvalues i)) + ∑' j, p (Sum.inr j)) :=
    HasSum.sum (hasSum_fintype _) ht.hasSum
  have hh := hf.div_const (partition p M hM)
  convert hh using 1
  · funext j
    cases j <;> rfl
  · rw [add_comm]
    change 1 = partition p M hM / partition p M hM
    exact (div_self (partition_pos p hp hs M hM).ne').symm

end FiniteBlock

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I J : Type*}

theorem basisMoment_smul_coeff (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞) (z : ℂ) (x : E) :
    basisMoment b w (z • x) = ENNReal.ofReal (‖z‖^2)*basisMoment b w x := by
  simp only [basisMoment, inner_smul_right, norm_mul, mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _)]
  rw [← ENNReal.tsum_mul_left]
  congr 1
  funext i
  exact mul_left_comm _ _ _

theorem basisMoment_add_le (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞) (x y : E) :
    basisMoment b w (x+y) ≤ 2*basisMoment b w x+2*basisMoment b w y := by
  simp only [basisMoment, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro i
  have hn : ‖inner ℂ (b i) (x+y)‖^2 ≤
      2*‖inner ℂ (b i) x‖^2+2*‖inner ℂ (b i) y‖^2 := by
    rw [inner_add_right]
    calc
      _ ≤ (‖inner ℂ (b i) x‖+‖inner ℂ (b i) y‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) _
      _ ≤ _ := by nlinarith [sq_nonneg (‖inner ℂ (b i) x‖-‖inner ℂ (b i) y‖)]
  calc
    _ ≤ w i*ENNReal.ofReal (2*‖inner ℂ (b i) x‖^2+2*‖inner ℂ (b i) y‖^2) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hn)
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      simp only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2), ENNReal.ofReal_ofNat]
      ring

def momentDomain (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞) : Submodule ℂ E where
  carrier := {x | basisMoment b w x < ⊤}
  zero_mem' := by simp [basisMoment]
  add_mem' := by
    intro x y hx hy
    exact (basisMoment_add_le b w x y).trans_lt (ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top (by norm_num) hx, ENNReal.mul_lt_top (by norm_num) hy⟩)
  smul_mem' := by
    intro z x hx
    change basisMoment b w (z • x) < ⊤
    rw [basisMoment_smul_coeff]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hx

@[simp] theorem mem_momentDomain (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞) (x : E) :
    x ∈ momentDomain b w ↔ basisMoment b w x < ⊤ := Iff.rfl

variable [CompleteSpace E]

end QuantumTrace

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

def expectation (v : I → E) (Z : E →L[ℂ] E) : ℂ :=
  ∑' i, inner ℂ (v i) (Z (v i))

end TraceEnsemble

namespace EntropyPhotonNumber

section
open TraceEnsemble

def expectation {n : ℕ} (ρ : State n) (Z : Fock n →L[ℂ] Fock n) : ℂ :=
  TraceEnsemble.expectation (rootColumn ρ) Z

end

open QuantumTrace TraceEnsemble

def spectralState {n : ℕ} {J : Type*} (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1) : State n where
  op := TraceEnsemble.operator (diagonalVector b p)
  positive := TraceEnsemble.positive (by simpa only [diagonalVector_norm_sq b p hp] using hs.summable)
  trace_one := by
    simpa only [numberBasis_apply, entry] using TraceEnsemble.trace
      (by simpa only [diagonalVector_norm_sq b p hp] using hs :
        HasSum (fun j => ‖diagonalVector b p j‖^2) 1) (numberBasis n)

@[simp] theorem spectralState_eigen {n : ℕ} {J : Type*} (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1) (j : J) :
    (spectralState b p hp hs).op (b j) = (p j : ℂ) • b j :=
  diagonalVector_eigen b p hp hs.summable j

def blockState {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1) (M : Matrix I I ℂ) (hM : M.IsHermitian) : State n :=
  spectralState (FiniteBlock.basis b hM.eigenvectorBasis) (FiniteBlock.weights p M hM)
    (fun j => (FiniteBlock.weights_pos p hp hs M hM j).le) (FiniteBlock.weights_hasSum p hp hs M hM)

end EntropyPhotonNumber

namespace FiniteBlock

section
open QuantumTrace
variable {I J E K : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FiniteBlock

namespace EntropyPhotonNumber
open QuantumTrace
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

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
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator

namespace FiniteBlock
variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FiniteBlock

namespace EntropyPhotonNumber

section
open QuantumTrace TraceEnsemble
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

end

section
open QuantumTrace
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

end

open QuantumTrace TraceEnsemble
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

end EntropyPhotonNumber

end

section
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

namespace QuantumCalculus

section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

local instance instNormedAlgebraRat_oAI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

end

section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
local instance instNormedAlgebraRat_oAI_1 : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

end

section
open scoped Matrix.Norms.Operator ComplexConjugate
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

def matrixReTrace : Matrix I I ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp (Matrix.traceLinearMap I ℝ ℂ).toContinuousLinearMap

omit [DecidableEq I] in
@[simp] theorem matrixReTrace_apply (M : Matrix I I ℂ) :
    matrixReTrace M = (Matrix.trace M).re := rfl

end

section
open Filter Asymptotics

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
local instance instNormedAlgebraRat_oAI_2 : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

end

section
open Matrix Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

end

section
open Filter Asymptotics
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
local instance instNormedAlgebraRat_oAI_3 : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

end

open Matrix Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

end QuantumCalculus

namespace FiniteBlock
open QuantumCalculus
variable {I J : Type*} [Fintype I] [DecidableEq I]

def tiltMatrix (p : I ⊕ J → ℝ) (Z : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  Matrix.diagonal (fun i => (Real.log (p (Sum.inl i)) : ℂ))+t • Z

omit [Fintype I] in
 theorem tiltMatrix_hermitian (p : I ⊕ J → ℝ) (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) (t : ℝ) :
    (tiltMatrix p Z t).IsHermitian := by
  exact (Matrix.isHermitian_diagonal_iff.mpr
    (by intro i; exact isSelfAdjoint_iff.mpr (Complex.conj_ofReal _))).add
      (show (t • Z).IsHermitian by unfold Matrix.IsHermitian at *; rw [Matrix.conjTranspose_smul, hZ]; simp)

end FiniteBlock

namespace EntropyPhotonNumber
open QuantumCalculus QuantumTrace Filter Asymptotics
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

def blockTilt (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1) (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) (t : ℝ) : State n :=
  blockState b p hp hs (FiniteBlock.tiltMatrix p Z t) (FiniteBlock.tiltMatrix_hermitian p Z hZ t)

end EntropyPhotonNumber

namespace FiniteBlock
variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def entries (b : HilbertBasis (I ⊕ J) ℂ E) (Z : E →L[ℂ] E) : Matrix I I ℂ :=
  fun i j => inner ℂ (b (Sum.inl i)) (Z (b (Sum.inl j)))

end FiniteBlock

namespace EntropyPhotonNumber
open QuantumTrace
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

end EntropyPhotonNumber

namespace QuantumCalculus
open Matrix Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

end QuantumCalculus

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

namespace QuantumCalculus

end QuantumCalculus

end

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

namespace EntropyPhotonNumber

section
open QuantumTrace TraceEnsemble
variable {n : ℕ}

def KrausFlow.dual (F : KrausFlow n) (Z : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  KrausBounded.dual F.V F.norm Z

end

section
open QuantumCalculus QuantumTrace Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

end

open QuantumCalculus QuantumTrace Filter Asymptotics

end EntropyPhotonNumber

namespace FiniteBlock
open DiagonalForms.System
variable {I J : Type*} [Fintype I]
def mean (p : I ⊕ J → ℝ) (X : Matrix I I ℂ) : ℝ := ∑ i, p (Sum.inl i)*(X i i).re

def variance (p : I ⊕ J → ℝ) (X : Matrix I I ℂ) : ℝ :=
  (∑ i, ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j))*Complex.normSq (X i j))-mean p X^2

def covariance (p : I ⊕ J → ℝ) (X Y : Matrix I I ℂ) (μ : ℝ) : ℝ :=
  (∑ i, ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j))*(X i j*Y j i).re)-μ*mean p X
end FiniteBlock

namespace EntropyPhotonNumber
open QuantumCalculus QuantumTrace Filter Asymptotics
open scoped Matrix.Norms.Operator

end EntropyPhotonNumber

namespace FiniteBlock
open DiagonalForms.System
open scoped ComplexConjugate
variable {I J : Type*} [Fintype I]

end FiniteBlock

namespace BKM
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end BKM

namespace EntropyPhotonNumber

section
open QuantumTrace DiagonalForms.System
open scoped ComplexConjugate
variable {n : ℕ} {J K L : Type*} [Fintype K] [DecidableEq K]

end

open QuantumTrace DiagonalForms.System
variable {n : ℕ} {K L : Type*} [Fintype K] [DecidableEq K]

end EntropyPhotonNumber

namespace BKM
open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

end BKM

namespace Complex
open scoped _root_.Complex
open scoped ComplexConjugate
end Complex

namespace BKM

section
open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
end

section
open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

def variance (b : HilbertBasis J ℂ E) (p : J → ℝ) (Z : E →L[ℂ] E) : ℝ :=
  quadratic b p Z - Complex.normSq (mean b p Z)

end

open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end BKM

namespace EntropyPhotonNumber

section
open scoped ComplexConjugate ComplexStarModule
variable {n : ℕ} {J : Type*}

end

section
open QuantumTrace DiagonalForms.System
open scoped ComplexStarModule
variable {n : ℕ} {K L J : Type*} [Fintype K] [DecidableEq K]

end

open QuantumTrace DiagonalForms.System
variable {n : ℕ} {J K L : Type*} [Fintype K] [DecidableEq K]
end EntropyPhotonNumber

namespace BKM
open scoped BigOperators
open DiagonalForms.System
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end BKM

namespace EntropyPhotonNumber
open QuantumTrace DiagonalForms.System
variable {n : ℕ} {J : Type*} [DecidableEq J]

end EntropyPhotonNumber

namespace BKM

section
open scoped BigOperators ComplexConjugate
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def vector (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : Summable p)
    (Z : E →L[ℂ] E) : lp (fun _ : J × J => ℂ) 2 :=
  EnsembleL2.vector (fun ij => (Real.sqrt (logMean (p ij.1) (p ij.2)):ℂ)*entry b Z ij.1 ij.2) (by
    convert logMean_summable b p hp hs Z using 1
    ext ij
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_ofReal,
      Real.mul_self_sqrt (logMean_pos (hp _) (hp _)).le])

@[simp] theorem vector_apply (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : Summable p)
    (Z : E →L[ℂ] E) (ij : J × J) :
    vector b p hp hs Z ij=(Real.sqrt (logMean (p ij.1) (p ij.2)):ℂ)*entry b Z ij.1 ij.2 := rfl

end

open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

end BKM

namespace CenteredTests
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
end CenteredTests

namespace EntropyPhotonNumber

section
open QuantumTrace DiagonalForms.System
variable {n : ℕ} {I J : Type*} [DecidableEq J]

end

open QuantumTrace DiagonalForms.System
variable {n : ℕ} {J : Type*} [DecidableEq J]
end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace
namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

def quarticLogarithm : Fock n →L[ℂ] Fock n :=
  logarithmSandwich (gibbsFactor rootNumberWeight rootNumberWeight_one_le k G.B)
    (inversePower rootNumberWeight rootNumberWeight_one_le 4) (Real.log (heatPartition G.eigenval))

end GibbsData
end EntropyPhotonNumber

end

end OAI
