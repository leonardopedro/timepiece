/-
prove2.me platform library module `Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Analysis_DirectCrouzeix_CircleFourier.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/CircleFourier.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness

namespace OAI

universe u_47 u_48 u_49 u_50 u_51 u_52 u_53 u_54 u_55 u_56 u_57 u_58 u_59 u_60 u_61 u_62 u_63 u_64
  u_65 u_66 u_67 u_68 u_69 u_70 u_71 u_72

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

abbrev BoundaryCircle := AddCircle (1 : ℝ)

abbrev circleMeasure : Measure BoundaryCircle := AddCircle.haarAddCircle

def hsCLM {ι : Type u_57} {κ : Type u_58} [Fintype ι] [Fintype κ] :
    Matrix ι κ ℂ →L[ℂ] EuclideanSpace ℂ (ι × κ) :=
  LinearMap.toContinuousLinearMap
    { toFun := hsVector
      map_add' := by intros; ext i; rfl
      map_smul' := by intros; ext i; rfl }

@[simp] theorem hsCLM_apply {ι : Type u_59} {κ : Type u_60} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) : hsCLM A = hsVector A := rfl

def compressionCLM {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin m) (Fin m) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun R => Yᴴ * R * X
      map_add' := by intros; simp [Matrix.mul_add,Matrix.add_mul]
      map_smul' := by intros; simp [Matrix.mul_smul,Matrix.smul_mul] }

@[simp] theorem compressionCLM_apply {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) ℂ)
    (R : Matrix (Fin n) (Fin n) ℂ) : compressionCLM X Y R = Yᴴ * R * X := rfl

def conjugateTransposeCLM {ι : Type u_67} {κ : Type u_68} [Fintype ι] [Fintype κ] :
    Matrix ι κ ℂ →L[ℝ] Matrix κ ι ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.conjTranspose
      map_add' := by intros; simp
      map_smul' := by intros; simp }

@[simp] theorem conjugateTransposeCLM_apply {ι : Type u_69} {κ : Type u_70} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) : conjugateTransposeCLM A = Aᴴ := rfl

end DirectCrouzeix

end

end OAI
