/-
prove2.me platform library module `Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/HilbertSchmidt.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus

namespace OAI

universe u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25
  u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem hsSq_eq_sum_norm_sq {ι : Type u_8} {κ : Type u_9} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : hsSq M = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  simp only [hsSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

def hsVector {ι : Type u_10} {κ : Type u_11} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) :
    EuclideanSpace ℂ (ι × κ) := WithLp.toLp 2 (fun p => M p.1 p.2)

def entryPair {ι : Type u_18} {κ : Type u_19} [Fintype ι] [Fintype κ]
    (M C : Matrix ι κ ℂ) : ℂ := ∑ i, ∑ j, M i j * C i j

end DirectCrouzeix

end

end OAI
