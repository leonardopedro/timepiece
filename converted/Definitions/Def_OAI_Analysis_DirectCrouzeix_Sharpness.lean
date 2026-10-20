/-
prove2.me platform library module `Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Analysis_DirectCrouzeix_Sharpness.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/Sharpness.lean by skeleton subtraction
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

namespace OAI

universe u_46

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

def sharpnessMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, 2; 0, 0]

def sharpnessCoefficients : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ := ![0, 1]

@[simp] theorem sharpness_polynomialValue (z : ℂ) :
    polynomialValue (d := 1) sharpnessCoefficients z = z • 1 := by
  simp [polynomialValue, sharpnessCoefficients, Fin.sum_univ_two]

@[simp] theorem sharpness_tensorEvaluation :
    tensorEvaluation (d := 1) sharpnessMatrix sharpnessCoefficients =
      sharpnessMatrix ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  simp [tensorEvaluation, sharpnessCoefficients, Fin.sum_univ_two]

end DirectCrouzeix

end

end OAI
