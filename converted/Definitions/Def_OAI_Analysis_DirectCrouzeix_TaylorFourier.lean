/-
prove2.me platform library module `Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Analysis_DirectCrouzeix_TaylorFourier.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/TaylorFourier.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_94 u_95 u_96 u_97 u_98 u_99 u_100 u_101 u_102 u_103 u_104 u_105

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

def taylorCoeff {E : Type u_94} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (k : ℕ) : E := (k.factorial : ℂ)⁻¹ • iteratedDeriv k f 0

@[simp] theorem taylorCoeff_zero {E : Type u_95} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) : taylorCoeff f 0 = f 0 := by simp [taylorCoeff]

@[simp] theorem taylorCoeff_const {E : Type u_101} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : E) (k : ℕ) : taylorCoeff (fun _ => v) k = if k = 0 then v else 0 := by
  by_cases hk : k = 0
  · subst k; simp
  · simp [taylorCoeff,iteratedDeriv_const,hk]

abbrev Angle := AddCircle (1:ℝ)

abbrev angularMeasure : Measure Angle := AddCircle.haarAddCircle

def unitPoint (t : Angle) : ℂ := fourier 1 t

@[simp] theorem unitPoint_norm (t : Angle) : ‖unitPoint t‖ = 1 := by
  simp [unitPoint,fourier_apply,Circle.norm_coe]

end DirectCrouzeix.Faber

end

end

end OAI
