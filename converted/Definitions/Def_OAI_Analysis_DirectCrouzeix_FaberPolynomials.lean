/-
prove2.me platform library module `Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/FaberPolynomials.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_106 u_107

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

def localL (c : ℂ) (g : ℂ → ℂ) (u : ℂ) : ℂ := (c+u*g u)⁻¹

def localW (c : ℂ) (g : ℂ → ℂ) (u : ℂ) : ℂ := u*localL c g u

def localN (c : ℂ) (g : ℂ → ℂ) (u : ℂ) : ℂ := (c-u^2*deriv g u)*localL c g u

def faberBasis (c : ℂ) (g : ℂ → ℂ) (k : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (k+1), Polynomial.monomial j
    (taylorCoeff (fun u => localN c g u * localW c g u ^ j) k)

@[simp] theorem localL_zero (c : ℂ) (g : ℂ → ℂ) : localL c g 0 = c⁻¹ := by simp [localL]

@[simp] theorem localW_zero (c : ℂ) (g : ℂ → ℂ) : localW c g 0 = 0 := by simp [localW]

@[simp] theorem localN_zero {c : ℂ} (hc : c ≠ 0) (g : ℂ → ℂ) : localN c g 0 = 1 := by
  simp [localN,localL,hc]

def scalarGenerating (c : ℂ) (g : ℂ → ℂ) (z u : ℂ) : ℂ :=
  (c-u^2*deriv g u)/(c+u*(g u-z))

@[simp] theorem unitPoint_neg (t : Angle) : unitPoint (-t) = (unitPoint t)⁻¹ := by
  simp [unitPoint,fourier_apply,AddCircle.toCircle_neg,Circle.coe_inv]

end DirectCrouzeix.Faber

end

end

end OAI
