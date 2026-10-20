/-
prove2.me platform library module `Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/BoundaryKernel.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_108 u_109 u_110 u_111 u_112 u_113 u_114 u_115 u_116

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

def boundary (c : ℂ) (g : ℂ → ℂ) (t : Angle) : ℂ := exterior c g (unitPoint t)

def boundaryCorrection (c : ℂ) (g : ℂ → ℂ) (t s : Angle) : ℂ :=
  correction c g ((unitPoint t)⁻¹) ((unitPoint s)⁻¹)

def boundaryCoefficient (c : ℂ) (g : ℂ → ℂ) (k : ℕ) (s : Angle) : ℂ :=
  fourierCoeff (fun t => boundaryCorrection c g t s) (-(k:ℤ))

def boundaryKernel (c : ℂ) (g : ℂ → ℂ) (t s : Angle) : ℝ :=
  1 + 2*(boundaryCorrection c g t s).re

end DirectCrouzeix.Faber

end

end

end OAI
