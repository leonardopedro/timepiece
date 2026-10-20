/-
prove2.me platform library module `Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Analysis_DirectCrouzeix_FaberEnergy.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/FaberEnergy.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_128 u_129

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

section FaberHilbert

variable {E : Type u_128} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def faberBoundarySeries {N : ℕ} (c : ℂ) (g : ℂ → ℂ) (C : Fin N → E) (t : Angle) : E :=
  ∑ k : Fin N, (faberBasis c g k).eval (boundary c g t) • C k

def boundaryRemainder {N : ℕ} (c : ℂ) (g : ℂ → ℂ) (C : Fin N → E) (t : Angle) : E :=
  ∑ k : Fin N, boundaryCoefficient c g k t • C k

def nonconstantCoefficients {N : ℕ} (C : Fin N → E) (k : Fin N) : E :=
  if (k:ℕ) = 0 then 0 else C k

end FaberHilbert

def boundaryNormal (c : ℂ) (g : ℂ → ℂ) (t : Angle) : ℂ :=
  unitPoint t * (c-(unitPoint t)⁻¹^2*deriv g ((unitPoint t)⁻¹))

section BanachAlgebra

variable {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]

end BanachAlgebra

end DirectCrouzeix.Faber

end

end

end OAI
