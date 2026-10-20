/-
prove2.me platform library module `Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Analysis_DirectCrouzeix_Resolvent.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/Resolvent.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

def quadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) : ℂ :=
  inner ℂ u (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u)

end DirectCrouzeix

end

end OAI
