/-
prove2.me platform library module `Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Analysis_DirectCrouzeix_SingularPairs.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/SingularPairs.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt

namespace OAI

universe u_37 u_38 u_39 u_40

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

def matrixify {n m : ℕ} (x : EuclideanSpace ℂ (Fin n × Fin m)) :
    Matrix (Fin n) (Fin m) ℂ := fun i j => x (i, j)

@[simp] theorem hsVector_matrixify {n m : ℕ} (x : EuclideanSpace ℂ (Fin n × Fin m)) :
    hsVector (matrixify x) = x := by
  apply WithLp.ofLp_injective
  rfl

end DirectCrouzeix

end

end OAI
