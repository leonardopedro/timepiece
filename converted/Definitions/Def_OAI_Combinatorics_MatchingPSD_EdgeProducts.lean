/-
prove2.me platform library module `Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Combinatorics_MatchingPSD_EdgeProducts.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/EdgeProducts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingPSD mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingPSD

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
variable {E : Type u_1} {X : Type u_2}

def lowDegree (x : E → X → ℝ) (d : ℕ) : Submodule ℝ (X → ℝ) :=
  Submodule.span ℝ {f | ∃ l : List E, l.length ≤ d ∧ f = (l.map x).prod}

end MatchingSmoothing

end OAI
