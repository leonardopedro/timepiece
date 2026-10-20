/-
prove2.me platform library module `Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/RepresentationDimension.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingPSD mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1

namespace MatchingSmoothing
section StandardPairs

abbrev Vertices (h : ℕ) := Fin h × Bool

variable {h : ℕ}

def firstVertices (h t : ℕ) : Finset (Vertices h) :=
  (Finset.univ.filter fun i : Fin h => i.val < t) ×ˢ Finset.univ

@[simp] lemma mem_firstVertices (t : ℕ) (v : Vertices h) :
    v ∈ firstVertices h t ↔ v.1.val < t := by simp [firstVertices]

def pairSwap (i : Fin h) : Equiv.Perm (Vertices h) :=
  Equiv.swap (i, false) (i, true)

end StandardPairs
end MatchingSmoothing

end OAI
