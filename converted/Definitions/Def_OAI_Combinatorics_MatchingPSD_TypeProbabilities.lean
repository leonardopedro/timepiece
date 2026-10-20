/-
prove2.me platform library module `Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/TypeProbabilities.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingPSD mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace MatchingSmoothing

section ProductTypes
variable {H : Type u_5} {A : Type u_6} {T : Type u_7} [Fintype H] [DecidableEq H] [Fintype A] [Fintype T]
  [DecidableEq A] [DecidableEq T]

noncomputable def functionFiberEquiv (η : A → T) (k : H → T) :
    {f : H → A // η ∘ f = k} ≃ ((i : H) → {a : A // η a = k i}) where
  toFun f i := ⟨f.1 i, congrFun f.2 i⟩
  invFun g := ⟨fun i => (g i).1, funext (fun i => (g i).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

end ProductTypes

end MatchingSmoothing

end OAI
