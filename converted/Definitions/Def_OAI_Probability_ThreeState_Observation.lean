/-
prove2.me platform library module `Definitions.Def_OAI_Probability_ThreeState_Observation`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Probability_ThreeState_Observation.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/Observation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateSupercritical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic
import Definitions.Def_OAI_Probability_ThreeState_Expectations
import Definitions.Def_OAI_Probability_ThreeState_Messages

namespace OAI

/-! Ordered and unlabelled boundary observations and information degradation. -/

namespace ThreeState

 

 
end ThreeState

namespace ThreeState

end ThreeState
universe u
namespace ThreeState

instance pmfCommApplicative : CommApplicative PMF where
  commutative_prod a b := by
    change ((a.map Prod.mk).bind (fun f => b.map f)) =
      ((b.map (fun y x => (x,y))).bind (fun f => a.map f))
    simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
    exact PMF.bind_comm a b (fun x y => PMF.pure (x,y))

 

noncomputable def grow (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    (n : ℕ) → Observation n → PMF (Observation (n+1))
  | 0 => observedLaw offspring lam h 1
  | n+1 => Multiset.traverse (grow offspring lam h n)

 
 
 
end ThreeState

end OAI
