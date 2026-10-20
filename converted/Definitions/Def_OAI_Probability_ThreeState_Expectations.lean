/-
prove2.me platform library module `Definitions.Def_OAI_Probability_ThreeState_Expectations`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Probability_ThreeState_Expectations.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/Expectations.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateSupercritical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic

namespace OAI

/-! Expectations, second moments and the regular and Poisson offspring laws. -/

namespace ThreeState
open scoped Classical

 
noncomputable def mean {α : Type*} (p : PMF α) (f : α → ℝ) : ℝ :=
  ∑' a, mass p a * f a

def HasMean {α : Type*} (p : PMF α) (f : α → ℝ) : Prop :=
  Summable (fun a => mass p a * f a)

end ThreeState
namespace ThreeState
open scoped Classical

 

structure Moments {α : Type*} (p : PMF α) (f : α → ℝ) (m s : ℝ) : Prop where
  square : HasMean p (fun a => (f a)^2)
  first : mean p f = m
  second : mean p (fun a => (f a)^2) = s

end ThreeState
namespace ThreeState

 
end ThreeState

namespace ThreeState

 
end ThreeState

end OAI
