/-
prove2.me platform library module `Definitions.Def_OAI_Probability_ThreeState_PosteriorMoments`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Probability_ThreeState_PosteriorMoments.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/PosteriorMoments.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateSupercritical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic
import Definitions.Def_OAI_Probability_ThreeState_Expectations
import Definitions.Def_OAI_Probability_ThreeState_Messages
import Definitions.Def_OAI_Probability_ThreeState_Observation
import Definitions.Def_OAI_Probability_ThreeState_Update
import Definitions.Def_OAI_Probability_ThreeState_RadialMoments
import Definitions.Def_OAI_Probability_ThreeState_RadialDerivatives

namespace OAI

/-! Posterior deviation moments and positive-channel estimates. -/

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
open Radial (avg)

noncomputable def messageDeviation (m : Message) : Spin → ℝ := fun i => m i-1
noncomputable def messageX (m : Message) : ℝ := Radial.momentX (messageDeviation m)
 

end ThreeState

end OAI
