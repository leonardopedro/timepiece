/-
prove2.me platform library module `Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/IncidenceKernels.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace MatchingSmoothing
open Matrix

section FiniteSums
variable {G : Type u_1} {X : Type u_2} [Fintype G] [Group G] [Fintype X] [MulAction G X]

end FiniteSums

section KernelTrace
variable {G : Type u_3} {X : Type u_4} [Fintype G] [Group G] [Fintype X] [DecidableEq X]
  [MulAction G X]

end KernelTrace

section Incidence
variable {X : Type u_5} {Z : Type u_6} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq Z]

noncomputable def incidence (P : X → Z → Prop) : Matrix Z X ℝ :=
  by classical exact fun z x => if P x z then 1 else 0

noncomputable def commonIncidence (P : X → Z → Prop) (x y : X) : ℝ :=
  by classical exact (Fintype.card {z // P x z ∧ P y z} : ℝ)

noncomputable def incidenceKernel (P : X → Z → Prop) (D : ℝ) : Matrix X X ℝ :=
  fun x y => (Fintype.card Z : ℝ) / D ^ 2 * commonIncidence P x y

noncomputable def incidenceOperator (P : X → Z → Prop) (D : ℝ) : Matrix X X ℝ :=
  fun x y => incidenceKernel P D x y / Fintype.card X

noncomputable def conditionalAverage (P : X → Z → Prop) (E : ℝ) (f : X → ℝ) (z : Z) : ℝ :=
  (∑ x, incidence P z x * f x) / E

end Incidence
end MatchingSmoothing

end OAI
