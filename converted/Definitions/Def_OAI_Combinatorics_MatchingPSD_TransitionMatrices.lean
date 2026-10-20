/-
prove2.me platform library module `Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/TransitionMatrices.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingPSD mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
open Matrix

variable {V : Type u_1} {C : Type u_2} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

noncomputable def tensorKernel (U : Matrix C C ℝ) : Matrix (V → C) (V → C) ℝ :=
  fun f g => ∏ v, U (f v) (g v)

variable {H : Type u_3} [Fintype H] [DecidableEq H]

noncomputable def pairDiagonal (d : C → ℝ) (f : H × Bool → C) : ℝ :=
  if pairConstant f then ∏ i, d (f (i, false)) else 0

noncomputable def pairWeight (A : Matrix C C ℝ) (f : H × Bool → C) : ℝ :=
  ∏ i, A (f (i, false)) (f (i, true))

end MatchingSmoothing

end OAI
