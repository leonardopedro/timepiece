/-
prove2.me platform library module `Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Combinatorics_MatchingPSD_TableMoments.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/TableMoments.lean by skeleton subtraction
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

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace MatchingSmoothing
open Matrix
section TableKernel
variable {H : Type u_1} {C : Type u_2} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

end TableKernel
end MatchingSmoothing

namespace MatchingSmoothing
open Matrix

def threeEdgeType (p : Fin 3 × Fin 3) : Fin 6 :=
  (![![0, 1, 2], ![1, 3, 4], ![2, 4, 5]] : Fin 3 → Fin 3 → Fin 6) p.1 p.2

def typeMultiplicity : Fin 6 → ℕ := ![1, 2, 2, 1, 2, 1]

section ThreeTables
variable {H : Type u_3} [Fintype H] [DecidableEq H]

noncomputable def pairColorEquiv : (H × Bool → Fin 3) ≃ (H → Fin 3 × Fin 3) where
  toFun f i := (f (i,false), f (i,true))
  invFun k v := if v.2 then (k v.1).2 else (k v.1).1
  left_inv f := by funext ⟨i,b⟩; cases b <;> rfl
  right_inv k := by funext i; rfl

noncomputable def threeTable (f : H × Bool → Fin 3) : Fin 6 → ℕ :=
  histogram (threeEdgeType ∘ pairColorEquiv f)

noncomputable def tableGamma (f : H × Bool → Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ((threeTable f (threeEdgeType (i,j)) : ℝ) / Fintype.card H) /
    typeMultiplicity (threeEdgeType (i,j))

noncomputable def tablePi (f : H × Bool → Fin 3) : Fin 3 → ℝ :=
  fun i => (histogram f i : ℝ) / (2 * Fintype.card H)

end ThreeTables

section Probability
variable {V : Type u_6} {C : Type u_7} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

end Probability

section TableNormalization
variable {H : Type u_8} {C : Type u_9} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

end TableNormalization

section ThreeTableMoment
variable {H : Type u_10} [Fintype H] [DecidableEq H]

end ThreeTableMoment
end MatchingSmoothing

end OAI
