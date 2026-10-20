/-
prove2.me platform library module `Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/MatchingIncidence.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels

namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing

namespace Pairing
variable {V : Type u_1} [Fintype V] [DecidableEq V]

noncomputable instance : Fintype (Pairing V) := Fintype.ofFinite _

instance relabelMulAction : MulAction (Equiv.Perm V) (Pairing V) where
  smul := relabel
  one_smul := relabel_one
  mul_smul := relabel_mul

noncomputable def table (M : Pairing V) (f : V → Fin 3) (t : Fin 6) : ℕ :=
  histogram (fun v => threeEdgeType (f v, f (M.1 v))) t / 2

end Pairing

section StandardTable
variable {H : Type u_2} [Fintype H] [DecidableEq H]

def standardPairing : Pairing (H × Bool) :=
  ⟨Equiv.prodCongr (Equiv.refl H) Equiv.boolNot,
    by rintro ⟨i,b⟩; cases b <;> rfl,
    by rintro ⟨i,b⟩ h; have he := congrArg Prod.snd h; cases b <;> contradiction⟩

end StandardTable

section MatchingIncidence
variable {H : Type u_3} [Fintype H] [DecidableEq H]

noncomputable def tableRelation (f₀ : H × Bool → Fin 3) :
    Pairing (H × Bool) → Colorings (H × Bool) (Fin 3) (histogram f₀) → Prop :=
  fun M z => M.table z.1 = threeTable f₀

noncomputable def coloringPerm (s : Fin 3 → ℕ) (p : Equiv.Perm (H × Bool)) :
    Equiv.Perm (Colorings (H × Bool) (Fin 3) s) where
  toFun z := ⟨z.1 ∘ p, (histogram_comp_perm z.1 p).trans z.2⟩
  invFun z := ⟨z.1 ∘ p.symm, (histogram_comp_perm z.1 p.symm).trans z.2⟩
  left_inv z := by apply Subtype.ext; funext v; simp
  right_inv z := by apply Subtype.ext; funext v; simp

end MatchingIncidence
end MatchingSmoothing

end OAI
