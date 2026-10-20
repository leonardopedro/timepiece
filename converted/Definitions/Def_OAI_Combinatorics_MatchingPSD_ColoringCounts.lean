/-
prove2.me platform library module `Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Combinatorics_MatchingPSD_ColoringCounts.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/ColoringCounts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingPSD mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace MatchingSmoothing

variable {α : Type u_1} {β : Type u_2} [Fintype α] [DecidableEq β]

noncomputable def histogram (f : α → β) (b : β) : ℕ :=
  Fintype.card {a // f a = b}

abbrev Colorings (α : Type u_3) (β : Type u_4) [Fintype α] [DecidableEq β] (s : β → ℕ) :=
  {f : α → β // histogram f = s}

noncomputable instance coloringsFintype [Fintype β] (s : β → ℕ) :
    Fintype (Colorings α β s) := Fintype.ofFinite _

noncomputable def fiberEquivOfHistogram {f g : α → β} (h : histogram f = histogram g)
    (b : β) : {a // f a = b} ≃ {a // g a = b} :=
  Fintype.equivOfCardEq (congrFun h b)

noncomputable def permOfHistogram {f g : α → β} (h : histogram f = histogram g) :
    Equiv.Perm α :=
  (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight (fiberEquivOfHistogram h)).trans (Equiv.sigmaFiberEquiv g))

lemma histogram_comp_perm (f : α → β) (σ : Equiv.Perm α) :
    histogram (f ∘ σ) = histogram f := by
  funext b
  apply Fintype.card_congr
  exact { toFun := fun x => ⟨σ x, x.property⟩
          invFun := fun y => ⟨σ.symm y, by simpa using y.property⟩
          left_inv := by intro x; ext; simp
          right_inv := by intro x; ext; simp }

noncomputable def fiberPermEquiv (f g : α → β) :
    {σ : Equiv.Perm α // f ∘ σ = g} ≃
      (∀ b, {a // g a = b} ≃ {a // f a = b}) where
  toFun σ b :=
    { toFun := fun x => ⟨σ.1 x, (congrFun σ.2 x).trans x.property⟩
      invFun := fun y => ⟨σ.1.symm y, by
        exact (congrFun σ.2 (σ.1.symm y)).symm.trans (by simpa using y.property)⟩
      left_inv := by intro x; ext; simp
      right_inv := by intro x; ext; simp }
  invFun e := ⟨Equiv.ofFiberEquiv e, by
    funext a; exact Equiv.ofFiberEquiv_map e a⟩
  left_inv σ := by apply Subtype.ext; ext a; rfl
  right_inv e := by
    funext b
    apply Equiv.ext
    rintro ⟨a, ha⟩
    subst b
    rfl

variable {H : Type u_5} [Fintype H] [DecidableEq H]

def pairConstant (f : H × Bool → β) : Prop := ∀ i, f (i, false) = f (i, true)

instance pairConstantDecidable (f : H × Bool → β) : Decidable (pairConstant f) :=
  inferInstanceAs (Decidable (∀ i, f (i, false) = f (i, true)))

def duplicateColoring (k : H → β) : H × Bool → β := fun v => k v.1

noncomputable def pairConstantEquiv : {f : H × Bool → β // pairConstant f} ≃ (H → β) where
  toFun f i := f.1 (i, false)
  invFun k := ⟨duplicateColoring k, by intro i; rfl⟩
  left_inv f := by
    apply Subtype.ext
    funext ⟨i, b⟩
    cases b
    · rfl
    · exact f.2 i
  right_inv k := rfl

def spliceColoring (k l : H → β) : H × Bool → β :=
  fun v => if v.2 then l v.1 else k v.1

omit [DecidableEq H] in
lemma histogram_spliceColoring (k l : H → β) :
    histogram (spliceColoring k l) = histogram k + histogram l := by
  funext b
  change Fintype.card {v : H × Bool // spliceColoring k l v = b} = _
  let e : {v : H × Bool // spliceColoring k l v = b} ≃
      ({i // k i = b} ⊕ {i // l i = b}) :=
    { toFun := fun v => if h : v.1.2 = true then
        Sum.inr ⟨v.1.1, by simpa [spliceColoring, h] using v.2⟩ else
        Sum.inl ⟨v.1.1, by simpa [spliceColoring, h] using v.2⟩
      invFun := Sum.elim (fun i => ⟨(i.1, false), i.2⟩) (fun i => ⟨(i.1, true), i.2⟩)
      left_inv := by
        rintro ⟨⟨i, b⟩, h⟩
        cases b <;> rfl
      right_inv := by intro v; cases v <;> rfl }
  rw [Fintype.card_congr e, Fintype.card_sum]
  rfl

omit [DecidableEq H] in
lemma histogram_duplicateColoring (k : H → β) :
    histogram (duplicateColoring k) = fun b => 2 * histogram k b := by
  have he : duplicateColoring k = spliceColoring k k := by
    funext ⟨i, b⟩; cases b <;> rfl
  rw [he, histogram_spliceColoring]
  funext b
  simp [two_mul]

noncomputable def constantColoringsEquiv (s : β → ℕ) :
    {g : Colorings (H × Bool) β (fun b => 2 * s b) // pairConstant g.1} ≃
      Colorings H β s where
  toFun g := ⟨fun i => g.1.1 (i, false), by
    have he : duplicateColoring (fun i => g.1.1 (i, false)) = g.1.1 := by
      funext ⟨i, b⟩
      cases b
      · rfl
      · exact g.2 i
    have hh := congrArg histogram he
    rw [histogram_duplicateColoring, g.1.2] at hh
    funext b
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (congrFun hh b)⟩
  invFun k := ⟨⟨duplicateColoring k.1, by rw [histogram_duplicateColoring, k.2]⟩,
    by intro i; rfl⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    funext ⟨i, b⟩
    cases b
    · rfl
    · exact g.2 i
  right_inv k := by apply Subtype.ext; rfl

noncomputable def boundedHistogram (f : H → β) : β → Fin (Fintype.card H + 1) :=
  fun b => ⟨histogram f b, Nat.lt_succ_of_le
    (Fintype.card_le_of_injective (fun a : {a // f a = b} => a.1) Subtype.val_injective)⟩

end MatchingSmoothing

end OAI
