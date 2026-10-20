/-
prove2.me platform library module `Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Combinatorics_MatchingPSD_Pairings.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/Pairings.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingPSD mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts

namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
abbrev Pairing (α : Type u_1) :=
  {M : Equiv.Perm α // Function.Involutive M ∧ ∀ a, M a ≠ a}

namespace Pairing
variable {α : Type u_2}

@[ext] lemma ext {M N : Pairing α} (h : ∀ a, M.1 a = N.1 a) : M = N :=
  Subtype.ext (Equiv.ext h)

@[simp] lemma partner_partner (M : Pairing α) (a : α) : M.1 (M.1 a) = a := M.2.1 a

lemma partner_ne (M : Pairing α) (a : α) : M.1 a ≠ a := M.2.2 a

@[simp] lemma partner_eq_iff (M : Pairing α) (a b : α) : M.1 a = b ↔ M.1 b = a := by
  constructor <;> intro h <;> rw [← h, partner_partner]

def relabel (p : Equiv.Perm α) (M : Pairing α) : Pairing α :=
  ⟨p * M.1 * p⁻¹, by
    constructor
    · intro a
      simp [Equiv.Perm.mul_apply]
    · intro a h
      apply M.partner_ne (p⁻¹ a)
      simpa using
        congrArg (fun b => p⁻¹ b) h⟩

@[simp] lemma relabel_apply (p : Equiv.Perm α) (M : Pairing α) (a : α) :
    (relabel p M).1 a = p (M.1 (p⁻¹ a)) := rfl

@[simp] lemma relabel_one (M : Pairing α) : relabel 1 M = M := by ext a; simp

@[simp] lemma relabel_mul (p q : Equiv.Perm α) (M : Pairing α) :
    relabel (p * q) M = relabel p (relabel q M) := by
  ext a
  simp [Equiv.Perm.mul_apply]

def relabelEquiv (p : Equiv.Perm α) : Equiv.Perm (Pairing α) where
  toFun := relabel p
  invFun := relabel p⁻¹
  left_inv M := by rw [← relabel_mul, inv_mul_cancel, relabel_one]
  right_inv M := by rw [← relabel_mul, mul_inv_cancel, relabel_one]

def act (p : Equiv.Perm α) : (Pairing α → ℝ) ≃ₗ[ℝ] (Pairing α → ℝ) where
  toFun f M := f (relabel p⁻¹ M)
  invFun f M := f (relabel p M)
  left_inv f := by ext M; simp [← relabel_mul]
  right_inv f := by ext M; simp [← relabel_mul]
  map_add' f g := rfl
  map_smul' c f := rfl

@[simp] lemma act_apply (p : Equiv.Perm α) (f : Pairing α → ℝ) (M : Pairing α) :
    act p f M = f (relabel p⁻¹ M) := rfl

@[simp] lemma act_mul (p q : Equiv.Perm α) (f : Pairing α → ℝ) :
    act (p * q) f = act p (act q f) := by
  ext M
  simp [← relabel_mul]

@[simp] lemma act_one (f : Pairing α → ℝ) : act 1 f = f := by ext M; simp

@[simp] lemma partner_sq (M : Pairing α) : M.1 ^ 2 = 1 := by
  ext a
  simp [pow_two, Equiv.Perm.mul_apply]

@[simp] lemma relabel_swap_partner [DecidableEq α] (M : Pairing α) (a : α) :
    relabel (Equiv.swap a (M.1 a)) M = M := by
  apply Subtype.ext
  change Equiv.swap a (M.1 a) * M.1 * (Equiv.swap a (M.1 a))⁻¹ = M.1
  have hc : M.1 * Equiv.swap a (M.1 a) = Equiv.swap a (M.1 a) * M.1 := by
    rw [Equiv.mul_swap_eq_swap_mul, partner_partner, Equiv.swap_comm]
  rw [← hc, mul_inv_cancel_right]

def SameInternal (U : Finset α) (M N : Pairing α) : Prop :=
  ∀ a ∈ U, ∀ b ∈ U, M.1 a = b ↔ N.1 a = b

def restrict (M : Pairing α) (S : Finset α)
    (hS : ∀ a, M.1 a ∈ S ↔ a ∈ S) : Pairing S :=
  ⟨M.1.subtypePerm hS, by
    constructor
    · intro a; apply Subtype.ext; exact M.partner_partner a.1
    · intro a h; exact M.partner_ne a.1 (congrArg Subtype.val h)⟩

@[simp] lemma restrict_apply (M : Pairing α) (S : Finset α)
    (hS : ∀ a, M.1 a ∈ S ↔ a ∈ S) (a : S) :
    ((restrict M S hS).1 a).1 = M.1 a.1 := rfl

def closure [DecidableEq α] (M : Pairing α) (U : Finset α) : Finset α :=
  U ∪ U.image M.1

noncomputable def edgeCoord (e : α × α) (M : Pairing α) : ℝ := by
  classical
  exact if M.1 e.1 = e.2 then 1 else 0

noncomputable def internalPattern [DecidableEq α] (U : Finset α)
    (M : Pairing α) : Finset (α × α) :=
  (U ×ˢ U).filter fun e => M.1 e.1 = e.2

end Pairing
end MatchingSmoothing

end OAI
