/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 5b1db298-0240-4422-954a-5217bff8ea8f
* original name       : `TeschlQM.KatoRellich.kato_rellich`
* title               : Theorem 6.4 — Kato–Rellich (self-adjoint case, with the lower bound (6.3))
* statement author    : mikedeng1
* solution author     : moona3k (submission 74575c12-fdac-43a8-94f3-12e71c8c58d0,
                        accepted 2026-10-05T00:33:45.617986+00:00)
* source              : Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 135, Theorem 6.4, Eq. (6.3)
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/operator-qm/TeschlQM.KatoRellich.kato_rellich.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/TeschlQM_KatoRellich_kato_rellich.diff`.
-/
import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_KatoRellich_IsRelativelyBounded
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Theorems.Thm_TeschlQM_KatoRellich_kato_rellich_essentiallySelfAdjoint

open scoped ENNReal

namespace TeschlQM.KatoRellich.Goal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma closure_eq_self {S : H →ₗ.[ℂ] H} (hS : S.IsClosed) : S.closure = S := by
  have h := hS.isClosable.graph_closure_eq_closure_graph
  rw [hS.submodule_topologicalClosure_eq] at h
  exact (LinearPMap.eq_of_eq_graph h).symm

lemma ess_of_selfAdjoint {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hcl : A.IsClosed) :
    TeschlQM.Shared.IsEssentiallySelfAdjoint A := by
  unfold TeschlQM.Shared.IsEssentiallySelfAdjoint
  rw [closure_eq_self hcl]
  exact hA

lemma domain_le_right_of_sum_domain_eq {A B : H →ₗ.[ℂ] H} (hdom : (A + B).domain = A.domain) :
    A.domain ≤ B.domain := by
  intro x hx
  have : x ∈ A.domain ⊓ B.domain := by
    rw [← LinearPMap.add_domain, hdom]
    exact hx
  exact this.2

lemma sum_eq_sum_closure_right {A B : H →ₗ.[ℂ] H} (hdom : (A + B).domain = A.domain) :
    A + B = A + B.closure := by
  have hBd : A.domain ≤ B.domain := domain_le_right_of_sum_domain_eq hdom
  have hDomEq : (A + B).domain = (A + B.closure).domain := by
    calc
      (A + B).domain = A.domain := hdom
      _ = A.domain ⊓ B.closure.domain := (inf_eq_left.mpr (hBd.trans B.le_closure.1)).symm
      _ = (A + B.closure).domain := by rw [← LinearPMap.add_domain]
  apply LinearPMap.ext hDomEq
  intro x hg hg'
  have hxA : x ∈ A.domain := by simpa [hdom] using hg
  have hxB : x ∈ B.domain := hBd hxA
  have hxBcl : x ∈ B.closure.domain := B.le_closure.1 hxB
  simp only [LinearPMap.add_apply, hg, hg', hxA, hxB, hxBcl,
    B.le_closure.2 (x := ⟨x, hxB⟩) (y := ⟨x, hxBcl⟩) rfl]

lemma selfAdjoint_of_esa_and_closure_eq {T : H →ₗ.[ℂ] H}
    (hE : TeschlQM.Shared.IsEssentiallySelfAdjoint T) (hcl : T.closure = T) :
    IsSelfAdjoint T := by
  unfold TeschlQM.Shared.IsEssentiallySelfAdjoint at hE
  rwa [hcl] at hE

end TeschlQM.KatoRellich.Goal

open TeschlQM.KatoRellich in
theorem _root_.Prove2me.Solution.TeschlQM_KatoRellich_kato_rellich {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (hB : TeschlQM.Shared.IsSymmetric B)
    (hbound : relativeBound A B < 1) :
    (A + B).domain = A.domain ∧ IsSelfAdjoint (A + B) ∧
      ∀ γ a b : ℝ, a < 1 → IsRelativelyBoundedWith A B a b →
        TeschlQM.Shared.IsBoundedBelowBy A γ →
        TeschlQM.Shared.IsBoundedBelowBy (A + B) (γ - max (a * |γ| + b) (b / (1 - a))) := by
  have hAesa := TeschlQM.KatoRellich.Goal.ess_of_selfAdjoint hA hA.isClosed
  rcases kato_rellich_essentiallySelfAdjoint A B hAesa hB hbound with
    ⟨hdom, hESA, _, hsumcl, hlb⟩
  refine ⟨hdom, ?_, hlb⟩
  have hA' := TeschlQM.KatoRellich.Goal.closure_eq_self hA.isClosed
  have hABcl : (A + B).closure = A + B := by
    rw [hsumcl, hA', TeschlQM.KatoRellich.Goal.sum_eq_sum_closure_right hdom]
  exact TeschlQM.KatoRellich.Goal.selfAdjoint_of_esa_and_closure_eq hESA hABcl

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

namespace TeschlQM.KatoRellich

open scoped ENNReal

/-- Teschl, Theorem 6.4 (Kato–Rellich), p. 135, self-adjoint case with the lower bound (6.3).
If `A` is self-adjoint and `B` is symmetric with `A`-bound less than one, then `A + B` with
`𝔇(A + B) = 𝔇(A)` is self-adjoint. If moreover `A ≥ γ` and (6.1) holds with constants `a < 1`, `b`,
then `A + B ≥ γ - max(a|γ| + b, b/(1 - a))`. The book prints `b/(a - 1)`, which is false
(see the moderation notes); `b/(1 - a)` is the corrected constant (Kato, Thm V.4.11). -/
theorem kato_rellich {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (hB : TeschlQM.Shared.IsSymmetric B)
    (hbound : relativeBound A B < 1) :
    (A + B).domain = A.domain ∧ IsSelfAdjoint (A + B) ∧
      ∀ γ a b : ℝ, a < 1 → IsRelativelyBoundedWith A B a b → TeschlQM.Shared.IsBoundedBelowBy A γ →
        TeschlQM.Shared.IsBoundedBelowBy (A + B) (γ - max (a * |γ| + b) (b / (1 - a))) := by
  first
  | exact _root_.Prove2me.Solution.TeschlQM_KatoRellich_kato_rellich A B hA hB hbound
  | (apply _root_.Prove2me.Solution.TeschlQM_KatoRellich_kato_rellich <;> assumption)

end TeschlQM.KatoRellich


end Prove2meStatement
