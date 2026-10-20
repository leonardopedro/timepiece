/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 77ec1fe5-c9c8-41bb-bcad-7cc40e6395bb
* original name       : `HeathcoteUnbounded.selfAdjoint_unbounded_domain`
* title               : Unbounded self-adjoint operators are defined only on dense proper subspaces
* statement author    : Lucas
* solution author     : fizzyinc3 (submission 9d684af4-ddbf-467e-9abc-e4124e49380e,
                        accepted 2026-10-17T08:24:44.733119+00:00)
* source              : A. Heathcote, "Unbounded Operators and the Incompleteness of Quantum Mechanics", Philosophy of Science 57 (1990), 523–534, p. 2, eqs. (1)–(2), footnotes 1–2
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/unfer-sirk/HeathcoteUnbounded.selfAdjoint_unbounded_domain.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/HeathcoteUnbounded_selfAdjoint_unbounded_domain.diff`.
-/
import Mathlib
import Definitions.Def_HeathcoteUnbounded_Psi

open MeasureTheory HeathcoteUnbounded Set

theorem _root_.Prove2me.Solution.HeathcoteUnbounded_selfAdjoint_unbounded_domain {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hunb : ¬ ∃ k : ℝ, ∀ ψ : A.domain, ‖A ψ‖ ≤ k * ‖(ψ : H)‖) :
    Dense (A.domain : Set H) ∧ A.domain ≠ ⊤ := by
  refine ⟨hA.dense_domain, fun htop => hunb ?_⟩
  set e := LinearEquiv.ofTop A.domain htop
  set f : H →ₗ[ℂ] H := A.toFun.comp e.symm.toLinearMap
  have hgraph : (f.graph : Set (H × H)) = (A.graph : Set (H × H)) := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, LinearPMap.mem_graph_iff]
    constructor
    · intro h
      refine ⟨e.symm x, ?_, ?_⟩
      · simp [e]
      · rw [h]; rfl
    · rintro ⟨z, hz, hzy⟩
      have : e.symm x = z := by
        apply Subtype.ext; simp [e, ← hz]
      rw [← hzy, ← this]; rfl
  have hcl : IsClosed (f.graph : Set (H × H)) := by
    rw [hgraph]; exact hA.isClosed
  have hcont : Continuous f := LinearMap.continuous_of_isClosed_graph f hcl
  let F : H →L[ℂ] H := ⟨f, hcont⟩
  refine ⟨‖F‖, fun ψ => ?_⟩
  have h1 : F ψ = A ψ := by
    show A.toFun (e.symm (ψ : H)) = A ψ
    congr 1
  rw [← h1]
  exact F.le_opNorm _

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

namespace HeathcoteUnbounded

theorem selfAdjoint_unbounded_domain {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hunb : ¬ ∃ k : ℝ, ∀ ψ : A.domain, ‖A ψ‖ ≤ k * ‖(ψ : H)‖) :
    Dense (A.domain : Set H) ∧ A.domain ≠ ⊤ :=
  _root_.Prove2me.Solution.HeathcoteUnbounded_selfAdjoint_unbounded_domain A hA hunb

end HeathcoteUnbounded

end Prove2meStatement
