/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 0ea5ad31-e8fb-4fbe-a42e-58aa5a8dacf3
* original name       : `FamousTheorems.hahn_banach_separation`
* title               : The Hahn–Banach separation theorem (open convex set)
* statement author    : cm_beta
* solution author     : cm_beta (submission fc70a650-79c5-4f7f-91e4-bc836b7996bf,
                        accepted 2026-09-24T02:17:46.165629+00:00)
* source              : Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `geometric_hahn_banach_open`. Proof here reduces to that Mathlib result.
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/cstar-gelfand/FamousTheorems.hahn_banach_separation.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/FamousTheorems_hahn_banach_separation.diff`.
-/
import Mathlib

theorem _root_.Prove2me.Solution.FamousTheorems_hahn_banach_separation {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] {s t : Set E} (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (ht : Convex ℝ t)
    (disj : Disjoint s t) :
    ∃ (f : StrongDual ℝ E) (u : ℝ), (∀ a ∈ s, f a < u) ∧ ∀ b ∈ t, u ≤ f b :=
  geometric_hahn_banach_open hs₁ hs₂ ht disj

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

namespace FamousTheorems

theorem hahn_banach_separation {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] {s t : Set E} (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (ht : Convex ℝ t)
    (disj : Disjoint s t) :
    ∃ (f : StrongDual ℝ E) (u : ℝ), (∀ a ∈ s, f a < u) ∧ ∀ b ∈ t, u ≤ f b :=
  _root_.Prove2me.Solution.FamousTheorems_hahn_banach_separation hs₁ hs₂ ht disj

end FamousTheorems

end Prove2meStatement
