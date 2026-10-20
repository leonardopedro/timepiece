/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : d06e3a26-0169-4a1e-a5cd-d7a02f0c4ba4
* original name       : `AlmostLossless.silentError_imp_collides`
* title               : A silent error can only happen through a codebook collision.
* statement author    : raver1975
* solution author     : Nickrobbins95 (submission 8671d376-dc5f-4074-9d0e-48aff61d5c57,
                        accepted 2026-09-17T11:27:33.976712+00:00)
* source              : https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessRandomCoding.lean#L303
* platform Mathlib rev: c5ea00351c28e24afc9f0f84379aa41082b1188f
* original file       : Downloads/logos-confluence/AlmostLossless.silentError_imp_collides.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/AlmostLossless_silentError_imp_collides.diff`.
-/
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessRandomCoding

open AlmostLossless in
theorem _root_.Prove2me.Solution.AlmostLossless_silentError_imp_collides {α : Type*} [DecidableEq α] {M : ℕ} {l : List α} {h : α → Fin M} {x : α}
    (hs : (hashScheme l h).SilentError x) :
    ∃ y ∈ l.toFinset, y ≠ x ∧ h y = h x := by
  have hscan : ∀ (i : Fin M) (l : List α),
      (scanCost h i l).1 = l.filter (fun y => decide (h y = i)) := by
    intro i l
    induction l with
    | nil => rfl
    | cons a t ih =>
      simp only [scanCost, List.filter_cons, ih]
      split_ifs <;> simp_all
  obtain ⟨y, hy, hne⟩ := hs
  have hy' : decodeList h l (h x) = some y := hy
  unfold decodeList at hy'
  split at hy'
  next y' heq =>
    have hyy : y' = y := Option.some.inj hy'
    subst hyy
    rw [hscan] at heq
    have hmem : y' ∈ l.filter (fun z => decide (h z = h x)) := by rw [heq]; simp
    rw [List.mem_filter] at hmem
    exact ⟨y', List.mem_toFinset.mpr hmem.1, hne, by simpa using hmem.2⟩
  next => simp at hy'

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open Finset BigOperators NonArchInfoTheory
open AlmostLossless

theorem AlmostLossless.silentError_imp_collides{l : List α} {h : α → Fin M} {x : α}
    (hs : (hashScheme l h).SilentError x) :
    ∃ y ∈ l.toFinset, y ≠ x ∧ h y = h x :=
  _root_.Prove2me.Solution.AlmostLossless_silentError_imp_collides



end Prove2meStatement
