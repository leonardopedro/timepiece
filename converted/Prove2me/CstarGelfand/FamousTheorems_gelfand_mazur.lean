/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 9e7c06bc-e5f2-48bf-85bf-e3259bf2b58d
* original name       : `FamousTheorems.gelfand_mazur`
* title               : The Gelfand–Mazur theorem
* statement author    : cm_beta
* solution author     : cm_beta (submission ea74e926-8e4b-46cc-b54b-cff0630a89ec,
                        accepted 2026-09-23T18:14:16.939611+00:00)
* source              : Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `NormedRing.algEquivComplexOfComplete`. Proof here reduces to that Mathlib result.
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/cstar-gelfand/FamousTheorems.gelfand_mazur.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/FamousTheorems_gelfand_mazur.diff`.
-/
import Mathlib

theorem _root_.Prove2me.Solution.FamousTheorems_gelfand_mazur {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (hA : ∀ {a : A}, IsUnit a ↔ a ≠ 0) :
    Nonempty (ℂ ≃ₐ[ℂ] A) :=
  ⟨NormedRing.algEquivComplexOfComplete hA⟩

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

namespace FamousTheorems

theorem gelfand_mazur {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (hA : ∀ {a : A}, IsUnit a ↔ a ≠ 0) :
    Nonempty (ℂ ≃ₐ[ℂ] A) :=
  _root_.Prove2me.Solution.FamousTheorems_gelfand_mazur hA

end FamousTheorems

end Prove2meStatement
