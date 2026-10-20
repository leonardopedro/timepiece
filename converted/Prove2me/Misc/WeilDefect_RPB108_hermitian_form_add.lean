/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 7f2139af-30e7-4e33-9693-70ed0041d012
* original name       : `WeilDefect.RPB108.hermitian_form_add`
* title               : Hermitian quadratic form on a sum
* statement author    : waitingintime
* solution author     : waitingintime (submission b7de239a-715d-4bc2-84a8-1b6df4340b79,
                        accepted 2026-10-11T05:27:38.124602+00:00)
* source              : https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/SesquilinearBlocks.lean#L6-L13; exact native theorem WeilDefect.RPB108.hermitian_form_add. SHA256 4dcb50ec0ebc06cc9c8d402695cb4b59283e9bc0957ac6db754398b8a7683994. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/misc/WeilDefect.RPB108.hermitian_form_add.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/WeilDefect_RPB108_hermitian_form_add.diff`.
-/
import Mathlib
import Definitions.Def_RPB108_ThreeGram

open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem _root_.Prove2me.Solution.WeilDefect_RPB108_hermitian_form_add {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : E →ₛₗ[starRingEnd ℂ] E →ₗ[ℂ] ℂ)
    (hherm : ∀ u v, F u v = star (F v u)) (u v : E) :
    (F (u+v) (u+v)).re = (F u u).re+2*(F u v).re+(F v v).re := by
  have hs : (F v u).re = (F u v).re := by rw [hherm]; simp
  simp only [map_add, LinearMap.add_apply, Complex.add_re]
  linarith

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem WeilDefect.RPB108.hermitian_form_add {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : E →ₛₗ[starRingEnd ℂ] E →ₗ[ℂ] ℂ)
    (hherm : ∀ u v, F u v = star (F v u)) (u v : E) :
    (F (u+v) (u+v)).re = (F u u).re+2*(F u v).re+(F v v).re := by
  first
  | exact _root_.Prove2me.Solution.WeilDefect_RPB108_hermitian_form_add F hherm u v
  | (apply _root_.Prove2me.Solution.WeilDefect_RPB108_hermitian_form_add <;> assumption)

end

end Prove2meStatement
