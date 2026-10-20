/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : c51330c2-c121-4bfa-a324-e6829be33cb4
* original name       : `WeilDefect.RPB108.sesquilinear_gram`
* title               : Finite sesquilinear Gram realization
* statement author    : waitingintime
* solution author     : waitingintime (submission 7e51f719-87e8-45e7-bb7b-7c67e804f603,
                        accepted 2026-10-11T05:30:30.547083+00:00)
* source              : https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/SesquilinearBlocks.lean#L27-L43; exact native theorem WeilDefect.RPB108.sesquilinear_gram. SHA256 4dcb50ec0ebc06cc9c8d402695cb4b59283e9bc0957ac6db754398b8a7683994. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/misc/WeilDefect.RPB108.sesquilinear_gram.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/WeilDefect_RPB108_sesquilinear_gram.diff`.
-/
import Mathlib
import Definitions.Def_RPB108_ThreeGram

open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem _root_.Prove2me.Solution.WeilDefect_RPB108_sesquilinear_gram {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : E →ₛₗ[starRingEnd ℂ] E →ₗ[ℂ] ℂ) (x : Fin 3 → E)
    (M : Fin 3 → Fin 3 → ℝ) (hM : ∀ i j, F (x i) (x j) = (M i j : ℂ))
    (z : Fin 3 → ℂ) :
    (F (∑ i, z i • x i) (∑ i, z i • x i)).re = complexGram M z := by
  rw [LinearMap.map_sum₂]
  simp only [map_sum, LinearMap.map_smulₛₗ₂,
    map_smul, smul_eq_mul, hM, Complex.re_sum, complexGram]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem WeilDefect.RPB108.sesquilinear_gram {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : E →ₛₗ[starRingEnd ℂ] E →ₗ[ℂ] ℂ) (x : Fin 3 → E)
    (M : Fin 3 → Fin 3 → ℝ) (hM : ∀ i j, F (x i) (x j) = (M i j : ℂ))
    (z : Fin 3 → ℂ) :
    (F (∑ i, z i • x i) (∑ i, z i • x i)).re = complexGram M z := by
  first
  | exact _root_.Prove2me.Solution.WeilDefect_RPB108_sesquilinear_gram F x M hM z
  | (apply _root_.Prove2me.Solution.WeilDefect_RPB108_sesquilinear_gram <;> assumption)

end

end Prove2meStatement
