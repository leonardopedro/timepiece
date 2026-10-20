/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 3040e185-e434-4f05-86b4-c85f7cb28188
* original name       : `OAI.DirectCrouzeix.isUnit_resolvent_of_not_mem`
* title               : Points outside the numerical range lie in the resolvent set
* statement author    : Shuze Chen
* solution author     : Shuze Chen (submission 3d4358a4-8bbf-477b-a0c3-f15752c479dd,
                        accepted 2026-10-18T06:45:31.007778+00:00)
* source              : https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/Resolvent.lean#L130-L142
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/crouzeix-convex/OAI.DirectCrouzeix.isUnit_resolvent_of_not_mem.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/OAI_DirectCrouzeix_isUnit_resolvent_of_not_mem.diff`.
-/
-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/Resolvent.lean:L130-L142
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.isUnit_resolvent_of_not_mem. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent

-- ---- from OAI.Analysis.DirectCrouzeix.Resolvent ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem mem_numericalRange_of_eigenvector {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {z : ℂ} {x : Fin n → ℂ} (hx : x ≠ 0) (he : A *ᵥ x = z • x) :
    z ∈ numericalRange A := by
  let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
  have hv : v ≠ 0 := by simpa [v] using hx
  have he' : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A v = z • v := by
    simpa [v, Matrix.toEuclideanCLM_toLp] using congrArg (WithLp.toLp 2) he
  let u : EuclideanSpace ℂ (Fin n) := (‖v‖ : ℂ)⁻¹ • v
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hv
  have heu : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u = z • u := by
    simp [u, he', smul_smul, mul_comm]
  refine ⟨u, hu, ?_⟩
  rw [heu, inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
  simp

theorem isUnit_resolvent_of_not_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {z : ℂ} (hz : z ∉ numericalRange A) : IsUnit (z • 1 - A) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  by_contra hh
  have hv : x - y ≠ 0 := sub_ne_zero.mpr hh
  have hzero : (z • 1 - A) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have he : A *ᵥ (x - y) = z • (x - y) := by
    symm
    apply sub_eq_zero.mp
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hzero
  exact hz (mem_numericalRange_of_eigenvector A hv he)

end DirectCrouzeix

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder


theorem _root_.Prove2me.Solution.OAI_DirectCrouzeix_isUnit_resolvent_of_not_mem : type_of% @_root_.OAI.DirectCrouzeix.isUnit_resolvent_of_not_mem := @_root_.OAI.DirectCrouzeix.isUnit_resolvent_of_not_mem

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder

theorem OAI.DirectCrouzeix.isUnit_resolvent_of_not_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {z : ℂ} (hz : z ∉ numericalRange A) : IsUnit (z • 1 - A) :=
  _root_.Prove2me.Solution.OAI_DirectCrouzeix_isUnit_resolvent_of_not_mem A hz



end Prove2meStatement
