/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 006029e0-c97d-4c4c-9fb5-5de1eaac31aa
* original name       : `OAI.DirectCrouzeix.positive_block_hsSq`
* title               : Hilbert–Schmidt bound for the off-diagonal block of a positive semidefinite block matrix
* statement author    : Shuze Chen
* solution author     : Shuze Chen (submission f77e907f-e6fd-4efc-85e0-218092048fb3,
                        accepted 2026-10-18T06:43:55.13367+00:00)
* source              : https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/PositiveBlocks.lean#L35-L62
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/crouzeix-convex/OAI.DirectCrouzeix.positive_block_hsSq.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/OAI_DirectCrouzeix_positive_block_hsSq.diff`.
-/
-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/PositiveBlocks.lean:L35-L62
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.positive_block_hsSq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks

-- ---- from OAI.Analysis.DirectCrouzeix.PositiveBlocks ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem re_trace_mul_nonneg {ι : Type u_5} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A * B)).re := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hC, Matrix.star_eq_conjTranspose, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  exact (Complex.nonneg_iff.mp (hB.mul_mul_conjTranspose_same C).trace_nonneg).1

theorem re_trace_block_comparison {ι : Type u_6} [Fintype ι] [DecidableEq ι]
    (D J : Matrix ι ι ℂ) (hD : D.PosSemidef) (hJ : J.IsHermitian) :
    0 ≤ (Matrix.trace (D * J * D * J)).re := by
  have hp := re_trace_mul_nonneg hD (hD.mul_mul_conjTranspose_same J)
  simpa only [hJ.eq, Matrix.mul_assoc] using hp

theorem positive_block_hsSq {ι : Type u_7} [Fintype ι] [DecidableEq ι]
    {U V Z : Matrix ι ι ℂ}
    (h : (Matrix.fromBlocks U Zᴴ Z V).PosSemidef) :
    2 * hsSq Z ≤ hsSq U + hsSq V := by
  let D := Matrix.fromBlocks U Zᴴ Z V
  let J : Matrix (Sum ι ι) (Sum ι ι) ℂ := Matrix.fromBlocks 1 0 0 (-1)
  have hJ : J.IsHermitian := by
    exact Matrix.IsHermitian.fromBlocks Matrix.isHermitian_one (by simp)
      Matrix.isHermitian_one.neg
  have hU : U.IsHermitian := by
    have hh := h.isHermitian
    exact hh.submatrix Sum.inl
  have hV : V.IsHermitian := by
    have hh := h.isHermitian
    exact hh.submatrix Sum.inr
  have hp := re_trace_block_comparison D J h hJ
  have trace_blocks (A B C E : Matrix ι ι ℂ) :
      Matrix.trace (Matrix.fromBlocks A B C E) = Matrix.trace A + Matrix.trace E := by
    simp [Matrix.trace]
  have he : Matrix.trace (D * J * D * J) =
      Matrix.trace (U * U) + Matrix.trace (V * V) -
        2 * Matrix.trace (Zᴴ * Z) := by
    simp [D, J, Matrix.fromBlocks_multiply, trace_blocks,
      Matrix.trace_mul_comm Z Zᴴ]
    ring
  rw [he] at hp
  norm_num at hp
  simpa only [hsSq, hU.eq, hV.eq] using hp

end DirectCrouzeix

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder


theorem _root_.Prove2me.Solution.OAI_DirectCrouzeix_positive_block_hsSq : type_of% @_root_.OAI.DirectCrouzeix.positive_block_hsSq := @_root_.OAI.DirectCrouzeix.positive_block_hsSq

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), checked against the solution above.  The solution declares the platform theorem `OAI.DirectCrouzeix.positive_block_hsSq` itself, so the statement is restated as an `example`. -/

section Prove2meStatement

open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder

example {ι : Type u_7} [Fintype ι] [DecidableEq ι]
    {U V Z : Matrix ι ι ℂ}
    (h : (Matrix.fromBlocks U Zᴴ Z V).PosSemidef) :
    2 * hsSq Z ≤ hsSq U + hsSq V := by
  first
  | exact _root_.Prove2me.Solution.OAI_DirectCrouzeix_positive_block_hsSq h
  | (apply _root_.Prove2me.Solution.OAI_DirectCrouzeix_positive_block_hsSq <;> assumption)


end Prove2meStatement
