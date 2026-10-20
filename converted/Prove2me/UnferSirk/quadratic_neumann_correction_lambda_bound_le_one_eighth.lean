/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 3d65ad9b-375c-4ad3-80aa-20460aa929d5
* original name       : `quadratic_neumann_correction_lambda_bound_le_one_eighth`
* title               : None
* statement author    : Shuze Chen
* solution author     : Shuze Chen (submission f47b2387-24e0-48a5-8677-0ad3a78b138b,
                        accepted 2026-06-21T03:08:33.815511+00:00)
* source              : Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.
* platform Mathlib rev: c5ea00351c28e24afc9f0f84379aa41082b1188f
* original file       : Downloads/unfer-sirk/quadratic_neumann_correction_lambda_bound_le_one_eighth.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/quadratic_neumann_correction_lambda_bound_le_one_eighth.diff`.
-/
import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open MatrixCompletion

theorem _root_.Prove2me.Solution.quadratic_neumann_correction_lambda_bound_le_one_eighth
    (C₂ : ℝ) (hC₂ : 0 < C₂) :
    C₂ * Real.rpow (max 1 ((8 * C₂) ^ 2)) (-((3 : ℝ) / 2)) ≤
      (1 : ℝ) / 8 := by
  by_cases hsmall : 8 * C₂ ≤ 1
  · have hsquare_le : (8 * C₂) ^ 2 ≤ (1 : ℝ) := by nlinarith
    rw [max_eq_left hsquare_le]
    have hC₂_le : C₂ ≤ (1 : ℝ) / 8 := by linarith
    simpa [Real.rpow_eq_pow] using hC₂_le
  · have hlarge : 1 ≤ 8 * C₂ := le_of_not_ge hsmall
    have hsquare_ge : (1 : ℝ) ≤ (8 * C₂) ^ 2 := by nlinarith
    rw [max_eq_right hsquare_ge, Real.rpow_eq_pow]
    rw [Real.rpow_neg (sq_nonneg (8 * C₂)) ((3 : ℝ) / 2)]
    rw [Real.rpow_div_two_eq_sqrt (3 : ℝ) (sq_nonneg (8 * C₂))]
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg (by linarith : 0 ≤ 8 * C₂)]
    have hx_nonneg : 0 ≤ C₂ * 8 := by linarith
    have hx_sq_ge : 1 ≤ (C₂ * 8) ^ 2 := by
      nlinarith [sq_nonneg (C₂ * 8 - 1)]
    have hx_le_cube : C₂ * 8 ≤ (C₂ * 8) ^ 3 := by
      calc
        C₂ * 8 = (C₂ * 8) * 1 := by ring
        _ ≤ (C₂ * 8) * ((C₂ * 8) ^ 2) :=
          mul_le_mul_of_nonneg_left hx_sq_ge hx_nonneg
        _ = (C₂ * 8) ^ 3 := by ring
    field_simp [hC₂.ne']
    simpa [Real.rpow_natCast] using hx_le_cube

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open MatrixCompletion

theorem quadratic_neumann_correction_lambda_bound_le_one_eighth
    (C₂ : ℝ) (hC₂ : 0 < C₂) :
    C₂ * Real.rpow (max 1 ((8 * C₂) ^ 2)) (-((3 : ℝ) / 2)) ≤
      (1 : ℝ) / 8 := by
  first
  | exact _root_.Prove2me.Solution.quadratic_neumann_correction_lambda_bound_le_one_eighth C₂ hC₂
  | (apply _root_.Prove2me.Solution.quadratic_neumann_correction_lambda_bound_le_one_eighth <;> assumption)


end Prove2meStatement
