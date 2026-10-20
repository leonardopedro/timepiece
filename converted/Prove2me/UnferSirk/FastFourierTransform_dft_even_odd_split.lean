/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : ffc67fdb-812d-4e6e-bff5-a3df1ec2c658
* original name       : `FastFourierTransform.dft_even_odd_split`
* title               : Danielson–Lanczos even/odd splitting
* statement author    : Lucas
* solution author     : cm_beta (submission 04918e64-e9be-4b96-aa47-a134bf47d438,
                        accepted 2026-09-23T09:29:06.562056+00:00)
* source              : Danielson & Lanczos 1942 (doubling step), as reported in Fast Fourier transform, Wikipedia (snapshot supplied by the mission captain's user), https://en.wikipedia.org/wiki/Fast_Fourier_transform, sections 'History' and 'Algorithms — Cooley–Tukey algorithm'
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/unfer-sirk/FastFourierTransform.dft_even_odd_split.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/FastFourierTransform_dft_even_odd_split.diff`.
-/
import Mathlib
import Definitions.Def_FastFourierTransform_dft

open FastFourierTransform

namespace Ag3Aux_DftEvenOdd

theorem sum_range_two_mul (N : ℕ) (f : ℕ → ℂ) :
    ∑ m ∈ Finset.range (2 * N), f m = ∑ m ∈ Finset.range N, (f (2 * m) + f (2 * m + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

end Ag3Aux_DftEvenOdd

open Ag3Aux_DftEvenOdd

theorem _root_.Prove2me.Solution.FastFourierTransform_dft_even_odd_split (N : ℕ) (hN : 0 < N) (x : ℕ → ℂ) (k : ℕ) :
    dft (2 * N) x k =
      dft N (fun m => x (2 * m)) k
        + Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / ((2 * N : ℕ) : ℂ)))
            * dft N (fun m => x (2 * m + 1)) k := by
  unfold dft
  rw [sum_range_two_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  congr 1
  · congr 2
    push_cast; field_simp
  · rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast; field_simp; ring

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

namespace FastFourierTransform

theorem dft_even_odd_split (N : ℕ) (hN : 0 < N) (x : ℕ → ℂ) (k : ℕ) :
    dft (2 * N) x k =
      dft N (fun m => x (2 * m)) k
        + Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / ((2 * N : ℕ) : ℂ)))
            * dft N (fun m => x (2 * m + 1)) k := by
  first
  | exact _root_.Prove2me.Solution.FastFourierTransform_dft_even_odd_split N hN x k
  | (apply _root_.Prove2me.Solution.FastFourierTransform_dft_even_odd_split <;> assumption)

end FastFourierTransform


end Prove2meStatement
