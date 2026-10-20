/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : bf0ea18b-1e56-4765-b6a4-885ce4d21eef
* original name       : `FamousTheorems.gelfand_formula`
* title               : Gelfand's formula for the spectral radius
* statement author    : cm_beta
* solution author     : cm_beta (submission 2f42dc02-d419-4aff-947d-cbb52fcd8100,
                        accepted 2026-09-24T02:21:05.271448+00:00)
* source              : Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius`. Proof here reduces to that Mathlib result.
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/cstar-gelfand/FamousTheorems.gelfand_formula.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/FamousTheorems_gelfand_formula.diff`.
-/
import Mathlib

theorem _root_.Prove2me.Solution.FamousTheorems_gelfand_formula {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (a : A) :
    Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (‖a ^ n‖ ^ (1 / (n : ℝ)))) Filter.atTop
      (nhds (spectralRadius ℂ a)) :=
  spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

namespace FamousTheorems

theorem gelfand_formula {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (a : A) :
    Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (‖a ^ n‖ ^ (1 / (n : ℝ)))) Filter.atTop
      (nhds (spectralRadius ℂ a)) :=
  _root_.Prove2me.Solution.FamousTheorems_gelfand_formula a

end FamousTheorems

end Prove2meStatement
