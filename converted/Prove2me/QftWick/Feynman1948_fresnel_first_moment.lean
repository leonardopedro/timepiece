/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : d5ea0cc1-81b1-41f3-98e3-5667e7e64606
* original name       : `Feynman1948.fresnel_first_moment`
* title               : Eq. (26), second integral: $\int e^{im\xi^2/2\hbar\varepsilon}\,\xi\,d\xi = 0$
* statement author    : Lucas
* solution author     : Mazecto (submission 91068b99-b218-4d0d-b8b3-03e48f958a92,
                        accepted 2026-10-02T19:15:55.927614+00:00)
* source              : R. P. Feynman, Space-Time Approach to Non-Relativistic Quantum Mechanics, Rev. Mod. Phys. 20, 367 (1948), https://doi.org/10.1103/RevModPhys.20.367, p. 375, Eq. (26), second formula; footnote 13 (p. 376)
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/qft-wick/Feynman1948.fresnel_first_moment.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/Feynman1948_fresnel_first_moment.diff`.
-/
import Definitions.Def_Feynman1948_WaveEquation
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

open Complex MeasureTheory Feynman1948

theorem _root_.Prove2me.Solution.Feynman1948_fresnel_first_moment (ħ m ε : ℝ) (_hħ : 0 < ħ) (_hm : 0 < m) (_hε : 0 < ε) :
    ∀ δ : ℝ, 0 < δ → regularizedMoment ħ m ε δ 1 = 0 := by
  intro δ hδ
  unfold regularizedMoment
  simp only [pow_one]
  have h := integral_neg_eq_self
    (fun ξ : ℝ => (ξ : ℂ) *
      exp (I * m * (ξ : ℂ) ^ 2 / (2 * (ħ * (1 - I * δ)) * ε))) volume
  simp only [Complex.ofReal_neg, neg_sq, neg_mul] at h
  rw [integral_neg] at h
  apply Complex.ext
  · exact eq_zero_of_neg_eq (congrArg Complex.re h)
  · exact eq_zero_of_neg_eq (congrArg Complex.im h)

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open Complex Filter Topology SchwartzMap

namespace Feynman1948

theorem fresnel_first_moment (ħ m ε : ℝ) (hħ : 0 < ħ) (hm : 0 < m) (hε : 0 < ε) :
    ∀ δ : ℝ, 0 < δ → regularizedMoment ħ m ε δ 1 = 0 := by
  first
  | exact _root_.Prove2me.Solution.Feynman1948_fresnel_first_moment ħ m ε hħ hm hε
  | (apply _root_.Prove2me.Solution.Feynman1948_fresnel_first_moment <;> assumption)

end Feynman1948


end Prove2meStatement
