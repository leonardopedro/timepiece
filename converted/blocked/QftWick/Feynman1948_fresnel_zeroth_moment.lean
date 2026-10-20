/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : e547a4b2-ee7f-4ee8-a631-2fbe18b6c75a
* original name       : `Feynman1948.fresnel_zeroth_moment`
* title               : Eq. (26), first integral: $\int e^{im\xi^2/2\hbar\varepsilon}\,d\xi = (2\pi\hbar\varepsilon i/m)^{1/2}$
* statement author    : Lucas
* solution author     : Mazecto (submission 2c6c7d8f-6c71-4c88-9e79-db656de5d0ac,
                        accepted 2026-10-02T20:18:50.051363+00:00)
* source              : R. P. Feynman, Space-Time Approach to Non-Relativistic Quantum Mechanics, Rev. Mod. Phys. 20, 367 (1948), https://doi.org/10.1103/RevModPhys.20.367, p. 375, Eq. (26), first formula; footnote 13 (p. 376)
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/qft-wick/Feynman1948.fresnel_zeroth_moment.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/Feynman1948_fresnel_zeroth_moment.diff`.
-/
import Definitions.Def_Feynman1948_WaveEquation
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

open Complex Filter MeasureTheory Topology Feynman1948

theorem _root_.Prove2me.Solution.Feynman1948_fresnel_zeroth_moment (ħ m ε : ℝ) (hħ : 0 < ħ) (hm : 0 < m) (hε : 0 < ε) :
    Tendsto (fun δ : ℝ => regularizedMoment ħ m ε δ 0) (𝓝[>] 0)
      (𝓝 (normalizingFactor ħ m ε)) := by
  let c : ℝ := m / (2 * ħ * ε)
  have hc : 0 < c := div_pos hm (mul_pos (mul_pos (by norm_num) hħ) hε)
  let b : ℝ → ℂ := fun δ => (c : ℂ) * ((δ : ℂ) - I) / ((1 + δ ^ 2 : ℝ) : ℂ)
  have hbpos (δ : ℝ) (hδ : 0 < δ) : 0 < (b δ).re := by
    simp only [b, Complex.div_ofReal_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.I_re, sub_zero, zero_mul, sub_zero]
    exact div_pos (mul_pos hc hδ) (by positivity)
  have hcoef (δ : ℝ) : -b δ = I * m / (2 * (ħ * (1 - I * δ)) * ε) := by
    have hd : (1 - I * (δ : ℂ)) ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      simp at hh
    have hs : (1 + δ ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
    dsimp [b, c]
    push_cast
    field_simp [hd, Complex.ofReal_ne_zero.mpr hħ.ne',
      Complex.ofReal_ne_zero.mpr hε.ne', Complex.ofReal_ne_zero.mpr hs]
    ring_nf
    have hsc : (1 + (δ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hs
    have hdc : (1 - (δ : ℂ) * I) ≠ 0 := by simpa [mul_comm] using hd
    field_simp [hsc, hdc]
    ring_nf
    simp [Complex.I_sq]
  have hmoment (δ : ℝ) (hδ : 0 < δ) : regularizedMoment ħ m ε δ 0 =
      ((Real.pi : ℂ) / b δ) ^ (1 / 2 : ℂ) := by
    rw [← integral_gaussian_complex (hbpos δ hδ)]
    apply integral_congr_ae
    filter_upwards [] with ξ
    simp only [pow_zero, one_mul]
    congr 1
    rw [hcoef]
    ring
  have hb0 : b 0 = -(c : ℂ) * I := by simp [b]
  have hbne : b 0 ≠ 0 := by
    rw [hb0]
    exact mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hc.ne')) I_ne_zero
  have hbcont : ContinuousAt b 0 := by
    dsimp [b]
    fun_prop (disch := norm_num)
  have hratio : (Real.pi : ℂ) / b 0 = 2 * Real.pi * ħ * ε * I / m := by
    rw [hb0]
    dsimp [c]
    push_cast
    field_simp
    ring_nf
    simp [Complex.I_sq]
  have hslit : (Real.pi : ℂ) / b 0 ∈ Complex.slitPlane := by
    rw [hratio]
    apply Or.inr
    have hp : 0 < 2 * Real.pi * ħ * ε / m :=
      div_pos (mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hħ) hε) hm
    simpa using hp.ne'
  have hratlim : Tendsto (fun δ : ℝ => (Real.pi : ℂ) / b δ) (𝓝[>] 0)
      (𝓝 ((Real.pi : ℂ) / b 0)) :=
    (continuousAt_const.div hbcont hbne).tendsto.mono_left nhdsWithin_le_nhds
  have hlim := (continuousAt_cpow_const (b := (1 / 2 : ℂ)) hslit).tendsto.comp hratlim
  have hlim' : Tendsto (fun δ : ℝ => ((Real.pi : ℂ) / b δ) ^ (1 / 2 : ℂ))
      (𝓝[>] 0) (𝓝 (normalizingFactor ħ m ε)) := by
    simpa only [Function.comp_def, hratio, normalizingFactor] using hlim
  apply hlim'.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (hmoment δ hδ).symm

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open Complex Filter Topology SchwartzMap

namespace Feynman1948

theorem fresnel_zeroth_moment (ħ m ε : ℝ) (hħ : 0 < ħ) (hm : 0 < m) (hε : 0 < ε) :
    Tendsto (fun δ : ℝ => regularizedMoment ħ m ε δ 0) (𝓝[>] 0)
      (𝓝 (normalizingFactor ħ m ε)) :=
  _root_.Prove2me.Solution.Feynman1948_fresnel_zeroth_moment ħ m ε hħ hm hε

end Feynman1948

end Prove2meStatement
