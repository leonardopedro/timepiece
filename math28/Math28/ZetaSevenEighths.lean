import Mathlib

/-!
# Zeros of `ζ` and of Dirichlet `L`-functions right of `7/8` (openai/math family 003)

**Source** (read-only snapshot, Lean v4.34.1, not imported):
`math/OAI/NumberTheory/DirichletL/Nonvanishing.lean`

* `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` —
  `(7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0`;
* `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` —
  `(7 / 8 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) → LFunction χ s ≠ 0`.

**Status of the source.**  The import closure (2,924 modules) contains no `sorry`, `axiom` or
`native_decide`, but it imports modules of two packages that are *not* part of the snapshot
(`PrimeNumberTheoremAnd.Wiener` and `RellichKondrachov…Rellich`), so the snapshot alone does not
determine the proof.  It was not re-elaborated here (the snapshot pins Lean v4.34.1).  A
zero-free half-plane `Re s > 7/8` for `ζ` is far beyond the zero-free regions in the published
literature known to this file's author; treat these statements strictly as named hypotheses.

## What this module states

* `RiemannZetaSevenEighths`, `DirichletSevenEighths` — the two source statements, verbatim
  (`riemannZeta`, `DirichletCharacter.LFunction` are the Mathlib names, re-checked on v4.28.0).

## Proved consequences (from the named hypothesis and Mathlib only)

* `riemannZetaSevenEighths_of_dirichlet` — the zeta statement is the trivial-character case
  of the Dirichlet statement.
* `re_mem_strip_of_zeta_eq_zero` — every zero of `ζ` other than the trivial zeros
  `-2, -4, …` has `1/8 ≤ Re s ≤ 7/8` (the left edge by the functional equation
  `riemannZeta_one_sub`).
* `zeroFreeRightHalfPlane_iff_band` — this project's RH proposition
  `RandomMap2RH.ZeroFreeRightHalfPlane` (`∀ s, 1/2 < s.re → riemannZeta s ≠ 0`, restated here
  as `ZeroFreeRightHalfPlane` so as not to import the `RandomMap` library) is equivalent, under
  the hypothesis, to zero-freeness of the band `1/2 < Re s ≤ 7/8`.
-/

namespace Math28.ZetaSevenEighths

open Complex

/-- **Named hypothesis — `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`.** -/
def RiemannZetaSevenEighths : Prop :=
  ∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0

/-- **Named hypothesis — `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`.** -/
def DirichletSevenEighths : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    (7 / 8 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- The project's RH proposition (`RandomMap/RandomMap2RH.lean`, `ZeroFreeRightHalfPlane`). -/
def ZeroFreeRightHalfPlane : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0

theorem riemannZetaSevenEighths_of_dirichlet (h : DirichletSevenEighths) :
    RiemannZetaSevenEighths := by
  intro s hs
  by_cases hs1 : s = 1
  · subst hs1
    exact riemannZeta_ne_zero_of_one_le_re (by simp)
  have := h 1 (1 : DirichletCharacter ℂ 1) s hs (fun h' => hs1 h'.2)
  rwa [DirichletCharacter.LFunction_modOne_eq] at this

/-- Every zero of `ζ` which is not a trivial zero `-2(n+1)` lies in the strip
`1/8 ≤ Re s ≤ 7/8`. -/
theorem re_mem_strip_of_zeta_eq_zero (h : RiemannZetaSevenEighths) {s : ℂ}
    (hs : riemannZeta s = 0) (htriv : ∀ n : ℕ, s ≠ -2 * (n + 1)) :
    1 / 8 ≤ s.re ∧ s.re ≤ 7 / 8 := by
  refine ⟨?_, ?_⟩
  · by_contra hlt
    push_neg at hlt
    set w : ℂ := 1 - s with hw
    have hwre : (7 / 8 : ℝ) < w.re := by
      simp only [hw, sub_re, one_re]; linarith
    have hwpos : 0 < w.re := by linarith
    have hwn : ∀ n : ℕ, w ≠ -n := by
      intro n hn
      have := congrArg Complex.re hn
      simp at this
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [riemannZeta_zero] at hs
      norm_num at hs
    have hw1 : w ≠ 1 := by
      intro h1; apply hs0; simp only [hw] at h1; linear_combination -h1
    have hfe := riemannZeta_one_sub hwn hw1
    have h1w : 1 - w = s := by simp [hw]
    rw [h1w, hs] at hfe
    have hz : riemannZeta w ≠ 0 := h w hwre
    have hG : Gamma w ≠ 0 := Gamma_ne_zero_of_re_pos hwpos
    have hpow : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]
      push_neg
      intro h0
      exfalso
      have : (2 * (Real.pi : ℂ)) ≠ 0 := by
        have := Real.pi_pos
        exact mul_ne_zero two_ne_zero (by exact_mod_cast this.ne')
      exact this h0
    have hcos : Complex.cos (Real.pi * w / 2) = 0 := by
      have h0 : 2 * (2 * (Real.pi : ℂ)) ^ (-w) * Gamma w * Complex.cos (Real.pi * w / 2)
          * riemannZeta w = 0 := hfe.symm
      rcases mul_eq_zero.mp h0 with h0 | h0
      · rcases mul_eq_zero.mp h0 with h0 | h0
        · rcases mul_eq_zero.mp h0 with h0 | h0
          · rcases mul_eq_zero.mp h0 with h0 | h0
            · norm_num at h0
            · exact absurd h0 hpow
          · exact absurd h0 hG
        · exact h0
      · exact absurd h0 hz
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
    have hwk : w = 2 * k + 1 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
      field_simp at hk
      exact hk
    have hsk : s = -2 * k := by linear_combination -hwk + hw.symm
    have hkre : (s.re : ℝ) = -2 * k := by rw [hsk]; simp
    have hk0 : (0 : ℤ) < k := by
      by_contra hk0
      push_neg at hk0
      rcases lt_or_eq_of_le hk0 with hk0 | hk0
      · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk0
        linarith
      · apply hs0; rw [hsk, hk0]; simp
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k = n + 1 := ⟨(k - 1).toNat, by omega⟩
    apply htriv n
    rw [hsk, hn]
    push_cast
    ring
  · by_contra hlt
    push_neg at hlt
    exact h s hlt hs

/-- Under the hypothesis, the project's RH proposition reduces to the band `1/2 < Re s ≤ 7/8`. -/
theorem zeroFreeRightHalfPlane_iff_band (h : RiemannZetaSevenEighths) :
    ZeroFreeRightHalfPlane ↔
      ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 7 / 8 → riemannZeta s ≠ 0 := by
  constructor
  · intro hz s hs _
    exact hz s hs
  · intro hb s hs
    by_cases h78 : s.re ≤ 7 / 8
    · exact hb s hs h78
    · exact h s (by push_neg at h78; exact_mod_cast h78)

end Math28.ZetaSevenEighths
