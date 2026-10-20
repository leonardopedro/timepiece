/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 9af28805-41b4-4416-9b42-bdf30c63dca3
* original name       : `ConnesRZ.weil_positivity_implies_RH`
* title               : Positivity of the Weil distribution implies the Riemann hypothesis
* statement author    : Lucas
* solution author     : waitingintime (submission c868df42-aaba-43d7-a385-cca362419f54,
                        accepted 2026-10-06T21:19:08.319248+00:00)
* source              : A. Connes, Noncommutative geometry and the Riemann zeta function, in: Mathematics: Frontiers and Perspectives, AMS (2000); section 3 "Weil positivity and the Trace formula", pp. 13-22. Transform: eq. (12), p. 15. Explicit formula: eq. (11), p. 15. Positivity/RH equivalence: concluding paragraph, p. 22. Specialised throughout to the global field k = Q with trivial Grossencharakter, so that the L-function is the Riemann zeta function.
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/analytic-nt/ConnesRZ.weil_positivity_implies_RH.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/ConnesRZ_weil_positivity_implies_RH.diff`.
-/
import Theorems.Thm_ConnesRZ_spectral_star_square
import Theorems.Thm_ConnesRZ_exists_pair_localization

open Complex MeasureTheory ConnesRZ

namespace ConnesRZCertificate

/-- Regrouping two distinct terms of an unconditionally convergent real family. -/
lemma hasSum_two_terms {ι : Type*} [DecidableEq ι] (f : ι → ℝ) (a b : ι) (hab : a ≠ b) (r : ℝ)
    (htail : HasSum (fun i => if i = a ∨ i = b then 0 else f i) r) :
    HasSum f (f a + f b + r) := by
  classical
  have h := ((hasSum_ite_eq a (f a)).add (hasSum_ite_eq b (f b))).add htail
  convert h using 1
  funext i
  by_cases ha : i = a
  · subst i; simp [hab]
  · by_cases hb : i = b
    · subst i; simp [Ne.symm hab]
    · simp [ha, hb]

/-- A checked certificate: interpolated values on one off-line pair, with a small tail,
force strictly negative Weil energy. Existence of this certificate is not asserted. -/
theorem negative_of_pair_certificate (s : ℂ) (hs : IsCriticalZero s)
    (hσ : IsCriticalZero (1 - (starRingEnd ℂ) s))
    (hne : s ≠ 1 - (starRingEnd ℂ) s)
    (hm : 0 < zeroMult s) (hmσ : 0 < zeroMult (1 - (starRingEnd ℂ) s))
    (g : ℝ → ℂ) (hg : IsTest g)
    (hgs : mellinHat g s = 1)
    (hgσ : mellinHat g (1 - (starRingEnd ℂ) s) = -1)
    (r : ℝ) (hr : r < 1)
    (htail : HasSum
      (fun ρ : {z : ℂ // IsCriticalZero z} =>
        if ρ.1 = s ∨ ρ.1 = 1 - (starRingEnd ℂ) s then 0 else
          ((zeroMult ρ.1 : ℂ) * (mellinHat g ρ.1 *
            (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) ρ.1)))).re) r) :
    (weilDistribution (conv g (starInv g))).re < 0 := by
  classical
  let a : {z : ℂ // IsCriticalZero z} := ⟨s, hs⟩
  let b : {z : ℂ // IsCriticalZero z} := ⟨1 - (starRingEnd ℂ) s, hσ⟩
  let f : {z : ℂ // IsCriticalZero z} → ℝ := fun ρ =>
    ((zeroMult ρ.1 : ℂ) * (mellinHat g ρ.1 *
      (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) ρ.1)))).re
  have hab : a ≠ b := by
    intro h; exact hne (congrArg Subtype.val h)
  have htail' : HasSum (fun i => if i = a ∨ i = b then 0 else f i) r := by
    simpa only [a, b, f, Subtype.ext_iff] using htail
  have hsum := hasSum_two_terms f a b hab r htail'
  have hfull := Complex.reCLM.hasSum (spectral_star_square g hg)
  have heq : f a + f b + r = (weilDistribution (conv g (starInv g))).re :=
    hsum.unique hfull
  have ha : f a = -(zeroMult s : ℝ) := by
    simp [f, a, hgs, hgσ]
  have hb : f b = -(zeroMult (1 - (starRingEnd ℂ) s) : ℝ) := by
    simp [f, b, hgs, hgσ]
  have hm' : (1 : ℝ) ≤ zeroMult s := by exact_mod_cast hm
  have hmσ' : (1 : ℝ) ≤ zeroMult (1 - (starRingEnd ℂ) s) := by exact_mod_cast hmσ
  rw [ha, hb] at heq
  linarith

end ConnesRZCertificate

/-- A tracked reduction to the open Burnol localization child. -/
theorem _root_.Prove2me.Solution.ConnesRZ_weil_positivity_implies_RH
    (hpos : ∀ g : ℝ → ℂ, IsTest g →
      0 ≤ (weilDistribution (conv g (starInv g))).re) :
    ∀ s : ℂ, IsCriticalZero s → s.re = 1 / 2 := by
  intro s hs
  by_contra hline
  obtain ⟨g, hg, hσ, hm, hmσ, hgs, hgσ, r, hr, htail⟩ := ConnesRZ.exists_pair_localization s hs hline
  have hne : s ≠ 1 - (starRingEnd ℂ) s := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    apply hline
    linarith
  have hnegative := ConnesRZCertificate.negative_of_pair_certificate s hs hσ hne hm hmσ
    g hg hgs hgσ r hr htail
  exact (not_lt_of_ge (hpos g hg)) hnegative

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open Complex

namespace ConnesRZ

theorem weil_positivity_implies_RH
    (hpos : ∀ g : ℝ → ℂ, IsTest g → 0 ≤ (weilDistribution (conv g (starInv g))).re) :
    ∀ s : ℂ, IsCriticalZero s → s.re = 1 / 2 := by
  first
  | exact _root_.Prove2me.Solution.ConnesRZ_weil_positivity_implies_RH hpos
  | (apply _root_.Prove2me.Solution.ConnesRZ_weil_positivity_implies_RH <;> assumption)

end ConnesRZ


end Prove2meStatement
