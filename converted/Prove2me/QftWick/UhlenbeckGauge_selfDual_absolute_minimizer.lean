/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 540bade1-d585-4bf6-9c68-b022fabf478a
* original name       : `UhlenbeckGauge.selfDual_absolute_minimizer`
* title               : Proposition 3.1.1 — (anti-)self-dual connections are absolute minimizers of Yang-Mills (box version)
* statement author    : Lucas
* solution author     : SamenHossain (submission ca0bbcd4-1e8e-4a62-9eb4-bcb95e49e018,
                        accepted 2026-10-10T21:46:17.824798+00:00)
* source              : K. Uhlenbeck, *Equations of Gauge Theory*, lecture notes by L. Fredrickson (Emil Grosswald Lectures, Temple University, February 7-9, 2012), Chapter 3, Section 3.1, pp. 29-32, Proposition 3.1.1 (p. 31)
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/qft-wick/UhlenbeckGauge.selfDual_absolute_minimizer.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/UhlenbeckGauge_selfDual_absolute_minimizer.diff`.
-/
import Definitions.Def_uhlenbeck_gauge_box_defs
import Theorems.Thm_UhlenbeckGauge_yangMills_ge_boundaryChernSimons
import Theorems.Thm_UhlenbeckGauge_yangMills_eq_boundaryChernSimons_iff
import Theorems.Thm_UhlenbeckGauge_boundaryChernSimons_eq_of_eq_on_boundary

open UhlenbeckGauge MeasureTheory
set_option autoImplicit false

/-- Proposition 3.1.1 (box version). On a non-degenerate box, the (anti-)self-dual `A` attains
the energy bound with equality, `Ym(A) = ∓ Re ∫_{∂Ω} CS(A)`; the Chern–Simons boundary term of
`A` equals that of `B` because the two connections agree on `∂Ω`; and `B` satisfies the energy
bound `Ym(B) ≥ ∓ Re ∫_{∂Ω} CS(B)`. On a degenerate box both energies vanish. -/
theorem _root_.Prove2me.Solution.UhlenbeckGauge_selfDual_absolute_minimizer {n : ℕ} (a b : R4) (A B : Connection n)
    (hA : IsSUConnection A) (hB : IsSUConnection B)
    (hbdry : ∀ x, OnBoxBoundary a b x → A x = B x)
    (hdual : (∀ x ∈ Set.Icc a b, IsSelfDual (curvature A x)) ∨
      (∀ x ∈ Set.Icc a b, IsAntiSelfDual (curvature A x))) :
    yangMills a b A ≤ yangMills a b B := by
  by_cases hlt : ∀ μ, a μ < b μ
  · have hab : a ≤ b := fun μ => (hlt μ).le
    -- the boundary term is determined by the boundary data
    have hCS : boundaryChernSimons a b A = boundaryChernSimons a b B :=
      boundaryChernSimons_eq_of_eq_on_boundary a b hab A B hA hB hbdry
    -- energy bound for `B`, both signs
    obtain ⟨hB1, hB2⟩ := yangMills_ge_boundaryChernSimons a b hab B hB
    -- equality case for `A`
    obtain ⟨hA1, hA2⟩ := yangMills_eq_boundaryChernSimons_iff a b hlt A hA
    rcases hdual with h | h
    · rw [hA1.mpr h, hCS]
      exact hB1
    · rw [hA2.mpr h, hCS]
      exact hB2
  · -- degenerate box: `[a, b]` is a null set, so both energies are `0`
    push Not at hlt
    obtain ⟨μ, hμ⟩ := hlt
    have hvol : volume (Set.Icc a b) = 0 := by
      rw [Real.volume_Icc_pi]
      exact Finset.prod_eq_zero (Finset.mem_univ μ) (by simp [hμ])
    have h0 : ∀ C : Connection n, yangMills a b C = 0 := fun C => by
      unfold yangMills
      rw [Measure.restrict_eq_zero.mpr hvol, integral_zero_measure]
    rw [h0 A, h0 B]

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open UhlenbeckGauge

namespace UhlenbeckGauge

theorem selfDual_absolute_minimizer {n : ℕ} (a b : R4) (A B : Connection n)
    (hA : IsSUConnection A) (hB : IsSUConnection B)
    (hbdry : ∀ x, OnBoxBoundary a b x → A x = B x)
    (hdual : (∀ x ∈ Set.Icc a b, IsSelfDual (curvature A x)) ∨
      (∀ x ∈ Set.Icc a b, IsAntiSelfDual (curvature A x))) :
    yangMills a b A ≤ yangMills a b B := by
  first
  | exact _root_.Prove2me.Solution.UhlenbeckGauge_selfDual_absolute_minimizer a b A B hA hB hbdry hdual
  | (apply _root_.Prove2me.Solution.UhlenbeckGauge_selfDual_absolute_minimizer <;> assumption)

end UhlenbeckGauge


end Prove2meStatement
