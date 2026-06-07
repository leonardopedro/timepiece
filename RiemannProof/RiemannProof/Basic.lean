import Mathlib

open Complex

/-!
# Basic.lean — Minimal shared utilities for the Riemann Hypothesis project

This file contains only the lemmas needed by `ContourStrategy.lean`.
All other material (unit circle space, universal correction, limit exchange,
Hurwitz-based strategy) has been moved to `Legacy.lean`.
-/

/-- The functional equation symmetry: if ζ(s) = 0 for 0 < Re(s) < 1,
    then ζ(1 - s) = 0. -/
lemma zeta_symm (s : ℂ) (h1 : 0 < s.re) (h2 : s.re < 1)
    (hs : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 := by
  have h_ne_nat : ∀ (n : ℕ), s ≠ -↑n := by
    intro n hn
    have h_re : s.re = (-↑n : ℂ).re := by rw [hn]
    simp only [neg_re, Complex.natCast_re] at h_re
    have : (n : ℝ) ≥ 0 := Nat.cast_nonneg n
    linarith
  have h_ne_one : s ≠ 1 := by
    intro hn
    have h_re : s.re = (1 : ℂ).re := by rw [hn]
    simp only [one_re] at h_re
    linarith
  rw [riemannZeta_one_sub h_ne_nat h_ne_one, hs]
  ring
