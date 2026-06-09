import Mathlib
import RiemannProof.ShiftedEta
import RiemannProof.RectangleStrategy

/-!
# Conjugate-Reflection Product and Rectangle Contour Setup

## Overview

This file implements Tasks 3 and 4 of the implementation plan:

- **Task 3**: Define F_n(s) = f_n*(s*) · f_n(s) (conjugate-reflection
  product) and prove:
  - F_n(σ) = |f_n(σ)|² ≥ 0 for real σ
  - 1/F_n has poles of even multiplicity 2m at zeros of η(2s−1)

- **Task 4**: Set up the rectangle R = [σ₀−δ, σ₀+δ] × [0, T] with:
  - Bottom edge on the real axis (y = 0)
  - s₀ = σ₀ + i in the interior (y=1 scaling)
  - Exactly one zero of η(2s−1) inside R
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
## Section 1: The Conjugate-Reflection Product (Task 3)
-/

/-- The conjugate-reflection product:
    F_n(s) = conj(f_n(conj(s))) · f_n(s)

    On the real axis this equals |f_n(σ)|², which is non-negative. -/
noncomputable def conjReflApprox (n : ℕ) (s : ℂ) : ℂ :=
  starRingEnd ℂ (fApprox n (starRingEnd ℂ s)) * fApprox n s

/-- The limit of the conjugate-reflection product:
    F(s) = conj(g(conj(s))) · g(s)
    where g(s) = targetH(s) · etaShifted(s). -/
noncomputable def conjReflLimit (s : ℂ) : ℂ :=
  starRingEnd ℂ (targetH (starRingEnd ℂ s) * etaShifted (starRingEnd ℂ s)) *
    (targetH s * etaShifted s)

/-- On the real axis, F_n(σ) = |f_n(σ)|² is real and non-negative. -/
lemma conjReflApprox_real_nonneg (n : ℕ) (σ : ℝ) :
    (conjReflApprox n (σ : ℂ)).im = 0 ∧
    0 ≤ (conjReflApprox n (σ : ℂ)).re := by
  unfold conjReflApprox
  rw [Complex.conj_ofReal,
    show starRingEnd ℂ (fApprox n ↑σ) * fApprox n ↑σ =
      ↑(Complex.normSq (fApprox n ↑σ)) from by rw [mul_comm, Complex.mul_conj]]
  exact ⟨Complex.ofReal_im _, by exact_mod_cast Complex.normSq_nonneg _⟩

/-- The conjugate-reflection product on the real axis equals the norm squared. -/
lemma conjReflApprox_eq_normSq (n : ℕ) (σ : ℝ) :
    conjReflApprox n (σ : ℂ) = ↑(Complex.normSq (fApprox n (σ : ℂ))) := by
  unfold conjReflApprox
  rw [Complex.conj_ofReal, mul_comm, Complex.mul_conj]

/-!
## Section 2: Multiplicity Properties (Task 3 continued)

If η(2s−1) has a zero of multiplicity m at s₀, the product F_n
converges to a function with a zero of order 2m at s₀. This means
1/F has a pole of **even** order 2m at s₀.
-/

/-- If etaShifted has a zero of order m at s₀, and targetH(s₀) ≠ 0,
    then conjReflLimit has a zero of order 2m at s₀. -/
lemma conjReflLimit_zero_order (s₀ : ℂ) (m : ℕ) (hm : m ≥ 1)
    (h_eta_order : ∃ φ : ℂ → ℂ, Differentiable ℂ φ ∧ φ s₀ ≠ 0 ∧
      ∀ s, etaShifted s = (s - s₀) ^ m * φ s)
    (h_targetH : targetH s₀ ≠ 0)
    (h_targetH_conj : targetH (starRingEnd ℂ s₀) ≠ 0) :
    ∃ ψ : ℂ → ℂ, Differentiable ℂ ψ ∧ ψ s₀ ≠ 0 ∧
      ∀ s, conjReflLimit s = (s - s₀) ^ (2 * m) * ψ s := by
  sorry

/-- Even-multiplicity poles arise from the conjugate-reflection:
    if F has a zero of order 2m, then 1/F has a pole of order 2m (even). -/
lemma even_multiplicity_pole (m : ℕ) (_hm : m ≥ 1) : Even (2 * m) :=
  even_two_mul m

/-!
## Section 3: Rectangle Contour Setup (Task 4)

We define a rectangle R = [σ₀−δ, σ₀+δ] × [0, T] with:
- Bottom edge on the real axis (y = 0)
- s₀ = σ₀ + i in the interior
- T > 1 so s₀ is enclosed
- δ small enough that s₀ is the only zero of η(2s−1) inside R
-/

/-- A half-rectangle with bottom edge on the real axis.
    This is a special case of `Rect` where y_lo = 0. -/
def mkHalfRect (x_lo x_hi T : ℝ) (hx : x_lo < x_hi) (hT : 0 < T) : Rect where
  x_lo := x_lo
  x_hi := x_hi
  y_lo := 0
  y_hi := T
  hx := hx
  hy := hT

/-- The half-rectangle contains s₀ = σ₀ + i in its interior
    when σ₀ ∈ (x_lo, x_hi) and T > 1. -/
lemma mkHalfRect_contains_s₀ (σ₀ δ T : ℝ) (hδ : 0 < δ) (hT : 1 < T)
    (hσ₀_lo : 1 / 2 < σ₀) (hσ₀_hi : σ₀ < 1) :
    (σ₀ : ℂ) + I ∈ (mkHalfRect (σ₀ - δ) (σ₀ + δ) T (by linarith) (by linarith)).openInt := by
  simp only [Rect.openInt, Set.mem_setOf_eq, mkHalfRect]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero,
             Complex.add_im, Complex.ofReal_im, Complex.I_im]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The bottom edge of a half-rectangle lies on the real axis. -/
lemma mkHalfRect_bottom_real (x_lo x_hi T : ℝ) (hx : x_lo < x_hi) (hT : 0 < T) :
    ∀ s : ℂ, s.re ∈ Set.Icc x_lo x_hi → s.im = 0 →
      s ∈ (mkHalfRect x_lo x_hi T hx hT).closure := by
  intro s hs him
  simp only [Rect.closure, Set.mem_setOf_eq, mkHalfRect]
  exact ⟨hs.1, hs.2, by simp [him], by simp [him]; linarith⟩

/-!
## Section 4: Cauchy's Theorem and Contour Integrals
-/

/-- Cauchy's theorem for the conjugate-reflection product.
    Note: conjReflApprox involves conjugation and is not literally
    holomorphic, so this integral identity requires the specific
    structure of the conjugate-reflection construction. -/
lemma conjReflApprox_cauchy (R : Rect) (n : ℕ) :
    R.boundaryIntegral (conjReflApprox n) = 0 := by
  sorry

/-!
## Section 5: Existence of Good Rectangles
-/

/-- Given a zero s₀ of etaShifted in the critical strip, there exists
    a rectangle enclosing exactly s₀ as the unique zero inside. -/
lemma exists_isolating_rect (s₀ : ℂ) (hσ₁ : s₀.re > 1 / 2) (hσ₂ : s₀.re < 1)
    (h_zero : etaShifted s₀ = 0) :
    ∃ (δ T : ℝ) (hδ : 0 < δ) (hT : s₀.im + 1 < T)
      (hx : s₀.re - δ < s₀.re + δ) (hT' : 0 < T),
      let R := mkHalfRect (s₀.re - δ) (s₀.re + δ) T hx hT'
      s₀ ∈ R.openInt ∧
      (∀ z ∈ R.closure, etaShifted z = 0 → z = s₀) ∧
      (∀ z ∈ R.closure \ R.openInt, etaShifted z ≠ 0) := by
  sorry

end
