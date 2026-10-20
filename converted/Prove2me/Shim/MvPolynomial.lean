import Mathlib

/-!
# Shim: `MvPolynomial.coeff_pderiv`

The prove2.me platform Mathlib provides `MvPolynomial.coeff_pderiv`, which the pinned
Mathlib lacks.  It is proved here from the pinned API, under the platform name, so that
the converted platform modules keep their text.
-/

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R]

/-- The coefficient of a partial derivative: `∂ᵢ (x^(m + eᵢ)) = (mᵢ + 1) x^m`. -/
theorem coeff_pderiv [DecidableEq σ] (i : σ) (p : MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m (pderiv i p) = (m i + 1) * coeff (m + Finsupp.single i 1) p := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, mul_add]
  | monomial n a =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : n = m + Finsupp.single i 1
    · subst h
      simp [mul_comm]
    · rw [if_neg h, mul_zero]
      split_ifs with h'
      · have hi : n i = 0 := by
          by_contra hne
          apply h
          rw [← h']
          ext j
          by_cases hj : j = i
          · subst hj; simp; omega
          · simp [Ne.symm hj]
        simp [hi]
      · rfl

end MvPolynomial
