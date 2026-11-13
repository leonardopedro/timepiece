import Mathlib
import BookProof.Toolbox.ChapterHermiteVanishing

/-!
# The quartic Hermite entry

In the normalized product-Hermite basis the *quartic* matrix entry is the integer-valued-radical
number familiar from the oscillator algebra:

`⟨ψ_{n+4}, x⁴ ψ_n⟩ = √((n+1)(n+2)(n+3)(n+4))`.

This is the entry that a magnetic field-strength term of degree four produces in the Hermite
coordinates of the Yang–Mills gate library, so it is the analytic input the commutator-gate
analysis of `BookProof.FockWeightedGateSharpness` needs.

## Proof

Both ingredients are degree statements, not integral computations.

* **Cancellation.**  `x⁴ He_n` and `He_{n+4}` are both monic of degree `n + 4`
  (`IsMonicOfDegree.natDegree_sub_lt`), so the difference `x⁴ He_n − He_{n+4}` has total degree
  below `n + 4`.
* **Vanishing.**  `∫ He_{n+4} · q e^{-x²/2} = 0` for every polynomial of degree below `n + 4`, by
  expanding `q` in monomials and applying the single-variable vanishing lemma
  `gint_X_pow_hermiteR_zero` of `BookProof.HermiteVanishing`.  Hence the quartic integral equals
  `∫ He_{n+4}² e^{-x²/2} = ‖He_{n+4}‖²`, and after dividing by the two norms the entry is the
  *ratio of consecutive normalizing constants* `hermiteNorm (n+4) / hermiteNorm n`.  Four
  applications of `hermiteNorm_succ` (which is `√(n+1)` per step) give the radical.

## Contents

* `gint_sum` — linearity of the Gaussian integral over a finite sum;
* `isMonicOfDegree_hermiteR` — `He_n` is monic of degree `n`;
* `natDegree_X_pow_mul_sub_hermiteR` — `x⁴ He_n − He_{n+4}` has degree below `n + 4`;
* `gint_hermiteR_mul_eq_zero` — `∫ He_n · q e^{-x²/2} = 0` for `deg q < n`;
* `gint_hermiteR_quartic` — the quartic integral is `‖He_{n+4}‖²`;
* `hermiteNorm_four`, `hermiteNorm_ratio` — `‖He_{n+4}‖/‖He_n‖ = √((n+1)⋯(n+4))`;
* `quartic_hermite_entry` — **the entry** `⟨ψ_{n+4}, x⁴ ψ_n⟩ = √((n+1)(n+2)(n+3)(n+4))`;
* the quadratic companions `gint_hermiteR_square`, `hermiteNorm_two`, `hermiteNorm_ratio_two`
  and `quadratic_hermite_entry` — `⟨ψ_{n+2}, x² ψ_n⟩ = √((n+1)(n+2))`, the factor a two-coordinate
  quartic entry is built from.

## Honest boundary

These are the one-dimensional statements written in the Gaussian-weighted inner product that
`hermiteInner` uses, i.e. the normalized basis `ψ_n = He_n / ‖He_n‖`.  The `d`-dimensional entries
along a coordinate `⟨ψ_{α+4e_i}, x_i⁴ ψ_α⟩` follows from it by Fubini the same way
`inner_monomial_hermiteMv` follows from the one-dimensional integral, but that reduction is not
carried out here.
-/

namespace BookProof.HermiteQuartic

open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteVanishing
open BookProof.HermiteProductBasis

noncomputable section

/-! ## Linearity of the Gaussian integral -/

/-- The Gaussian integral of a finite sum is the sum of the integrals. -/
theorem gint_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ) :
    gint (s.sum f) = s.sum (fun i => gint (f i)) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, gint_add, ih]

/-! ## The degree statement -/

/-- `He_n` is monic of degree `n`. -/
theorem isMonicOfDegree_hermiteR (n : ℕ) : (hermiteR n).IsMonicOfDegree n := by
  rw [Polynomial.isMonicOfDegree_iff]
  exact ⟨le_of_eq (natDegree_hermiteR n), coeff_hermiteR_self n⟩

/-- **`x⁴ He_n − He_{n+4}` has degree below `n + 4`**: the two polynomials have the same leading
term. -/
theorem natDegree_X_pow_mul_sub_hermiteR (n : ℕ) :
    (Polynomial.X ^ 4 * hermiteR n - hermiteR (n + 4)).natDegree < n + 4 := by
  have hmul : (Polynomial.X ^ 4 * hermiteR n).IsMonicOfDegree (n + 4) := by
    have h := (Polynomial.isMonicOfDegree_X_pow (R := ℝ) 4).mul (isMonicOfDegree_hermiteR n)
    simpa [Nat.add_comm] using h
  exact IsMonicOfDegree.natDegree_sub_lt (Nat.succ_ne_zero (n + 3)) hmul
    (isMonicOfDegree_hermiteR (n + 4))

/-! ## Vanishing against a low-degree polynomial -/

/-- **`∫ He_n · q e^{-x²/2} = 0` for `deg q < n`**: expand `q` in monomials and apply the
single-variable vanishing lemma to each of them. -/
theorem gint_hermiteR_mul_eq_zero {n : ℕ} {q : Polynomial ℝ} (hq : q.natDegree < n) :
    gint (hermiteR n * q) = 0 := by
  have hqsum : q = (Finset.range n).sum
      (fun i => Polynomial.C (q.coeff i) * Polynomial.X ^ i) := by
    simpa using Polynomial.as_sum_range_C_mul_X_pow' q hq
  rw [hqsum, Finset.mul_sum, gint_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hin : i < n := Finset.mem_range.mp hi
  have hterm : hermiteR n * (Polynomial.C (q.coeff i) * Polynomial.X ^ i)
      = Polynomial.C (q.coeff i) * (Polynomial.X ^ i * hermiteR n) := by ring
  rw [hterm, gint_C_mul, gint_X_pow_hermiteR_zero n i hin, mul_zero]

/-! ## The quartic integral and the norm ratio -/

/-- **The quartic integral**: `∫ He_{n+4} · x⁴ He_n e^{-x²/2} = ‖He_{n+4}‖²`, because the
difference `x⁴ He_n − He_{n+4}` has too low a degree to contribute. -/
theorem gint_hermiteR_quartic (n : ℕ) :
    gint (hermiteR (n + 4) * (Polynomial.X ^ 4 * hermiteR n))
      = hermiteInner (n + 4) (n + 4) := by
  have hsplit : Polynomial.X ^ 4 * hermiteR n
      = hermiteR (n + 4) + (Polynomial.X ^ 4 * hermiteR n - hermiteR (n + 4)) := by ring
  rw [hsplit, mul_add, gint_add, gint_hermiteR_mul_eq_zero (natDegree_X_pow_mul_sub_hermiteR n),
    add_zero, hermiteInner]

/-- Four steps of `hermiteNorm_succ`. -/
theorem hermiteNorm_four (n : ℕ) :
    hermiteNorm (n + 4) = hermiteNorm n * (Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 2)
      * Real.sqrt ((n : ℝ) + 3) * Real.sqrt ((n : ℝ) + 4)) := by
  have h1 := hermiteNorm_succ n
  have h2 := hermiteNorm_succ (n + 1)
  have h3 := hermiteNorm_succ (n + 2)
  have h4 := hermiteNorm_succ (n + 3)
  have h2' : hermiteNorm (n + 1) * Real.sqrt ((n : ℝ) + 1)
      = hermiteNorm n * (Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)) := by
    rw [h1]; ring
  have e2 : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  have e3 : ((n + 2 : ℕ) : ℝ) + 1 = (n : ℝ) + 3 := by push_cast; ring
  have e4 : ((n + 3 : ℕ) : ℝ) + 1 = (n : ℝ) + 4 := by push_cast; ring
  rw [show n + 4 = (n + 3) + 1 from rfl, h4, e4,
    show n + 3 = (n + 2) + 1 from rfl, h3, e3,
    show n + 2 = (n + 1) + 1 from rfl, h2, e2, h1]
  ring

/-- **The norm ratio**: `‖He_{n+4}‖ / ‖He_n‖ = √((n+1)(n+2)(n+3)(n+4))`. -/
theorem hermiteNorm_ratio (n : ℕ) :
    hermiteNorm (n + 4) / hermiteNorm n
      = Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4)) := by
  rw [hermiteNorm_four, mul_div_cancel_left₀ _ (ne_of_gt (hermiteNorm_pos n))]
  have h1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) ≤ ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  have h3 : (0 : ℝ) ≤ ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) := by positivity
  rw [← Real.sqrt_mul h1, ← Real.sqrt_mul h2, ← Real.sqrt_mul h3]

/-! ## The quadratic entry -/

/-- **`x² He_n − He_{n+2}` has degree below `n + 2`**. -/
theorem natDegree_X_pow_two_mul_sub_hermiteR (n : ℕ) :
    (Polynomial.X ^ 2 * hermiteR n - hermiteR (n + 2)).natDegree < n + 2 := by
  have hmul : (Polynomial.X ^ 2 * hermiteR n).IsMonicOfDegree (n + 2) := by
    have h := (Polynomial.isMonicOfDegree_X_pow (R := ℝ) 2).mul (isMonicOfDegree_hermiteR n)
    simpa [Nat.add_comm] using h
  exact IsMonicOfDegree.natDegree_sub_lt (Nat.succ_ne_zero (n + 1)) hmul
    (isMonicOfDegree_hermiteR (n + 2))

/-- **The quadratic integral**: `∫ He_{n+2} · x² He_n e^{-x²/2} = ‖He_{n+2}‖²`. -/
theorem gint_hermiteR_square (n : ℕ) :
    gint (hermiteR (n + 2) * (Polynomial.X ^ 2 * hermiteR n))
      = hermiteInner (n + 2) (n + 2) := by
  have hsplit : Polynomial.X ^ 2 * hermiteR n
      = hermiteR (n + 2) + (Polynomial.X ^ 2 * hermiteR n - hermiteR (n + 2)) := by ring
  rw [hsplit, mul_add, gint_add,
    gint_hermiteR_mul_eq_zero (natDegree_X_pow_two_mul_sub_hermiteR n), add_zero, hermiteInner]

/-- Two steps of `hermiteNorm_succ`. -/
theorem hermiteNorm_two (n : ℕ) :
    hermiteNorm (n + 2) = hermiteNorm n * (Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 2)) := by
  have h1 := hermiteNorm_succ n
  have h2 := hermiteNorm_succ (n + 1)
  have e2 : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  rw [show n + 2 = (n + 1) + 1 from rfl, h2, e2, h1]
  ring

/-- **The quadratic norm ratio**: `‖He_{n+2}‖ / ‖He_n‖ = √((n+1)(n+2))`. -/
theorem hermiteNorm_ratio_two (n : ℕ) :
    hermiteNorm (n + 2) / hermiteNorm n = Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  rw [hermiteNorm_two, mul_div_cancel_left₀ _ (ne_of_gt (hermiteNorm_pos n))]
  have h1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [← Real.sqrt_mul h1]

/-! ## The entries -/

/-- **The quartic Hermite entry in the normalized basis**:
`⟨ψ_{n+4}, x⁴ ψ_n⟩ = √((n+1)(n+2)(n+3)(n+4))`. -/
theorem quartic_hermite_entry (n : ℕ) :
    gint (hermiteR (n + 4) * (Polynomial.X ^ 4 * hermiteR n))
        / (hermiteNorm (n + 4) * hermiteNorm n)
      = Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4)) := by
  rw [gint_hermiteR_quartic, hermiteInner_eq, if_pos rfl, ← hermiteNorm_sq (n + 4)]
  have hA := ne_of_gt (hermiteNorm_pos (n + 4))
  have hB := ne_of_gt (hermiteNorm_pos n)
  rw [show hermiteNorm (n + 4) * hermiteNorm (n + 4)
        / (hermiteNorm (n + 4) * hermiteNorm n) = hermiteNorm (n + 4) / hermiteNorm n by
    field_simp]
  exact hermiteNorm_ratio n

/-- **The quadratic Hermite entry in the normalized basis**:
`⟨ψ_{n+2}, x² ψ_n⟩ = √((n+1)(n+2))`. -/
theorem quadratic_hermite_entry (n : ℕ) :
    gint (hermiteR (n + 2) * (Polynomial.X ^ 2 * hermiteR n))
        / (hermiteNorm (n + 2) * hermiteNorm n)
      = Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  rw [gint_hermiteR_square, hermiteInner_eq, if_pos rfl, ← hermiteNorm_sq (n + 2)]
  have hA := ne_of_gt (hermiteNorm_pos (n + 2))
  have hB := ne_of_gt (hermiteNorm_pos n)
  rw [show hermiteNorm (n + 2) * hermiteNorm (n + 2)
        / (hermiteNorm (n + 2) * hermiteNorm n) = hermiteNorm (n + 2) / hermiteNorm n by
    field_simp]
  exact hermiteNorm_ratio_two n

end

end BookProof.HermiteQuartic
