import Mathlib
import BookProof.Toolbox.ChapterHermiteProductBasis

/-!
# The monomial–Hermite vanishing lemma

`BookProof.HermiteProductBasis` computes `⟨ψ_α, ψ_β⟩`: the product Hermite functions are
orthogonal, with norms `∏ᵢ √(αᵢ! √(2π))`.  It says nothing about the inner product of a
*monomial* Gauss function `x^α e^{-‖x‖²/4}` with a product Hermite function `ψ_β`, and in
particular not the fact that makes the `coreBasis`/`hermBasisN` bridge work: **`ψ_β` is
orthogonal to every monomial Gauss function of strictly smaller coordinatewise degree.**

That is what this module supplies.  The one-dimensional input is
`∫ x^m He_n(x) e^{-x²/2} dx = 0` for `m < n`, proved from the integration-by-parts
identity `gint_ibp` of `BookProof.ChapterHermiteFunctions` by a double induction on
`(n, m)`; the `d`-dimensional statement is then Fubini (`integral_prod_coord`) over the
coordinates, exactly as in `inner_pgLp_hermiteMv`.

## Contents

* `gint_X_pow_hermiteR_zero` — `∫ xᵐ Heₙ(x) e^{-x²/2} dx = 0` when `m < n`;
* `integral_pow_mul_gaussH_mul_hermiteFun` — the same integral in the `L²(ℝ)` shape
  `∫ (xᵐ e^{-x²/4}) ψₙ`;
* `inner_monomial_hermiteMv` — `⟨x^α e^{-‖x‖²/4}, ψ_β⟩ = ∏ᵢ ∫ x^{αᵢ} He_{βᵢ} e^{-x²/2}`;
* `inner_monomial_hermiteMv_eq_zero` — the vanishing, hence
  `inner_monomial_hermiteMvLp_eq_zero` for the *normalized* Hermite functions, which is the
  form the Gram–Schmidt argument consumes.

## Honest boundary

Nothing here identifies the Gram–Schmidt vectors of the monomial family with the Hermite
functions; that also needs the monic-triangularity of `He_β` and a count of the monomials of
each degree.  What is proved is the orthogonality input those two steps are missing.
-/

namespace BookProof.HermiteVanishing

open MeasureTheory BookProof.HermiteCore BookProof.HermiteProductCore
  BookProof.HermiteProductBasis

noncomputable section

variable {d : ℕ}

/-! ## The one-dimensional vanishing -/

/-- One step of the recurrence for `∫ xᵐ Heₙ e^{-x²/2}`: integrating `x^{m+1} · ∂(He_{k+1})`
by parts turns it into a boundary-free relation between neighbouring `(m, n)`. -/
theorem gint_X_succ_hermiteR (m k : ℕ) :
    gint (Polynomial.X ^ (m + 2) * hermiteR (k + 1))
      = ((m : ℝ) + 1) * gint (Polynomial.X ^ m * hermiteR (k + 1))
        + ((k : ℝ) + 1) * gint (Polynomial.X ^ (m + 1) * hermiteR k) := by
  have h := gint_ibp (Polynomial.X ^ (m + 1)) (hermiteR (k + 1))
  have hd : Polynomial.derivative (Polynomial.X ^ (m + 1))
      = Polynomial.C ((m : ℝ) + 1) * Polynomial.X ^ m := by
    rw [Polynomial.derivative_X_pow]
    norm_num
  have hL : gint (Polynomial.derivative (Polynomial.X ^ (m + 1)) * hermiteR (k + 1))
      = ((m : ℝ) + 1) * gint (Polynomial.X ^ m * hermiteR (k + 1)) := by
    rw [hd, ← gint_C_mul]
    congr 1
    ring
  have hR : gint (Polynomial.X ^ (m + 1)
        * (Polynomial.X * hermiteR (k + 1) - Polynomial.derivative (hermiteR (k + 1))))
      = gint (Polynomial.X ^ (m + 2) * hermiteR (k + 1))
        - ((k : ℝ) + 1) * gint (Polynomial.X ^ (m + 1) * hermiteR k) := by
    have hsplit : Polynomial.X ^ (m + 1)
          * (Polynomial.X * hermiteR (k + 1) - Polynomial.C ((k : ℝ) + 1) * hermiteR k)
        = Polynomial.X ^ (m + 2) * hermiteR (k + 1)
          - Polynomial.C ((k : ℝ) + 1) * (Polynomial.X ^ (m + 1) * hermiteR k) := by ring
    rw [derivative_hermiteR k, hsplit, gint_sub, gint_C_mul]
  rw [hL, hR] at h
  linarith

/-- One more step, for the exponent `1`: integrating `∂(He_{k+1})` against `1` by parts. -/
theorem gint_X_one_hermiteR (k : ℕ) :
    gint (Polynomial.X ^ 1 * hermiteR (k + 1))
      = ((k : ℝ) + 1) * gint (Polynomial.X ^ 0 * hermiteR k) := by
  have h := gint_ibp (hermiteR (k + 1)) (1 : Polynomial ℝ)
  have hL : gint (Polynomial.derivative (hermiteR (k + 1)) * 1)
      = ((k : ℝ) + 1) * gint (Polynomial.X ^ 0 * hermiteR k) := by
    rw [derivative_hermiteR k, ← gint_C_mul]
    congr 1
    ring
  have hR : gint (hermiteR (k + 1) * (Polynomial.X * 1 - Polynomial.derivative 1))
      = gint (Polynomial.X ^ 1 * hermiteR (k + 1)) := by
    congr 1
    rw [Polynomial.derivative_one, sub_zero, mul_one, pow_one, mul_comm]
  rw [hL, hR] at h
  exact h.symm

/-- **The monomial–Hermite integral vanishes below the degree**:
`∫ xᵐ Heₙ(x) e^{-x²/2} dx = 0` for `m < n`. -/
theorem gint_X_pow_hermiteR_zero : ∀ (n m : ℕ), m < n →
    gint (Polynomial.X ^ m * hermiteR n) = 0 := by
  intro n
  induction n with
  | zero => intro m hm; omega
  | succ n ih =>
    intro m hm
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
      rcases m with _ | _ | m
      · -- exponent `0`
        have h : gint (Polynomial.X ^ 0 * hermiteR (n + 1)) = hermiteInner 0 (n + 1) := by
          rw [hermiteInner, hermiteR_zero]
          simp
        rw [h, hermiteInner_eq]
        simp
      · -- exponent `1`
        rw [gint_X_one_hermiteR n]
        have hn : 0 < n := by omega
        have h0 : gint (Polynomial.X ^ 0 * hermiteR n) = 0 := by
          have h : gint (Polynomial.X ^ 0 * hermiteR n) = hermiteInner 0 n := by
            rw [hermiteInner, hermiteR_zero]
            simp
          rw [h, hermiteInner_eq, if_neg (by omega)]
        rw [h0, mul_zero]
      · -- exponent `m + 2`
        have hmn : m + 1 < n := by omega
        have hm' : m < n + 1 := by omega
        rw [gint_X_succ_hermiteR m n, ihm m (by omega) hm', ih (m + 1) hmn, mul_zero, mul_zero,
          add_zero]

/-! ## The same integral in the `L²(ℝ)` shape -/

/-- `∫ (xᵐ e^{-x²/4}) ψₙ = ∫ xᵐ Heₙ e^{-x²/2}`, the Hermite function carrying the other
half of the Gaussian. -/
theorem integral_pow_mul_gaussH_mul_hermiteFun (m n : ℕ) :
    ∫ t : ℝ, ((t ^ m * gaussH t : ℝ) : ℂ) * ((hermiteFun n t : ℝ) : ℂ)
      = ((gint (Polynomial.X ^ m * hermiteR n) : ℝ) : ℂ) := by
  have hreal : ∫ t : ℝ, (t ^ m * gaussH t * hermiteFun n t : ℝ)
      = gint (Polynomial.X ^ m * hermiteR n) := by
    rw [gint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hermiteFun, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← gaussH_sq]
    ring
  have hL : ∫ t : ℝ, ((t ^ m * gaussH t : ℝ) : ℂ) * ((hermiteFun n t : ℝ) : ℂ)
      = ((∫ t : ℝ, (t ^ m * gaussH t * hermiteFun n t : ℝ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp only [← Complex.ofReal_mul]
  rw [hL, hreal]

/-- The vanishing in the `L²(ℝ)` shape. -/
theorem integral_pow_mul_gaussH_mul_hermiteFun_eq_zero {m n : ℕ} (h : m < n) :
    ∫ t : ℝ, ((t ^ m * gaussH t : ℝ) : ℂ) * ((hermiteFun n t : ℝ) : ℂ) = 0 := by
  rw [integral_pow_mul_gaussH_mul_hermiteFun, gint_X_pow_hermiteR_zero n m h]
  simp

/-! ## The monomial Gauss function as a product of coordinates -/

/-- A monomial Gauss function is the product of the one-dimensional pieces
`xᵢ^{αᵢ} e^{-xᵢ²/4}`. -/
theorem pgFun_monomial_eq_prod (a : Fin d →₀ ℕ) (x : Vd d) :
    pgFun (MvPolynomial.monomial a (1 : ℂ)) x
      = ∏ i, ((x i ^ a i * gaussH (x i) : ℝ) : ℂ) := by
  have hsupp : (∏ i ∈ a.support, ((x i : ℝ) : ℂ) ^ a i) = ∏ i, ((x i : ℝ) : ℂ) ^ a i := by
    refine Finset.prod_subset (Finset.subset_univ a.support) ?_
    intro i _ hi
    rw [Finsupp.notMem_support_iff.mp hi]
    simp
  rw [pgFun, MvPolynomial.eval_monomial, gaussD_eq_prod, Finsupp.prod, Complex.ofReal_prod,
    one_mul, hsupp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul]

/-! ## The multivariate inner product -/

/-- **The inner product of a monomial Gauss function with a product Hermite function is the
product of the one-dimensional integrals.** -/
theorem inner_monomial_hermiteMv (a b : Fin d →₀ ℕ) :
    (inner ℂ (pgLp (MvPolynomial.monomial a (1 : ℂ))) (pgLp (hermiteMv b)) : ℂ)
      = ((∏ i, gint (Polynomial.X ^ (a i) * hermiteR (b i)) : ℝ) : ℂ) := by
  rw [inner_pgLp]
  have key : (∫ x : Vd d, (starRingEnd ℂ) (pgFun (MvPolynomial.monomial a (1 : ℂ)) x)
        * (pgLp (hermiteMv b) : Vd d → ℂ) x)
      = ∫ x : Vd d, ∏ i,
          (((x i ^ a i * gaussH (x i) : ℝ) : ℂ) * ((hermiteFun (b i) (x i) : ℝ) : ℂ)) := by
    refine integral_congr_ae ?_
    filter_upwards [pgLp_coeFn (hermiteMv b)] with x hx
    rw [hx, conj_pgFun_monomial_one, pgFun_monomial_eq_prod, pgFun_hermiteMv,
      Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  rw [key, integral_prod_coord (fun i t => ((t ^ a i * gaussH t : ℝ) : ℂ)
      * ((hermiteFun (b i) t : ℝ) : ℂ)), Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun i _ => integral_pow_mul_gaussH_mul_hermiteFun (a i) (b i)

/-- **The monomial–Hermite vanishing lemma**: a product Hermite function is orthogonal to
every monomial Gauss function whose multi-index is smaller in some coordinate. -/
theorem inner_monomial_hermiteMv_eq_zero (a b : Fin d →₀ ℕ) (h : ∃ i, a i < b i) :
    inner ℂ (pgLp (MvPolynomial.monomial a (1 : ℂ))) (pgLp (hermiteMv b)) = 0 := by
  obtain ⟨i, hi⟩ := h
  have hzero : (∏ i, gint (Polynomial.X ^ (a i) * hermiteR (b i)) : ℝ) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (gint_X_pow_hermiteR_zero _ _ hi)
  have := inner_monomial_hermiteMv (d := d) a b
  rw [hzero] at this
  simpa using this

/-- The vanishing for the **normalized** product Hermite functions, which is the form the
Gram–Schmidt argument uses. -/
theorem inner_monomial_hermiteMvLp_eq_zero (a b : Fin d →₀ ℕ) (h : ∃ i, a i < b i) :
    inner ℂ (pgLp (MvPolynomial.monomial a (1 : ℂ))) (hermiteMvLp b) = 0 := by
  rw [hermiteMvLp, inner_smul_right]
  rw [inner_monomial_hermiteMv_eq_zero a b h, mul_zero]

end

end BookProof.HermiteVanishing
