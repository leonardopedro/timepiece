import Mathlib
import BookProof.ChapterHermiteFunctions
import BookProof.ChapterHermiteProductCore.Part3

/-!
# The Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`

`PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F asks for the *field-space* realization
of the gauge-fixed Yang–Mills Hamiltonian: the fields must act as genuine
multiplication and differentiation operators on a dense core of `L²(ℝ⁹⁹)`,
rather than abstractly on the occupation-number space `ℓ²(ℕ, ℂ)`.

This module builds that core in an arbitrary finite dimension `d`:

* `gaussD x = e^{-‖x‖²/4}` is the `d`-dimensional Gaussian, and for a polynomial
  `p ∈ ℂ[X₀, …, X_{d-1}]` the function `pgFun p x = p(x) · e^{-‖x‖²/4}` is square
  integrable (`memLp_pgFun`); `pgMap` is the resulting linear map
  `ℂ[X] →ₗ[ℂ] L²(ℝᵈ)`, and it is **injective** (`pgMap_injective`);
* `polyGaussCore = range pgMap` — the polynomials times the Gaussian.  This is
  exactly the span of the *product Hermite functions*
  `ψ_α(x) = ∏ᵢ He_{αᵢ}(xᵢ) e^{-xᵢ²/4}` (`polyGaussCore_eq_hermiteSpan`), i.e. the
  `d`-dimensional Hermite core (the span of the product Hermite polynomials is
  the whole polynomial ring, `span_hermiteMv`);
* the core is **dense** (`polyGaussCore_dense`), proved by the multidimensional
  version of the Fourier/moment argument of `BookProof.ChapterHermiteFunctions`;
* the **Gaussian integration-by-parts identity** (`gaussInt_pderiv`) which makes
  the momentum operators symmetric on the core;
* an orthonormal basis `coreBasis` of `L²(ℝᵈ)` adapted to the core, whose span —
  the *finite-mode domain* of the project's Friedrichs/Hashimoto theorems — is
  exactly the core (`span_range_coreBasis`).

The one-dimensional Hermite machinery of `BookProof.ChapterHermiteFunctions`
(`hermiteR`, `gint`, `gint_ibp`) is reused throughout: the `d`-dimensional
statements are reduced to it by Fubini (`integral_prod_coord`).
-/

namespace BookProof.HermiteProductCore

open MeasureTheory Complex MvPolynomial BookProof.HermiteCore
open scoped FourierTransform
open SchwartzMap

noncomputable section

variable {d : ℕ}
/-! ## The core is the span of the product Hermite functions

The core was defined as *all* polynomials times the Gaussian.  The name "product
Hermite core" is justified here: the products `∏ᵢ He_{αᵢ}(xᵢ)` of probabilists'
Hermite polynomials span the same space, because the three-term recurrence
`X · He_n = He_{n+1} + n · He_{n-1}` makes their span stable under multiplication
by each coordinate. -/

/-- The derivative of the probabilists' Hermite polynomial, over `ℤ`. -/
theorem derivative_hermiteZ (n : ℕ) :
    Polynomial.derivative (Polynomial.hermite (n + 1))
      = Polynomial.C ((n : ℤ) + 1) * Polynomial.hermite n := by
  induction n with
  | zero => simp [Polynomial.hermite_zero]
  | succ n ih =>
    have key : Polynomial.derivative (Polynomial.hermite (n + 1 + 1))
        = Polynomial.hermite (n + 1) + Polynomial.C ((n : ℤ) + 1)
          * (Polynomial.X * Polynomial.hermite n
              - Polynomial.derivative (Polynomial.hermite n)) := by
      rw [Polynomial.hermite_succ (n + 1), Polynomial.derivative_sub,
        Polynomial.derivative_mul, Polynomial.derivative_X, ih, Polynomial.derivative_C_mul]
      ring
    have hC : (Polynomial.C (((n : ℕ) + 1 : ℕ) + 1 : ℤ) : Polynomial ℤ)
        = Polynomial.C ((n : ℤ) + 1) + 1 := by
      push_cast
      rw [show ((n : ℤ) + 1 + 1) = ((n : ℤ) + 1) + 1 from rfl, Polynomial.C_add, Polynomial.C_1]
    rw [key, ← Polynomial.hermite_succ n, hC, add_mul, one_mul, add_comm]

/-- The **three-term recurrence** `X · He_n = He_{n+1} + n · He_{n-1}`, over `ℤ`. -/
theorem hermiteZ_X_mul (n : ℕ) :
    (Polynomial.X : Polynomial ℤ) * Polynomial.hermite n
      = Polynomial.hermite (n + 1) + (n : ℤ) • Polynomial.hermite (n - 1) := by
  cases n with
  | zero => simp [Polynomial.hermite_succ, Polynomial.hermite_zero]
  | succ m =>
    rw [Polynomial.hermite_succ (m + 1), derivative_hermiteZ m]
    simp [Polynomial.smul_eq_C_mul]

/-- The probabilists' Hermite polynomial with complex coefficients. -/
def hermiteCx (n : ℕ) : Polynomial ℂ := (Polynomial.hermite n).map (Int.castRingHom ℂ)

theorem hermiteCx_zero : hermiteCx 0 = 1 := by
  simp [hermiteCx, Polynomial.hermite_zero]

theorem hermiteCx_X_mul (n : ℕ) :
    (Polynomial.X : Polynomial ℂ) * hermiteCx n
      = hermiteCx (n + 1) + (n : ℂ) • hermiteCx (n - 1) := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℂ)) (hermiteZ_X_mul n)
  simpa [hermiteCx, Polynomial.smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_add] using h

/-- The Hermite factor `He_n(x_i)` in the `i`-th coordinate. -/
def hermiteFactor (i : Fin d) (n : ℕ) : MvPolynomial (Fin d) ℂ :=
  Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) (hermiteCx n)

theorem hermiteFactor_zero (i : Fin d) : hermiteFactor i 0 = 1 := by
  simp [hermiteFactor, hermiteCx_zero]

theorem hermiteFactor_X_mul (i : Fin d) (n : ℕ) :
    X i * hermiteFactor i n = hermiteFactor i (n + 1) + (n : ℂ) • hermiteFactor i (n - 1) := by
  have h := congrArg (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ)) (hermiteCx_X_mul n)
  simpa [hermiteFactor, map_add, map_smul] using h

/-- The **product Hermite polynomial** `∏ᵢ He_{αᵢ}(xᵢ)`. -/
def hermiteMv (a : Fin d →₀ ℕ) : MvPolynomial (Fin d) ℂ := ∏ i, hermiteFactor i (a i)

theorem hermiteMv_zero : hermiteMv (0 : Fin d →₀ ℕ) = 1 := by
  simp [hermiteMv, hermiteFactor_zero]

theorem hermiteMv_erase (i : Fin d) (a : Fin d →₀ ℕ) :
    hermiteMv a = hermiteFactor i (a i) * ∏ j ∈ Finset.univ.erase i, hermiteFactor j (a j) := by
  rw [hermiteMv, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]

/-- **The three-term recurrence in `d` variables**: multiplying a product Hermite
polynomial by a coordinate stays inside the family. -/
theorem hermiteMv_X_mul (i : Fin d) (a : Fin d →₀ ℕ) :
    X i * hermiteMv a
      = hermiteMv (a + Finsupp.single i 1) + ((a i : ℂ)) • hermiteMv (a - Finsupp.single i 1) := by
  classical
  have hrest : ∀ b : Fin d →₀ ℕ, (∀ j : Fin d, j ≠ i → b j = a j) →
      ∏ j ∈ Finset.univ.erase i, hermiteFactor j (b j)
        = ∏ j ∈ Finset.univ.erase i, hermiteFactor j (a j) := by
    intro b hb
    exact Finset.prod_congr rfl fun j hj => by rw [hb j (Finset.ne_of_mem_erase hj)]
  have hadd : ∀ j : Fin d, j ≠ i → (a + Finsupp.single i 1 : Fin d →₀ ℕ) j = a j := by
    intro j hj; simp [hj]
  have hsub : ∀ j : Fin d, j ≠ i → (a - Finsupp.single i 1 : Fin d →₀ ℕ) j = a j := by
    intro j hj; simp [Finsupp.tsub_apply, hj]
  have hai : (a + Finsupp.single i 1 : Fin d →₀ ℕ) i = a i + 1 := by simp
  have hsi : (a - Finsupp.single i 1 : Fin d →₀ ℕ) i = a i - 1 := by simp [Finsupp.tsub_apply]
  rw [hermiteMv_erase i a, hermiteMv_erase i (a + Finsupp.single i 1),
    hermiteMv_erase i (a - Finsupp.single i 1), hrest _ hadd, hrest _ hsub, hai, hsi,
    ← mul_assoc, hermiteFactor_X_mul i (a i)]
  rw [add_mul, smul_mul_assoc]

/-- The span of the product Hermite polynomials is stable under multiplication by
each coordinate. -/
theorem mul_X_mem_span_hermiteMv (i : Fin d) {p : MvPolynomial (Fin d) ℂ}
    (hp : p ∈ Submodule.span ℂ (Set.range (hermiteMv (d := d)))) :
    X i * p ∈ Submodule.span ℂ (Set.range (hermiteMv (d := d))) := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [hermiteMv_X_mul]
    exact add_mem (Submodule.subset_span ⟨_, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

/-- **The product Hermite polynomials span all polynomials.** -/
theorem span_hermiteMv :
    Submodule.span ℂ (Set.range (hermiteMv (d := d))) = ⊤ := by
  rw [eq_top_iff]
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : (C a : MvPolynomial (Fin d) ℂ) = a • hermiteMv (0 : Fin d →₀ ℕ) := by
      rw [hermiteMv_zero, MvPolynomial.smul_eq_C_mul, mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp => rw [mul_comm]; exact mul_X_mem_span_hermiteMv i hp

/-- **The Gauss–polynomial core is exactly the span of the product Hermite
functions** `∏ᵢ He_{αᵢ}(xᵢ) · e^{-‖x‖²/4}` — the `d`-dimensional Hermite core. -/
theorem polyGaussCore_eq_hermiteSpan :
    polyGaussCore (d := d)
      = Submodule.span ℂ (Set.range fun a : Fin d →₀ ℕ => pgLp (hermiteMv a)) := by
  have hrange : (Set.range fun a : Fin d →₀ ℕ => pgLp (hermiteMv a))
      = (pgMap (d := d)) '' (Set.range (hermiteMv (d := d))) := by
    rw [← Set.range_comp]
    rfl
  rw [hrange, ← Submodule.map_span, span_hermiteMv, Submodule.map_top, polyGaussCore]

end

end BookProof.HermiteProductCore
