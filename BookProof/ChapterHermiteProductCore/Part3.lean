import Mathlib
import BookProof.ChapterHermiteFunctions
import BookProof.ChapterHermiteProductCore.Part2

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
/-! ## Gaussian moments and integration by parts

The momentum operators are symmetric on the core because of the Gaussian
integration-by-parts identity `∫ (∂ⱼ r) e^{-‖x‖²/2} = ∫ xⱼ r e^{-‖x‖²/2}`, which is
proved here by reducing to the one-dimensional identity `gint_ibp` of
`BookProof.ChapterHermiteFunctions` by Fubini. -/

/-- The Gaussian weight `e^{-‖x‖²/2} = (e^{-‖x‖²/4})²`. -/
def gaussWD (x : Vd d) : ℝ := Real.exp (-‖x‖ ^ 2 / 2)

theorem gaussWD_eq_sq (x : Vd d) : gaussWD x = gaussD x * gaussD x := by
  rw [gaussWD, gaussD, ← Real.exp_add]
  ring_nf

theorem norm_sq_eq_sum (x : Vd d) : ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]

theorem gaussWD_eq_prod (x : Vd d) : gaussWD x = ∏ i, Real.exp (-(x i) ^ 2 / 2) := by
  rw [gaussWD, norm_sq_eq_sum, ← Real.exp_sum]
  congr 1
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `r ↦ ∫ r(x) e^{-‖x‖²/2} dx`, the Gaussian-weighted integral of a polynomial:
the `d`-dimensional analogue of `BookProof.HermiteCore.gint`. -/
def gaussInt (r : MvPolynomial (Fin d) ℂ) : ℂ :=
  ∫ x : Vd d, MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) r * (gaussWD x : ℂ)

theorem gwFun_eq (r : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) r * (gaussWD x : ℂ) = pgFun r x * pgFun 1 x := by
  simp only [pgFun, gaussWD_eq_sq, map_one]
  push_cast
  ring

theorem integrable_gwFun (r : MvPolynomial (Fin d) ℂ) :
    Integrable (fun x : Vd d =>
      MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) r * (gaussWD x : ℂ)) := by
  refine (integrable_mul_of_memLp_two (memLp_pgFun r) (memLp_pgFun 1)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simpa using (gwFun_eq r x).symm

theorem gaussInt_add (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r + s) = gaussInt r + gaussInt s := by
  rw [gaussInt, gaussInt, gaussInt, ← integral_add (integrable_gwFun r) (integrable_gwFun s)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [add_mul]

theorem gaussInt_smul (c : ℂ) (r : MvPolynomial (Fin d) ℂ) :
    gaussInt (c • r) = c * gaussInt r := by
  rw [gaussInt, gaussInt, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_assoc]

theorem gaussInt_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ) :
    gaussInt (∑ v ∈ s, f v) = ∑ v ∈ s, gaussInt (f v) := by
  classical
  induction s using Finset.induction with
  | empty => simp [gaussInt]
  | insert v s hv ih =>
      rw [Finset.sum_insert hv, Finset.sum_insert hv, gaussInt_add, ih]

/-- The one-dimensional Gaussian moments `M k = ∫ tᵏ e^{-t²/2} dt`. -/
def gaussMoment (k : ℕ) : ℝ := gint ((Polynomial.X : Polynomial ℝ) ^ k)

/-- **The moment recurrence** `M_{k+1} = k · M_{k-1}`, one-dimensional integration
by parts against the Gaussian (`BookProof.HermiteCore.gint_ibp`).  For `k = 0` it
reads `M₁ = 0`. -/
theorem gaussMoment_succ (k : ℕ) : gaussMoment (k + 1) = (k : ℝ) * gaussMoment (k - 1) := by
  have h := gint_ibp ((Polynomial.X : Polynomial ℝ) ^ k) 1
  rw [Polynomial.derivative_X_pow, mul_one, Polynomial.derivative_one, sub_zero, mul_one] at h
  rw [gint_C_mul] at h
  rw [gaussMoment, gaussMoment, h, pow_succ]

/-- The Gaussian integral of a monomial factorizes into one-dimensional moments. -/
theorem gaussInt_monomial (a : Fin d →₀ ℕ) :
    gaussInt (monomial a (1 : ℂ)) = ∏ i, ((gaussMoment (a i) : ℝ) : ℂ) := by
  have hpt : ∀ x : Vd d,
      MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (monomial a (1 : ℂ)) * (gaussWD x : ℂ)
        = ∏ i, (((x i) ^ (a i) * Real.exp (-(x i) ^ 2 / 2) : ℝ) : ℂ) := by
    intro x
    rw [MvPolynomial.eval_monomial, one_mul, gaussWD_eq_prod,
      Finsupp.prod_of_support_subset a (Finset.subset_univ _) _ (fun i _ => by simp)]
    push_cast
    rw [← Finset.prod_mul_distrib]
  rw [gaussInt]
  simp_rw [hpt]
  rw [integral_prod_coord (fun i t => (((t ^ (a i) * Real.exp (-t ^ 2 / 2) : ℝ)) : ℂ))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussMoment, gint]
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  norm_cast
  simp [gaussW]

/-- **Gaussian integration by parts in `d` dimensions**:
`∫ (∂ⱼ r) e^{-‖x‖²/2} = ∫ xⱼ r e^{-‖x‖²/2}`. -/
theorem gaussInt_pderiv (j : Fin d) (r : MvPolynomial (Fin d) ℂ) :
    gaussInt (pderiv j r) = gaussInt (X j * r) := by
  classical
  have hmono : ∀ a : Fin d →₀ ℕ,
      gaussInt (pderiv j (monomial a (1 : ℂ))) = gaussInt (X j * monomial a (1 : ℂ)) := by
    intro a
    have hL : pderiv j (monomial a (1 : ℂ))
        = ((a j : ℂ)) • monomial (a - Finsupp.single j 1) 1 := by
      rw [MvPolynomial.pderiv_monomial, one_mul]
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have hR : (X j : MvPolynomial (Fin d) ℂ) * monomial a 1
        = monomial (a + Finsupp.single j 1) 1 := by
      rw [X, monomial_mul]
      simp [add_comm]
    rw [hL, hR, gaussInt_smul, gaussInt_monomial, gaussInt_monomial]
    have hsplit : ∀ b : Fin d →₀ ℕ, ∏ i, ((gaussMoment (b i) : ℝ) : ℂ)
        = ((gaussMoment (b j) : ℝ) : ℂ)
          * ∏ i ∈ Finset.univ.erase j, ((gaussMoment (b i) : ℝ) : ℂ) := by
      intro b
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    have hprod_eq : ∏ i ∈ Finset.univ.erase j,
          ((gaussMoment ((a - Finsupp.single j 1 : Fin d →₀ ℕ) i) : ℝ) : ℂ)
        = ∏ i ∈ Finset.univ.erase j,
          ((gaussMoment ((a + Finsupp.single j 1 : Fin d →₀ ℕ) i) : ℝ) : ℂ) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      have h1 : ((a - Finsupp.single j 1 : Fin d →₀ ℕ) i) = a i := by
        simp [Finsupp.tsub_apply, hij]
      have h2 : ((a + Finsupp.single j 1 : Fin d →₀ ℕ) i) = a i := by
        simp [hij]
      rw [h1, h2]
    rw [hsplit (a - Finsupp.single j 1), hsplit (a + Finsupp.single j 1), hprod_eq]
    have hj1 : ((a - Finsupp.single j 1 : Fin d →₀ ℕ) j) = a j - 1 := by
      simp [Finsupp.tsub_apply]
    have hj2 : ((a + Finsupp.single j 1 : Fin d →₀ ℕ) j) = a j + 1 := by simp
    rw [hj1, hj2, gaussMoment_succ]
    push_cast
    ring
  have hsum : r = ∑ v ∈ r.support, (MvPolynomial.coeff v r) • monomial v (1 : ℂ) := by
    nth_rewrite 1 [← MvPolynomial.support_sum_monomial_coeff r]
    exact Finset.sum_congr rfl fun v _ => by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hsum]
  rw [map_sum, Finset.mul_sum, gaussInt_sum, gaussInt_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Derivation.map_smul, gaussInt_smul, mul_smul_comm, gaussInt_smul, hmono v]

/-! ## An orthonormal basis of `L²(ℝᵈ)` whose finite-mode domain is the core

The abstract Friedrichs/Hashimoto theorems of the project are stated for the
*finite-mode domain* `span (range b)` of a `HilbertBasis ℕ`.  Enumerating the
monomials and orthonormalizing the resulting family of Gauss–polynomials by the
Gram–Schmidt process produces such a basis whose finite-mode domain is exactly
the core `polyGaussCore`. -/

/-- The enumerated monomial family is the monomial basis precomposed with the
enumeration. -/
theorem monomialFamily_eq (e : ℕ ≃ (Fin d →₀ ℕ)) :
    (⇑(MvPolynomial.basisMonomials (Fin d) ℂ) ∘ ⇑e)
      = fun n : ℕ => (monomial (e n) (1 : ℂ)) := rfl

/-- The monomials times the Gaussian, enumerated by `ℕ`. -/
def coreFamily (e : ℕ ≃ (Fin d →₀ ℕ)) : ℕ → L2d d := fun n => pgLp (monomial (e n) 1)

theorem coreFamily_linearIndependent (e : ℕ ≃ (Fin d →₀ ℕ)) :
    LinearIndependent ℂ (coreFamily (d := d) e) := by
  have hmon : LinearIndependent ℂ (fun n : ℕ => (monomial (e n) (1 : ℂ))) := by
    have hb := (MvPolynomial.basisMonomials (Fin d) ℂ).linearIndependent
    have hcomp := hb.comp e e.injective
    rwa [monomialFamily_eq (d := d) e] at hcomp
  exact hmon.map' (pgMap (d := d))
    (LinearMap.ker_eq_bot.mpr (pgMap_injective (d := d)))

theorem span_coreFamily (e : ℕ ≃ (Fin d →₀ ℕ)) :
    Submodule.span ℂ (Set.range (coreFamily (d := d) e)) = polyGaussCore (d := d) := by
  have hrange : Set.range (coreFamily (d := d) e)
      = (pgMap (d := d)) '' (Set.range fun n : ℕ => (monomial (e n) (1 : ℂ))) := by
    rw [← Set.range_comp]
    rfl
  rw [hrange, ← Submodule.map_span]
  have hspan : Submodule.span ℂ (Set.range fun n : ℕ => (monomial (e n) (1 : ℂ)))
      = (⊤ : Submodule ℂ (MvPolynomial (Fin d) ℂ)) := by
    have hb := (MvPolynomial.basisMonomials (Fin d) ℂ).span_eq
    have hrng : Set.range (fun n : ℕ => (monomial (e n) (1 : ℂ)))
        = Set.range (MvPolynomial.basisMonomials (Fin d) ℂ) := by
      rw [← monomialFamily_eq (d := d) e]
      exact e.surjective.range_comp _
    rw [hrng, hb]
  rw [hspan, Submodule.map_top, polyGaussCore]

/-- **An orthonormal basis of `L²(ℝᵈ)` adapted to the core**: the Gram–Schmidt
orthonormalization of the enumerated Gauss–polynomials. -/
def coreBasis (e : ℕ ≃ (Fin d →₀ ℕ)) : HilbertBasis ℕ ℂ (L2d d) :=
  HilbertBasis.mk
    (InnerProductSpace.gramSchmidtNormed_orthonormal (coreFamily_linearIndependent e))
    (by
      have hspan : Submodule.span ℂ
            (Set.range (InnerProductSpace.gramSchmidtNormed ℂ (coreFamily (d := d) e)))
          = polyGaussCore (d := d) := by
        rw [InnerProductSpace.span_gramSchmidtNormed_range,
          InnerProductSpace.span_gramSchmidt, span_coreFamily]
      rw [hspan]
      have hd := polyGaussCore_dense (d := d)
      rw [Submodule.dense_iff_topologicalClosure_eq_top] at hd
      rw [hd])

/-- The span of the basis vectors — the *finite-mode domain* of the abstract
theorems — is exactly the Gauss–polynomial core. -/
theorem span_range_coreBasis (e : ℕ ≃ (Fin d →₀ ℕ)) :
    Submodule.span ℂ (Set.range (coreBasis (d := d) e)) = polyGaussCore (d := d) := by
  rw [coreBasis, HilbertBasis.coe_mk, InnerProductSpace.span_gramSchmidtNormed_range,
    InnerProductSpace.span_gramSchmidt, span_coreFamily]


end

end BookProof.HermiteProductCore
