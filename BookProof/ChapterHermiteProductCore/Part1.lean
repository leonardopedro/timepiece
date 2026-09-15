import Mathlib
import BookProof.ChapterHermiteFunctions

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

/-- The field space `ℝᵈ`, a `d`-dimensional Euclidean space. -/
abbrev Vd (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- `L²(ℝᵈ)`. -/
abbrev L2d (d : ℕ) := Lp ℂ 2 (volume : Measure (Vd d))

variable {d : ℕ}

/-! ## Fubini in the coordinates -/

/-- **Fubini in the coordinates of `ℝᵈ`**: the integral of a product of functions
of the separate coordinates is the product of the one-dimensional integrals. -/
theorem integral_prod_coord (f : Fin d → ℝ → ℂ) :
    ∫ x : Vd d, ∏ i, f i (x i) = ∏ i, ∫ t : ℝ, f i t := by
  rw [← ((PiLp.volume_preserving_toLp (Fin d)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
      (fun x : Vd d => ∏ i, f i (x i)))]
  exact MeasureTheory.integral_fintype_prod_eq_prod (fun i => f i)

/-- Each coordinate is dominated by the norm. -/
theorem coord_abs_le_norm (x : Vd d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq]
  have h : |x i| ^ 2 ≤ ∑ j, |x j| ^ 2 :=
    Finset.single_le_sum (f := fun j => |x j| ^ 2) (by intros; positivity) (Finset.mem_univ i)
  calc |x i| = Real.sqrt (|x i| ^ 2) := (Real.sqrt_sq (abs_nonneg _)).symm
    _ ≤ _ := by
        refine Real.sqrt_le_sqrt ?_
        simpa [Real.norm_eq_abs] using h

/-! ## The Gaussian -/

/-- The `d`-dimensional Gaussian `e^{-‖x‖²/4}`, the square root of the Gaussian
weight `e^{-‖x‖²/2}`. -/
def gaussD (x : Vd d) : ℝ := Real.exp (-‖x‖ ^ 2 / 4)

theorem gaussD_pos (x : Vd d) : 0 < gaussD x := Real.exp_pos _

theorem gaussD_ne_zero (x : Vd d) : gaussD x ≠ 0 := ne_of_gt (gaussD_pos x)

theorem continuous_gaussD : Continuous (gaussD (d := d)) := by
  unfold gaussD; fun_prop

/-- The Gaussian `e^{-c‖x‖²}` is integrable on `ℝᵈ` for every `c > 0`. -/
theorem integrable_gauss {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Vd d => Real.exp (-c * ‖x‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Vd d)
    (b := (c : ℂ)) (by simpa using hc) 0 0
  refine h.norm.congr (Filter.Eventually.of_forall fun v => ?_)
  simp [Complex.norm_exp, ← Complex.ofReal_pow]

/-- A polynomial factor is absorbed by a Gaussian: `tᵏ e^{-t²/8}` is bounded. -/
theorem pow_mul_exp_bound (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ k * Real.exp (-t ^ 2 / 8) ≤ 1 + 8 ^ k * (Nat.factorial k) := by
  have hexp_le_one : Real.exp (-t ^ 2 / 8) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_; nlinarith [sq_nonneg t]
  have hexp_pos : 0 < Real.exp (-t ^ 2 / 8) := Real.exp_pos _
  have hfacpos : (0 : ℝ) < 8 ^ k * (Nat.factorial k) := by positivity
  rcases le_or_gt t 1 with h1 | h1
  · have hk : t ^ k ≤ 1 := pow_le_one₀ ht h1
    have : t ^ k * Real.exp (-t ^ 2 / 8) ≤ 1 := mul_le_one₀ hk (le_of_lt hexp_pos) hexp_le_one
    linarith
  · have hkey : (t ^ 2 / 8) ^ k / (Nat.factorial k) ≤ Real.exp (t ^ 2 / 8) :=
      Real.pow_div_factorial_le_exp _ (by positivity) k
    have hfac : (0 : ℝ) < (Nat.factorial k) := by exact_mod_cast Nat.factorial_pos k
    have h2 : (t ^ 2 / 8) ^ k ≤ (Nat.factorial k) * Real.exp (t ^ 2 / 8) := by
      rw [div_le_iff₀ hfac] at hkey; linarith [hkey]
    have hpow : t ^ k ≤ t ^ (2 * k) := by
      refine pow_le_pow_right₀ (le_of_lt h1) ?_; omega
    have hexp_eq : Real.exp (-t ^ 2 / 8) = (Real.exp (t ^ 2 / 8))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    have hE : (0 : ℝ) < Real.exp (t ^ 2 / 8) := Real.exp_pos _
    have h3 : t ^ (2 * k) * Real.exp (-t ^ 2 / 8) ≤ 8 ^ k * (Nat.factorial k) := by
      rw [hexp_eq, mul_inv_le_iff₀ hE, pow_mul]
      have hrw : (t ^ 2) ^ k = 8 ^ k * (t ^ 2 / 8) ^ k := by
        rw [← mul_pow]; ring_nf
      rw [hrw]
      have hmul := mul_le_mul_of_nonneg_left h2 (le_of_lt (pow_pos (by norm_num : (0:ℝ) < 8) k))
      calc (8 : ℝ) ^ k * (t ^ 2 / 8) ^ k ≤ 8 ^ k * ((Nat.factorial k) * Real.exp (t ^ 2 / 8)) :=
            hmul
        _ = 8 ^ k * (Nat.factorial k) * Real.exp (t ^ 2 / 8) := by ring
    nlinarith [mul_le_mul_of_nonneg_right hpow (le_of_lt hexp_pos)]

/-- `‖x‖ᵏ e^{-‖x‖²/4}` is square integrable on `ℝᵈ`. -/
theorem memLp_pow_mul_gaussD (k : ℕ) :
    MemLp (fun x : Vd d => ‖x‖ ^ k * gaussD x) 2 (volume : Measure (Vd d)) := by
  set C : ℝ := 1 + 8 ^ k * (Nat.factorial k) with hC
  have hCpos : 0 ≤ C := by positivity
  have hgmem : MemLp (fun x : Vd d => C * Real.exp (-‖x‖ ^ 2 / 8)) 2 (volume : Measure (Vd d)) := by
    refine (memLp_two_iff_integrable_sq (by fun_prop)).mpr ?_
    have hint : Integrable (fun x : Vd d => Real.exp (-(1/4 : ℝ) * ‖x‖ ^ 2)) :=
      integrable_gauss (by norm_num)
    refine (hint.const_mul (C ^ 2)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
    ring_nf
  refine hgmem.mono (by unfold gaussD; fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  have hb := pow_mul_exp_bound (t := ‖x‖) k (norm_nonneg x)
  have hgauss : gaussD x = Real.exp (-‖x‖ ^ 2 / 8) * Real.exp (-‖x‖ ^ 2 / 8) := by
    rw [← Real.exp_add]; unfold gaussD; ring_nf
  have hpos : (0 : ℝ) < Real.exp (-‖x‖ ^ 2 / 8) := Real.exp_pos _
  have hnn : 0 ≤ ‖x‖ ^ k * gaussD x := by
    have := gaussD_pos x; positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ C * Real.exp (-‖x‖ ^ 2 / 8))]
  calc ‖x‖ ^ k * gaussD x
      = (‖x‖ ^ k * Real.exp (-‖x‖ ^ 2 / 8)) * Real.exp (-‖x‖ ^ 2 / 8) := by
        rw [hgauss]; ring
    _ ≤ C * Real.exp (-‖x‖ ^ 2 / 8) := by
        exact mul_le_mul_of_nonneg_right hb (le_of_lt hpos)

/-! ## Polynomials times the Gaussian -/

/-- `pgFun p x = p(x) · e^{-‖x‖²/4}`: a polynomial in the coordinates of `ℝᵈ`
times the Gaussian. -/
def pgFun (p : MvPolynomial (Fin d) ℂ) (x : Vd d) : ℂ :=
  MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p * (gaussD x : ℂ)

theorem continuous_polyEval (p : MvPolynomial (Fin d) ℂ) :
    Continuous (fun x : Vd d => MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      exact hp.mul (by fun_prop)

theorem continuous_pgFun (p : MvPolynomial (Fin d) ℂ) : Continuous (pgFun p) := by
  unfold pgFun
  exact (continuous_polyEval p).mul (Complex.continuous_ofReal.comp continuous_gaussD)

@[simp] theorem pgFun_zero : pgFun (0 : MvPolynomial (Fin d) ℂ) = 0 := by
  funext x; simp [pgFun]

theorem pgFun_add (p q : MvPolynomial (Fin d) ℂ) : pgFun (p + q) = pgFun p + pgFun q := by
  funext x; simp [pgFun, add_mul]

theorem pgFun_smul (c : ℂ) (p : MvPolynomial (Fin d) ℂ) : pgFun (c • p) = c • pgFun p := by
  funext x; simp [pgFun, smul_eq_mul, mul_assoc]

/-- A monomial times the Gaussian is square integrable. -/
theorem memLp_pgFun_monomial (a : Fin d →₀ ℕ) (c : ℂ) :
    MemLp (pgFun (monomial a c)) 2 (volume : Measure (Vd d)) := by
  set k : ℕ := ∑ b ∈ a.support, a b with hk
  have hmem : MemLp (fun x : Vd d => ‖c‖ * (‖x‖ ^ k * gaussD x)) 2 (volume : Measure (Vd d)) :=
    (memLp_pow_mul_gaussD (d := d) k).const_mul ‖c‖
  refine hmem.mono ((continuous_pgFun (monomial a c)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  have hgauss : (0 : ℝ) < gaussD x := gaussD_pos x
  have hprod : ∏ b ∈ a.support, ‖((x b : ℝ) : ℂ) ^ a b‖ ≤ ‖x‖ ^ k := by
    rw [hk, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => ?_)
    rw [norm_pow]
    have h1 : ‖((x i : ℝ) : ℂ)‖ ≤ ‖x‖ := by simpa using coord_abs_le_norm x i
    exact pow_le_pow_left₀ (norm_nonneg _) h1 _
  have hval : ‖pgFun (monomial a c) x‖
      = ‖c‖ * (∏ b ∈ a.support, ‖((x b : ℝ) : ℂ) ^ a b‖) * gaussD x := by
    rw [pgFun, MvPolynomial.eval_monomial, norm_mul, norm_mul, Finsupp.prod, norm_prod]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgauss]
  have hrhs : ‖‖c‖ * (‖x‖ ^ k * gaussD x)‖ = ‖c‖ * (‖x‖ ^ k * gaussD x) :=
    Real.norm_of_nonneg (by positivity)
  rw [hval, hrhs]
  have hstep := mul_le_mul_of_nonneg_right hprod (le_of_lt hgauss)
  calc ‖c‖ * (∏ b ∈ a.support, ‖((x b : ℝ) : ℂ) ^ a b‖) * gaussD x
      = ‖c‖ * ((∏ b ∈ a.support, ‖((x b : ℝ) : ℂ) ^ a b‖) * gaussD x) := by ring
    _ ≤ ‖c‖ * (‖x‖ ^ k * gaussD x) := mul_le_mul_of_nonneg_left hstep (norm_nonneg c)

/-- **A polynomial times the Gaussian is square integrable.** -/
theorem memLp_pgFun (p : MvPolynomial (Fin d) ℂ) :
    MemLp (pgFun p) 2 (volume : Measure (Vd d)) := by
  have hsum : p = ∑ v ∈ p.support, (monomial v) (MvPolynomial.coeff v p) :=
    (MvPolynomial.support_sum_monomial_coeff p).symm
  have hfun : pgFun p = fun x => ∑ v ∈ p.support, pgFun ((monomial v) (coeff v p)) x := by
    funext x
    rw [pgFun]
    nth_rewrite 1 [hsum]
    simp only [map_sum, Finset.sum_mul, pgFun]
  rw [hfun]
  exact memLp_finset_sum _ fun v _ => memLp_pgFun_monomial v _

/-! ## The core as the range of a linear map -/

/-- `p ↦ [p · e^{-‖x‖²/4}]` as an element of `L²(ℝᵈ)`. -/
def pgLp (p : MvPolynomial (Fin d) ℂ) : L2d d := (memLp_pgFun p).toLp _

theorem pgLp_coeFn (p : MvPolynomial (Fin d) ℂ) :
    (pgLp p : Vd d → ℂ) =ᵐ[volume] pgFun p := (memLp_pgFun p).coeFn_toLp

/-- **The Gauss–polynomial map** `ℂ[X₀, …, X_{d-1}] →ₗ[ℂ] L²(ℝᵈ)`. -/
def pgMap : MvPolynomial (Fin d) ℂ →ₗ[ℂ] L2d d where
  toFun := pgLp
  map_add' p q := by
    have h : pgFun (p + q) = pgFun p + pgFun q := pgFun_add p q
    simp only [pgLp]
    rw [← MemLp.toLp_add (memLp_pgFun p) (memLp_pgFun q)]
    congr 1
  map_smul' c p := by
    have h : pgFun (c • p) = c • pgFun p := pgFun_smul c p
    simp only [pgLp, RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c (memLp_pgFun p)]
    congr 1

@[simp] theorem pgMap_apply (p : MvPolynomial (Fin d) ℂ) : pgMap p = pgLp p := rfl

/-- A multivariate polynomial with complex coefficients vanishing at every *real*
point of `ℝᵈ` is the zero polynomial. -/
theorem mvpoly_eq_zero_of_eval_real : ∀ {n : ℕ} {p : MvPolynomial (Fin n) ℂ},
    (∀ x : Fin n → ℝ, eval (fun i => ((x i : ℝ) : ℂ)) p = 0) → p = 0 := by
  intro n
  induction n with
  | zero =>
      intro p h
      refine MvPolynomial.funext fun x => ?_
      have hx : x = fun i => (((fun _ : Fin 0 => (0 : ℝ)) i : ℝ) : ℂ) := by
        funext i; exact i.elim0
      rw [hx, h, map_zero]
  | succ n ih =>
      intro p h
      set P := (MvPolynomial.finSuccEquiv ℂ n) p with hP
      have hcoeff : ∀ k, P.coeff k = 0 := by
        intro k
        refine ih (p := P.coeff k) fun x => ?_
        have hQ : Polynomial.map (eval (fun i => ((x i : ℝ) : ℂ))) P = 0 := by
          refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
          refine Set.Infinite.mono (s := Set.range ((↑) : ℝ → ℂ)) ?_ ?_
          · rintro _ ⟨y, rfl⟩
            have hy := h (Fin.cons y x)
            have hcons : (fun i : Fin (n + 1) => (((Fin.cons y x : Fin (n + 1) → ℝ) i : ℝ) : ℂ))
                = Fin.cons ((y : ℝ) : ℂ) (fun i => ((x i : ℝ) : ℂ)) := by
              funext i
              refine Fin.cases ?_ ?_ i <;> simp
            rw [hcons, MvPolynomial.eval_eq_eval_mv_eval'] at hy
            simpa [Polynomial.IsRoot, hP] using hy
          · exact Set.infinite_range_of_injective Complex.ofReal_injective
        have hc := congrArg (fun q : Polynomial ℂ => q.coeff k) hQ
        simpa using hc
      have hP0 : P = 0 := Polynomial.ext fun k => by simpa using hcoeff k
      have hfin := congrArg (MvPolynomial.finSuccEquiv ℂ n).symm hP0
      simpa [hP] using hfin

/-- **The Gauss–polynomial map is injective**: distinct polynomials give distinct
elements of `L²(ℝᵈ)`.  Equivalently the monomials times the Gaussian are linearly
independent. -/
theorem pgMap_injective : Function.Injective (pgMap (d := d)) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hae : pgFun p =ᵐ[volume] 0 := by
    have h0 : (pgLp p : Vd d → ℂ) =ᵐ[volume] 0 := by
      have hp0 : pgLp p = 0 := by simpa [pgMap_apply] using hp
      rw [hp0]
      exact Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure (Vd d)))
    exact (pgLp_coeFn p).symm.trans h0
  have hzero : pgFun p = 0 :=
    ((continuous_pgFun p).ae_eq_iff_eq volume continuous_const).mp hae
  refine mvpoly_eq_zero_of_eval_real fun x => ?_
  have hx := congrFun hzero ((WithLp.toLp 2 x : Vd d))
  simp only [pgFun, Pi.zero_apply, mul_eq_zero] at hx
  rcases hx with hx | hx
  · simpa using hx
  · exact absurd (by exact_mod_cast hx) (gaussD_ne_zero _)

/-- **The Gauss–polynomial (product Hermite) core** of `L²(ℝᵈ)`: all polynomials
times the Gaussian `e^{-‖x‖²/4}`. -/
def polyGaussCore : Submodule ℂ (L2d d) := LinearMap.range (pgMap (d := d))

theorem pgLp_mem_core (p : MvPolynomial (Fin d) ℂ) : pgLp p ∈ polyGaussCore (d := d) :=
  ⟨p, rfl⟩

end

end BookProof.HermiteProductCore
