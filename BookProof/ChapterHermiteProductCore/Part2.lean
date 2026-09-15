import Mathlib
import BookProof.ChapterHermiteFunctions
import BookProof.ChapterHermiteProductCore.Part1

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
/-! ## Density of the core: the multidimensional Fourier/moment argument -/

/-- `x ↦ e^{c‖x‖} e^{-‖x‖²/4}` is square integrable: the Gaussian beats every
exponential, in every dimension. -/
theorem memLp_two_exp_norm_mul_gaussD (c : ℝ) :
    MemLp (fun x : Vd d => ((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ)) 2
      (volume : Measure (Vd d)) := by
  have hcont : Continuous fun x : Vd d => ((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ) := by
    refine Complex.continuous_ofReal.comp ?_
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_norm)).mul continuous_gaussD
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  have hdom :
      Integrable (fun x : Vd d => Real.exp (4 * c ^ 2) * Real.exp (-(1/4 : ℝ) * ‖x‖ ^ 2)) :=
    (integrable_gauss (by norm_num)).const_mul _
  refine hdom.mono' (hcont.norm.pow 2).aestronglyMeasurable ?_
  filter_upwards with x
  have hsq : ‖((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ)‖ ^ 2
      = Real.exp (2 * c * ‖x‖ - ‖x‖ ^ 2 / 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_pos (Real.exp_pos _) (gaussD_pos x)).le]
    rw [gaussD, mul_pow, pow_two (Real.exp _), pow_two (Real.exp _), ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add]
    ring_nf
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hsq]
  have hb : 2 * c * ‖x‖ - ‖x‖ ^ 2 / 2 ≤ 4 * c ^ 2 + -(1/4 : ℝ) * ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ / 2 - 2 * c), norm_nonneg x]
  calc Real.exp (2 * c * ‖x‖ - ‖x‖ ^ 2 / 2)
      ≤ Real.exp (4 * c ^ 2 + -(1/4 : ℝ) * ‖x‖ ^ 2) := Real.exp_le_exp.mpr hb
    _ = Real.exp (4 * c ^ 2) * Real.exp (-(1/4 : ℝ) * ‖x‖ ^ 2) := Real.exp_add _ _

/-- The product of two square-integrable functions is integrable. -/
theorem integrable_mul_of_memLp_two {f g : Vd d → ℂ} (hf : MemLp f 2 (volume : Measure (Vd d)))
    (hg : MemLp g 2 (volume : Measure (Vd d))) : Integrable (fun x : Vd d => f x * g x) := by
  simpa [Pi.mul_def] using hf.integrable_mul hg

/-- The linear polynomial `x ↦ ⟪ x, w ⟫`. -/
def innerPoly (w : Vd d) : MvPolynomial (Fin d) ℂ := ∑ i, C ((w i : ℝ) : ℂ) * X i

theorem eval_innerPoly (w x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (innerPoly w) = ((inner ℝ x w : ℝ) : ℂ) := by
  rw [innerPoly, map_sum]
  push_cast [PiLp.inner_apply, RCLike.inner_apply]
  simp [mul_comm]

theorem pgFun_innerPoly_pow (w x : Vd d) (k : ℕ) :
    pgFun ((innerPoly w) ^ k) x = ((inner ℝ x w : ℝ) : ℂ) ^ k * (gaussD x : ℂ) := by
  rw [pgFun, map_pow, eval_innerPoly]

/-- **The multidimensional Fourier/moment lemma.**  If `u ∈ L²(ℝᵈ)` is orthogonal
to every polynomial times the Gaussian, then the Fourier transform of the `L¹`
function `e^{-‖x‖²/4} u` vanishes identically. -/
theorem fourier_gaussD_mul_eq_zero {u : Vd d → ℂ} (hu : MemLp u 2 (volume : Measure (Vd d)))
    (hmom : ∀ p : MvPolynomial (Fin d) ℂ, ∫ x : Vd d, pgFun p x * u x = 0) (w : Vd d) :
    𝓕 (fun x : Vd d => ((gaussD x : ℝ) : ℂ) * u x) w = 0 := by
  set F : ℕ → Vd d → ℂ := fun N x =>
    (∑ k ∈ Finset.range N,
        (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ))
      * (((gaussD x : ℝ) : ℂ) * u x) with hF
  have hterm : ∀ p : MvPolynomial (Fin d) ℂ, Integrable (fun x : Vd d => pgFun p x * u x) :=
    fun p => integrable_mul_of_memLp_two (memLp_pgFun p) hu
  have hFint : ∀ N, ∫ x : Vd d, F N x = 0 := by
    intro N
    have hpt : ∀ x : Vd d, F N x = ∑ k ∈ Finset.range N,
        ((Complex.I * ((-2 * Real.pi : ℝ) : ℂ)) ^ k / (k.factorial : ℂ))
          * (pgFun ((innerPoly w) ^ k) x * u x) := by
      intro x
      simp only [hF, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pgFun_innerPoly_pow]
      push_cast
      ring
    simp_rw [hpt]
    rw [integral_finset_sum _ (fun k _ => (hterm _).const_mul _)]
    simp [integral_const_mul, hmom]
  set c : ℝ := 2 * Real.pi * ‖w‖ with hc
  have hcnn : 0 ≤ c := by positivity
  have hbdd : Integrable (fun x : Vd d => ((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ) * u x) :=
    integrable_mul_of_memLp_two (memLp_two_exp_norm_mul_gaussD c) hu
  have hmeas : ∀ N, AEStronglyMeasurable (F N) (volume : Measure (Vd d)) := by
    intro N
    refine AEStronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_) ?_
    · refine continuous_finset_sum _ fun k _ => ?_
      refine Continuous.div_const ?_ _
      exact (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_const.mul (by fun_prop)))).pow k
    · exact ((Complex.continuous_ofReal.comp continuous_gaussD).aestronglyMeasurable).mul hu.1
  have hdom : ∀ N, ∀ᵐ x : Vd d, ‖F N x‖
      ≤ ‖((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ) * u x‖ := by
    intro N
    filter_upwards with x
    have hinner : |(inner ℝ x w : ℝ)| ≤ ‖x‖ * ‖w‖ := abs_real_inner_le_norm x w
    have hsum : ‖∑ k ∈ Finset.range N,
        (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)‖
        ≤ Real.exp (c * ‖x‖) := by
      have hstep : ∀ k ∈ Finset.range N,
          ‖(Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)‖
            ≤ (c * ‖x‖) ^ k / (k.factorial : ℝ) := by
        intro k _
        rw [norm_div, norm_pow]
        have hnum : ‖Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)‖ ≤ c * ‖x‖ := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
            hc]
          have h2pi : |(-2 * Real.pi : ℝ)| = 2 * Real.pi := by
            rw [abs_of_nonpos (by nlinarith [Real.pi_pos] : (-2 * Real.pi : ℝ) ≤ 0)]; ring
          rw [h2pi]
          calc 2 * Real.pi * |(inner ℝ x w : ℝ)| ≤ 2 * Real.pi * (‖x‖ * ‖w‖) := by
                exact mul_le_mul_of_nonneg_left hinner (by positivity)
            _ = 2 * Real.pi * ‖w‖ * ‖x‖ := by ring
        have hden : ‖(k.factorial : ℂ)‖ = (k.factorial : ℝ) := by
          simp
        rw [hden]
        gcongr
      calc ‖∑ k ∈ Finset.range N,
            (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)‖
          ≤ ∑ k ∈ Finset.range N,
              ‖(Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k
                / (k.factorial : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range N, (c * ‖x‖) ^ k / (k.factorial : ℝ) :=
            Finset.sum_le_sum hstep
        _ ≤ Real.exp (c * ‖x‖) := Real.sum_le_exp_of_nonneg (by positivity) N
    simp only [hF, norm_mul]
    have h1 : ‖((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ)‖ = Real.exp (c * ‖x‖) * gaussD x := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_pos (Real.exp_pos _) (gaussD_pos x)).le]
    have h2 : ‖((gaussD x : ℝ) : ℂ)‖ = gaussD x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussD_pos x)]
    rw [h1, h2]
    have hg : (0 : ℝ) ≤ gaussD x * ‖u x‖ := mul_nonneg (gaussD_pos x).le (norm_nonneg _)
    calc ‖∑ k ∈ Finset.range N,
          (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)‖
            * (gaussD x * ‖u x‖)
        ≤ Real.exp (c * ‖x‖) * (gaussD x * ‖u x‖) := mul_le_mul_of_nonneg_right hsum hg
      _ = Real.exp (c * ‖x‖) * gaussD x * ‖u x‖ := by ring
  have hlim : ∀ᵐ x : Vd d, Filter.Tendsto (fun N => F N x) Filter.atTop
      (nhds (Complex.exp (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ))
        * (((gaussD x : ℝ) : ℂ) * u x))) := by
    filter_upwards with x
    have hsum := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ)
      (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)))
    have hsum' : HasSum (fun k : ℕ =>
        (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ))
        (Complex.exp (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ))) := by
      simpa [Complex.exp_eq_exp_ℂ] using hsum
    exact hsum'.tendsto_sum_nat.mul_const _
  have hconv := MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x : Vd d => ‖((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ) * u x‖)
    hmeas hbdd.norm hdom hlim
  have hval : ∫ x : Vd d, Complex.exp (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ))
      * (((gaussD x : ℝ) : ℂ) * u x) = 0 := by
    have hc0 : Filter.Tendsto (fun _ : ℕ => (0 : ℂ)) Filter.atTop
        (nhds (∫ x : Vd d, Complex.exp (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ))
          * (((gaussD x : ℝ) : ℂ) * u x))) := by
      simpa [hFint] using hconv
    exact tendsto_nhds_unique hc0 tendsto_const_nhds
  rw [Real.fourier_eq', ← hval]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  congr 2
  push_cast
  ring

/-- **Fourier uniqueness on `ℝᵈ`** (the multiplication formula). -/
theorem integral_fourier_mul_comm {f g : Vd d → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ xi : Vd d, 𝓕 f xi * g xi = ∫ x : Vd d, f x * 𝓕 g x := by
  have hflip : ((innerₗ (Vd d)) : Vd d →ₗ[ℝ] Vd d →ₗ[ℝ] ℝ).flip = innerₗ (Vd d) := by
    refine LinearMap.ext fun x : Vd d => LinearMap.ext fun y : Vd d => ?_
    simp [real_inner_comm y x]
  have hcont : Continuous fun p : Vd d × Vd d => (innerₗ (Vd d)) p.1 p.2 := by
    simpa using (continuous_inner (𝕜 := ℝ) (E := Vd d))
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (V := Vd d) (W := Vd d) (E := ℂ) (F := ℂ) (G := ℂ) (μ := volume) (ν := volume)
    (L := innerₗ (Vd d)) (e := Real.fourierChar) (f := f) (g := g)
    (ContinuousLinearMap.mul ℂ ℂ) Real.continuous_fourierChar hcont hf hg
  simpa [hflip, ContinuousLinearMap.mul_apply'] using h

/-- An integrable function on `ℝᵈ` whose Fourier transform vanishes identically is
zero almost everywhere. -/
theorem ae_eq_zero_of_fourier_eq_zero {v : Vd d → ℂ} (hv : Integrable v)
    (h : ∀ w : Vd d, 𝓕 v w = 0) : ∀ᵐ x : Vd d, v x = 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hv.locallyIntegrable ?_
  intro g hg hgsupp
  set psi : 𝓢(Vd d, ℂ) := HasCompactSupport.toSchwartzMap
    (f := fun x : Vd d => ((g x : ℝ) : ℂ))
    (by exact hgsupp.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp))
    (Complex.ofRealCLM.contDiff.comp hg) with hpsi
  set phi : 𝓢(Vd d, ℂ) := 𝓕⁻ psi with hphi
  have hfourier : 𝓕 (phi : Vd d → ℂ) = (psi : Vd d → ℂ) := by
    rw [← SchwartzMap.fourier_coe, hphi]
    simp
  have hkey := integral_fourier_mul_comm hv (phi : 𝓢(Vd d, ℂ)).integrable
  rw [hfourier] at hkey
  have hzero : ∫ xi : Vd d, 𝓕 v xi * (phi : Vd d → ℂ) xi = 0 := by simp [h]
  rw [hzero] at hkey
  have hrw : ∫ x : Vd d, g x • v x = ∫ x : Vd d, v x * (psi : Vd d → ℂ) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [hpsi, Complex.real_smul]
    ring
  rw [hrw, ← hkey]

/-- **Vanishing of all Gaussian moments forces `u = 0`** on `ℝᵈ`. -/
theorem ae_eq_zero_of_moments {u : Vd d → ℂ} (hu : MemLp u 2 (volume : Measure (Vd d)))
    (hmom : ∀ p : MvPolynomial (Fin d) ℂ, ∫ x : Vd d, pgFun p x * u x = 0) :
    ∀ᵐ x : Vd d, u x = 0 := by
  have hg : MemLp (fun x : Vd d => ((gaussD x : ℝ) : ℂ)) 2 (volume : Measure (Vd d)) := by
    have h1 : pgFun (1 : MvPolynomial (Fin d) ℂ) = fun x : Vd d => ((gaussD x : ℝ) : ℂ) := by
      funext x; simp [pgFun]
    rw [← h1]
    exact memLp_pgFun 1
  have hv : Integrable (fun x : Vd d => ((gaussD x : ℝ) : ℂ) * u x) :=
    integrable_mul_of_memLp_two hg hu
  have hzero := ae_eq_zero_of_fourier_eq_zero hv (fun w => fourier_gaussD_mul_eq_zero hu hmom w)
  filter_upwards [hzero] with x hx
  have hne : ((gaussD x : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (gaussD_pos x)
  exact (mul_eq_zero.mp hx).resolve_left hne

/-! ## The core is dense -/

theorem inner_pgLp (p : MvPolynomial (Fin d) ℂ) (u : L2d d) :
    (inner ℂ (pgLp p) u : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) (pgFun p x) * (u : Vd d → ℂ) x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [pgLp_coeFn p] with x hx
  rw [hx, RCLike.inner_apply, mul_comm]

/-- A monomial with coefficient `1` is real valued on `ℝᵈ`. -/
theorem conj_pgFun_monomial_one (a : Fin d →₀ ℕ) (x : Vd d) :
    (starRingEnd ℂ) (pgFun (monomial a (1 : ℂ)) x) = pgFun (monomial a 1) x := by
  rw [pgFun, MvPolynomial.eval_monomial]
  simp [Finsupp.prod, map_prod, Complex.conj_ofReal]

/-- **The Gauss–polynomial core is dense in `L²(ℝᵈ)`.**  This is the
`d`-dimensional completeness of the Hermite functions. -/
theorem polyGaussCore_dense : Dense ((polyGaussCore : Submodule ℂ (L2d d)) : Set (L2d d)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro u hu
  have hmon : ∀ a : Fin d →₀ ℕ,
      ∫ x : Vd d, pgFun (monomial a (1 : ℂ)) x * (u : Vd d → ℂ) x = 0 := by
    intro a
    have h0 : (inner ℂ (pgLp (monomial a (1 : ℂ))) u : ℂ) = 0 :=
      hu _ (pgLp_mem_core _)
    rw [inner_pgLp] at h0
    rw [← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [conj_pgFun_monomial_one]
  have hmom : ∀ p : MvPolynomial (Fin d) ℂ,
      ∫ x : Vd d, pgFun p x * (u : Vd d → ℂ) x = 0 := by
    intro p
    have hu2 : MemLp (u : Vd d → ℂ) 2 (volume : Measure (Vd d)) := Lp.memLp u
    have hsum : p = ∑ v ∈ p.support, (monomial v) (MvPolynomial.coeff v p) :=
      (MvPolynomial.support_sum_monomial_coeff p).symm
    have hpt : ∀ x : Vd d, pgFun p x * (u : Vd d → ℂ) x
        = ∑ v ∈ p.support, MvPolynomial.coeff v p *
            (pgFun (monomial v (1 : ℂ)) x * (u : Vd d → ℂ) x) := by
      intro x
      rw [pgFun]
      nth_rewrite 1 [hsum]
      rw [map_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [pgFun, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
      ring
    simp_rw [hpt]
    rw [integral_finset_sum _ (fun v _ =>
      ((integrable_mul_of_memLp_two (memLp_pgFun (monomial v (1 : ℂ))) hu2)).const_mul _)]
    simp [integral_const_mul, hmon]
  have hzero := ae_eq_zero_of_moments (Lp.memLp u) hmom
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hzero

end

end BookProof.HermiteProductCore
