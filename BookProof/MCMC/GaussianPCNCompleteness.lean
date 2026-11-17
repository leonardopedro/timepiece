import Mathlib
import BookProof.MCMC.GaussianPCNSpectrum
import BookProof.Toolbox.ChapterHermiteFunctions

/-!
# Chapter GaussianPCNCompleteness — the Hermite polynomials are an eigenbasis of `L²(π)`

Plan: `pcnl.md`, packet **T1**.  `GaussianPCNSpectrum` proves that each probabilists' Hermite
polynomial `Heₙ` is an eigenvector of the pCN operator (`P Heₙ = ρⁿ Heₙ`).  Eigenvectors alone do
not determine an operator; this chapter supplies the **completeness** half: the classes of the
`Heₙ` span a dense subspace of `L²(π)`, so they are an eigen**basis** and not merely a family of
eigenvectors.

## The argument

The analytic input is already in the corpus.  `BookProof.HermiteCore` (chapter
`HermiteFunctions`) proves, from scratch, that the Hermite *functions* `ψₙ = Hₙ e^{-x²/4}` are an
orthonormal basis of `L²(ℝ, dx)` and, as its key step, the moment lemma
`ae_eq_zero_of_moments`: a function in `L²(dx)` whose Gaussian moments `∫ xᵏ e^{-x²/4} u` all
vanish is zero almost everywhere.

The transfer to the probabilists' weight: for `π = N(0,1)` and `f ∈ L²(π)`, put
`u = f · e^{-x²/4}`.  Then `u ∈ L²(dx)`, because `|u|² dx = |f|² dπ` up to the constant `√(2π)`.
Orthogonality of `f` to every `Heₙ` reads `∫ u Heₙ e^{-x²/4} = 0`, and since `Heₙ` is monic of
degree `n`, an induction on degree turns that into vanishing of *all* moments
`∫ u xᵏ e^{-x²/4} = 0`.  The moment lemma gives `u = 0`, hence `f = 0`.

## What is proved here

* `gaussianPDFReal_zero_one` — the density of `π`: `gaussianPDFReal 0 1 x = (√(2π))⁻¹ e^{-x²/2}`.
* **`integral_gaussianReal_one_eq`** — **the change of weight**: for any `g` into a real normed
  space, `∫ g ∂π = ∫ x, ((√(2π))⁻¹ e^{-x²/2}) • g x ∂volume`.  No integrability hypothesis: this
  is the raw `withDensity` identity.
* `integrable_gaussW_mul_norm_sq` — `f ∈ L²(π)` implies `|f|² e^{-x²/2} ∈ L¹(dx)`.
* `memLp_gaussH_mul` — the half-weight transfer: `f ∈ L²(π)` implies `f · e^{-x²/4} ∈ L²(dx)`.
* `hermiteReal_eq_hermiteR` — `MehlerEigenvalueReal`'s `hermiteReal` is the corpus' `hermiteR`.
* **`integral_hermiteRealComplex_mul`** — **orthogonality**: `∫ Heₘ Heₙ ∂π = δₘₙ n!`, from
  `HermiteCore.hermiteInner_eq` (`∫ Hₘ Hₙ e^{-x²/2} = δₘₙ n! √(2π)`).
* **`integral_poly_mul_gaussH_eq_zero`** — the degree induction: vanishing against every `Heₙ`
  gives vanishing against every polynomial.
* **`ae_eq_zero_of_forall_integral_hermiteReal`** — **completeness at the function level**: if
  `f ∈ L²(π)` satisfies `∫ f Heₙ ∂π = 0` for every `n`, then `f = 0` a.e.
* **`dense_span_hermiteReal`** — **the eigenbasis statement**: the `ℂ`-span of the classes of
  `Heₙ` is dense in `Lp ℂ 2 π`.

## Honest boundary

* The completeness theorem is density of the span, i.e. the eigenfunctions are complete.  It is
  *not* a statement that the operator is self-adjoint, nor a spectral theorem, nor a statement
  that each eigenvalue `ρⁿ` is simple.  The `Lp` statement is inherited from the function-level
  statement through `Submodule.topologicalClosure_eq_top_iff` and `L2.inner_def`, exactly as the
  corpus proves `hermiteLp_span_dense` for `L²(ℝ, dx)`.
* The analytic input (Hermite-function completeness and the moment lemma) is
  `BookProof.HermiteCore`, not this chapter; this chapter performs the change of weight and the
  polynomial-degree induction.  Neither uses a `sorry` or a new axiom.
* Orthogonality is stated for the *unnormalised* polynomials with the exact constants
  (`∫ Heₙ Heₙ ∂π = n!`); no normalised orthonormal basis is constructed here.
-/

noncomputable section

namespace BookProof.MCMC

open MeasureTheory ProbabilityTheory Filter Polynomial
open scoped ENNReal NNReal Polynomial
open BookProof.HermiteCore

/-! ## 1. The unit Gaussian density and the change of weight -/

/-- **The density of the unit Gaussian**: `gaussianPDFReal 0 1 x = (√(2π))⁻¹ e^{-x²/2}`. -/
theorem gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * gaussW x := by
  rw [gaussianPDFReal_def, gaussW]
  norm_num

/-- **The change of weight `π → volume`.**  For any function into a real normed space,
`∫ g ∂π = ∫ x, ((√(2π))⁻¹ e^{-x²/2}) • g x ∂volume`.  There is no integrability hypothesis:
this is the raw `withDensity` identity, so both sides are junk (`0`) together. -/
theorem integral_gaussianReal_one_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) :
    ∫ x, g x ∂(gaussianReal 0 1)
      = ∫ x, ((Real.sqrt (2 * Real.pi))⁻¹ * gaussW x) • g x := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [gaussianPDFReal_zero_one]

/-- `(√(2π))⁻¹` is invertible, hence nonzero. -/
theorem sqrt_two_pi_inv_ne_zero : (Real.sqrt (2 * Real.pi))⁻¹ ≠ 0 :=
  inv_ne_zero (Real.sqrt_ne_zero'.2 (by positivity))

/-- **`L²(π)` functions have `L¹` square against the Gaussian weight.** -/
theorem integrable_gaussW_mul_norm_sq {f : ℝ → ℂ} (hf : MemLp f 2 (gaussianReal 0 1)) :
    Integrable (fun x : ℝ => gaussW x * ‖f x‖ ^ 2) (volume : Measure ℝ) := by
  have hsq : Integrable (fun x : ℝ => ‖f x‖ ^ 2) (gaussianReal 0 1) :=
    hf.integrable_norm_pow (p := 2) (by norm_num)
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)] at hsq
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hsq
  refine (hsq.congr (Eventually.of_forall fun x => by
    simp only
    rw [toReal_gaussianPDF, gaussianPDFReal_zero_one, smul_eq_mul])).const_mul
    (Real.sqrt (2 * Real.pi)) |>.congr (Eventually.of_forall fun x => ?_)
  simp only
  have h : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  field_simp

/-- **The half-weight transfer**: `f ∈ L²(π)` implies `f · e^{-x²/4} ∈ L²(dx)`. -/
theorem memLp_gaussH_mul {f : ℝ → ℂ} (hf : MemLp f 2 (gaussianReal 0 1)) :
    MemLp (fun x : ℝ => f x * (gaussH x : ℂ)) 2 (volume : Measure ℝ) := by
  have hπ : gaussianReal 0 1 =
      (volume : Measure ℝ).withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)
  have hae : f =ᵐ[(volume : Measure ℝ)] hf.aestronglyMeasurable.mk f := by
    rw [← withDensity_ae_eq (measurable_gaussianPDF 0 1).aemeasurable
      (ae_of_all _ fun x => (gaussianPDF_pos 0 (by norm_num : (1 : ℝ≥0) ≠ 0) x).ne'), ← hπ]
    exact hf.aestronglyMeasurable.ae_eq_mk
  have hfm : AEStronglyMeasurable f (volume : Measure ℝ) :=
    ⟨hf.aestronglyMeasurable.mk f, hf.aestronglyMeasurable.stronglyMeasurable_mk, hae⟩
  have hgH : AEStronglyMeasurable (fun x : ℝ => (gaussH x : ℂ)) (volume : Measure ℝ) :=
    (Complex.continuous_ofReal.comp continuous_gaussH).stronglyMeasurable.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun x : ℝ => f x * (gaussH x : ℂ)) (volume : Measure ℝ) :=
    hfm.mul hgH
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  refine (integrable_gaussW_mul_norm_sq hf).congr (Eventually.of_forall fun x => ?_)
  show gaussW x * ‖f x‖ ^ 2 = ‖f x * (gaussH x : ℂ)‖ ^ 2
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussH_pos x), mul_pow,
    ← gaussH_sq]
  ring

/-! ## 2. Orthogonality in `L²(π)` -/

/-- `MehlerEigenvalueReal`'s `hermiteReal` is the corpus' `hermiteR`: both are
`(Polynomial.hermite n).map (Int.castRingHom ℝ)`. -/
theorem hermiteReal_eq_hermiteR (n : ℕ) : hermiteReal n = hermiteR n := rfl

/-- **Orthogonality of the Hermite polynomials in `L²(π)`**: `∫ Heₘ Heₙ ∂π = δₘₙ n!`.  This is
`HermiteCore.hermiteInner_eq` (`∫ Hₘ Hₙ e^{-x²/2} = δₘₙ n! √(2π)`) after the change of weight. -/
theorem integral_hermiteRealComplex_mul (m n : ℕ) :
    ∫ x, hermiteRealComplex m x * hermiteRealComplex n x ∂(gaussianReal 0 1)
      = if m = n then ((n.factorial : ℝ) : ℂ) else 0 := by
  rw [integral_gaussianReal_one_eq
    (fun x => hermiteRealComplex m x * hermiteRealComplex n x)]
  have hint : Integrable
      (fun x : ℝ => (hermiteR m * hermiteR n).eval x * gaussW x) (volume : Measure ℝ) :=
    integrable_poly_mul_gaussW _
  have hcast : ∫ x : ℝ, (((hermiteR m * hermiteR n).eval x * gaussW x : ℝ) : ℂ)
      = ((hermiteInner m n : ℝ) : ℂ) := by
    rw [show (fun x : ℝ => (((hermiteR m * hermiteR n).eval x * gaussW x : ℝ) : ℂ))
        = fun x => Complex.ofRealCLM ((hermiteR m * hermiteR n).eval x * gaussW x) from rfl,
      Complex.ofRealCLM.integral_comp_comm (φ := fun x : ℝ =>
        (hermiteR m * hermiteR n).eval x * gaussW x) hint]
    rfl
  have hfun : (fun x : ℝ => ((Real.sqrt (2 * Real.pi))⁻¹ * gaussW x) •
        (hermiteRealComplex m x * hermiteRealComplex n x))
      = fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ •
          (((hermiteR m * hermiteR n).eval x * gaussW x : ℝ) : ℂ) := by
    funext x
    rw [Complex.real_smul, Complex.real_smul]
    simp only [hermiteRealComplex_apply, hermiteReal_eq_hermiteR, Polynomial.eval_mul]
    push_cast
    ring
  rw [hfun, integral_smul, Complex.real_smul, hcast, hermiteInner_eq]
  split_ifs with hmn
  · have hne : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (by positivity))
    rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
    field_simp
  · rw [Complex.ofReal_zero, mul_zero]

/-! ## 3. Vanishing against every polynomial -/

/-- A polynomial times the half weight times an `L²(dx)` function is integrable. -/
theorem integrable_poly_mul_gaussH_mul {u : ℝ → ℂ} (hu : MemLp u 2 (volume : Measure ℝ))
    (p : ℝ[X]) :
    Integrable (fun x : ℝ => (((p.eval x * gaussH x : ℝ)) : ℂ) * u x) :=
  integrable_mul_of_memLp_two (memLp_poly_mul_gaussH p) hu

/-- **Vanishing against every `Heₙ` forces vanishing against every polynomial.**  The Hermite
polynomials are monic of degree `n`, so `p` of degree `≤ n+1` splits as `r + c He_{n+1}` with
`r` of degree `≤ n`, and the integral is linear in the polynomial. -/
theorem integral_poly_mul_gaussH_eq_zero {u : ℝ → ℂ} (hu : MemLp u 2 (volume : Measure ℝ))
    (h : ∀ n : ℕ, ∫ x, ((((hermiteR n).eval x * gaussH x : ℝ)) : ℂ) * u x = 0) :
    ∀ (n : ℕ) (p : ℝ[X]), p.natDegree ≤ n →
      ∫ x, ((((p.eval x * gaussH x : ℝ)) : ℂ) * u x) = 0 := by
  intro n
  induction n with
  | zero =>
    intro p hp
    have hpC : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hp
    have hkey : (fun x : ℝ => (((p.eval x * gaussH x : ℝ)) : ℂ) * u x)
        = fun x => ((p.coeff 0 : ℂ) *
            (((((hermiteR 0).eval x * gaussH x : ℝ)) : ℂ) * u x)) := by
      funext x
      rw [hpC]
      simp only [Polynomial.eval_C, Polynomial.coeff_C_zero, hermiteR_zero,
        Polynomial.eval_one]
      push_cast
      ring
    rw [hkey, integral_const_mul, h 0, mul_zero]
  | succ n ih =>
    intro p hp
    set c : ℝ := p.coeff (n + 1) with hc
    set r : ℝ[X] := p - C c * hermiteR (n + 1) with hr
    have hrdeg : r.natDegree ≤ n := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hr, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hN) with hN' | hN'
      · rw [← hN', coeff_hermiteR_self, ← hc]
        ring
      · have h1 : p.coeff N = 0 :=
          Polynomial.natDegree_le_iff_coeff_eq_zero.mp hp N hN'
        have h2 : (hermiteR (n + 1)).coeff N = 0 := coeff_hermiteR_of_lt hN'
        rw [h1, h2]
        ring
    have hsplit : p = r + C c * hermiteR (n + 1) := by
      rw [hr]
      ring
    have hkey : (fun x : ℝ => (((p.eval x * gaussH x : ℝ)) : ℂ) * u x)
        = fun x => (((((r.eval x * gaussH x : ℝ)) : ℂ) * u x)
            + c * (((((hermiteR (n + 1)).eval x * gaussH x : ℝ)) : ℂ) * u x)) := by
      funext x
      rw [hsplit]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      push_cast
      ring
    rw [hkey, integral_add (integrable_poly_mul_gaussH_mul hu r)
      ((integrable_poly_mul_gaussH_mul hu (hermiteR (n + 1))).const_mul c),
      integral_const_mul, h (n + 1), mul_zero, add_zero]
    exact ih r hrdeg

/-- **Vanishing of all moments**, the form consumed by `HermiteCore.ae_eq_zero_of_moments`. -/
theorem integral_pow_mul_gaussH_eq_zero {u : ℝ → ℂ} (hu : MemLp u 2 (volume : Measure ℝ))
    (h : ∀ n : ℕ, ∫ x, ((((hermiteR n).eval x * gaussH x : ℝ)) : ℂ) * u x = 0) (k : ℕ) :
    ∫ x, ((((x ^ k * gaussH x : ℝ)) : ℂ) * u x) = 0 := by
  have hdeg : (X ^ k : ℝ[X]).natDegree ≤ k := by simp
  simpa [Polynomial.eval_pow] using integral_poly_mul_gaussH_eq_zero hu h k (X ^ k) hdeg

/-! ## 4. Completeness of the Hermite family in `L²(π)` -/

/-- **Completeness at the function level**: an `L²(π)` function orthogonal to every Hermite
polynomial is zero almost everywhere.  The proof transfers to `L²(dx)` by the half weight, uses
the degree induction to get all moments, and concludes with `HermiteCore.ae_eq_zero_of_moments`.
-/
theorem ae_eq_zero_of_forall_integral_hermiteReal {f : ℝ → ℂ}
    (hf : MemLp f 2 (gaussianReal 0 1))
    (h : ∀ n : ℕ, ∫ x, f x * hermiteRealComplex n x ∂(gaussianReal 0 1) = 0) :
    f =ᵐ[gaussianReal 0 1] 0 := by
  have hu : MemLp (fun x : ℝ => f x * (gaussH x : ℂ)) 2 (volume : Measure ℝ) :=
    memLp_gaussH_mul hf
  have hhalf : ∀ n : ℕ,
      ∫ x, ((((hermiteR n).eval x * gaussH x : ℝ)) : ℂ) *
        (f x * (gaussH x : ℂ)) = 0 := by
    intro n
    have hg := integral_gaussianReal_one_eq (fun x => f x * hermiteRealComplex n x)
    rw [h n] at hg
    rw [show (fun x : ℝ => ((Real.sqrt (2 * Real.pi))⁻¹ * gaussW x) •
          (f x * hermiteRealComplex n x))
        = fun x => (Real.sqrt (2 * Real.pi))⁻¹ •
            (((((hermiteR n).eval x * gaussH x : ℝ)) : ℂ) * (f x * (gaussH x : ℂ)))
        from funext fun x => by
          rw [Complex.real_smul, Complex.real_smul, hermiteRealComplex_apply,
            hermiteReal_eq_hermiteR, ← gaussH_sq]
          push_cast
          ring] at hg
    have hg' : ∫ x, (Real.sqrt (2 * Real.pi))⁻¹ •
        (((((hermiteR n).eval x * gaussH x : ℝ)) : ℂ) * (f x * (gaussH x : ℂ))) = 0 :=
      hg.symm
    rw [integral_smul, smul_eq_zero] at hg'
    exact hg'.resolve_left sqrt_two_pi_inv_ne_zero
  have hz : (fun x : ℝ => f x * (gaussH x : ℂ)) =ᵐ[(volume : Measure ℝ)] 0 :=
    HermiteCore.ae_eq_zero_of_moments hu (integral_pow_mul_gaussH_eq_zero hu hhalf)
  have hzπ : (fun x : ℝ => f x * (gaussH x : ℂ)) =ᵐ[gaussianReal 0 1] 0 := by
    rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
    exact (withDensity_ae_eq (measurable_gaussianPDF 0 1).aemeasurable
      (ae_of_all _ fun x =>
        (gaussianPDF_pos 0 (by norm_num : (1 : ℝ≥0) ≠ 0) x).ne')).mpr hz
  filter_upwards [hzπ] with x hx
  have hgx : (gaussH x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (gaussH_pos x)
  exact (mul_eq_zero.mp hx).resolve_right hgx

/-- **The Hermite polynomials are an eigenbasis of `L²(π)`**: the `ℂ`-span of the classes of
`Heₙ` is dense in `Lp ℂ 2 π`.

Together with `gaussianPCNop_hermiteReal` (`P [Heₙ] = ρⁿ • [Heₙ]`) this says that the operator is
diagonalised by a complete family of eigenvectors. -/
theorem dense_span_hermiteReal :
    (⊤ : Submodule ℂ (Lp ℂ 2 (gaussianReal 0 1)))
      ≤ (Submodule.span ℂ (Set.range (fun n : ℕ =>
          MemLp.toLp (hermiteRealComplex n) (memLp_two_hermiteReal n)))).topologicalClosure := by
  rw [top_le_iff, Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  have horth : ∀ n : ℕ,
      ∫ x, (f : ℝ → ℂ) x * hermiteRealComplex n x ∂(gaussianReal 0 1) = 0 := by
    intro n
    have hinner : (inner ℂ (MemLp.toLp (hermiteRealComplex n) (memLp_two_hermiteReal n)) f
        : ℂ) = 0 :=
      hf _ (Submodule.subset_span ⟨n, rfl⟩)
    rw [L2.inner_def] at hinner
    rw [← hinner]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_two_hermiteReal n)] with x hx
    rw [hx, RCLike.inner_apply]
    simp only [hermiteRealComplex_apply, Complex.conj_ofReal]
  exact Lp.eq_zero_iff_ae_eq_zero.mpr
    (ae_eq_zero_of_forall_integral_hermiteReal (Lp.memLp f) horth)

end BookProof.MCMC
