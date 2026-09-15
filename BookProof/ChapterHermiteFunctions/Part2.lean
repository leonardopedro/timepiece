import Mathlib
import BookProof.ChapterHermiteFunctions.Part1

/-!
# The Hermite functions: orthonormality, completeness, and the Hermite core of `L²(ℝ)`

This chapter supplies the concrete object that the abstract Galerkin/Friedrichs
chapter (`BookProof/ChapterHermiteGalerkinFriedrichs.lean`) and the quantum
gravity chapter (`BookProof/ChapterQuantumGravityDensitized.lean`) so far only
used *abstractly*: a genuine **Hilbert basis of Hermite functions** of `L²(ℝ)`,
and hence a genuine **Hermite core** — the space of finite linear combinations of
Hermite functions, i.e. "polynomials times the Gaussian".

The convention is the probabilists' one: `H_{n+1} = X H_n − H_n'`
(`Polynomial.hermite` of Mathlib), and the Hermite *functions* are

  `ψ_n(x) = H_n(x) e^{-x²/4}`,   `∫ ψ_m ψ_n = δ_{mn} n! √(2π)`.

Contents:

* `hermiteR`, `derivative_hermiteR`, `hermiteR_ode` — the polynomials, the
  derivative rule `H_{n+1}' = (n+1) H_n` and the Hermite differential equation;
* `gint_ibp` — integration by parts against the Gaussian weight on all of `ℝ`;
* `hermiteInner_eq` — the orthogonality relations
  `∫ H_m H_n e^{-x²/2} = δ_{mn} n! √(2π)`;
* `orthonormal_hermiteLp` — the normalized Hermite functions are orthonormal in
  `L²(ℝ, ℂ)`;
* `hermiteLp_span_dense`, `hermiteBasis` — completeness: they form a Hilbert
  basis (proved from scratch: orthogonality to all `xⁿ e^{-x²/4}` forces the
  Fourier transform of `e^{-x²/4} u` to vanish identically);
* `hermiteFun_oscillator` — each Hermite function is an eigenfunction of the
  harmonic oscillator `-d²/dx² + x²/4` with eigenvalue `n + 1/2`.
-/

namespace BookProof.HermiteCore

open MeasureTheory Polynomial Filter Topology FourierTransform SchwartzMap

noncomputable section
/-! ## Completeness

The completeness proof is elementary but not short.  If `u ∈ L²(ℝ)` is
orthogonal to every Hermite function then it is orthogonal to every `xᵏ e^{-x²/4}`
(the Hermite polynomials are monic of every degree), hence — expanding the
character `e^{-2πiwx}` in its power series and integrating term by term, which
dominated convergence allows because `e^{c|x|}e^{-x²/4}` is still square
integrable — the Fourier transform of the `L¹` function `e^{-x²/4} u` vanishes
identically, so `u = 0`. -/

/-- `x ↦ e^{c|x|} e^{-x²/4}` is square integrable: the Gaussian beats every
exponential. -/
theorem memLp_two_exp_abs_mul_gaussH (c : ℝ) :
    MemLp (fun x : ℝ => ((Real.exp (c * |x|) * gaussH x : ℝ) : ℂ)) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => ((Real.exp (c * |x|) * gaussH x : ℝ) : ℂ))
      (volume : Measure ℝ) := by
    refine Continuous.aestronglyMeasurable (Complex.continuous_ofReal.comp ?_)
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul continuous_gaussH
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hdom : Integrable (fun x : ℝ => Real.exp (4 * c ^ 2) * Real.exp (-(1/4 : ℝ) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num)).const_mul _
  have hcont : Continuous fun x : ℝ => ‖((Real.exp (c * |x|) * gaussH x : ℝ) : ℂ)‖ ^ 2 :=
    ((Complex.continuous_ofReal.comp ((Real.continuous_exp.comp
      (continuous_const.mul continuous_abs)).mul continuous_gaussH)).norm.pow 2)
  refine hdom.mono' hcont.aestronglyMeasurable ?_
  filter_upwards with x
  have hsq : ‖((Real.exp (c * |x|) * gaussH x : ℝ) : ℂ)‖ ^ 2
      = Real.exp (2 * c * |x| - x ^ 2 / 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_pos (Real.exp_pos _) (gaussH_pos x)).le]
    rw [gaussH, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hsq]
  have hb : 2 * c * |x| - x ^ 2 / 2 ≤ 4 * c ^ 2 + -(1/4 : ℝ) * x ^ 2 := by
    nlinarith [sq_nonneg (|x| / 2 - 2 * c), sq_abs x, abs_nonneg x]
  calc Real.exp (2 * c * |x| - x ^ 2 / 2)
      ≤ Real.exp (4 * c ^ 2 + -(1/4 : ℝ) * x ^ 2) := Real.exp_le_exp.mpr hb
    _ = Real.exp (4 * c ^ 2) * Real.exp (-(1/4 : ℝ) * x ^ 2) := Real.exp_add _ _

/-- The product of two square-integrable functions is integrable. -/
theorem integrable_mul_of_memLp_two {f g : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ)) : Integrable (fun x : ℝ => f x * g x) := by
  simpa [Pi.mul_def] using hf.integrable_mul hg

/-- The multiplication formula for the Fourier transform on `ℝ`:
`∫ (𝓕 f) g = ∫ f (𝓕 g)`. -/
theorem integral_fourier_mul_comm {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ xi : ℝ, 𝓕 f xi * g xi = ∫ x : ℝ, f x * 𝓕 g x := by
  have hflip : ((innerₗ ℝ) : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by ext; simp
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (V := ℝ) (W := ℝ) (E := ℂ) (F := ℂ) (G := ℂ) (μ := volume) (ν := volume)
    (L := innerₗ ℝ) (e := Real.fourierChar) (f := f) (g := g)
    (ContinuousLinearMap.mul ℂ ℂ) Real.continuous_fourierChar (by fun_prop) hf hg
  simpa [hflip, ContinuousLinearMap.mul_apply'] using h

/-- **Fourier uniqueness**: an integrable function whose Fourier transform
vanishes identically is zero almost everywhere. -/
theorem ae_eq_zero_of_fourier_eq_zero {v : ℝ → ℂ} (hv : Integrable v)
    (h : ∀ w : ℝ, 𝓕 v w = 0) : ∀ᵐ x : ℝ, v x = 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hv.locallyIntegrable ?_
  intro g hg hgsupp
  set psi : 𝓢(ℝ, ℂ) := HasCompactSupport.toSchwartzMap
    (f := fun x : ℝ => ((g x : ℝ) : ℂ))
    (by exact hgsupp.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp))
    (Complex.ofRealCLM.contDiff.comp hg) with hpsi
  set phi : 𝓢(ℝ, ℂ) := 𝓕⁻ psi with hphi
  have hfourier : 𝓕 (phi : ℝ → ℂ) = (psi : ℝ → ℂ) := by
    rw [← SchwartzMap.fourier_coe, hphi]
    simp
  have hkey := integral_fourier_mul_comm hv (phi : 𝓢(ℝ, ℂ)).integrable
  rw [hfourier] at hkey
  have hzero : ∫ xi : ℝ, 𝓕 v xi * (phi : ℝ → ℂ) xi = 0 := by simp [h]
  rw [hzero] at hkey
  have hrw : ∫ x : ℝ, g x • v x = ∫ x : ℝ, v x * (psi : ℝ → ℂ) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [hpsi, Complex.real_smul]
    ring
  rw [hrw, ← hkey]

/-- The exponential series for `Complex.exp`. -/
theorem complex_exp_hasSum (z : ℂ) :
    HasSum (fun k : ℕ => z ^ k / (k.factorial : ℂ)) (Complex.exp z) := by
  simpa [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) z

/-- If `u ∈ L²` is orthogonal to every `xᵏ e^{-x²/4}`, then the Fourier transform
of the `L¹` function `e^{-x²/4} u` vanishes identically. -/
theorem fourier_gaussH_mul_eq_zero {u : ℝ → ℂ} (hu : MemLp u 2 (volume : Measure ℝ))
    (hmom : ∀ k : ℕ, ∫ x : ℝ, ((x ^ k * gaussH x : ℝ) : ℂ) * u x = 0) (w : ℝ) :
    𝓕 (fun x : ℝ => ((gaussH x : ℝ) : ℂ) * u x) w = 0 := by
  set a : ℝ := -2 * Real.pi * w with ha
  have hmono : ∀ k : ℕ,
      MemLp (fun x : ℝ => ((x ^ k * gaussH x : ℝ) : ℂ)) 2 (volume : Measure ℝ) := by
    intro k
    simpa using memLp_poly_mul_gaussH ((X : Polynomial ℝ) ^ k)
  have hterm : ∀ k : ℕ, Integrable (fun x : ℝ => ((x ^ k * gaussH x : ℝ) : ℂ) * u x) :=
    fun k => integrable_mul_of_memLp_two (hmono k) hu
  set F : ℕ → ℝ → ℂ := fun N x =>
    (∑ k ∈ Finset.range N, (Complex.I * (a : ℂ) * (x : ℂ)) ^ k / (k.factorial : ℂ))
      * (((gaussH x : ℝ) : ℂ) * u x) with hF
  have hFint : ∀ N, ∫ x : ℝ, F N x = 0 := by
    intro N
    have hpt : ∀ x : ℝ, F N x = ∑ k ∈ Finset.range N,
        ((Complex.I * (a : ℂ)) ^ k / (k.factorial : ℂ))
          * (((x ^ k * gaussH x : ℝ) : ℂ) * u x) := by
      intro x
      simp only [hF, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    simp_rw [hpt]
    rw [integral_finset_sum _ (fun k _ => (hterm k).const_mul _)]
    have hmom' : ∀ k : ℕ, ∫ x : ℝ, (x : ℂ) ^ k * ((gaussH x : ℝ) : ℂ) * u x = 0 := by
      intro k
      have h := hmom k
      push_cast at h
      simpa [mul_assoc] using h
    simp [integral_const_mul, hmom']
  have hbdd : Integrable (fun x : ℝ => ((Real.exp (|a| * |x|) * gaussH x : ℝ) : ℂ) * u x) :=
    integrable_mul_of_memLp_two (memLp_two_exp_abs_mul_gaussH |a|) hu
  have hmeas : ∀ N, AEStronglyMeasurable (F N) (volume : Measure ℝ) := by
    intro N
    refine AEStronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    exact ((Complex.continuous_ofReal.comp continuous_gaussH).aestronglyMeasurable).mul hu.1
  have hdom : ∀ N, ∀ᵐ x : ℝ, ‖F N x‖
      ≤ ‖((Real.exp (|a| * |x|) * gaussH x : ℝ) : ℂ) * u x‖ := by
    intro N
    filter_upwards with x
    have hsum : ‖∑ k ∈ Finset.range N, (Complex.I * (a : ℂ) * (x : ℂ)) ^ k / (k.factorial : ℂ)‖
        ≤ Real.exp (|a| * |x|) := by
      calc ‖∑ k ∈ Finset.range N, (Complex.I * (a : ℂ) * (x : ℂ)) ^ k / (k.factorial : ℂ)‖
          ≤ ∑ k ∈ Finset.range N, ‖(Complex.I * (a : ℂ) * (x : ℂ)) ^ k / (k.factorial : ℂ)‖ :=
            norm_sum_le _ _
        _ = ∑ k ∈ Finset.range N, (|a| * |x|) ^ k / (k.factorial : ℝ) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [norm_div, norm_pow]
            simp
        _ ≤ Real.exp (|a| * |x|) := Real.sum_le_exp_of_nonneg (by positivity) N
    simp only [hF, norm_mul]
    have h1 : ‖((Real.exp (|a| * |x|) * gaussH x : ℝ) : ℂ)‖
        = Real.exp (|a| * |x|) * gaussH x := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_pos (Real.exp_pos _) (gaussH_pos x)).le]
    have h2 : ‖((gaussH x : ℝ) : ℂ)‖ = gaussH x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussH_pos x)]
    rw [h1, h2]
    have hg : (0 : ℝ) ≤ gaussH x * ‖u x‖ := mul_nonneg (gaussH_pos x).le (norm_nonneg _)
    calc ‖∑ k ∈ Finset.range N, (Complex.I * (a : ℂ) * (x : ℂ)) ^ k / (k.factorial : ℂ)‖
          * (gaussH x * ‖u x‖)
        ≤ Real.exp (|a| * |x|) * (gaussH x * ‖u x‖) := mul_le_mul_of_nonneg_right hsum hg
      _ = Real.exp (|a| * |x|) * gaussH x * ‖u x‖ := by ring
  have hlim : ∀ᵐ x : ℝ, Filter.Tendsto (fun N => F N x) Filter.atTop
      (nhds (Complex.exp (Complex.I * (a : ℂ) * (x : ℂ)) * (((gaussH x : ℝ) : ℂ) * u x))) := by
    filter_upwards with x
    exact ((complex_exp_hasSum (Complex.I * (a : ℂ) * (x : ℂ))).tendsto_sum_nat).mul_const _
  have hconv := MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x : ℝ => ‖((Real.exp (|a| * |x|) * gaussH x : ℝ) : ℂ) * u x‖)
    hmeas hbdd.norm hdom hlim
  have hval : ∫ x : ℝ, Complex.exp (Complex.I * (a : ℂ) * (x : ℂ)) * (((gaussH x : ℝ) : ℂ) * u x)
      = 0 := by
    have hc : Filter.Tendsto (fun _ : ℕ => (0 : ℂ)) Filter.atTop
        (nhds (∫ x : ℝ, Complex.exp (Complex.I * (a : ℂ) * (x : ℂ))
          * (((gaussH x : ℝ) : ℂ) * u x))) := by
      simpa [hFint] using hconv
    exact tendsto_nhds_unique hc tendsto_const_nhds
  rw [Real.fourier_real_eq_integral_exp_smul, ← hval]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  congr 2
  rw [ha]
  push_cast
  ring

/-- **Vanishing of all Gaussian moments forces `u = 0`.** -/
theorem ae_eq_zero_of_moments {u : ℝ → ℂ} (hu : MemLp u 2 (volume : Measure ℝ))
    (hmom : ∀ k : ℕ, ∫ x : ℝ, ((x ^ k * gaussH x : ℝ) : ℂ) * u x = 0) :
    ∀ᵐ x : ℝ, u x = 0 := by
  have hg : MemLp (fun x : ℝ => ((gaussH x : ℝ) : ℂ)) 2 (volume : Measure ℝ) := by
    simpa using memLp_poly_mul_gaussH (1 : Polynomial ℝ)
  have hv : Integrable (fun x : ℝ => ((gaussH x : ℝ) : ℂ) * u x) :=
    integrable_mul_of_memLp_two hg hu
  have hzero := ae_eq_zero_of_fourier_eq_zero hv (fun w => fourier_gaussH_mul_eq_zero hu hmom w)
  filter_upwards [hzero] with x hx
  have hne : ((gaussH x : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (gaussH_pos x)
  exact (mul_eq_zero.mp hx).resolve_left hne

theorem coeff_hermiteR_self (n : ℕ) : (hermiteR n).coeff n = 1 := by
  simp [hermiteR, Polynomial.coeff_map, Polynomial.coeff_hermite_self]

theorem coeff_hermiteR_of_lt {n k : ℕ} (h : n < k) : (hermiteR n).coeff k = 0 := by
  simp [hermiteR, Polynomial.coeff_map, Polynomial.coeff_hermite_of_lt h]

theorem natDegree_hermiteR (n : ℕ) : (hermiteR n).natDegree = n := by
  have hinj : Function.Injective ⇑(Int.castRingHom ℝ) := fun a b h => by
    simpa [Int.castRingHom] using h
  rw [hermiteR, Polynomial.natDegree_map_eq_of_injective hinj, Polynomial.natDegree_hermite]

/-- Adding polynomials adds the corresponding `L²` elements. -/
theorem toLp_poly_add (p q : Polynomial ℝ) :
    (memLp_poly_mul_gaussH (p + q)).toLp _
      = (memLp_poly_mul_gaussH p).toLp _ + (memLp_poly_mul_gaussH q).toLp _ := by
  rw [Lp.ext_iff]
  filter_upwards [(memLp_poly_mul_gaussH (p + q)).coeFn_toLp,
    Lp.coeFn_add ((memLp_poly_mul_gaussH p).toLp _) ((memLp_poly_mul_gaussH q).toLp _),
    (memLp_poly_mul_gaussH p).coeFn_toLp, (memLp_poly_mul_gaussH q).coeFn_toLp]
    with x h0 h1 h2 h3
  rw [h0, h1, Pi.add_apply, h2, h3]
  simp only [Polynomial.eval_add]
  push_cast
  ring

/-- A multiple of a Hermite polynomial times the Gaussian is a multiple of a
Hermite function. -/
theorem toLp_hermiteR_smul (n : ℕ) (c : ℝ) :
    (memLp_poly_mul_gaussH (C c * hermiteR n)).toLp _
      = ((c * hermiteNorm n : ℝ) : ℂ) • hermiteLp n := by
  rw [Lp.ext_iff]
  filter_upwards [(memLp_poly_mul_gaussH (C c * hermiteR n)).coeFn_toLp,
    Lp.coeFn_smul (((c * hermiteNorm n : ℝ) : ℂ)) (hermiteLp n), hermiteLp_coeFn n] with x h0 h1 h2
  rw [h0, h1, Pi.smul_apply, h2]
  have hne : ((hermiteNorm n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (hermiteNorm_pos n)
  simp only [hermiteC, hermiteFun, Polynomial.eval_mul, Polynomial.eval_C, smul_eq_mul]
  rw [div_eq_mul_inv]
  push_cast
  field_simp

/-- Every polynomial times the half Gaussian lies in the span of the Hermite
functions (the Hermite polynomials are monic of every degree). -/
theorem poly_mul_gaussH_mem_span_aux (n : ℕ) : ∀ p : Polynomial ℝ, p.natDegree ≤ n →
    (memLp_poly_mul_gaussH p).toLp _ ∈ Submodule.span ℂ (Set.range hermiteLp) := by
  induction n with
  | zero =>
    intro p hp
    have hpC : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hp
    have : (memLp_poly_mul_gaussH p).toLp _
        = ((p.coeff 0 * hermiteNorm 0 : ℝ) : ℂ) • hermiteLp 0 := by
      rw [← toLp_hermiteR_smul 0 (p.coeff 0)]
      refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
      rw [hermiteR_zero, mul_one, ← hpC]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  | succ n ih =>
    intro p hp
    set c : ℝ := p.coeff (n + 1) with hc
    set r : Polynomial ℝ := p - C c * hermiteR (n + 1) with hr
    have hrdeg : r.natDegree ≤ n := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hr, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hN) with h | h
      · rw [← h, coeff_hermiteR_self, ← hc]
        ring
      · have h1 : p.coeff N = 0 :=
          Polynomial.natDegree_le_iff_coeff_eq_zero.mp hp N h
        have h2 : (hermiteR (n + 1)).coeff N = 0 := coeff_hermiteR_of_lt h
        rw [h1, h2]
        ring
    have hsplit : (memLp_poly_mul_gaussH p).toLp _
        = (memLp_poly_mul_gaussH r).toLp _
          + (memLp_poly_mul_gaussH (C c * hermiteR (n + 1))).toLp _ := by
      rw [← toLp_poly_add]
      refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
      rw [hr]
      simp only [Polynomial.eval_add, Polynomial.eval_sub]
      ring_nf
    rw [hsplit, toLp_hermiteR_smul]
    exact Submodule.add_mem _ (ih r hrdeg)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨n + 1, rfl⟩))

theorem poly_mul_gaussH_mem_span (p : Polynomial ℝ) :
    (memLp_poly_mul_gaussH p).toLp _ ∈ Submodule.span ℂ (Set.range hermiteLp) :=
  poly_mul_gaussH_mem_span_aux p.natDegree p le_rfl

/-- **Completeness of the Hermite functions**: their span is dense in `L²(ℝ)`. -/
theorem hermiteLp_span_dense :
    (⊤ : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)))
      ≤ (Submodule.span ℂ (Set.range hermiteLp)).topologicalClosure := by
  rw [top_le_iff, Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro u hu
  have hmom : ∀ k : ℕ, ∫ x : ℝ, ((x ^ k * gaussH x : ℝ) : ℂ) * (u : ℝ → ℂ) x = 0 := by
    intro k
    have hmem := poly_mul_gaussH_mem_span (X ^ k)
    have hinner : (inner ℂ ((memLp_poly_mul_gaussH (X ^ k)).toLp _) u : ℂ) = 0 :=
      hu _ hmem
    rw [L2.inner_def] at hinner
    rw [← hinner]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_poly_mul_gaussH (X ^ k : Polynomial ℝ)).coeFn_toLp] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, Polynomial.eval_pow, Polynomial.eval_X, Complex.ofReal_mul,
      map_mul, Complex.conj_ofReal]
    ring
  have hzero := ae_eq_zero_of_moments (Lp.memLp u) hmom
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hzero

/-- **The Hermite basis of `L²(ℝ)`.** -/
def hermiteBasis : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  HilbertBasis.mk orthonormal_hermiteLp hermiteLp_span_dense

@[simp] theorem hermiteBasis_apply (n : ℕ) : hermiteBasis n = hermiteLp n := by
  rw [hermiteBasis, HilbertBasis.coe_mk]

/-! ## The harmonic oscillator -/

/-- The first derivative of a Hermite function. -/
theorem hasDerivAt_hermiteFun (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteFun n)
      (((derivative (hermiteR n)).eval x - x / 2 * (hermiteR n).eval x) * gaussH x) x := by
  have h := ((hermiteR n).hasDerivAt x).mul (hasDerivAt_gaussH x)
  convert h using 1
  ring

/-- The derivative of "polynomial times half Gaussian" is again of that form. -/
theorem hasDerivAt_poly_mul_gaussH (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => p.eval y * gaussH y)
      ((derivative p - C (1 / 2 : ℝ) * (X * p)).eval x * gaussH x) x := by
  have h := (p.hasDerivAt x).mul (hasDerivAt_gaussH x)
  convert h using 1
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

theorem deriv_poly_mul_gaussH (p : Polynomial ℝ) :
    deriv (fun y : ℝ => p.eval y * gaussH y)
      = fun x : ℝ => (derivative p - C (1 / 2 : ℝ) * (X * p)).eval x * gaussH x :=
  funext fun x => (hasDerivAt_poly_mul_gaussH p x).deriv

/-- **The Hermite functions are the eigenfunctions of the harmonic oscillator**
`-d²/dx² + x²/4`, with eigenvalues `n + 1/2`. -/
theorem hermiteFun_oscillator (n : ℕ) (x : ℝ) :
    -(deriv (deriv (hermiteFun n)) x) + x ^ 2 / 4 * hermiteFun n x
      = ((n : ℝ) + 1 / 2) * hermiteFun n x := by
  set q : Polynomial ℝ := derivative (hermiteR n) - C (1 / 2 : ℝ) * (X * hermiteR n) with hq
  have h1 : hermiteFun n = fun y : ℝ => (hermiteR n).eval y * gaussH y := rfl
  have h2 : deriv (hermiteFun n) = fun y : ℝ => q.eval y * gaussH y := by
    rw [h1, deriv_poly_mul_gaussH]
  have h3 : deriv (deriv (hermiteFun n)) x
      = (derivative q - C (1 / 2 : ℝ) * (X * q)).eval x * gaussH x := by
    rw [h2, deriv_poly_mul_gaussH]
  have hq' : derivative q = derivative (derivative (hermiteR n))
      - C (1 / 2 : ℝ) * (hermiteR n + X * derivative (hermiteR n)) := by
    rw [hq, derivative_sub, derivative_C_mul, derivative_mul, derivative_X, one_mul]
  have hode := congrArg (Polynomial.eval x) (hermiteR_ode n)
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_zero] at hode
  rw [h3, hq', hq, h1]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  linear_combination (-gaussH x) * hode

end

end BookProof.HermiteCore
