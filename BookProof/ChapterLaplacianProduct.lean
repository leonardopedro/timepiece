import BookProof.ChapterRadialLaplacian

/-!
# The Laplacian of a product, and of (radial) × (harmonic homogeneous)

Continuation of `BookProof.ChapterRadialLaplacian`, which computed the Laplacian
of a radial function in order to state Note 68 of `book.tex` §A.5 in space.  The
eigenfunctions of `−∂⃗²` with angular momentum `l ≥ 1` are *not* radial: they are
products of a radial factor with an angular one (a spherical harmonic, i.e. a
harmonic polynomial homogeneous of degree `l`, divided by `rˡ`).  This module
supplies the two missing general facts.

## Contents

* `laplacian_mul` — **the product rule for the Laplacian**, which Mathlib does
  not have: `Δ(fg) = (Δf)g + f(Δg) + 2 ∑ᵢ ∂ᵢf ∂ᵢg` in any orthonormal basis;
* `fderiv_radial` — the derivative of a radial function,
  `D(y ↦ g‖y‖)(x) = (g'(‖x‖)/‖x‖) ⟪x, ·⟫`;
* `sum_inner_mul_apply` — the basis identity `∑ᵢ ⟪x, vᵢ⟫ L(vᵢ) = L(x)`;
* `laplacian_radial_mul_harmonic` — **the Laplacian of a radial function times a
  harmonic function homogeneous of degree `l`** (homogeneity used only through
  Euler's identity `DH(x)(x) = l·H(x)`):
  `Δ(y ↦ g‖y‖ · H y)(x) = (g''(‖x‖) + ((n − 1 + 2l)/‖x‖) g'(‖x‖)) · H x`;
* `helmholtz_radial_mul_harmonic` — consequently, if the radial factor solves the
  reduced equation `g'' + ((n−1+2l)/r) g' = −p² g`, the product is an
  eigenfunction of `−∂⃗²` with eigenvalue `p²`;
* `harmonic_clm`, `euler_clm` — every continuous linear functional is harmonic
  and homogeneous of degree one, so the degree-`1` case of the hypotheses is
  realized (for example by a coordinate `x³` on `ℝ³`).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ChapterLaplacianProduct

open Filter Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A function that is twice continuously differentiable at a point has a
differentiable Fréchet derivative there. -/
theorem diffAt_fderiv {f : E → ℝ} {x : E} (h : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (fderiv ℝ f) x := by
  obtain ⟨u, hu, hfu⟩ := h.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨v, hvu, hvo, hqv⟩ := mem_nhds_iff.1 hu
  have h2 : ContDiffOn ℝ 1 (fderiv ℝ f) v := (hfu.mono hvu).fderiv_of_isOpen hvo (by norm_num)
  exact (h2.differentiableOn (by norm_num)).differentiableAt (hvo.mem_nhds hqv)

theorem fderiv_mul_eventually {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    (fderiv ℝ fun y : E => f y * g y) =ᶠ[nhds x]
      fun y => g y • fderiv ℝ f y + f y • fderiv ℝ g y := by
  have hfe : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by simp)] with y hy using hy.differentiableAt (by norm_num)
  have hge : ∀ᶠ y in nhds x, DifferentiableAt ℝ g y := by
    filter_upwards [hg.eventually (by simp)] with y hy using hy.differentiableAt (by norm_num)
  filter_upwards [hfe, hge] with y hy hy'
  have h := fderiv_mul (𝕜 := ℝ) (c := f) (d := g) hy hy'
  rw [show (fun y : E => f y * g y) = f * g from rfl, h]
  abel

theorem fderiv_fderiv_mul {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ fun y : E => f y * g y) x
      = (g x) • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x)
        + ((f x) • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ f x).smulRight (fderiv ℝ g x)) := by
  have hdf : HasFDerivAt f (fderiv ℝ f x) x := (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hdg : HasFDerivAt g (fderiv ℝ g x) x := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hDf : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x := (diffAt_fderiv hf).hasFDerivAt
  have hDg : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) x := (diffAt_fderiv hg).hasFDerivAt
  have h12 : HasFDerivAt (fun y : E => g y • fderiv ℝ f y + f y • fderiv ℝ g y)
      ((g x) • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x)
        + ((f x) • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ f x).smulRight (fderiv ℝ g x))) x :=
    (hdg.smul hDf).add (hdf.smul hDg)
  rw [(fderiv_mul_eventually hf hg).fderiv_eq, h12.fderiv]

/-- **The product rule for the Laplacian**:
`Δ(fg) = (Δf)g + f(Δg) + 2 ∑ᵢ ∂ᵢf ∂ᵢg`, the sum being over any orthonormal
basis. -/
theorem laplacian_mul [FiniteDimensional ℝ E] {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    (Δ fun y : E => f y * g y) x
      = (Δ f) x * g x + f x * (Δ g) x
        + 2 * ∑ i, fderiv ℝ f x ((stdOrthonormalBasis ℝ E) i)
            * fderiv ℝ g x ((stdOrthonormalBasis ℝ E) i) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis g]
  have hterm : ∀ i, iteratedFDeriv ℝ 2 (fun y : E => f y * g y) x
      ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]
      = g x * iteratedFDeriv ℝ 2 f x
          ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]
        + f x * iteratedFDeriv ℝ 2 g x
          ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]
        + 2 * (fderiv ℝ f x ((stdOrthonormalBasis ℝ E) i)
            * fderiv ℝ g x ((stdOrthonormalBasis ℝ E) i)) := by
    intro i
    rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply,
      fderiv_fderiv_mul hf hg]
    simp
    ring
  simp only [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  ring

/-- The derivative of a radial function: `D(y ↦ g‖y‖)(x) = (g'(‖x‖)/‖x‖) ⟪x, ·⟫`. -/
theorem fderiv_radial {g : ℝ → ℝ} {x : E} (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g ‖x‖) :
    fderiv ℝ (fun y : E => g ‖y‖) x = (deriv g ‖x‖ / ‖x‖) • innerCLM E x := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsq : Real.sqrt (‖x‖ ^ 2) = ‖x‖ := Real.sqrt_sq (norm_nonneg x)
  have hfun : (fun y : E => g ‖y‖) = fun y : E => (fun q => g (Real.sqrt q)) (‖y‖ ^ 2) := by
    funext y; simp [Real.sqrt_sq (norm_nonneg y)]
  have hG : ContDiffAt ℝ 2 (fun q => g (Real.sqrt q)) (‖x‖ ^ 2) := by
    have hsqrt : ContDiffAt ℝ 2 (fun q : ℝ => Real.sqrt q) (‖x‖ ^ 2) :=
      Real.contDiffAt_sqrt (pow_ne_zero 2 (ne_of_gt hr))
    have h : ContDiffAt ℝ 2 g (Real.sqrt (‖x‖ ^ 2)) := by rw [hsq]; exact hg
    exact h.comp (‖x‖ ^ 2) hsqrt
  obtain ⟨hd1, -⟩ := deriv_sqrt_comp hr hg
  rw [hfun, (fderiv_comp_normSq hG).self_of_nhds]
  simp only [hd1]
  congr 1
  field_simp

/-- Expansion of a continuous linear functional in an orthonormal basis:
`∑ᵢ ⟪x, vᵢ⟫ L(vᵢ) = L(x)`. -/
theorem sum_inner_mul_apply [FiniteDimensional ℝ E] (L : E →L[ℝ] ℝ) (x : E) :
    ∑ i, ⟪x, (stdOrthonormalBasis ℝ E) i⟫ * L ((stdOrthonormalBasis ℝ E) i) = L x := by
  have hx : ∑ i, ⟪(stdOrthonormalBasis ℝ E) i, x⟫ • (stdOrthonormalBasis ℝ E) i = x :=
    (stdOrthonormalBasis ℝ E).sum_repr' x
  calc ∑ i, ⟪x, (stdOrthonormalBasis ℝ E) i⟫ * L ((stdOrthonormalBasis ℝ E) i)
      = L (∑ i, ⟪(stdOrthonormalBasis ℝ E) i, x⟫ • (stdOrthonormalBasis ℝ E) i) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, real_inner_comm]
        simp
    _ = L x := by rw [hx]

/-- **The Laplacian of a radial function times a harmonic function homogeneous of
degree `l`.**  Homogeneity is used only through Euler's identity
`DH(x)(x) = l · H x`. -/
theorem laplacian_radial_mul_harmonic [FiniteDimensional ℝ E] {g : ℝ → ℝ} {H : E → ℝ} {x : E}
    {l : ℕ} (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g ‖x‖) (hH : ContDiffAt ℝ 2 H x)
    (hharm : (Δ H) x = 0) (heuler : fderiv ℝ H x x = l * H x) :
    (Δ fun y : E => g ‖y‖ * H y) x
      = (deriv (deriv g) ‖x‖
          + (((Module.finrank ℝ E : ℝ) - 1 + 2 * l) / ‖x‖) * deriv g ‖x‖) * H x := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hr' : ‖x‖ ≠ 0 := ne_of_gt hr
  have hf : ContDiffAt ℝ 2 (fun y : E => g ‖y‖) x := by
    have hnorm : ContDiffAt ℝ 2 (fun y : E => ‖y‖) x := contDiffAt_norm ℝ hx
    exact hg.comp x hnorm
  have hprod := laplacian_mul hf hH
  -- the cross term
  have hcross : ∑ i, fderiv ℝ (fun y : E => g ‖y‖) x ((stdOrthonormalBasis ℝ E) i)
      * fderiv ℝ H x ((stdOrthonormalBasis ℝ E) i)
      = (deriv g ‖x‖ / ‖x‖) * ((l : ℝ) * H x) := by
    have hsum : ∑ i, (deriv g ‖x‖ / ‖x‖) * (⟪x, (stdOrthonormalBasis ℝ E) i⟫
        * fderiv ℝ H x ((stdOrthonormalBasis ℝ E) i))
        = (deriv g ‖x‖ / ‖x‖) * fderiv ℝ H x x := by
      rw [← Finset.mul_sum, sum_inner_mul_apply (fderiv ℝ H x) x]
    rw [← heuler, ← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_radial hx hg]
    simp [mul_assoc]
  rw [hprod, hcross, hharm, laplacian_radial hx hg]
  field_simp
  ring

/-- If in addition the radial factor solves the reduced radial equation, the
product is an eigenfunction of `−∂⃗²` with eigenvalue `p²`. -/
theorem helmholtz_radial_mul_harmonic [FiniteDimensional ℝ E] {g : ℝ → ℝ} {H : E → ℝ} {x : E}
    {l : ℕ} {p : ℝ} (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g ‖x‖) (hH : ContDiffAt ℝ 2 H x)
    (hharm : (Δ H) x = 0) (heuler : fderiv ℝ H x x = l * H x)
    (hradial : deriv (deriv g) ‖x‖
      + (((Module.finrank ℝ E : ℝ) - 1 + 2 * l) / ‖x‖) * deriv g ‖x‖ = -(p ^ 2) * g ‖x‖) :
    -(Δ fun y : E => g ‖y‖ * H y) x = p ^ 2 * (g ‖x‖ * H x) := by
  rw [laplacian_radial_mul_harmonic hx hg hH hharm heuler, hradial]
  ring

/-! ## The degree-one case is realized: linear functionals are harmonic -/

theorem harmonic_clm [FiniteDimensional ℝ E] (L : E →L[ℝ] ℝ) (x : E) :
    (Δ fun y : E => L y) x = 0 := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  have hterm : ∀ i, iteratedFDeriv ℝ 2 (fun y : E => L y) x
      ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i] = 0 := by
    intro i
    rw [iteratedFDeriv_two_apply]
    have hfd : (fderiv ℝ fun y : E => L y) = fun _ => (L : E →L[ℝ] ℝ) := by
      funext y; exact L.fderiv
    rw [hfd]
    simp
  simp [hterm]

theorem euler_clm (L : E →L[ℝ] ℝ) (x : E) : fderiv ℝ (fun y : E => L y) x x = (1 : ℕ) * L x := by
  rw [L.fderiv]
  simp

end BookProof.ChapterLaplacianProduct
