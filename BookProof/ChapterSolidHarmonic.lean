import BookProof.ChapterSolidHarmonicTools
import BookProof.ChapterLegendrePolynomial

/-!
# Solid harmonics: `rˡ Y_{lμ}` is harmonic and homogeneous of degree `l`

This module closes the boundary recorded in `BookProof.ChapterBesselHarmonic`:
the identification of the associated Legendre functions / spherical harmonics
`Y_{lμ}` of `book.tex` §A.5 with harmonic functions homogeneous of degree `l`,
for *all* `l` and `μ ≤ l`.

The setting is a three-dimensional real inner product space with an orthonormal
triple `(u, v, e)`; on `ℝ³` this is the standard frame, `⟪u,x⟫ = x¹`,
`⟪v,x⟫ = x²`, `⟪e,x⟫ = x³`.  Write `w(x) = ⟪u,x⟫ + i⟪v,x⟫` (this is
`ρ e^{iφ}` in cylindrical coordinates), `z(x) = ⟪e,x⟫` and `s(x) = ‖x‖²`.

The **solid harmonic** of degree `l` and order `μ` is

`S_{lμ}(x) = Re(w(x)^μ) · ∑ₘ P_l^{(μ)}[l−μ−2m] z(x)^{l−μ−2m} s(x)^m`

(and the same with `Im`), where `P_l^{(μ)}[k]` is the `k`-th coefficient of the
`μ`-th derivative of the Legendre polynomial.  In spherical coordinates this is
exactly `rˡ (sin θ)^μ P_l^{(μ)}(cos θ) cos(μφ)`, i.e. `rˡ Y_{lμ}` up to
normalization (`solidHarmonic_spherical`).

## Contents

* `nullCLM` — the null linear form `w = ⟪u,·⟫ + i⟪v,·⟫`, with
  `sum_nullCLM_sq : ∑ᵢ w(bᵢ)² = 0`;
* `angular_harmonic`, `angular_euler`, `angular_axis` — the angular factor
  `Re(wᵘ)` is harmonic, homogeneous of degree `μ` and constant along the axis;
* `solidHarmonic`, `solidHarmonicIm` — the solid harmonics;
* `solidHarmonic_harmonic`, `solidHarmonic_euler` — **they are harmonic and
  homogeneous of degree `l`**, for every `l` and every `μ ≤ l`;
* `solidHarmonic_spherical` — in spherical coordinates the solid harmonic is
  `rˡ (sin θ)^μ P_l^{(μ)}(cos θ) cos(μ φ)`, the classical `rˡ Y_{lμ}`;
* `assocLegendre` — the associated Legendre function
  `P_l^μ(t) = (1−t²)^{μ/2} P_l^{(μ)}(t)`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ChapterSolidHarmonic

open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The null linear form and the angular factor -/

/-- The complex linear form `w = ⟪u,·⟫ + i⟪v,·⟫`. -/
noncomputable def nullCLM (u v : E) : E →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (innerCLM E u) + Complex.I • (Complex.ofRealCLM.comp (innerCLM E v))

@[simp] theorem nullCLM_apply (u v x : E) :
    nullCLM u v x = (⟪u, x⟫_ℝ : ℂ) + Complex.I * (⟪v, x⟫_ℝ : ℂ) := rfl

/-- For an orthonormal pair `u, v` the form `w` is *null*: `∑ᵢ w(bᵢ)² = 0`.
This is what makes its powers harmonic. -/
theorem sum_nullCLM_sq {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) :
    ∑ i, (nullCLM u v (stdOrthonormalBasis ℝ E i)) ^ 2 = 0 := by
  have h1 : ∑ i, (⟪u, (stdOrthonormalBasis ℝ E) i⟫_ℝ) ^ 2 = 1 := by
    rw [sum_inner_sq u, hu]; norm_num
  have h2 : ∑ i, (⟪v, (stdOrthonormalBasis ℝ E) i⟫_ℝ) ^ 2 = 1 := by
    rw [sum_inner_sq v, hv]; norm_num
  have h3 : ∑ i, ⟪u, (stdOrthonormalBasis ℝ E) i⟫_ℝ * ⟪v, (stdOrthonormalBasis ℝ E) i⟫_ℝ = 0 := by
    have h := sum_inner_mul_apply (innerCLM E v) u
    simp only [innerCLM_apply] at h
    rw [h, real_inner_comm]
    exact huv
  have expand : ∀ i, (nullCLM u v (stdOrthonormalBasis ℝ E i)) ^ 2
      = (((⟪u, (stdOrthonormalBasis ℝ E) i⟫_ℝ) ^ 2 - (⟪v, (stdOrthonormalBasis ℝ E) i⟫_ℝ) ^ 2 : ℝ)
          : ℂ)
        + Complex.I * ((2 * ⟪u, (stdOrthonormalBasis ℝ E) i⟫_ℝ
            * ⟪v, (stdOrthonormalBasis ℝ E) i⟫_ℝ : ℝ) : ℂ) := by
    intro i
    rw [nullCLM_apply]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [expand]
  rw [Finset.sum_add_distrib, ← Complex.ofReal_sum, ← Finset.mul_sum, ← Complex.ofReal_sum]
  have hsub : ∑ i, ((⟪u, (stdOrthonormalBasis ℝ E) i⟫_ℝ) ^ 2
      - (⟪v, (stdOrthonormalBasis ℝ E) i⟫_ℝ) ^ 2) = 0 := by
    rw [Finset.sum_sub_distrib, h1, h2, sub_self]
  have hmix : ∑ i, (2 * ⟪u, (stdOrthonormalBasis ℝ E) i⟫_ℝ
      * ⟪v, (stdOrthonormalBasis ℝ E) i⟫_ℝ) = 0 := by
    simp only [mul_assoc]
    rw [← Finset.mul_sum, h3, mul_zero]
  rw [hsub, hmix]
  simp

/-- The angular factor `A(x) = Re(w(x)^μ)`. -/
noncomputable def angular (u v : E) (μ : ℕ) (x : E) : ℝ := ((nullCLM u v x) ^ μ).re

/-- The angular factor `Im(w(x)^μ)`. -/
noncomputable def angularIm (u v : E) (μ : ℕ) (x : E) : ℝ := ((nullCLM u v x) ^ μ).im

theorem contDiff_angular (u v : E) (μ : ℕ) : ContDiff ℝ 2 (angular u v μ) :=
  Complex.reCLM.contDiff.comp (contDiff_clmPow (nullCLM u v) μ)

theorem contDiff_angularIm (u v : E) (μ : ℕ) : ContDiff ℝ 2 (angularIm u v μ) :=
  Complex.imCLM.contDiff.comp (contDiff_clmPow (nullCLM u v) μ)

/-- **The angular factor is harmonic.** -/
theorem angular_harmonic {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0)
    (μ : ℕ) (x : E) : (Δ (angular u v μ)) x = 0 := by
  have hc : ContDiffAt ℝ 2 (fun y : E => (nullCLM u v y) ^ μ) x :=
    (contDiff_clmPow (nullCLM u v) μ).contDiffAt
  have h := hc.laplacian_CLM_comp_left (l := Complex.reCLM)
  have hz : (Δ fun y : E => (nullCLM u v y) ^ μ) x = 0 := by
    rw [laplacian_clmPow, sum_nullCLM_sq hu hv huv, mul_zero]
  have hrw : angular u v μ = Complex.reCLM ∘ fun y : E => (nullCLM u v y) ^ μ := rfl
  rw [hrw, h]
  simp only [Function.comp_apply, hz]
  simp

theorem angularIm_harmonic {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0)
    (μ : ℕ) (x : E) : (Δ (angularIm u v μ)) x = 0 := by
  have hc : ContDiffAt ℝ 2 (fun y : E => (nullCLM u v y) ^ μ) x :=
    (contDiff_clmPow (nullCLM u v) μ).contDiffAt
  have h := hc.laplacian_CLM_comp_left (l := Complex.imCLM)
  have hz : (Δ fun y : E => (nullCLM u v y) ^ μ) x = 0 := by
    rw [laplacian_clmPow, sum_nullCLM_sq hu hv huv, mul_zero]
  have hrw : angularIm u v μ = Complex.imCLM ∘ fun y : E => (nullCLM u v y) ^ μ := rfl
  rw [hrw, h]
  simp only [Function.comp_apply, hz]
  simp

theorem fderiv_angular (u v : E) (μ : ℕ) (x w : E) :
    fderiv ℝ (angular u v μ) x w = ((μ : ℂ) * (nullCLM u v x) ^ (μ - 1) * nullCLM u v w).re := by
  have h : HasFDerivAt (angular u v μ)
      (Complex.reCLM.comp (((μ : ℂ) * (nullCLM u v x) ^ (μ - 1)) • (nullCLM u v))) x :=
    Complex.reCLM.hasFDerivAt.comp x (hasFDerivAt_clmPow (nullCLM u v) μ x)
  rw [h.fderiv]
  simp [mul_assoc]

theorem fderiv_angularIm (u v : E) (μ : ℕ) (x w : E) :
    fderiv ℝ (angularIm u v μ) x w = ((μ : ℂ) * (nullCLM u v x) ^ (μ - 1) * nullCLM u v w).im := by
  have h : HasFDerivAt (angularIm u v μ)
      (Complex.imCLM.comp (((μ : ℂ) * (nullCLM u v x) ^ (μ - 1)) • (nullCLM u v))) x :=
    Complex.imCLM.hasFDerivAt.comp x (hasFDerivAt_clmPow (nullCLM u v) μ x)
  rw [h.fderiv]
  simp [mul_assoc]

/-- **Euler's identity for the angular factor**: it is homogeneous of degree `μ`. -/
theorem angular_euler (u v : E) (μ : ℕ) (x : E) :
    fderiv ℝ (angular u v μ) x x = (μ : ℝ) * angular u v μ x := by
  rw [fderiv_angular]
  rcases μ with _ | n
  · simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    rw [show ((n : ℂ) + 1) * (nullCLM u v x) ^ n * nullCLM u v x
        = ((n : ℂ) + 1) * (nullCLM u v x) ^ (n + 1) from by ring]
    simp [Complex.mul_re]

theorem angularIm_euler (u v : E) (μ : ℕ) (x : E) :
    fderiv ℝ (angularIm u v μ) x x = (μ : ℝ) * angularIm u v μ x := by
  rw [fderiv_angularIm]
  rcases μ with _ | n
  · simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    rw [show ((n : ℂ) + 1) * (nullCLM u v x) ^ n * nullCLM u v x
        = ((n : ℂ) + 1) * (nullCLM u v x) ^ (n + 1) from by ring]
    simp [Complex.mul_im]

/-- The angular factor does not vary along the axis. -/
theorem angular_axis {u v e : E} (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0) (μ : ℕ) (x : E) :
    fderiv ℝ (angular u v μ) x e = 0 := by
  have h0 : nullCLM u v e = 0 := by
    rw [nullCLM_apply, hue, hve]
    simp
  rw [fderiv_angular, h0, mul_zero]
  simp

theorem angularIm_axis {u v e : E} (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0) (μ : ℕ) (x : E) :
    fderiv ℝ (angularIm u v μ) x e = 0 := by
  have h0 : nullCLM u v e = 0 := by
    rw [nullCLM_apply, hue, hve]
    simp
  rw [fderiv_angularIm, h0, mul_zero]
  simp

/-! ## The radial (cylindrical) factor and the solid harmonics -/

/-- The polynomial factor `∑ₘ P_l^{(μ)}[l−μ−2m] ⟪e,x⟫^{l−μ−2m} (‖x‖²)ᵐ`, which is
the homogeneous extension of `P_l^{(μ)}(cos θ)`. -/
noncomputable def radialFactor (e : E) (l μ : ℕ) (x : E) : ℝ :=
  ∑ m ∈ Finset.range ((l - μ) / 2 + 1),
    (derivative^[μ] (legendre l)).coeff (l - μ - 2 * m)
      * ((⟪e, x⟫_ℝ) ^ (l - μ - 2 * m) * (‖x‖ ^ 2) ^ m)

/-- **The solid harmonic** `rˡ Y_{lμ}` (real part convention). -/
noncomputable def solidHarmonic (u v e : E) (l μ : ℕ) (x : E) : ℝ :=
  angular u v μ x * radialFactor e l μ x

/-- **The solid harmonic** `rˡ Y_{lμ}` (imaginary part convention). -/
noncomputable def solidHarmonicIm (u v e : E) (l μ : ℕ) (x : E) : ℝ :=
  angularIm u v μ x * radialFactor e l μ x

theorem laplacian_const_mul {f : E → ℝ} {x : E} (c : ℝ) (hf : ContDiffAt ℝ 2 f x) :
    (Δ fun y => c * f y) x = c * (Δ f) x := by
  have hrw : (fun y => c * f y) = c • f := by funext y; simp
  rw [hrw, laplacian_smul c hf]
  simp

theorem contDiff_cylTerm (e : E) (j m : ℕ) :
    ContDiff ℝ 2 fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m :=
  (contDiff_rclmPow (innerCLM E e) j).mul (contDiff_normSqPow m)

/-- The abstract harmonicity criterion: an angular factor times a cylindrical
polynomial whose coefficients satisfy the Gegenbauer recursion is harmonic. -/
theorem laplacian_angular_mul_sum {A : E → ℝ} {x e : E} (he : ‖e‖ = 1) {μ : ℕ} (n : ℕ)
    (h3 : Module.finrank ℝ E = 3)
    (hA : ContDiffAt ℝ 2 A x) (hharm : (Δ A) x = 0)
    (heuler : fderiv ℝ A x x = μ * A x) (haxis : fderiv ℝ A x e = 0)
    (g : ℕ → ℝ)
    (hrec : ∀ j : ℕ, ((j : ℝ) + 2) * ((j : ℝ) + 1) * g (j + 2)
      = -(((n : ℝ) - j) * ((n : ℝ) + j + 2 * μ + 1)) * g j) :
    (Δ fun y : E => ∑ m ∈ Finset.range (n / 2 + 1),
        g (n - 2 * m) * (A y * ((⟪e, y⟫_ℝ) ^ (n - 2 * m) * (‖y‖ ^ 2) ^ m))) x = 0 := by
  classical
  have hterm : ∀ m ∈ Finset.range (n / 2 + 1),
      ContDiffAt ℝ 2 (fun y : E => g (n - 2 * m)
        * (A y * ((⟪e, y⟫_ℝ) ^ (n - 2 * m) * (‖y‖ ^ 2) ^ m))) x := by
    intro m _
    exact (contDiffAt_const (c := g (n - 2 * m))).mul
      (hA.mul (contDiff_cylTerm e (n - 2 * m) m).contDiffAt)
  rw [laplacian_sum _ _ x hterm]
  have hval : ∀ m ∈ Finset.range (n / 2 + 1),
      (Δ fun y : E => g (n - 2 * m) * (A y * ((⟪e, y⟫_ℝ) ^ (n - 2 * m) * (‖y‖ ^ 2) ^ m))) x
      = g (n - 2 * m) * (A x *
          (((n - 2 * m : ℕ) : ℝ) * (((n - 2 * m : ℕ) : ℝ) - 1)
              * (⟪e, x⟫_ℝ) ^ (n - 2 * m - 2) * (‖x‖ ^ 2) ^ m
            + (4 * m * ((m : ℝ) - 1) + 2 * 3 * m + 4 * ((n - 2 * m : ℕ) : ℝ) * m + 4 * μ * m)
              * (⟪e, x⟫_ℝ) ^ (n - 2 * m) * (‖x‖ ^ 2) ^ (m - 1))) := by
    intro m _
    rw [laplacian_const_mul _ (hA.mul (contDiff_cylTerm e (n - 2 * m) m).contDiffAt),
      laplacian_angular_mul_cylTerm he (n - 2 * m) m hA hharm heuler haxis, h3]
    push_cast
    ring
  rw [Finset.sum_congr rfl hval]
  -- split into the two families and telescope
  set M := n / 2 with hM
  set z := ⟪e, x⟫_ℝ with hz
  set s := ‖x‖ ^ 2 with hs
  have hsplit : ∀ m : ℕ, g (n - 2 * m) * (A x *
      (((n - 2 * m : ℕ) : ℝ) * (((n - 2 * m : ℕ) : ℝ) - 1) * z ^ (n - 2 * m - 2) * s ^ m
        + (4 * m * ((m : ℝ) - 1) + 2 * 3 * m + 4 * ((n - 2 * m : ℕ) : ℝ) * m + 4 * μ * m)
          * z ^ (n - 2 * m) * s ^ (m - 1)))
      = (A x * (g (n - 2 * m) * (((n - 2 * m : ℕ) : ℝ) * (((n - 2 * m : ℕ) : ℝ) - 1)
            * z ^ (n - 2 * m - 2) * s ^ m)))
        + (A x * (g (n - 2 * m)
            * ((4 * m * ((m : ℝ) - 1) + 2 * 3 * m + 4 * ((n - 2 * m : ℕ) : ℝ) * m + 4 * μ * m)
              * z ^ (n - 2 * m) * s ^ (m - 1)))) := by
    intro m; ring
  simp only [hsplit, Finset.sum_add_distrib]
  set F1 : ℕ → ℝ := fun m => A x * (g (n - 2 * m) * (((n - 2 * m : ℕ) : ℝ)
    * (((n - 2 * m : ℕ) : ℝ) - 1) * z ^ (n - 2 * m - 2) * s ^ m)) with hF1
  set F2 : ℕ → ℝ := fun m => A x * (g (n - 2 * m)
    * ((4 * m * ((m : ℝ) - 1) + 2 * 3 * m + 4 * ((n - 2 * m : ℕ) : ℝ) * m + 4 * μ * m)
      * z ^ (n - 2 * m) * s ^ (m - 1))) with hF2
  have hlast : F1 M = 0 := by
    have hcase : n - 2 * M = 0 ∨ n - 2 * M = 1 := by omega
    rcases hcase with h | h <;> simp [hF1, h]
  have hfirst : F2 0 = 0 := by simp [hF2]
  have h1 : ∑ m ∈ Finset.range (M + 1), F1 m = ∑ m ∈ Finset.range M, F1 m := by
    rw [Finset.sum_range_succ, hlast, add_zero]
  have h2 : ∑ m ∈ Finset.range (M + 1), F2 m = ∑ m ∈ Finset.range M, F2 (m + 1) := by
    rw [Finset.sum_range_succ' F2 M, hfirst, add_zero]
  rw [h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hmM : m < M := Finset.mem_range.mp hm
  have hbound : 2 * m + 2 ≤ n := by omega
  set jj := n - 2 * m - 2 with hjj
  have e1 : n - 2 * m = jj + 2 := by omega
  have e2 : n - 2 * (m + 1) = jj := by omega
  have e3 : n - 2 * m - 2 = jj := by omega
  have e4 : m + 1 - 1 = m := by omega
  have ecast1 : ((n - 2 * m : ℕ) : ℝ) = (jj : ℝ) + 2 := by rw [e1]; push_cast; ring
  have ecast2 : ((n - 2 * (m + 1) : ℕ) : ℝ) = (jj : ℝ) := by rw [e2]
  have ecastn : ((n : ℕ) : ℝ) = (jj : ℝ) + 2 * m + 2 := by
    have : n = jj + 2 * m + 2 := by omega
    rw [this]; push_cast; ring
  have hrecj := hrec jj
  rw [ecastn] at hrecj
  simp only [hF1, hF2, e1, e2, e3, e4, ecast1, ecast2]
  push_cast
  linear_combination (A x * z ^ jj * s ^ m) * hrecj

/-- The Legendre coefficients satisfy the recursion in the factored form used by
`laplacian_angular_mul_sum`. -/
theorem legendre_rec_factored {l μ : ℕ} (hμ : μ ≤ l) (j : ℕ) :
    ((j : ℝ) + 2) * ((j : ℝ) + 1) * (derivative^[μ] (legendre l)).coeff (j + 2)
      = -((((l - μ : ℕ) : ℝ) - j) * (((l - μ : ℕ) : ℝ) + j + 2 * μ + 1))
        * (derivative^[μ] (legendre l)).coeff j := by
  rw [legendre_deriv_coeff_rec l μ j]
  congr 1
  rw [Nat.cast_sub hμ]
  ring

/-- **The solid harmonic is harmonic**, for every degree `l` and every order
`μ ≤ l`. -/
theorem solidHarmonic_harmonic {u v e : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1)
    (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0)
    (h3 : Module.finrank ℝ E = 3) {l μ : ℕ} (hμ : μ ≤ l) (x : E) :
    (Δ (solidHarmonic u v e l μ)) x = 0 := by
  have hfun : solidHarmonic u v e l μ
      = fun y : E => ∑ m ∈ Finset.range ((l - μ) / 2 + 1),
          (derivative^[μ] (legendre l)).coeff (l - μ - 2 * m)
            * (angular u v μ y * ((⟪e, y⟫_ℝ) ^ (l - μ - 2 * m) * (‖y‖ ^ 2) ^ m)) := by
    funext y
    rw [solidHarmonic, radialFactor, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hfun]
  exact laplacian_angular_mul_sum he (l - μ) h3 (contDiff_angular u v μ).contDiffAt
    (angular_harmonic hu hv huv μ x) (angular_euler u v μ x) (angular_axis hue hve μ x) _
    (legendre_rec_factored hμ)

theorem solidHarmonicIm_harmonic {u v e : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1)
    (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0)
    (h3 : Module.finrank ℝ E = 3) {l μ : ℕ} (hμ : μ ≤ l) (x : E) :
    (Δ (solidHarmonicIm u v e l μ)) x = 0 := by
  have hfun : solidHarmonicIm u v e l μ
      = fun y : E => ∑ m ∈ Finset.range ((l - μ) / 2 + 1),
          (derivative^[μ] (legendre l)).coeff (l - μ - 2 * m)
            * (angularIm u v μ y * ((⟪e, y⟫_ℝ) ^ (l - μ - 2 * m) * (‖y‖ ^ 2) ^ m)) := by
    funext y
    rw [solidHarmonicIm, radialFactor, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hfun]
  exact laplacian_angular_mul_sum he (l - μ) h3 (contDiff_angularIm u v μ).contDiffAt
    (angularIm_harmonic hu hv huv μ x) (angularIm_euler u v μ x) (angularIm_axis hue hve μ x) _
    (legendre_rec_factored hμ)

/-! ## Homogeneity -/

theorem contDiff_radialFactor (e : E) (l μ : ℕ) : ContDiff ℝ 2 (radialFactor e l μ) := by
  refine ContDiff.sum fun m _ => ?_
  exact contDiff_const.mul (contDiff_cylTerm e (l - μ - 2 * m) m)

theorem hasFDerivAt_radialFactor (e : E) (l μ : ℕ) (x : E) :
    HasFDerivAt (radialFactor e l μ)
      (∑ m ∈ Finset.range ((l - μ) / 2 + 1),
        ((derivative^[μ] (legendre l)).coeff (l - μ - 2 * m)) •
          ((((l - μ - 2 * m : ℕ) : ℝ) * (⟪e, x⟫_ℝ) ^ (l - μ - 2 * m - 1) * (‖x‖ ^ 2) ^ m)
              • innerCLM E e
            + (2 * m * (⟪e, x⟫_ℝ) ^ (l - μ - 2 * m) * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x)) x := by
  refine HasFDerivAt.fun_sum (u := Finset.range ((l - μ) / 2 + 1)) fun m _ => ?_
  exact (hasFDerivAt_cylTerm e (l - μ - 2 * m) m x).const_mul
    ((derivative^[μ] (legendre l)).coeff (l - μ - 2 * m))

/-- **Euler's identity for the radial factor**: it is homogeneous of degree
`l − μ`. -/
theorem radialFactor_euler (e : E) (l μ : ℕ) (x : E) :
    fderiv ℝ (radialFactor e l μ) x x = ((l - μ : ℕ) : ℝ) * radialFactor e l μ x := by
  rw [(hasFDerivAt_radialFactor e l μ x).fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, innerCLM_apply]
  rw [radialFactor, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm2 : 2 * m ≤ l - μ := by
    have := Finset.mem_range.mp hm
    omega
  have hxx : ⟪x, x⟫_ℝ = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  have t1 : ((l - μ - 2 * m : ℕ) : ℝ) * (⟪e, x⟫_ℝ) ^ (l - μ - 2 * m - 1) * ⟪e, x⟫_ℝ
      = ((l - μ - 2 * m : ℕ) : ℝ) * (⟪e, x⟫_ℝ) ^ (l - μ - 2 * m) := by
    rcases Nat.eq_zero_or_pos (l - μ - 2 * m) with h | h
    · simp [h]
    · obtain ⟨k, hk⟩ : ∃ k, l - μ - 2 * m = k + 1 := ⟨l - μ - 2 * m - 1, by omega⟩
      rw [hk]
      simp only [Nat.add_sub_cancel, pow_succ]
      ring
  have t2 : 2 * (m : ℝ) * ((‖x‖ ^ 2) ^ (m - 1) * ⟪x, x⟫_ℝ) = 2 * (m : ℝ) * (‖x‖ ^ 2) ^ m := by
    rw [hxx]
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [hk]
      simp only [Nat.add_sub_cancel, pow_succ]
  have hnat : ((l - μ : ℕ) : ℝ) = ((l - μ - 2 * m : ℕ) : ℝ) + 2 * m := by
    have h : (l - μ - 2 * m) + 2 * m = l - μ := by omega
    calc ((l - μ : ℕ) : ℝ) = (((l - μ - 2 * m) + 2 * m : ℕ) : ℝ) := by rw [h]
      _ = ((l - μ - 2 * m : ℕ) : ℝ) + 2 * m := by push_cast; ring
  rw [hnat]
  linear_combination
    (((derivative^[μ] (legendre l)).coeff (l - μ - 2 * m)) * (‖x‖ ^ 2) ^ m) * t1
      + (((derivative^[μ] (legendre l)).coeff (l - μ - 2 * m))
          * (⟪e, x⟫_ℝ) ^ (l - μ - 2 * m)) * t2

/-- **Euler's identity for the solid harmonic**: it is homogeneous of degree
`l`. -/
theorem solidHarmonic_euler (u v e : E) {l μ : ℕ} (hμ : μ ≤ l) (x : E) :
    fderiv ℝ (solidHarmonic u v e l μ) x x = (l : ℝ) * solidHarmonic u v e l μ x := by
  have hA : HasFDerivAt (angular u v μ) (fderiv ℝ (angular u v μ) x) x :=
    ((contDiff_angular u v μ).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hB : HasFDerivAt (radialFactor e l μ) (fderiv ℝ (radialFactor e l μ) x) x :=
    ((contDiff_radialFactor e l μ).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hprod := (hA.mul hB).fderiv
  have hrw : solidHarmonic u v e l μ = angular u v μ * radialFactor e l μ := rfl
  rw [hrw, hprod]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, Pi.mul_apply]
  rw [angular_euler, radialFactor_euler]
  have hcast : ((l - μ : ℕ) : ℝ) + (μ : ℝ) = (l : ℝ) := by
    rw [Nat.cast_sub hμ]; ring
  linear_combination (angular u v μ x * radialFactor e l μ x) * hcast

theorem solidHarmonicIm_euler (u v e : E) {l μ : ℕ} (hμ : μ ≤ l) (x : E) :
    fderiv ℝ (solidHarmonicIm u v e l μ) x x = (l : ℝ) * solidHarmonicIm u v e l μ x := by
  have hA : HasFDerivAt (angularIm u v μ) (fderiv ℝ (angularIm u v μ) x) x :=
    ((contDiff_angularIm u v μ).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hB : HasFDerivAt (radialFactor e l μ) (fderiv ℝ (radialFactor e l μ) x) x :=
    ((contDiff_radialFactor e l μ).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hprod := (hA.mul hB).fderiv
  have hrw : solidHarmonicIm u v e l μ = angularIm u v μ * radialFactor e l μ := rfl
  rw [hrw, hprod]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, Pi.mul_apply]
  rw [angularIm_euler, radialFactor_euler]
  have hcast : ((l - μ : ℕ) : ℝ) + (μ : ℝ) = (l : ℝ) := by
    rw [Nat.cast_sub hμ]; ring
  linear_combination (angularIm u v μ x * radialFactor e l μ x) * hcast

theorem contDiff_solidHarmonic (u v e : E) (l μ : ℕ) : ContDiff ℝ 2 (solidHarmonic u v e l μ) :=
  (contDiff_angular u v μ).mul (contDiff_radialFactor e l μ)

theorem contDiff_solidHarmonicIm (u v e : E) (l μ : ℕ) :
    ContDiff ℝ 2 (solidHarmonicIm u v e l μ) :=
  (contDiff_angularIm u v μ).mul (contDiff_radialFactor e l μ)

/-! ## The radial factor is the homogeneous extension of `P_l^{(μ)}(cos θ)` -/

/-- **The radial factor evaluated**: `radialFactor e l μ x = ‖x‖^{l−μ} P_l^{(μ)}(⟪e,x⟫/‖x‖)`. -/
theorem radialFactor_eval (e : E) {l μ : ℕ} (hμ : μ ≤ l) {x : E} (hx : x ≠ 0) :
    radialFactor e l μ x
      = ‖x‖ ^ (l - μ) * (derivative^[μ] (legendre l)).eval (⟪e, x⟫_ℝ / ‖x‖) := by
  classical
  set n := l - μ with hn
  set r := ‖x‖ with hr
  have hr0 : 0 < r := by rw [hr]; exact norm_pos_iff.mpr hx
  set Y : ℝ[X] := derivative^[μ] (legendre l) with hY
  have hdeg : Y.natDegree < n + 1 := by
    by_contra hcon
    push_neg at hcon
    have hzero : Y.coeff Y.natDegree = 0 := by
      apply legendre_deriv_coeff_eq_zero
      omega
    have : Y = 0 := by
      by_contra hne
      exact (Polynomial.leadingCoeff_ne_zero.mpr hne) hzero
    simp [this] at hcon
  rw [Polynomial.eval_eq_sum_range' hdeg, Finset.mul_sum]
  set T : Finset ℕ := (Finset.range (n / 2 + 1)).image (fun m => n - 2 * m) with hT
  have hTsub : T ⊆ Finset.range (n + 1) := by
    intro k hk
    rw [hT, Finset.mem_image] at hk
    obtain ⟨m, hm, rfl⟩ := hk
    exact Finset.mem_range.mpr (by omega)
  have hvanish : ∀ k ∈ Finset.range (n + 1), k ∉ T →
      r ^ n * (Y.coeff k * (⟪e, x⟫_ℝ / r) ^ k) = 0 := by
    intro k hk hkT
    have hpar : k % 2 ≠ n % 2 := by
      intro hcon
      apply hkT
      rw [hT, Finset.mem_image]
      refine ⟨(n - k) / 2, Finset.mem_range.mpr ?_, ?_⟩
      · have := Finset.mem_range.mp hk
        omega
      · have := Finset.mem_range.mp hk
        omega
    rw [legendre_deriv_coeff_parity l μ hμ k hpar]
    ring
  have hinj : Set.InjOn (fun m => n - 2 * m) ↑(Finset.range (n / 2 + 1)) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only at hab
    omega
  rw [← Finset.sum_subset hTsub hvanish, hT, Finset.sum_image hinj]
  rw [radialFactor]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm2 : 2 * m ≤ n := by
    have := Finset.mem_range.mp hm
    omega
  obtain ⟨k, hk⟩ : ∃ k, n = k + 2 * m := ⟨n - 2 * m, by omega⟩
  have hk' : n - 2 * m = k := by omega
  have hpow : r ^ n * ((⟪e, x⟫_ℝ / r) ^ (n - 2 * m))
      = (⟪e, x⟫_ℝ) ^ (n - 2 * m) * (r ^ 2) ^ m := by
    rw [hk', hk, div_pow, pow_add, pow_mul]
    field_simp
  rw [← hpow]
  ring

/-! ## Spherical coordinates: the solid harmonic is `rˡ Y_{lμ}` -/

/-- **The associated Legendre function** `P_l^μ(t) = (1−t²)^{μ/2} P_l^{(μ)}(t)`
(without the Condon–Shortley phase `(−1)^μ`). -/
noncomputable def assocLegendre (l μ : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (1 - t ^ 2) ^ μ * (derivative^[μ] (legendre l)).eval t

/-- The point of spherical coordinates `(r, θ, φ)` in the frame `(u, v, e)`. -/
noncomputable def spherePt (u v e : E) (r θ φ : ℝ) : E :=
  (r * Real.sin θ * Real.cos φ) • u + (r * Real.sin θ * Real.sin φ) • v + (r * Real.cos θ) • e

section Frame

variable {u v e : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1)
  (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0)

include hu hv he huv hue hve

theorem inner_u_spherePt (r θ φ : ℝ) :
    ⟪u, spherePt u v e r θ φ⟫_ℝ = r * Real.sin θ * Real.cos φ := by
  have hvu : ⟪v, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact huv
  have heu : ⟪e, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact hue
  simp only [spherePt, inner_add_right, real_inner_smul_right, huv, hue,
    real_inner_self_eq_norm_sq, hu]
  ring

theorem inner_v_spherePt (r θ φ : ℝ) :
    ⟪v, spherePt u v e r θ φ⟫_ℝ = r * Real.sin θ * Real.sin φ := by
  have hvu : ⟪v, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact huv
  simp only [spherePt, inner_add_right, real_inner_smul_right, hvu, hve,
    real_inner_self_eq_norm_sq, hv]
  ring

theorem inner_e_spherePt (r θ φ : ℝ) :
    ⟪e, spherePt u v e r θ φ⟫_ℝ = r * Real.cos θ := by
  have heu : ⟪e, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact hue
  have hev : ⟪e, v⟫_ℝ = 0 := by rw [real_inner_comm]; exact hve
  simp only [spherePt, inner_add_right, real_inner_smul_right, heu, hev,
    real_inner_self_eq_norm_sq, he]
  ring

theorem norm_spherePt {r : ℝ} (hr : 0 ≤ r) (θ φ : ℝ) : ‖spherePt u v e r θ φ‖ = r := by
  have hvu : ⟪v, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact huv
  have heu : ⟪e, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact hue
  have hev : ⟪e, v⟫_ℝ = 0 := by rw [real_inner_comm]; exact hve
  have hnu : ∀ c : ℝ, ‖c • u‖ ^ 2 = c ^ 2 := by
    intro c; rw [norm_smul, hu, Real.norm_eq_abs]; simp [sq_abs]
  have hnv : ∀ c : ℝ, ‖c • v‖ ^ 2 = c ^ 2 := by
    intro c; rw [norm_smul, hv, Real.norm_eq_abs]; simp [sq_abs]
  have hne : ∀ c : ℝ, ‖c • e‖ ^ 2 = c ^ 2 := by
    intro c; rw [norm_smul, he, Real.norm_eq_abs]; simp [sq_abs]
  have hsq : ‖spherePt u v e r θ φ‖ ^ 2 = r ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [spherePt, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, huv, hue, hve, hvu, heu, hev, real_inner_self_eq_norm_sq,
      hnu, hnv, hne]
    have hs := Real.sin_sq_add_cos_sq φ
    have ht := Real.sin_sq_add_cos_sq θ
    linear_combination (r ^ 2 * Real.sin θ ^ 2) * hs + r ^ 2 * ht
  have h1 : 0 ≤ ‖spherePt u v e r θ φ‖ := norm_nonneg _
  nlinarith [hsq, h1, hr]

/-- **The solid harmonic in spherical coordinates**: it is
`rˡ P_l^μ(cos θ) cos(μ φ)`, i.e. `rˡ Y_{lμ}(θ, φ)` up to normalization. -/
theorem solidHarmonic_spherical {l μ : ℕ} (hμ : μ ≤ l) {r : ℝ} (hr : 0 < r) {θ : ℝ}
    (hθ : 0 ≤ Real.sin θ) (φ : ℝ) :
    solidHarmonic u v e l μ (spherePt u v e r θ φ)
      = r ^ l * assocLegendre l μ (Real.cos θ) * Real.cos (μ * φ) := by
  set x := spherePt u v e r θ φ with hx
  have hnorm : ‖x‖ = r := norm_spherePt hu hv he huv hue hve hr.le θ φ
  have hxne : x ≠ 0 := by
    intro hcon
    rw [hcon] at hnorm
    simp at hnorm
    exact absurd hnorm.symm (ne_of_gt hr)
  have hiu : ⟪u, x⟫_ℝ = r * Real.sin θ * Real.cos φ := inner_u_spherePt hu hv he huv hue hve r θ φ
  have hiv : ⟪v, x⟫_ℝ = r * Real.sin θ * Real.sin φ := inner_v_spherePt hu hv he huv hue hve r θ φ
  have hie : ⟪e, x⟫_ℝ = r * Real.cos θ := inner_e_spherePt hu hv he huv hue hve r θ φ
  -- the angular factor
  have hw : nullCLM u v x = ((r * Real.sin θ : ℝ) : ℂ) * Complex.exp (φ * Complex.I) := by
    rw [nullCLM_apply, hiu, hiv, Complex.exp_mul_I]
    push_cast
    ring
  have hang : angular u v μ x = (r * Real.sin θ) ^ μ * Real.cos (μ * φ) := by
    have hcast : (((r * Real.sin θ : ℝ) : ℂ)) ^ μ = (((r * Real.sin θ) ^ μ : ℝ) : ℂ) := by
      push_cast; ring
    rw [angular, hw, mul_pow, ← Complex.exp_nat_mul, hcast,
      show (μ : ℂ) * (φ * Complex.I) = ((μ : ℝ) * φ : ℝ) * Complex.I from by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  -- the radial factor
  have hrad : radialFactor e l μ x
      = r ^ (l - μ) * (derivative^[μ] (legendre l)).eval (Real.cos θ) := by
    rw [radialFactor_eval e hμ hxne, hnorm, hie]
    congr 2
    field_simp
  have hsin : Real.sqrt (1 - Real.cos θ ^ 2) = Real.sin θ := by
    rw [show 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 from by
      have := Real.sin_sq_add_cos_sq θ; linarith]
    exact Real.sqrt_sq hθ
  rw [solidHarmonic, hang, hrad, assocLegendre, hsin]
  have hrl : r ^ μ * r ^ (l - μ) = r ^ l := by
    rw [← pow_add]
    congr 1
    omega
  rw [mul_pow]
  ring_nf
  rw [show r ^ μ * r ^ (l - μ) = r ^ l from hrl]

end Frame

end BookProof.ChapterSolidHarmonic
