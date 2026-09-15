import BookProof.ChapterLaplacianProduct

/-!
# Note 68 for angular momentum `l`: `jₗ(p‖x⃗‖)/‖x⃗‖ˡ · H(x⃗)` solves `−∂⃗²u = p²u`

Last step of the Note 68 wave (`book.tex` §A.5, `book.tex` line ~5860).
`BookProof.ChapterRadialLaplacian` gave the identity `−∂⃗²u = p²u` in the
`s`-wave sector, and `BookProof.ChapterLaplacianProduct` the Laplacian of a
radial factor times a harmonic factor homogeneous of degree `l`.  What is added
here is the one-variable computation showing that the radial factor
`g(r) = jₗ(p r)/rˡ` solves the reduced radial equation
`g'' + ((n − 1 + 2l)/r) g' = −p² g` in dimension `n = 3`, so that the product
with any harmonic function homogeneous of degree `l` is an eigenfunction of
`−∂⃗²` with eigenvalue `p²` — which is exactly the book's

`−∂⃗² 𝓗_P⁻¹{ψ}(x⃗) = 𝓗_P⁻¹{p²ψ}(x⃗)`

on the sector of angular momentum `l` (the angular factor `Y_{lμ}(θ,φ)` being
`H(x⃗)/‖x⃗‖ˡ` for a harmonic `H` homogeneous of degree `l`).

## Contents

* `hasDerivAt_quot`, `reduced_from_radial` — the one-variable reduction: if `R`
  solves `R'' + (2/r)R' + (p² − l(l+1)/r²)R = 0`, then `g = R/rˡ` solves
  `g'' + ((2 + 2l)/r)g' = −p²g`;
* `reduced_radial_sbessel` — the instance `R(r) = jₗ(p r)`;
* `helmholtz_sbessel_harmonic` — **Note 68 in the sector of angular momentum
  `l`**: on a three-dimensional real inner product space,
  `−∂⃗²(jₗ(p‖x⃗‖)/‖x⃗‖ˡ · H(x⃗)) = p² · (jₗ(p‖x⃗‖)/‖x⃗‖ˡ · H(x⃗))` for every
  harmonic `H` homogeneous of degree `l`;
* `helmholtz_sbessel_one_clm` — the degree-one instance realized concretely:
  `H = L` any continuous linear functional (for example a coordinate `x³`), so
  the statement is not vacuous for `l = 1`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).

## Boundaries, now closed elsewhere

* the harmonic homogeneous factors `H` for **every** `l` and every order
  `μ ≤ l` — the solid harmonics `rˡ Y_{lμ}` — are constructed in
  `BookProof.ChapterSolidHarmonic`, and Note 68 is stated in every mode in
  `BookProof.ChapterNote68AllModes`;
* the **unitarity** of the spherical transform in the `s`-wave sector is proved
  in `BookProof.ChapterSphericalPlancherel`.
-/

namespace BookProof.ChapterBesselHarmonic

open Filter Laplacian InnerProductSpace
open BookProof.ChapterSphericalBessel BookProof.ChapterSphericalBesselODE
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open scoped InnerProductSpace RealInnerProductSpace

/-- The derivative of `t ↦ R t / tˡ`. -/
theorem hasDerivAt_quot {R : ℝ → ℝ} {l : ℕ} {s : ℝ} (hs : s ≠ 0) (hR : DifferentiableAt ℝ R s) :
    HasDerivAt (fun t => R t / t ^ l)
      (deriv R s / s ^ l - (l : ℝ) * R s / s ^ (l + 1)) s := by
  have hp : HasDerivAt (fun t : ℝ => t ^ l) ((l : ℝ) * s ^ (l - 1)) s := hasDerivAt_pow l s
  have h := (hR.hasDerivAt).div hp (pow_ne_zero l hs)
  convert h using 1
  rw [pow_pred_coef l hs]
  field_simp
  ring

/-- **The reduction of the radial equation.**  If `R` solves
`R'' + (2/r)R' + (p² − l(l+1)/r²)R = 0`, then `g = R/rˡ` solves
`g'' + ((2 + 2l)/r)g' = −p²g`. -/
theorem reduced_from_radial {R : ℝ → ℝ} {l : ℕ} {p r : ℝ} (hr : r ≠ 0)
    (hR : DifferentiableAt ℝ R r) (hR' : DifferentiableAt ℝ (deriv R) r)
    (hRev : ∀ᶠ s in nhds r, DifferentiableAt ℝ R s)
    (hode : deriv (deriv R) r + (2 / r) * deriv R r
      + (p ^ 2 - (l : ℝ) * (l + 1) / r ^ 2) * R r = 0) :
    deriv (deriv fun s => R s / s ^ l) r
        + ((2 + 2 * (l : ℝ)) / r) * deriv (fun s => R s / s ^ l) r
      = -(p ^ 2) * (R r / r ^ l) := by
  have hne : ∀ᶠ s in nhds r, s ≠ 0 := isOpen_ne.mem_nhds hr
  have hEq : (deriv fun s => R s / s ^ l) =ᶠ[nhds r]
      fun s => deriv R s / s ^ l - (l : ℝ) * R s / s ^ (l + 1) := by
    filter_upwards [hRev, hne] with s hs hs0 using (hasDerivAt_quot hs0 hs).deriv
  have h1 : HasDerivAt (fun s => deriv R s / s ^ l)
      (deriv (deriv R) r / r ^ l - (l : ℝ) * deriv R r / r ^ (l + 1)) r :=
    hasDerivAt_quot hr hR'
  have hq : HasDerivAt (fun s => R s / s ^ (l + 1))
      (deriv R r / r ^ (l + 1) - ((l : ℝ) + 1) * R r / r ^ (l + 1 + 1)) r := by
    have h := hasDerivAt_quot (l := l + 1) hr hR
    push_cast at h
    exact h
  have h2 : HasDerivAt (fun s => (l : ℝ) * R s / s ^ (l + 1))
      ((l : ℝ) * (deriv R r / r ^ (l + 1) - ((l : ℝ) + 1) * R r / r ^ (l + 1 + 1))) r := by
    have h := hq.const_mul (l : ℝ)
    have hfun : (fun s => (l : ℝ) * (R s / s ^ (l + 1)))
        = fun s => (l : ℝ) * R s / s ^ (l + 1) := by
      funext s; ring
    rw [hfun] at h
    exact h
  have h12 : HasDerivAt (fun s => deriv R s / s ^ l - (l : ℝ) * R s / s ^ (l + 1))
      ((deriv (deriv R) r / r ^ l - (l : ℝ) * deriv R r / r ^ (l + 1))
        - (l : ℝ) * (deriv R r / r ^ (l + 1)
            - ((l : ℝ) + 1) * R r / r ^ (l + 1 + 1))) r := h1.sub h2
  have hderiv2 : deriv (deriv fun s => R s / s ^ l) r
      = (deriv (deriv R) r / r ^ l - (l : ℝ) * deriv R r / r ^ (l + 1))
        - (l : ℝ) * (deriv R r / r ^ (l + 1)
            - ((l : ℝ) + 1) * R r / r ^ (l + 1 + 1)) := by
    rw [hEq.deriv_eq, h12.deriv]
  have hderiv1 : deriv (fun s => R s / s ^ l) r
      = deriv R r / r ^ l - (l : ℝ) * R r / r ^ (l + 1) := (hasDerivAt_quot hr hR).deriv
  rw [hderiv2, hderiv1]
  have expand : ((deriv (deriv R) r / r ^ l - (l : ℝ) * deriv R r / r ^ (l + 1))
        - (l : ℝ) * (deriv R r / r ^ (l + 1)
            - ((l : ℝ) + 1) * R r / r ^ (l + 1 + 1)))
      + ((2 + 2 * (l : ℝ)) / r) * (deriv R r / r ^ l - (l : ℝ) * R r / r ^ (l + 1))
      = (1 / r ^ l) * (deriv (deriv R) r + (2 / r) * deriv R r
          + (p ^ 2 - (l : ℝ) * (l + 1) / r ^ 2) * R r) - p ^ 2 * (R r / r ^ l) := by
    field_simp
    ring
  rw [expand, hode]
  ring

/-- The radial factor `g(r) = jₗ(p r)/rˡ` solves the reduced radial equation. -/
theorem reduced_radial_sbessel (l : ℕ) {p r : ℝ} (hp : p ≠ 0) (hr : r ≠ 0) :
    deriv (deriv fun s => sbessel l (p * s) / s ^ l) r
        + ((2 + 2 * (l : ℝ)) / r) * deriv (fun s => sbessel l (p * s) / s ^ l) r
      = -(p ^ 2) * (sbessel l (p * r) / r ^ l) := by
  have hpr : p * r ≠ 0 := mul_ne_zero hp hr
  have hR : DifferentiableAt ℝ (fun s => sbessel l (p * s)) r :=
    (hasDerivAt_sbessel_scaled l hp hr).differentiableAt
  have hRev : ∀ᶠ s in nhds r, DifferentiableAt ℝ (fun s => sbessel l (p * s)) s := by
    filter_upwards [isOpen_ne.mem_nhds hr] with s hs using
      (hasDerivAt_sbessel_scaled l hp hs).differentiableAt
  have hR' : DifferentiableAt ℝ (deriv fun s => sbessel l (p * s)) r := by
    have hEq : (deriv fun s => sbessel l (p * s)) =ᶠ[nhds r]
        fun s => deriv (sbessel l) (p * s) * p := by
      filter_upwards [isOpen_ne.mem_nhds hr] with s hs using
        (hasDerivAt_sbessel_scaled l hp hs).deriv
    have hmul : DifferentiableAt ℝ (fun s : ℝ => p * s) r :=
      (differentiableAt_const p).mul differentiableAt_id
    have hcomp : DifferentiableAt ℝ (fun s : ℝ => deriv (sbessel l) (p * s)) r :=
      (diffAt_deriv_sbessel l hpr).comp r hmul
    exact (hcomp.mul_const p).congr_of_eventuallyEq hEq
  have hode : deriv (deriv fun s => sbessel l (p * s)) r
      + (2 / r) * deriv (fun s => sbessel l (p * s)) r
      + (p ^ 2 - (l : ℝ) * (l + 1) / r ^ 2) * sbessel l (p * r) = 0 := by
    have h := sbessel_radial_eigen l hp hr
    have hexp : (p ^ 2 - (l : ℝ) * (l + 1) / r ^ 2) * sbessel l (p * r)
        = p ^ 2 * sbessel l (p * r) - ((l : ℝ) * (l + 1) / r ^ 2) * sbessel l (p * r) := by
      ring
    rw [hexp]
    linarith [h]
  exact reduced_from_radial hr hR hR' hRev hode

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Note 68 in the sector of angular momentum `l`.**  On a three-dimensional
real inner product space, away from the origin, the product of the radial factor
`jₗ(p‖x⃗‖)/‖x⃗‖ˡ` with any harmonic function `H` homogeneous of degree `l`
(homogeneity entering only through Euler's identity) satisfies `−∂⃗²u = p²u`. -/
theorem helmholtz_sbessel_harmonic [FiniteDimensional ℝ E] (h3 : Module.finrank ℝ E = 3)
    {l : ℕ} {H : E → ℝ} {x : E} {p : ℝ} (hp : p ≠ 0) (hx : x ≠ 0)
    (hH : ContDiffAt ℝ 2 H x) (hharm : (Δ H) x = 0) (heuler : fderiv ℝ H x x = l * H x) :
    -(Δ fun y : E => (sbessel l (p * ‖y‖) / ‖y‖ ^ l) * H y) x
      = p ^ 2 * ((sbessel l (p * ‖x‖) / ‖x‖ ^ l) * H x) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hr' : ‖x‖ ≠ 0 := ne_of_gt hr
  have hg : ContDiffAt ℝ 2 (fun s : ℝ => sbessel l (p * s) / s ^ l) ‖x‖ := by
    have hmul : ContDiffAt ℝ 2 (fun s : ℝ => p * s) ‖x‖ :=
      (contDiff_const.mul contDiff_id).contDiffAt
    have hb : ContDiffAt ℝ 2 (fun s : ℝ => sbessel l (p * s)) ‖x‖ :=
      (contDiffAt_sbessel l (mul_ne_zero hp hr')).comp ‖x‖ hmul
    have hpow : ContDiffAt ℝ 2 (fun s : ℝ => s ^ l) ‖x‖ := (contDiff_id.pow l).contDiffAt
    exact hb.div hpow (pow_ne_zero l hr')
  have hradial : deriv (deriv fun s : ℝ => sbessel l (p * s) / s ^ l) ‖x‖
      + (((Module.finrank ℝ E : ℝ) - 1 + 2 * l) / ‖x‖)
        * deriv (fun s : ℝ => sbessel l (p * s) / s ^ l) ‖x‖
      = -(p ^ 2) * (sbessel l (p * ‖x‖) / ‖x‖ ^ l) := by
    rw [h3]
    have hcoef : ((3 : ℕ) : ℝ) - 1 + 2 * (l : ℝ) = 2 + 2 * (l : ℝ) := by push_cast; ring
    rw [hcoef]
    exact reduced_radial_sbessel l hp hr'
  exact helmholtz_radial_mul_harmonic (g := fun s : ℝ => sbessel l (p * s) / s ^ l)
    (H := H) (l := l) (p := p) hx hg hH hharm heuler hradial

/-- The degree-one case realized concretely: for a continuous linear functional
`L` (for instance a coordinate `x³` on `ℝ³`), `u(x⃗) = j₁(p‖x⃗‖) L(x⃗)/‖x⃗‖`
satisfies `−∂⃗²u = p²u`. -/
theorem helmholtz_sbessel_one_clm [FiniteDimensional ℝ E] (h3 : Module.finrank ℝ E = 3)
    (L : E →L[ℝ] ℝ) {x : E} {p : ℝ} (hp : p ≠ 0) (hx : x ≠ 0) :
    -(Δ fun y : E => (sbessel 1 (p * ‖y‖) / ‖y‖ ^ 1) * L y) x
      = p ^ 2 * ((sbessel 1 (p * ‖x‖) / ‖x‖ ^ 1) * L x) :=
  helmholtz_sbessel_harmonic h3 hp hx
    (L.contDiff (n := 2)).contDiffAt (harmonic_clm L x) (euler_clm L x)

end BookProof.ChapterBesselHarmonic
