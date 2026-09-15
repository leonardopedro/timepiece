import BookProof.ChapterSphericalBessel

/-!
# Chapter — Hankel–Majorana transform: the spherical Bessel equation for every `l`

Source: `book.tex`, §A.5, subsection *"Hankel–Majorana Transform"* (line ~5805),
Definitions 65–67 and **Note 68**.  The book defines the spherical transform

`𝓗_P{ψ}(p,l,μ) = ∫ r² dr d(cos θ) dφ (2p/√(2π)) jₗ(pr) Y_{lμ}(θ,φ) ψ(r,θ,φ)`

out of the spherical Bessel functions `jₗ` of `BookProof.ChapterSphericalBessel`
(the Rayleigh formula `jₗ(r) = rˡ (−(1/r) d/dr)ˡ (sin r / r)`), and states in
**Note 68** that, "due to the properties of the spherical harmonics and Bessel
functions", the inverse transform intertwines the Laplacian with multiplication
by `p²`:

`−∂⃗² 𝓗_P⁻¹{ψ} = 𝓗_P⁻¹{p² ψ}`.

The analytic heart of that statement — the only part of it that concerns the
Bessel functions themselves — is that `jₗ` solves the **spherical Bessel
equation**, equivalently that `r ↦ jₗ(p r)` is an eigenfunction, with eigenvalue
`p²`, of the radial part of `−∂⃗²` in the sector of angular momentum `l`.
`BookProof.ChapterSphericalBessel` proved this for `l = 0` only.  This module
proves it for **every** `l`, directly from the Rayleigh formula.

## Contents

* `gIter l` — the `l`-th Rayleigh iterate `(−(1/r) d/dr)ˡ (sin r / r)`, so that
  `jₗ(r) = rˡ · gIter l r`;
* `contDiffOn_gIter`, `diffAt_gIter`, `diffAt_deriv_gIter` — every iterate is
  smooth away from the origin (proved by induction, and needed to differentiate
  the iterates at all);
* `deriv_gIter_eq` — the Rayleigh step `gₗ'(r) = −r · gₗ₊₁(r)`;
* `gIter_ode` — the equation satisfied by the iterates:
  `r gₗ'' + (2l+2) gₗ' + r gₗ = 0`, proved by induction on `l`;
* `gIter_pred_eq` — the companion first-order identity
  `gₗ = (2l+3) gₗ₊₁ + r gₗ₊₁'`;
* `sbessel_ode` — **the spherical Bessel equation**
  `r² jₗ'' + 2 r jₗ' + (r² − l(l+1)) jₗ = 0` for every `l`;
* `sbessel_rayleigh_raise` — the Rayleigh raising relation
  `jₗ₊₁(r) = −rˡ · d/dr (jₗ(r)/rˡ)`;
* `sbessel_recurrence` — the three-term recurrence
  `jₗ₋₁(r) + jₗ₊₁(r) = ((2l+1)/r) jₗ(r)`;
* `sbessel_radial_eigen` — **Note 68 in the radial sector**: for `p > 0` the
  function `u(r) = jₗ(p r)` satisfies
  `−(u''(r) + (2/r) u'(r) − (l(l+1)/r²) u(r)) = p² u(r)`,
  i.e. it is an eigenfunction of the radial Laplacian with angular momentum `l`
  and eigenvalue `p²`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis.
-/

namespace BookProof.ChapterSphericalBesselODE

open BookProof.ChapterSphericalBessel

/-- The `l`-th Rayleigh iterate `gₗ = (−(1/r) d/dr)ˡ (sin r / r)`; the spherical
Bessel function is `jₗ(r) = rˡ gₗ(r)`. -/
noncomputable def gIter (l : ℕ) : ℝ → ℝ := rayleighOp^[l] sbesselBase

theorem sbessel_eq (l : ℕ) (r : ℝ) : sbessel l r = r ^ l * gIter l r := rfl

/-! ## Smoothness of the Rayleigh iterates away from the origin -/

theorem contDiffOn_sbesselBase : ContDiffOn ℝ (⊤ : ℕ∞) sbesselBase {r : ℝ | r ≠ 0} := by
  apply ContDiffOn.div Real.contDiff_sin.contDiffOn contDiff_id.contDiffOn
  intro x hx; exact hx

/-- Every Rayleigh iterate is smooth on the punctured line. -/
theorem contDiffOn_gIter (l : ℕ) : ContDiffOn ℝ (⊤ : ℕ∞) (gIter l) {r : ℝ | r ≠ 0} := by
  induction l with
  | zero => simpa [gIter] using contDiffOn_sbesselBase
  | succ n ih =>
      have hstep : gIter (n + 1) = rayleighOp (gIter n) := by
        simp [gIter, Function.iterate_succ_apply']
      rw [hstep]
      have hd : ContDiffOn ℝ (⊤ : ℕ∞) (deriv (gIter n)) {r : ℝ | r ≠ 0} :=
        ih.deriv_of_isOpen (m := (⊤ : ℕ∞)) isOpen_ne (by simp)
      have hinv : ContDiffOn ℝ (⊤ : ℕ∞) (fun r : ℝ => -(1 / r)) {r : ℝ | r ≠ 0} := by
        apply ContDiffOn.neg
        apply ContDiffOn.div contDiffOn_const contDiff_id.contDiffOn
        intro x hx; exact hx
      exact hinv.mul hd

theorem diffAt_gIter (l : ℕ) {r : ℝ} (hr : r ≠ 0) : DifferentiableAt ℝ (gIter l) r :=
  ((contDiffOn_gIter l).differentiableOn (by simp)).differentiableAt (isOpen_ne.mem_nhds hr)

theorem diffAt_deriv_gIter (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    DifferentiableAt ℝ (deriv (gIter l)) r :=
  (((contDiffOn_gIter l).deriv_of_isOpen (m := (⊤ : ℕ∞)) isOpen_ne (by simp)).differentiableOn
    (by simp)).differentiableAt (isOpen_ne.mem_nhds hr)

/-! ## The Rayleigh step and the equation satisfied by the iterates -/

theorem gIter_succ (l : ℕ) (r : ℝ) : gIter (l + 1) r = -(1 / r) * deriv (gIter l) r := by
  simp [gIter, Function.iterate_succ_apply', rayleighOp]

/-- The Rayleigh step, read as a formula for the derivative: `gₗ'(r) = −r gₗ₊₁(r)`. -/
theorem deriv_gIter_eq (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    deriv (gIter l) r = -r * gIter (l + 1) r := by
  rw [gIter_succ]; field_simp

theorem second_deriv_gIter (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    deriv (deriv (gIter l)) r = -gIter (l + 1) r - r * deriv (gIter (l + 1)) r := by
  have hEq : deriv (gIter l) =ᶠ[nhds r] fun x => -x * gIter (l + 1) x := by
    filter_upwards [isOpen_ne.mem_nhds hr] with x hx using deriv_gIter_eq l hx
  have hneg : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) r := by
    simpa using (hasDerivAt_id r).neg
  have hD : HasDerivAt (fun x : ℝ => -x * gIter (l + 1) x)
      (-1 * gIter (l + 1) r + -r * deriv (gIter (l + 1)) r) r :=
    hneg.mul ((diffAt_gIter (l + 1) hr).hasDerivAt)
  rw [hEq.deriv_eq, hD.deriv]
  ring

theorem hasDerivAt_sbesselBase {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt sbesselBase (Real.cos x / x - Real.sin x / x ^ 2) x := by
  have h := (Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx
  simp only [id_eq] at h
  have he : (Real.cos x * x - Real.sin x * 1) / x ^ 2
      = Real.cos x / x - Real.sin x / x ^ 2 := by field_simp
  rwa [he] at h

/-- The base case `l = 0` of `gIter_ode`: `r g₀'' + 2 g₀' + r g₀ = 0` for
`g₀(r) = sin r / r`. -/
theorem gIter_ode_zero {r : ℝ} (hr : r ≠ 0) :
    r * deriv (deriv (gIter 0)) r + 2 * deriv (gIter 0) r + r * gIter 0 r = 0 := by
  have hg0 : gIter 0 = sbesselBase := rfl
  rw [hg0]
  have hEq : deriv sbesselBase =ᶠ[nhds r] fun x => Real.cos x / x - Real.sin x / x ^ 2 := by
    filter_upwards [isOpen_ne.mem_nhds hr] with x hx using (hasDerivAt_sbesselBase hx).deriv
  have h3 : HasDerivAt (fun x : ℝ => Real.cos x / x)
      ((-Real.sin r * r - Real.cos r * 1) / r ^ 2) r := by
    simpa using (Real.hasDerivAt_cos r).div (hasDerivAt_id r) hr
  have h4 : HasDerivAt (fun x : ℝ => Real.sin x / x ^ 2)
      ((Real.cos r * r ^ 2 - Real.sin r * (2 * r)) / (r ^ 2) ^ 2) r := by
    have h : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
    exact (Real.hasDerivAt_sin r).div h (pow_ne_zero 2 hr)
  have h2 : HasDerivAt (fun x : ℝ => Real.cos x / x - Real.sin x / x ^ 2)
      ((-Real.sin r * r - Real.cos r * 1) / r ^ 2
        - (Real.cos r * r ^ 2 - Real.sin r * (2 * r)) / (r ^ 2) ^ 2) r := h3.sub h4
  rw [hEq.deriv_eq, h2.deriv, (hasDerivAt_sbesselBase hr).deriv, sbesselBase]
  field_simp
  ring

/-- **The equation satisfied by the Rayleigh iterates**:
`r gₗ''(r) + (2l+2) gₗ'(r) + r gₗ(r) = 0` for every `l` and every `r ≠ 0`. -/
theorem gIter_ode (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    r * deriv (deriv (gIter l)) r + (2 * l + 2) * deriv (gIter l) r + r * gIter l r = 0 := by
  induction l generalizing r with
  | zero => simpa using gIter_ode_zero hr
  | succ n ih =>
      -- the first-order identity `gₙ = (2n+3) gₙ₊₁ + r gₙ₊₁'`, valid on the punctured line
      have key : ∀ x : ℝ, x ≠ 0 →
          gIter n x = (2 * n + 3) * gIter (n + 1) x + x * deriv (gIter (n + 1)) x := by
        intro x hx
        have hIH := ih hx
        rw [second_deriv_gIter n hx, deriv_gIter_eq n hx] at hIH
        have hx0 : x * (gIter n x
            - ((2 * n + 3) * gIter (n + 1) x + x * deriv (gIter (n + 1)) x)) = 0 := by
          nlinarith [hIH]
        rcases mul_eq_zero.mp hx0 with h0 | h0
        · exact absurd h0 hx
        · linarith
      have hEq : gIter n =ᶠ[nhds r]
          fun x => (2 * (n : ℝ) + 3) * gIter (n + 1) x + x * deriv (gIter (n + 1)) x := by
        filter_upwards [isOpen_ne.mem_nhds hr] with x hx using key x hx
      have hD : HasDerivAt
          (fun x : ℝ => (2 * (n : ℝ) + 3) * gIter (n + 1) x + x * deriv (gIter (n + 1)) x)
          ((2 * (n : ℝ) + 3) * deriv (gIter (n + 1)) r
            + (1 * deriv (gIter (n + 1)) r + r * deriv (deriv (gIter (n + 1))) r)) r :=
        HasDerivAt.add (((diffAt_gIter (n + 1) hr).hasDerivAt).const_mul _)
          ((hasDerivAt_id r).mul ((diffAt_deriv_gIter (n + 1) hr).hasDerivAt))
      have hfin : deriv (gIter n) r = (2 * (n : ℝ) + 3) * deriv (gIter (n + 1)) r
          + (1 * deriv (gIter (n + 1)) r + r * deriv (deriv (gIter (n + 1))) r) := by
        rw [hEq.deriv_eq, hD.deriv]
      rw [deriv_gIter_eq n hr] at hfin
      push_cast
      linarith

/-- The companion first-order identity `gₗ = (2l+3) gₗ₊₁ + r gₗ₊₁'`. -/
theorem gIter_pred_eq (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    gIter l r = (2 * l + 3) * gIter (l + 1) r + r * deriv (gIter (l + 1)) r := by
  have hIH := gIter_ode l hr
  rw [second_deriv_gIter l hr, deriv_gIter_eq l hr] at hIH
  have hx0 : r * (gIter l r
      - ((2 * l + 3) * gIter (l + 1) r + r * deriv (gIter (l + 1)) r)) = 0 := by
    nlinarith [hIH]
  rcases mul_eq_zero.mp hx0 with h0 | h0
  · exact absurd h0 hr
  · linarith


/-! ## The spherical Bessel equation -/

theorem pow_pred_coef (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    (l : ℝ) * r ^ (l - 1) = r ^ l * ((l : ℝ) / r) := by
  cases l with
  | zero => simp
  | succ m =>
      simp only [Nat.add_sub_cancel]
      rw [pow_succ]
      field_simp

theorem hasDerivAt_sbessel (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (sbessel l) (r ^ l * ((l : ℝ) * gIter l r / r + deriv (gIter l) r)) r := by
  have hD : HasDerivAt (fun x : ℝ => x ^ l * gIter l x)
      ((l : ℝ) * r ^ (l - 1) * gIter l r + r ^ l * deriv (gIter l) r) r :=
    (hasDerivAt_pow l r).mul ((diffAt_gIter l hr).hasDerivAt)
  have hfun : (fun x : ℝ => x ^ l * gIter l x) = sbessel l := rfl
  rw [hfun] at hD
  have hval : r ^ l * ((l : ℝ) * gIter l r / r + deriv (gIter l) r)
      = (l : ℝ) * r ^ (l - 1) * gIter l r + r ^ l * deriv (gIter l) r := by
    rw [pow_pred_coef l hr]
    field_simp
  rw [hval]
  exact hD

/-- **The spherical Bessel equation** (Definition 67 / Note 68):
`r² jₗ''(r) + 2 r jₗ'(r) + (r² − l(l+1)) jₗ(r) = 0` for every `l` and `r ≠ 0`. -/
theorem sbessel_ode (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    r ^ 2 * deriv (deriv (sbessel l)) r + 2 * r * deriv (sbessel l) r
      + (r ^ 2 - l * (l + 1)) * sbessel l r = 0 := by
  have hEq : deriv (sbessel l) =ᶠ[nhds r]
      fun x => x ^ l * ((l : ℝ) * gIter l x / x + deriv (gIter l) x) := by
    filter_upwards [isOpen_ne.mem_nhds hr] with x hx using (hasDerivAt_sbessel l hx).deriv
  have hquot : HasDerivAt (fun x : ℝ => (l : ℝ) * gIter l x / x)
      (((l : ℝ) * deriv (gIter l) r * r - (l : ℝ) * gIter l r) / r ^ 2) r := by
    have h1 : HasDerivAt (fun x : ℝ => (l : ℝ) * gIter l x) ((l : ℝ) * deriv (gIter l) r) r :=
      ((diffAt_gIter l hr).hasDerivAt).const_mul _
    simpa using h1.div (hasDerivAt_id r) hr
  have hinner : HasDerivAt (fun x : ℝ => (l : ℝ) * gIter l x / x + deriv (gIter l) x)
      ((((l : ℝ) * deriv (gIter l) r * r - (l : ℝ) * gIter l r) / r ^ 2)
        + deriv (deriv (gIter l)) r) r :=
    hquot.add ((diffAt_deriv_gIter l hr).hasDerivAt)
  have hD : HasDerivAt (fun x : ℝ => x ^ l * ((l : ℝ) * gIter l x / x + deriv (gIter l) x))
      ((l : ℝ) * r ^ (l - 1) * ((l : ℝ) * gIter l r / r + deriv (gIter l) r)
        + r ^ l * ((((l : ℝ) * deriv (gIter l) r * r - (l : ℝ) * gIter l r) / r ^ 2)
          + deriv (deriv (gIter l)) r)) r := (hasDerivAt_pow l r).mul hinner
  have h2nd : deriv (deriv (sbessel l)) r
      = r ^ l * ((l : ℝ) / r) * ((l : ℝ) * gIter l r / r + deriv (gIter l) r)
        + r ^ l * ((((l : ℝ) * deriv (gIter l) r * r - (l : ℝ) * gIter l r) / r ^ 2)
          + deriv (deriv (gIter l)) r) := by
    rw [hEq.deriv_eq, hD.deriv, pow_pred_coef l hr]
  have hode := gIter_ode l hr
  rw [h2nd, (hasDerivAt_sbessel l hr).deriv, sbessel_eq]
  have expand : r ^ 2 * (r ^ l * ((l : ℝ) / r) * ((l : ℝ) * gIter l r / r + deriv (gIter l) r)
        + r ^ l * ((((l : ℝ) * deriv (gIter l) r * r - (l : ℝ) * gIter l r) / r ^ 2)
          + deriv (deriv (gIter l)) r))
      + 2 * r * (r ^ l * ((l : ℝ) * gIter l r / r + deriv (gIter l) r))
      + (r ^ 2 - l * (l + 1)) * (r ^ l * gIter l r)
      = r ^ l * r * (r * deriv (deriv (gIter l)) r + (2 * l + 2) * deriv (gIter l) r
          + r * gIter l r) := by
    field_simp
    ring
  rw [expand, hode, mul_zero]

/-- **The Rayleigh raising relation** in terms of the spherical Bessel functions
themselves: `jₗ₊₁(r) = −rˡ · d/dr (jₗ(r)/rˡ)`. -/
theorem sbessel_rayleigh_raise (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    sbessel (l + 1) r = -(r ^ l) * deriv (fun s => sbessel l s / s ^ l) r := by
  have hEq : (fun s : ℝ => sbessel l s / s ^ l) =ᶠ[nhds r] gIter l := by
    filter_upwards [isOpen_ne.mem_nhds hr] with s hs
    rw [sbessel_eq]
    field_simp
  rw [hEq.deriv_eq, deriv_gIter_eq l hr, sbessel_eq]
  ring

/-! ## The three-term recurrence -/

/-- **The three-term recurrence** `jₗ₋₁(r) + jₗ₊₁(r) = ((2l+1)/r) jₗ(r)`,
written without subtraction of naturals. -/
theorem sbessel_recurrence (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    sbessel l r + sbessel (l + 2) r = ((2 * (l + 1) + 1) / r) * sbessel (l + 1) r := by
  have hg : gIter l r = (2 * l + 3) * gIter (l + 1) r + r * deriv (gIter (l + 1)) r :=
    gIter_pred_eq l hr
  have hstep : deriv (gIter (l + 1)) r = -r * gIter (l + 2) r := deriv_gIter_eq (l + 1) hr
  rw [sbessel_eq, sbessel_eq, sbessel_eq, hg, hstep]
  field_simp
  ring

/-! ## Note 68 in the radial sector -/

theorem hasDerivAt_sbessel_scaled (l : ℕ) {p x : ℝ} (hp : p ≠ 0) (hx : x ≠ 0) :
    HasDerivAt (fun s : ℝ => sbessel l (p * s)) (deriv (sbessel l) (p * x) * p) x := by
  have hpx : p * x ≠ 0 := mul_ne_zero hp hx
  have hc : HasDerivAt (fun s : ℝ => p * s) p x := by
    simpa using (hasDerivAt_id x).const_mul p
  have hb : HasDerivAt (sbessel l) (deriv (sbessel l) (p * x)) (p * x) := by
    have h := hasDerivAt_sbessel l hpx
    rwa [h.deriv]
  exact hb.comp x hc

/-- The spherical Bessel function is smooth away from the origin. -/
theorem contDiffAt_sbessel (l : ℕ) {x : ℝ} (hx : x ≠ 0) : ContDiffAt ℝ 2 (sbessel l) x := by
  have hg : ContDiffAt ℝ (⊤ : ℕ∞) (gIter l) x :=
    (contDiffOn_gIter l).contDiffAt (isOpen_ne.mem_nhds hx)
  have hpow : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => s ^ l) x := (contDiff_id.pow l).contDiffAt
  have hmul : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => s ^ l * gIter l s) x := hpow.mul hg
  have hfun : sbessel l = fun s : ℝ => s ^ l * gIter l s := by
    funext s; rw [sbessel_eq]
  rw [hfun]
  exact hmul.of_le ENat.LEInfty.out

/-- The derivative of a spherical Bessel function is again differentiable away
from the origin. -/
theorem diffAt_deriv_sbessel (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ (deriv (sbessel l)) x := by
  have hEq : deriv (sbessel l) =ᶠ[nhds x]
      fun s => s ^ l * ((l : ℝ) * gIter l s / s + deriv (gIter l) s) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with s hs using (hasDerivAt_sbessel l hs).deriv
  have hdiff : DifferentiableAt ℝ
      (fun s : ℝ => s ^ l * ((l : ℝ) * gIter l s / s + deriv (gIter l) s)) x := by
    have h1 : DifferentiableAt ℝ (fun s : ℝ => s ^ l) x := (differentiable_pow l).differentiableAt
    have h2 : DifferentiableAt ℝ (fun s : ℝ => (l : ℝ) * gIter l s / s) x :=
      ((diffAt_gIter l hx).const_mul _).div differentiableAt_id hx
    exact h1.mul (h2.add (diffAt_deriv_gIter l hx))
  exact hdiff.congr_of_eventuallyEq hEq

/-- **Note 68, radial part.**  For `p ≠ 0` the function `u(r) = jₗ(p r)` is an
eigenfunction of the radial Laplacian in the sector of angular momentum `l`, with
eigenvalue `p²`:
`−(u''(r) + (2/r) u'(r) − (l(l+1)/r²) u(r)) = p² u(r)`. -/
theorem sbessel_radial_eigen (l : ℕ) {p r : ℝ} (hp : p ≠ 0) (hr : r ≠ 0) :
    -(deriv (deriv (fun s => sbessel l (p * s))) r
        + (2 / r) * deriv (fun s => sbessel l (p * s)) r
        - ((l : ℝ) * (l + 1) / r ^ 2) * sbessel l (p * r))
      = p ^ 2 * sbessel l (p * r) := by
  have hpr : p * r ≠ 0 := mul_ne_zero hp hr
  have hEq : deriv (fun s => sbessel l (p * s)) =ᶠ[nhds r]
      fun x => deriv (sbessel l) (p * x) * p := by
    filter_upwards [isOpen_ne.mem_nhds hr] with x hx using
      (hasDerivAt_sbessel_scaled l hp hx).deriv
  have hderiv2 : DifferentiableAt ℝ (deriv (sbessel l)) (p * r) := diffAt_deriv_sbessel l hpr
  have hc : HasDerivAt (fun s : ℝ => p * s) p r := by
    simpa using (hasDerivAt_id r).const_mul p
  have hD2 : HasDerivAt (fun x : ℝ => deriv (sbessel l) (p * x) * p)
      (deriv (deriv (sbessel l)) (p * r) * p * p) r :=
    (hderiv2.hasDerivAt.comp r hc).mul_const p
  have hsecond : deriv (deriv (fun s => sbessel l (p * s))) r
      = deriv (deriv (sbessel l)) (p * r) * p * p := by
    rw [hEq.deriv_eq, hD2.deriv]
  have hode := sbessel_ode l hpr
  rw [hsecond, (hasDerivAt_sbessel_scaled l hp hr).deriv]
  field_simp
  nlinarith [hode]

end BookProof.ChapterSphericalBesselODE
