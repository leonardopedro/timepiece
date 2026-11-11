import Mathlib
import BookProof.Qym.ChapterYangMillsAbelianNoGap

/-!
# S0: the Mehler/Gaussian representation bridge, and the S2 target signature

`softmodes.md` (work package S0) asks for the representation bridge before anything is bounded, and
its "Corrections" section makes one demand concrete: *prove the conjugation identity for the actual
momentum convention before comparing forms*, because the Gaussian representation change is unitary
and therefore says nothing about confinement by itself.  This module supplies that half of S0 — the
first- and second-order conjugation identities, the invariance of multiplication operators and the
norm identity — and fixes the S2 theorem signature.

## The bridge, in one coordinate

Write `γ x = exp(−x²/2)` for the Mehler (standard Gaussian) density and `γ^{1/2} x = exp(−x²/4)` for
its square root, `gaussRoot` here.  The representation change is multiplication by `γ^{1/2}`,

  `U f = γ^{1/2} · f`,  `U⁻¹ f = γ^{-1/2} · f`,

which is a unitary `L²(γ) → L²(dx)` because `(γ^{1/2})² = γ` (`gaussRoot_sq`).  The two identities
that the plan asks for are then

* **momentum.** `U ∂ U⁻¹ = ∂ + x/2` (`conj_deriv`).  Consequently the annihilation operator
  `a = ∂ + x/2` kills the weight (`gaussRoot_vacuum`), which is what makes `u = a† + a` and
  `π = i(a† − a)` the right convention for the *Gaussian* form — the convention the corpus's
  `momOp` uses, `momOp j = −i • (pderiv_j − ½ X_j ·)`;
* **the Dirichlet operator is an oscillator.** `U (∂*∂) U⁻¹ = −∂² + x²/4 − 1/2`
  (`gaussRoot_oscillator_ground` records the ground state `γ^{1/2}` and its eigenvalue `0`).

The second identity is the plan's "N — Gaussian representation is not confinement" corrected into a
statement: the Gaussian Dirichlet operator really is unitarily the oscillator, so its gap `1/2` is
the *reference* gap `href_spectral_gap` and never a gap of the Yang–Mills form.  Nothing here is a
claim about `q_h`; what changes under the transform is the derivative, not the multiplication
operator — which is exactly why the magnetic field `B = ε ∂ A` needs a separate estimate.

## What is proved and what is not

* **U — weights and first order:** `gaussRoot_sq`, `hasDerivAt_gaussRoot`, `deriv_gaussRoot`,
  `gaussRoot_vacuum`, `hasDerivAt_invGauss_mul`, **`conj_deriv`** (`U ∂ U⁻¹ = ∂ + x/2`),
  `hasDerivAt_deriv_gaussRoot`, `gaussRoot_oscillator_ground`.
* **U — second order:** **`conj_dirichlet`** is `U (−∂² + x∂) U⁻¹ = −∂² + x²/4 − 1/2` for any `f`
  with two derivatives, and **`conj_dirichlet_smooth`** is the same on the smooth core, where the
  derivatives are `deriv f` and `deriv (deriv f)`.  The proof is `conj_deriv` applied twice: the
  drift `x/2` in the first-order identity is exactly what supplies the `x²/4`, and its derivative
  supplies the `−1/2`.
* **U — multiplication:** **`conj_mult`** (`U (mult V) U⁻¹ = mult V`) and **`conj_mult_deriv`** (a
  potential is not differentiated by the drift).  These are the reason a magnetic term cannot be
  produced or destroyed by the representation change, which is the plan's
  "N — Gaussian representation is not confinement" as a pair of identities.
* **U — norm:** **`lintegral_norm_sq_conj`** is the squared form of the isometry,
  `∫ |γ^{1/2} f|² dx = ∫ |f|² d(γ dx)`, with `γ dx` realized as `volume.withDensity`.
* **C:** the product version over all `99` coordinates.  This does *not* follow by applying the
  one-coordinate identity coordinatewise: coordinatewise application covers only functions that
  depend on a single coordinate, while the `99`-coordinate statement needs the operator to be a sum
  of one-coordinate operators that survives the conjugation — either the tensor decomposition
  `U_{99} = ⨂_i U_i` on `⨂_i L²(γ)` with `D_{99} = Σ_i D_i` commuting with it, or the Laplacian
  Leibniz rule `Δ(gF) = gΔF + 2⟨∇g, ∇F⟩ + FΔg` together with the `d`-dimensional Gaussian identity
  `Δ γ^{1/2} = (|x|²/4 + d/2) γ^{1/2}`.  Neither is assembled here, so the coordinate-count factor
  `−99/2` is not proved in this module.
* **C — space level and extension inputs:** `lintegral_norm_sq_conj` is an identity of integrals,
  not the statement that multiplication by `γ^{1/2}` is a `LinearIsometryEquiv` between `Lp` spaces;
  and the module has no closability, form-core or Friedrichs-extension input.  The plan's S0
  acceptance list is exactly these: the closure of the Dirichlet form on the smooth core, the
  identification of its Friedrichs operator with `−Δ + x·∇` on the weighted space, and the same for
  the `99`-coordinate sum.  They are *inputs*, not consequences of the identities above.
* **B:** the module is one-dimensional analysis plus abstract linear algebra.  It does not identify
  the inner Hilbert space, does not construct a form core, and makes no spectral claim about `h`.

## The S2 signature

`HasOneParticleFormGap` is the target-1 statement as a named `Prop` on the concrete Gauss-polynomial
core, so that S2 has a signature to aim at instead of an anonymous `∀`.  Two checks keep it honest:
`abelian_no_one_particle_form_gap` shows it is *false* for the abelian instance (so S2 is not a
trivially true wrapper), and `no_absolute_gap_of_kernel_vector` records the plan's own warning that
target 2 does not imply target 1: any nonzero vector in the kernel of `h` defeats an absolute
constant, which is why an inner zero mode is a non-vacuum outer one-particle state rather than
something to be subtracted away.
-/

namespace BookProof.YangMillsMehlerBridge

open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.HermiteGalerkin
  BookProof.FarisLavine
open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

/-! ## The Gaussian root -/

/-- The square root of the Mehler density: `γ^{1/2}(x) = exp(−x²/4)`. -/
def gaussRoot (x : ℝ) : ℝ := Real.exp (-(x ^ 2) / 4)

/-- Its reciprocal, which is the multiplication by `γ^{-1/2}` of `U⁻¹`. -/
def invGauss (x : ℝ) : ℝ := Real.exp (x ^ 2 / 4)

theorem gaussRoot_pos (x : ℝ) : 0 < gaussRoot x := Real.exp_pos _

/-- `(γ^{1/2})² = γ`: this is what makes `U` an isometry onto `L²(dx)`. -/
theorem gaussRoot_sq (x : ℝ) : gaussRoot x ^ 2 = Real.exp (-(x ^ 2) / 2) := by
  rw [gaussRoot, sq, ← Real.exp_add]
  congr 1
  ring

theorem gaussRoot_mul_invGauss (x : ℝ) : gaussRoot x * invGauss x = 1 := by
  rw [gaussRoot, invGauss, ← Real.exp_add, show -(x ^ 2) / 4 + x ^ 2 / 4 = 0 by ring,
    Real.exp_zero]

theorem invGauss_mul_gaussRoot (x : ℝ) : invGauss x * gaussRoot x = 1 := by
  rw [mul_comm, gaussRoot_mul_invGauss]

/-- The derivative of the Gaussian root. -/
theorem hasDerivAt_gaussRoot (x : ℝ) :
    HasDerivAt gaussRoot (-(x / 2) * gaussRoot x) x := by
  have hinner : HasDerivAt (fun y : ℝ => -(y ^ 2) / 4) (-(x / 2)) x := by
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x)
    have h3 : HasDerivAt (fun y : ℝ => -(y ^ 2)) (-(2 * x)) x := h2.neg
    have h4 : HasDerivAt (fun y : ℝ => -(y ^ 2) / 4) (-(2 * x) / 4) x := h3.div_const 4
    convert h4 using 1
    ring
  have hexp := hinner.exp
  have hval : Real.exp (-(x ^ 2) / 4) * (-(x / 2)) = -(x / 2) * gaussRoot x := by
    rw [gaussRoot]
    ring
  rw [hval] at hexp
  exact hexp

theorem deriv_gaussRoot (x : ℝ) : deriv gaussRoot x = -(x / 2) * gaussRoot x :=
  (hasDerivAt_gaussRoot x).deriv

/-- **The momentum convention, first half.**  `a = ∂ + x/2` annihilates the weight `γ^{1/2}`, so the
Gaussian is the vacuum of the convention `u = a† + a`, `π = i(a† − a)`. -/
theorem gaussRoot_vacuum (x : ℝ) : deriv gaussRoot x + (x / 2) * gaussRoot x = 0 := by
  rw [deriv_gaussRoot]
  ring

/-- The derivative of `γ^{-1/2}`. -/
theorem hasDerivAt_invGauss (x : ℝ) :
    HasDerivAt invGauss (x / 2 * invGauss x) x := by
  have hinner : HasDerivAt (fun y : ℝ => y ^ 2 / 4) (2 * x / 4) x := by
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x)
    exact h2.div_const 4
  have hexp := hinner.exp
  have hval : Real.exp (x ^ 2 / 4) * (2 * x / 4) = x / 2 * invGauss x := by
    rw [invGauss]
    ring
  rw [hval] at hexp
  exact hexp

/-! ## The momentum identity `U ∂ U⁻¹ = ∂ + x/2` -/

/-- **`U ∂ U⁻¹` on a differentiable function.**  Multiplying by `γ^{-1/2}`, differentiating, and
multiplying back by `γ^{1/2}` adds the drift `x/2`: this is `U ∂ U⁻¹ = ∂ + x/2`. -/
theorem hasDerivAt_invGauss_mul {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => invGauss y * f y)
      (invGauss x * (f' + (x / 2) * f x)) x := by
  have h := (hasDerivAt_invGauss x).mul hf
  convert h using 1
  ring

/-- **`U ∂ U⁻¹ = ∂ + x/2`, as an operator identity on differentiable functions.** -/
theorem conj_deriv {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    gaussRoot x * deriv (fun y => invGauss y * f y) x = f' + (x / 2) * f x := by
  rw [(hasDerivAt_invGauss_mul hf).deriv, ← mul_assoc, gaussRoot_mul_invGauss, one_mul]

/-! ## The second-order identity: the Dirichlet operator is the oscillator -/

/-- The second derivative of the Gaussian root, which is the oscillator eigenvalue equation. -/
theorem hasDerivAt_deriv_gaussRoot (x : ℝ) :
    HasDerivAt (fun y => deriv gaussRoot y) ((x ^ 2 / 4 - 1 / 2) * gaussRoot x) x := by
  have hfun : (fun y => deriv gaussRoot y) = fun y => -(y / 2) * gaussRoot y := by
    funext y
    rw [deriv_gaussRoot]
  rw [hfun]
  have hlin : HasDerivAt (fun y : ℝ => -(y / 2)) (-(1 / 2)) x := by
    have h : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := (hasDerivAt_id x).div_const 2
    simpa using h.neg
  have hmul := hlin.mul (hasDerivAt_gaussRoot x)
  convert hmul using 1
  ring

/-- **The Gaussian Dirichlet operator is the oscillator.**  `γ^{1/2}` is an eigenvector of
`−∂² + x²/4 − 1/2` with eigenvalue `0`: the reference gap `1/2` is the oscillator's, and the
Gaussian representation change does not produce a gap for anything else. -/
theorem gaussRoot_oscillator_ground (x : ℝ) :
    -(deriv (fun y => deriv gaussRoot y) x) + x ^ 2 / 4 * gaussRoot x
        - (1 / 2) * gaussRoot x = 0 := by
  rw [(hasDerivAt_deriv_gaussRoot x).deriv]
  ring

/-! ## The second-order identity `U (−∂² + x∂) U⁻¹ = −∂² + x²/4 − 1/2` -/

/-- The weighted Dirichlet operator of the Gaussian measure, in one coordinate: the plan's
`∂*∂ = −∂² + x∂`.  The drift is `∇ log γ = −x`, so `∂` has `L²(γ)`-adjoint `−∂ + x` at the level of
functions and `∂*∂ = −∂² + x∂`. -/
def gaussDirichlet (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => -(deriv (fun y => deriv f y) x) + x * deriv f x

/-- **The second-order conjugation identity.**  Conjugating the weighted Dirichlet operator
`−∂² + x∂` by `U f = γ^{1/2} f` gives the oscillator `−∂² + x²/4 − 1/2`.

The proof is `conj_deriv` twice, and that is the point the plan makes: the first application turns
`U ∂ U⁻¹` into `∂ + x/2`, so the drift `x∂` of `∂*∂` is what supplies the `x²/4`, and the `−1/2`
comes from the derivative of the drift.  Nothing here involves the potential: the identity is a
statement about derivatives only, which is why a magnetic term cannot be obtained from it. -/
theorem conj_dirichlet {f f' f'' : ℝ → ℝ} (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf' : ∀ y, HasDerivAt f' (f'' y) y) (x : ℝ) :
    gaussRoot x * gaussDirichlet (fun z => invGauss z * f z) x
      = -f'' x + (x ^ 2 / 4 - 1 / 2) * f x := by
  have hfirst : ∀ y, deriv (fun z => invGauss z * f z) y
      = invGauss y * (f' y + (y / 2) * f y) := by
    intro y
    have h : gaussRoot y * deriv (fun z => invGauss z * f z) y = f' y + (y / 2) * f y :=
      conj_deriv (hf y)
    calc deriv (fun z => invGauss z * f z) y
        = invGauss y * (gaussRoot y * deriv (fun z => invGauss z * f z) y) := by
          rw [← mul_assoc, invGauss_mul_gaussRoot, one_mul]
      _ = invGauss y * (f' y + (y / 2) * f y) := by rw [h]
  have hF' : ∀ y, HasDerivAt (fun z => f' z + (z / 2) * f z)
      (f'' y + ((1 / 2) * f y + (y / 2) * f' y)) y := by
    intro y
    have hlin : HasDerivAt (fun z : ℝ => z / 2) (1 / 2) y := (hasDerivAt_id y).div_const 2
    have hprod : HasDerivAt (fun z => (z / 2) * f z) ((1 / 2) * f y + (y / 2) * f' y) y :=
      hlin.mul (hf y)
    have hsum := (hf' y).add hprod
    simpa only [Pi.add_apply] using hsum
  have hsecond : deriv (fun y => deriv (fun z => invGauss z * f z) y) x
      = deriv (fun y => invGauss y * (f' y + (y / 2) * f y)) x := by
    rw [funext hfirst]
  have h1 : gaussRoot x * deriv (fun z => invGauss z * f z) x = f' x + (x / 2) * f x :=
    conj_deriv (hf x)
  have h2 : gaussRoot x * deriv (fun y => invGauss y * (f' y + (y / 2) * f y)) x
      = (f'' x + ((1 / 2) * f x + (x / 2) * f' x)) + (x / 2) * (f' x + (x / 2) * f x) :=
    conj_deriv (hF' x)
  simp only [gaussDirichlet, hsecond]
  have hexpand : gaussRoot x *
      (-(deriv (fun y => invGauss y * (f' y + (y / 2) * f y)) x) +
        x * deriv (fun z => invGauss z * f z) x)
      = -(gaussRoot x * deriv (fun y => invGauss y * (f' y + (y / 2) * f y)) x) +
        x * (gaussRoot x * deriv (fun z => invGauss z * f z) x) := by
    ring
  rw [hexpand, h2, h1]
  ring

/-- **The second-order identity on the smooth core.**  For a smooth `f` the two derivatives are
`deriv f` and `deriv (deriv f)`, so the abstract statement above reads exactly as the plan writes
it: `U (−∂² + x∂) U⁻¹ f = −f'' + (x²/4 − 1/2) f`. -/
theorem conj_dirichlet_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (x : ℝ) :
    gaussRoot x * gaussDirichlet (fun z => invGauss z * f z) x
      = -deriv (fun y => deriv f y) x + (x ^ 2 / 4 - 1 / 2) * f x := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hd2 : Differentiable ℝ (deriv f) := (hf.of_le (le_top)).differentiable_deriv_two
  exact conj_dirichlet (fun y => (hd y).hasDerivAt) (fun y => (hd2 y).hasDerivAt) x

/-! ## Multiplication operators are fixed by the conjugation -/

/-- **The conjugation does not touch a potential.**  `U (mult V) U⁻¹ = mult V`: multiplication by
`γ^{1/2}` and its inverse cancel, so a multiplication operator — in particular the magnetic term
`½|B|²`, which is a function of `A`, not of `∂` — is transported to itself.  This is the exact
content of the plan's "N — Gaussian representation is not confinement": the representation change
can create the oscillator `x²/4` out of the *derivative*, and cannot move a magnetic gap, in either
direction. -/
theorem conj_mult (V f : ℝ → ℝ) (x : ℝ) :
    gaussRoot x * (V x * (invGauss x * f x)) = V x * f x := by
  calc gaussRoot x * (V x * (invGauss x * f x))
      = V x * (gaussRoot x * invGauss x) * f x := by ring
    _ = V x * f x := by rw [gaussRoot_mul_invGauss]; ring

/-- The mixed case: the Dirichlet operator of a multiplication operator is `x` times its gradient,
so `U(V ·)U⁻¹` keeps `V` and gains no drift — the drift `x/2` of `conj_deriv` multiplies `V`, it
does not differentiate it. -/
theorem conj_mult_deriv {V f : ℝ → ℝ} (hV : ∀ y, HasDerivAt V (deriv V y) y) {f' x : ℝ}
    (hf : HasDerivAt f f' x) :
    gaussRoot x * deriv (fun y => V y * (invGauss y * f y)) x
      = V x * (f' + (x / 2) * f x) + deriv V x * f x := by
  have h := (hV x).mul (hasDerivAt_invGauss_mul hf)
  have hmul : HasDerivAt (fun y => V y * (invGauss y * f y))
      (deriv V x * (invGauss x * f x) + V x * (invGauss x * (f' + (x / 2) * f x))) x :=
    h
  rw [hmul.deriv]
  have h2 : gaussRoot x * (V x * (invGauss x * (f' + (x / 2) * f x)))
      = V x * (f' + (x / 2) * f x) := conj_mult V (fun _ => f' + (x / 2) * f x) x
  have hexp : gaussRoot x *
      (deriv V x * (invGauss x * f x) + V x * (invGauss x * (f' + (x / 2) * f x)))
      = deriv V x * (gaussRoot x * (invGauss x * f x)) +
        gaussRoot x * (V x * (invGauss x * (f' + (x / 2) * f x))) := by
    ring
  rw [hexp, h2]
  have h3 : gaussRoot x * (invGauss x * f x) = f x := by
    rw [← mul_assoc, gaussRoot_mul_invGauss, one_mul]
  rw [h3]
  ring

/-! ## The norm identity: `U` is an isometry `L²(γ dx) → L²(dx)` -/

/-- **The norm identity**, in squared form: multiplying by `γ^{1/2}` moves the density from the
function to the measure, `∫ |γ^{1/2} f|² dx = ∫ |f|² d(γ dx)`.  This is the "norm" arrow of the S0
diagram, and it is why `U` is a *unitary* between `L²(γ dx)` and `L²(dx)` rather than a map with a
constant: the two spaces are isometric, so no estimate can be transported from one to the other
with a gain. -/
theorem lintegral_norm_sq_conj {f : ℝ → ℝ} (hf : Measurable f) :
    ∫⁻ x, ENNReal.ofReal ((gaussRoot x * f x) ^ 2) ∂(volume : Measure ℝ)
      = ∫⁻ x, ENNReal.ofReal (f x ^ 2)
          ∂((volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (gaussRoot x ^ 2))) := by
  have hdens : Measurable (fun x : ℝ => ENNReal.ofReal (gaussRoot x ^ 2)) := by
    have hcont : Continuous fun x : ℝ => gaussRoot x ^ 2 := by
      unfold gaussRoot
      fun_prop
    exact ENNReal.measurable_ofReal.comp hcont.measurable
  have hg : Measurable (fun x : ℝ => ENNReal.ofReal (f x ^ 2)) := by
    have hsq : Measurable fun x : ℝ => f x ^ 2 := by
      simpa only [pow_two] using hf.mul hf
    exact ENNReal.measurable_ofReal.comp hsq
  have hkey := lintegral_withDensity_eq_lintegral_mul (volume : Measure ℝ)
    (f := fun x => ENNReal.ofReal (gaussRoot x ^ 2)) hdens
    (g := fun x => ENNReal.ofReal (f x ^ 2)) hg
  rw [hkey]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  show ENNReal.ofReal ((gaussRoot x * f x) ^ 2)
      = ENNReal.ofReal (gaussRoot x ^ 2) * ENNReal.ofReal (f x ^ 2)
  rw [← ENNReal.ofReal_mul (by positivity), mul_pow]

/-! ## The normalization constant: `∫ γ dx = √(2π)` -/

/-- The Mehler density is **not** normalized: `∫ γ dx = √(2π)`, not `1`.  This is the
"normalized/unnormalized measure convention" the work package asks to fix before any frequency or
number-form comparison, and it is the constant `√(2π)` that a comparison against a Gaussian-measure
reference has to carry. -/
theorem integral_gaussRoot_sq :
    ∫ x, gaussRoot x ^ 2 ∂(volume : Measure ℝ) = Real.sqrt (2 * Real.pi) := by
  have hfun : ∫ x, gaussRoot x ^ 2 ∂(volume : Measure ℝ)
      = ∫ x, Real.exp (-(1 / 2) * x ^ 2) ∂(volume : Measure ℝ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [gaussRoot, pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hfun, integral_gaussian]
  congr 1
  ring

/-- The same constant in `ℝ≥0∞`, in the form used by the measure-density identities. -/
theorem lintegral_gaussRoot_sq :
    ∫⁻ x, ENNReal.ofReal (gaussRoot x ^ 2) ∂(volume : Measure ℝ)
      = ENNReal.ofReal (Real.sqrt (2 * Real.pi)) := by
  have hint : Integrable (fun x : ℝ => gaussRoot x ^ 2) (volume : Measure ℝ) := by
    refine Integrable.congr (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [gaussRoot, pow_two, ← Real.exp_add]
    congr 1
    ring
  have h := ofReal_integral_eq_lintegral_ofReal (μ := (volume : Measure ℝ))
    (f := fun x => gaussRoot x ^ 2) hint (Filter.Eventually.of_forall fun x => by positivity)
  rw [integral_gaussRoot_sq] at h
  exact h.symm

/-- **The normalized density has unit mass.**  Dividing by `√(2π)` turns the Mehler density into a
probability density; this is the correction factor every comparison with a normalized Gaussian
reference must apply. -/
theorem lintegral_normalized_eq_one :
    ∫⁻ x, ENNReal.ofReal (gaussRoot x ^ 2) * (ENNReal.ofReal (Real.sqrt (2 * Real.pi)))⁻¹
      ∂(volume : Measure ℝ) = 1 := by
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (gaussRoot x ^ 2) := by
    have hc : Continuous fun x : ℝ => gaussRoot x ^ 2 := by
      unfold gaussRoot
      fun_prop
    exact ENNReal.measurable_ofReal.comp hc.measurable
  rw [lintegral_mul_const _ hmeas, lintegral_gaussRoot_sq]
  refine ENNReal.mul_inv_cancel ?_ ?_
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.sqrt_pos.mpr (by positivity)
  · exact ENNReal.ofReal_ne_top

/-! ## The `n`-coordinate transfer

S2 asks for the 99-coordinate product, not just the one-coordinate identity.  Nothing in the
argument above is one-dimensional: the weight is a product, so the conjugation, the invariance of
multiplication operators and the isometry all tensorize with the same proofs, and the `n = 99` case
is the one the QYM mode space uses. -/

/-- The `n`-coordinate Gaussian root, `γ^{1/2}(x) = exp(−‖x‖²/4)`. -/
noncomputable def gaussRootN {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.exp (-(∑ i, x i ^ 2) / 4)

/-- Its reciprocal, `γ^{-1/2}`. -/
noncomputable def invGaussN {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.exp ((∑ i, x i ^ 2) / 4)

/-- The `n`-coordinate root is the product of the one-coordinate roots — the multiplicativity that
makes the 99-coordinate transfer a tensor product rather than a new calculation. -/
theorem gaussRootN_eq_prod {n : ℕ} (x : Fin n → ℝ) :
    (∏ i, gaussRoot (x i)) = gaussRootN x := by
  have hprod : (∏ i, gaussRoot (x i)) = ∏ i, Real.exp (-(x i ^ 2) / 4) :=
    Finset.prod_congr rfl fun i _ => by rw [gaussRoot]
  rw [hprod, gaussRootN, ← Real.exp_sum]
  congr 1
  rw [← Finset.sum_neg_distrib, ← Finset.sum_div]

/-- Squares of the `n`-coordinate root multiply to the Mehler density. -/
theorem gaussRootN_sq {n : ℕ} (x : Fin n → ℝ) :
    gaussRootN x ^ 2 = Real.exp (-(∑ i, x i ^ 2) / 2) := by
  rw [gaussRootN, pow_two, ← Real.exp_add]
  congr 1
  rw [← add_div]
  ring

theorem gaussRootN_pos {n : ℕ} (x : Fin n → ℝ) : 0 < gaussRootN x := Real.exp_pos _

theorem gaussRootN_mul_invGaussN {n : ℕ} (x : Fin n → ℝ) :
    gaussRootN x * invGaussN x = 1 := by
  rw [gaussRootN, invGaussN, ← Real.exp_add,
    show -(∑ i, x i ^ 2) / 4 + (∑ i, x i ^ 2) / 4 = 0 by ring, Real.exp_zero]

/-- A potential in `n` coordinates is likewise untouched by the conjugation. -/
theorem conj_mult_N {n : ℕ} (V F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    gaussRootN x * (V x * (invGaussN x * F x)) = V x * F x := by
  calc gaussRootN x * (V x * (invGaussN x * F x))
      = V x * (gaussRootN x * invGaussN x) * F x := by ring
    _ = V x * F x := by rw [gaussRootN_mul_invGaussN]; ring

/-- **The isometry in `n` coordinates**, which is the `n = 99` statement S2 asks for: multiplying
by `γ^{1/2}` moves the density from the function to the measure, with no constant lost. -/
theorem lintegral_norm_sq_conj_N {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : Measurable F) :
    ∫⁻ x, ENNReal.ofReal ((gaussRootN x * F x) ^ 2) ∂(volume : Measure (Fin n → ℝ))
      = ∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂((volume : Measure (Fin n → ℝ)).withDensity
          (fun x => ENNReal.ofReal (gaussRootN x ^ 2))) := by
  have hdens : Measurable (fun x : Fin n → ℝ => ENNReal.ofReal (gaussRootN x ^ 2)) := by
    have hcont : Continuous fun x : Fin n → ℝ => gaussRootN x ^ 2 := by
      unfold gaussRootN
      fun_prop
    exact ENNReal.measurable_ofReal.comp hcont.measurable
  have hg : Measurable (fun x : Fin n → ℝ => ENNReal.ofReal (F x ^ 2)) := by
    have hsq : Measurable fun x : Fin n → ℝ => F x ^ 2 := by
      simpa only [pow_two] using hF.mul hF
    exact ENNReal.measurable_ofReal.comp hsq
  have hkey := lintegral_withDensity_eq_lintegral_mul (volume : Measure (Fin n → ℝ))
    (f := fun x => ENNReal.ofReal (gaussRootN x ^ 2)) hdens
    (g := fun x => ENNReal.ofReal (F x ^ 2)) hg
  rw [hkey]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  show ENNReal.ofReal ((gaussRootN x * F x) ^ 2)
      = ENNReal.ofReal (gaussRootN x ^ 2) * ENNReal.ofReal (F x ^ 2)
  rw [← ENNReal.ofReal_mul (by positivity), mul_pow]

/-! ## The S2 signature and its two checks -/

/-- **Target 1 of the work package, as a named statement.**  The one-particle form is coercive on
the whole Gauss-polynomial core with constant `m`.  This is the input consumed by
`BookProof.YangMillsFockGapChain.ym_fock_mass_gap_of_one_particle_form_gap`, and it is what S2 must
deliver for the selected target; it is a `def` rather than an axiom so that no module can claim it
without proving it. -/
def HasOneParticleFormGap (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (m : ℝ) : Prop :=
  ∀ x : finiteModeDomain (coreBasis e),
    m * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x

/-- The signature is the abelian chapter's statement, unfolding the `def`. -/
theorem hasOneParticleFormGap_iff (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (m : ℝ) :
    HasOneParticleFormGap e fabc m ↔
      ∀ x : finiteModeDomain (coreBasis e),
        m * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x :=
  Iff.rfl

/-- **The signature is not vacuous.**  For the abelian structure constants no positive `m` satisfies
it, so S2 cannot be discharged by an empty constant: the structure constants are essential. -/
theorem abelian_no_one_particle_form_gap (e : ℕ ≃ (Fin 99 →₀ ℕ)) {m : ℝ} (hm : 0 < m) :
    ¬ HasOneParticleFormGap e (fun _ _ _ => (0 : ℝ)) m :=
  BookProof.YangMillsAbelianNoGap.ym_abelian_no_one_particle_form_gap e hm

/-- **Target 2 does not imply target 1.**  A nonzero vector in the kernel of `h` makes every
positive constant fail on the whole space, however well the form behaves on the orthogonal
complement of that zero mode.  This is the plan's warning in its sharpest form: an inner zero mode
is a non-vacuum zero-energy outer one-particle state, not a subtractable offset. -/
theorem no_absolute_gap_of_kernel_vector {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {h : E →ₗ[ℝ] E} {x₀ : E} (hx₀ : x₀ ≠ 0) (hker : h x₀ = 0) :
    ¬ ∃ m : ℝ, 0 < m ∧ ∀ u : E, m * ‖u‖ ^ 2 ≤ inner ℝ u (h u) := by
  rintro ⟨m, hm, hb⟩
  have hb0 : m * ‖x₀‖ ^ 2 ≤ 0 := by
    have h1 := hb x₀
    rw [hker, inner_zero_right] at h1
    exact h1
  have hnorm : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀
  nlinarith [pow_pos hnorm 2, hm]

/-! ## The derivative transfer in `n` coordinates

`conj_deriv` is the one-coordinate statement `U ∂ U⁻¹ = ∂ + x/2`.  On the `n`-coordinate mode
space the derivative is the coordinate derivative along a line, and the same identity holds there:
the weight factorizes, so the part of it outside the `j`-th coordinate cancels against itself and
leaves exactly the one-coordinate drift.  This is the derivative half of the 99-coordinate product
transfer; `lintegral_norm_sq_conj_N` above is the norm half. -/

/-- The squared norm of the coordinates other than `j`. -/
noncomputable def restSq {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i ∈ Finset.univ.erase j, x i ^ 2

theorem sum_sq_update {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    ∑ i, Function.update x j t i ^ 2 = t ^ 2 + restSq x j := by
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ j)]
  congr 1
  · simp
  · rw [Finset.sdiff_singleton_eq_erase, restSq]
    exact Finset.sum_congr rfl fun i hi => by simp [Finset.ne_of_mem_erase hi]

/-- The `n`-coordinate root along the `j`-th line is the one-coordinate root times the constant
carried by the other coordinates. -/
theorem gaussRootN_update {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    gaussRootN (Function.update x j t) = gaussRoot t * Real.exp (-(restSq x j) / 4) := by
  rw [gaussRootN, gaussRoot, sum_sq_update, ← Real.exp_add]
  congr 1
  ring

/-- The reciprocal weight along the `j`-th line. -/
theorem invGaussN_update {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    invGaussN (Function.update x j t) = invGauss t * Real.exp (restSq x j / 4) := by
  rw [invGaussN, invGauss, sum_sq_update, ← Real.exp_add]
  congr 1
  ring

/-- The value of the `n`-coordinate root at a point, split along coordinate `j`. -/
theorem gaussRootN_eq_root_mul_rest {n : ℕ} (x : Fin n → ℝ) (j : Fin n) :
    gaussRootN x = gaussRoot (x j) * Real.exp (-(restSq x j) / 4) :=
  by simpa [Function.update_eq_self] using gaussRootN_update x j (x j)

/-- **The derivative transfer in `n` coordinates**: conjugating the coordinate derivative `∂_j`
adds the drift `x_j / 2`, for every `n` — in particular for the `n = 99` mode space.  The inner
function is the conjugated one, `invGaussN · F`, exactly as on the core. -/
theorem conj_pderiv {n : ℕ} {F : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ) (j : Fin n) {d : ℝ}
    (hd : HasDerivAt (fun t => F (Function.update x j t)) d (x j)) :
    gaussRootN x * deriv (fun t => invGaussN (Function.update x j t)
        * F (Function.update x j t)) (x j) = d + (x j / 2) * F x := by
  have hfun : (fun t => invGaussN (Function.update x j t) * F (Function.update x j t))
      = fun t => Real.exp (restSq x j / 4) * (invGauss t * F (Function.update x j t)) := by
    funext t
    rw [invGaussN_update]
    ring
  rw [hfun]
  have hd' := (hasDerivAt_invGauss_mul hd).const_mul (Real.exp (restSq x j / 4))
  have hgg : gaussRoot (x j) * invGauss (x j) = 1 := gaussRoot_mul_invGauss (x j)
  have hEE : Real.exp (-(restSq x j) / 4) * Real.exp (restSq x j / 4) = 1 := by
    rw [← Real.exp_add]
    rw [show -(restSq x j) / 4 + restSq x j / 4 = 0 by ring]
    rw [Real.exp_zero]
  rw [hd'.deriv]
  rw [show F (Function.update x j (x j)) = F x by rw [Function.update_eq_self]]
  rw [gaussRootN_eq_root_mul_rest]
  calc gaussRoot (x j) * Real.exp (-(restSq x j) / 4) *
        (Real.exp (restSq x j / 4) * (invGauss (x j) * (d + (x j / 2) * F x)))
      = gaussRoot (x j) * invGauss (x j) *
          (Real.exp (-(restSq x j) / 4) * Real.exp (restSq x j / 4)) *
          (d + (x j / 2) * F x) := by ring
    _ = d + (x j / 2) * F x := by rw [hgg, hEE]; ring

/-! ## The core, as an explicit domain -/

/-- **The Gauss–polynomial core in `n` coordinates**, as an explicit domain: the functions
`p · γ^{1/2}` with `p` a polynomial in the `n` coordinates.  At `n = 99` this is the core the QYM
one-particle operator is defined on.  Density of this subspace in `L²(γ)` is *not* asserted here;
that is a separate hypothesis wherever it is needed. -/
def qymCore (n : ℕ) : Submodule ℝ ((Fin n → ℝ) → ℝ) where
  carrier := {φ | ∃ p : MvPolynomial (Fin n) ℝ, φ = fun x => MvPolynomial.eval x p * gaussRootN x}
  zero_mem' := ⟨0, by funext x; simp⟩
  add_mem' := by
    rintro φ ψ ⟨p, rfl⟩ ⟨q, rfl⟩
    refine ⟨p + q, ?_⟩
    funext x
    simp [MvPolynomial.eval_add, add_mul]
  smul_mem' := by
    rintro c φ ⟨p, rfl⟩
    refine ⟨MvPolynomial.C c * p, ?_⟩
    funext x
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C, Pi.smul_apply, smul_eq_mul]
    ring

/-- Membership in the core is exactly "a polynomial times the root". -/
theorem qymCore_mem {n : ℕ} {φ : (Fin n → ℝ) → ℝ} :
    φ ∈ qymCore n ↔
      ∃ p : MvPolynomial (Fin n) ℝ, φ = fun x => MvPolynomial.eval x p * gaussRootN x :=
  Iff.rfl

/-- The weight itself is in the core: it is the `p = 1` element. -/
theorem gaussRootN_mem_qymCore (n : ℕ) :
    (fun x : Fin n → ℝ => gaussRootN x) ∈ qymCore n :=
  ⟨1, by funext x; simp⟩

/-- **The second-order conjugation along one coordinate, on the core's coordinate.**  The weighted
Dirichlet operator of the `n`-coordinate Gaussian measure, restricted to the `j`-th line, conjugates
to the oscillator: `U (−∂² + x ∂) U⁻¹ = −∂² + x²/4 − 1/2`, with `x` the coordinate `x_j`.  The
rest of the `n`-coordinate weight cancels because it is constant along that line — which is why the
`n`-coordinate second-order statement needs no new analytic input. -/
theorem conj_gaussDirichlet_slice {n : ℕ} {F : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ) (j : Fin n)
    {d e : ℝ → ℝ} (hd : ∀ t, HasDerivAt (fun s => F (Function.update x j s)) (d t) t)
    (he : ∀ t, HasDerivAt d (e t) t) :
    gaussRootN x * gaussDirichlet
        (fun t => invGaussN (Function.update x j t) * F (Function.update x j t)) (x j)
      = -e (x j) + (x j ^ 2 / 4 - 1 / 2) * F x := by
  have hfun : (fun t => invGaussN (Function.update x j t) * F (Function.update x j t))
      = fun t => invGauss t * (Real.exp (restSq x j / 4) * F (Function.update x j t)) := by
    funext t
    rw [invGaussN_update]
    ring
  have hd' : ∀ t, HasDerivAt (fun s => Real.exp (restSq x j / 4) * F (Function.update x j s))
      (Real.exp (restSq x j / 4) * d t) t := fun t => (hd t).const_mul _
  have he' : ∀ t, HasDerivAt (fun s => Real.exp (restSq x j / 4) * d s)
      (Real.exp (restSq x j / 4) * e t) t := fun t => (he t).const_mul _
  have h1 := conj_dirichlet hd' he' (x j)
  rw [show Function.update x j (x j) = x from Function.update_eq_self j x] at h1
  have hEE : Real.exp (-(restSq x j) / 4) * Real.exp (restSq x j / 4) = 1 := by
    rw [← Real.exp_add, show -(restSq x j) / 4 + restSq x j / 4 = 0 by ring, Real.exp_zero]
  rw [hfun, gaussRootN_eq_root_mul_rest]
  calc gaussRoot (x j) * Real.exp (-(restSq x j) / 4) *
        gaussDirichlet
          (fun t => invGauss t * (Real.exp (restSq x j / 4) * F (Function.update x j t))) (x j)
      = Real.exp (-(restSq x j) / 4) *
        (gaussRoot (x j) *
          gaussDirichlet
            (fun t => invGauss t * (Real.exp (restSq x j / 4) * F (Function.update x j t)))
            (x j)) := by ring
    _ = -e (x j) + (x j ^ 2 / 4 - 1 / 2) * F x := by
        rw [h1]
        calc Real.exp (-(restSq x j) / 4) *
              (-(Real.exp (restSq x j / 4) * e (x j)) +
                (x j ^ 2 / 4 - 1 / 2) * (Real.exp (restSq x j / 4) * F x))
            = (Real.exp (-(restSq x j) / 4) * Real.exp (restSq x j / 4)) *
                (-e (x j) + (x j ^ 2 / 4 - 1 / 2) * F x) := by ring
          _ = -e (x j) + (x j ^ 2 / 4 - 1 / 2) * F x := by rw [hEE]; ring

/-! ## The bundled second-order conjugation in `n` coordinates

`conj_gaussDirichlet_slice` is the identity along one coordinate line.  Summing it over the `n`
coordinates gives the operator the QYM mode space actually uses: the `n`-coordinate weighted
Dirichlet operator `−Δ + x·∇`, conjugated by `U`, is the oscillator with the coordinate-count
factor `−n/2`.  That factor is the only place the number of coordinates enters, and it is why the
`n = 99` statement is not the one-coordinate statement: it is the sum of `99` copies of it. -/

/-- **The `n`-coordinate weighted Dirichlet operator, coordinate by coordinate**, applied to the
conjugated function `γ^{-1/2} F`: the sum over `j` of the one-coordinate `gaussDirichlet` along the
`j`-th line.  This is the operator whose conjugation the next theorem evaluates. -/
noncomputable def qymDirichletN {n : ℕ} (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ j, gaussDirichlet (fun t => invGaussN (Function.update x j t) * F (Function.update x j t)) (x j)

/-- The drift term: `∑_j (x_j²/4 − 1/2)` is `‖x‖²/4 − n/2`, the `n/2` being the `n` copies of the
`−1/2` of the one-coordinate identity. -/
theorem sum_oscillator_drift {n : ℕ} (x : Fin n → ℝ) (c : ℝ) :
    (∑ j, (x j ^ 2 / 4 - 1 / 2) * c) = ((∑ j, x j ^ 2) / 4 - n / 2) * c := by
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The second-order conjugation, bundled over the `n` coordinates.**  Conjugating the
`n`-coordinate weighted Dirichlet operator `−Δ + x·∇` by `U f = γ^{1/2} f` gives the
`n`-coordinate oscillator `−Δ + ‖x‖²/4 − n/2`:

  `U(−Δ + x·∇)U⁻¹ F(x) = −(∑_j e_j(x_j)) + (‖x‖²/4 − n/2) F(x)`,

where `e_j` is the second slice derivative of `F` along coordinate `j`.  The hypothesis is exactly
what the coordinate identity needs in each direction; on the core (`F` a polynomial) it holds.  At
`n = 99` this is the second-order half of the mode-space transfer, the first-order half being
`conj_pderiv`. -/
theorem conj_gaussDirichlet_bundled {n : ℕ} {F : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ)
    {d e : Fin n → ℝ → ℝ}
    (hd : ∀ (j : Fin n) (t : ℝ), HasDerivAt (fun s => F (Function.update x j s)) (d j t) t)
    (he : ∀ (j : Fin n) (t : ℝ), HasDerivAt (d j) (e j t) t) :
    gaussRootN x * qymDirichletN F x
      = -(∑ j, e j (x j)) + ((∑ j, x j ^ 2) / 4 - n / 2) * F x := by
  have hterm : ∀ j : Fin n, gaussRootN x *
      gaussDirichlet (fun t => invGaussN (Function.update x j t) * F (Function.update x j t)) (x j)
      = -e j (x j) + (x j ^ 2 / 4 - 1 / 2) * F x := fun j =>
    conj_gaussDirichlet_slice x j (hd j) (he j)
  rw [qymDirichletN, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun j _ => hterm j).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, sum_oscillator_drift]

/-- **The core's second-order conjugation, in the shape the mode space uses**: for a function whose
slice derivatives are the given `d` and `e`, the conjugated operator is the oscillator with the
`99`-coordinate factor.  This is the same statement at `n = 99`, written with `‖x‖²` expanded. -/
theorem conj_gaussDirichlet_bundled_99 {F : (Fin 99 → ℝ) → ℝ} (x : Fin 99 → ℝ)
    {d e : Fin 99 → ℝ → ℝ}
    (hd : ∀ (j : Fin 99) (t : ℝ), HasDerivAt (fun s => F (Function.update x j s)) (d j t) t)
    (he : ∀ (j : Fin 99) (t : ℝ), HasDerivAt (d j) (e j t) t) :
    gaussRootN x * qymDirichletN F x
      = -(∑ j, e j (x j)) + ((∑ j, x j ^ 2) / 4 - 99 / 2) * F x :=
  conj_gaussDirichlet_bundled x hd he

end

end BookProof.YangMillsMehlerBridge
