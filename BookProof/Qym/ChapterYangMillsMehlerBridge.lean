import Mathlib
import BookProof.Qym.ChapterYangMillsAbelianNoGap

/-!
# S0: the Mehler/Gaussian representation bridge, and the S2 target signature

`softmodes.md` (work package S0) asks for the representation bridge before anything is bounded, and
its "Corrections" section makes one demand concrete: *prove the conjugation identity for the actual
momentum convention before comparing forms*, because the Gaussian representation change is unitary
and therefore says nothing about confinement by itself.  This module supplies that half of S0 and
fixes the S2 theorem signature.

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

* **U:** `gaussRoot_sq`, `hasDerivAt_gaussRoot`, `deriv_gaussRoot`, `gaussRoot_vacuum`,
  `hasDerivAt_invGauss_mul`, `conj_deriv`, `hasDerivAt_deriv_gaussRoot`,
  `gaussRoot_oscillator_ground`.
* **C:** the second-order core identity `U (−∂² + x∂) U⁻¹ = −∂² + x²/4 − 1/2` on a dense core, and
  the product version over all `99` coordinates.  What is proved below is its ingredient: the
  ground state with its eigenvalue, and the first-order identity.  The product statement follows by
  applying the one-coordinate identity coordinatewise, which the corpus's `99 = 3 + 24 + 72`
  coordinate split (`idxA`, `idxD`) supports but which is not assembled here.
* **B:** the module is one-dimensional analysis plus one abstract linear-algebra statement.  It does
  not identify the inner Hilbert space, does not construct a form core, and makes no spectral claim
  about `h`.

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

end

end BookProof.YangMillsMehlerBridge
