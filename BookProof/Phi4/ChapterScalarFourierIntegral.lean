import BookProof.ChapterNsAdvectionConvolution
import BookProof.Phi4.ChapterScalarMomentumGap

/-!
# Continuous Fourier identities for the scalar λφ⁴ model

This chapter records the continuous momentum-space facts behind the gradient term
`½ |k|² φ²` and the quartic composite of the scalar model.  Every integral is over
the continuous momentum space `V`; there is no discrete momentum sum and no jet
constraint.

The spatial derivative is carried to multiplication by the symbol `2π i ⟪k, m⟫`
(`fourier_grad_sq_identity`), and the pointwise square and fourth power are carried
to convolution integrals over `V`
(`psiField_eq_fourier_mul`, `fourier_phi4_composite_integral`).
-/

namespace BookProof.Phi4

open MeasureTheory SchwartzMap FourierTransform
open BookProof.NsAdvectionConvolution LineDeriv

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The transform of a directional derivative is the symbol `2π i ⟪k, m⟫`; hence
the squared gradient is diagonal multiplication by `(2π ⟪k, m⟫)²`. -/
theorem fourier_grad_sq_identity (φ : 𝓢(V, ℂ)) (m k : V) :
    ‖(𝓕 ((∂_{m} φ : 𝓢(V, ℂ)) : V → ℂ)) k‖ ^ 2 =
      (2 * Real.pi * inner ℝ k m) ^ 2 * ‖(𝓕 (φ : V → ℂ)) k‖ ^ 2 := by
  rw [fourier_lineDeriv_apply]
  have hcoef : ‖(2 * Real.pi * Complex.I * ((inner ℝ k m : ℝ) : ℂ) : ℂ)‖ =
      2 * Real.pi * |inner ℝ k m| := by
    rw [show (2 * Real.pi * Complex.I * ((inner ℝ k m : ℝ) : ℂ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((inner ℝ k m : ℝ) : ℂ) by push_cast; ring]
    rw [norm_mul, norm_mul]
    have h2 : ‖((2 * Real.pi : ℝ) : ℂ)‖ = 2 * Real.pi := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    rw [h2, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
    ring
  rw [norm_mul, hcoef, mul_pow]
  rw [show (2 * Real.pi * |inner ℝ k m|) ^ 2 =
      (2 * Real.pi) ^ 2 * |inner ℝ k m| ^ 2 by ring]
  rw [sq_abs]
  ring

/-- The continuous momentum-space square of a Schwartz field:
`psiField φ Q = ∫ p, φ̂(p) φ̂(Q − p)`. -/
def psiField (φ : 𝓢(V, ℂ)) (Q : V) : ℂ :=
  ∫ p, (𝓕 (φ : V → ℂ)) p * (𝓕 (φ : V → ℂ)) (Q - p)

/-- The convolution integral is exactly the Fourier transform of the pointwise
square. -/
theorem psiField_eq_fourier_mul (φ : 𝓢(V, ℂ)) (Q : V) :
    psiField φ Q = 𝓕 (fun x => φ x * φ x) Q :=
  (fourier_mul_eq_convolution φ φ Q).symm

/-- The bundled Schwartz square of a field. -/
def phiSq (φ : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) φ φ

@[simp] theorem phiSq_apply (φ : 𝓢(V, ℂ)) (x : V) :
    phiSq φ x = φ x * φ x := by
  simp [phiSq, SchwartzMap.pairing_apply_apply]

/-- The bundled Schwartz fourth power of a field. -/
def phiFourth (φ : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (phiSq φ) (phiSq φ)

@[simp] theorem phiFourth_apply (φ : 𝓢(V, ℂ)) (x : V) :
    phiFourth φ x = φ x ^ 4 := by
  simp [phiFourth, phiSq, SchwartzMap.pairing_apply_apply]
  ring

/-- The fourth power is the continuous convolution square of `psiField`. -/
theorem fourier_phi4_composite_integral (φ : 𝓢(V, ℂ)) (R : V) :
    𝓕 (phiFourth φ) R = ∫ Q, psiField φ Q * psiField φ (R - Q) := by
  have hfour : (phiFourth φ : V → ℂ) = fun x => phiSq φ x * phiSq φ x := by
    funext x
    rw [phiFourth_apply, phiSq_apply]
    ring
  have hsq : (phiSq φ : V → ℂ) = fun x => φ x * φ x := by
    funext x
    rw [phiSq_apply]
  change (𝓕 (fun x => phiSq φ x * phiSq φ x) : V → ℂ) R = _
  rw [fourier_mul_eq_convolution]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Q => ?_)
  simp only [hsq]
  change 𝓕 (fun x => φ x * φ x) Q * 𝓕 (fun x => φ x * φ x) (R - Q) =
    psiField φ Q * psiField φ (R - Q)
  rw [← psiField_eq_fourier_mul, ← psiField_eq_fourier_mul]

end

end BookProof.Phi4
