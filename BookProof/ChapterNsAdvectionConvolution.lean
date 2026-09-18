import Mathlib

/-!
# The convolution algebra of the Navier–Stokes advection

Item 3 of the Navier–Stokes plan items of `CONSOLIDATED_PLAN.md`: *the convolution algebra*.  The
item asks for the momentum-space form of the nonlinearity, `Û_i(q) = 𝓕 u_i (q)` and the convolution
theorem

`ℱ[u_j ∂_j u_i](Q) = ∫ 2π i q_j Û_j(Q − q) Û_i(q) d q`,

which is the momentum-space replacement of the derivative-gauge generator `G_j`: the advection is
not a differential operator in momentum space but a convolution.

What is proved, for Schwartz velocity components on a finite-dimensional real inner-product space:

* `fourier_fourier_apply` — the double transform is the reflection, `𝓕(𝓕 f)(x) = f(−x)`;
* `fourier_mul_eq_convolution` — **the product-to-convolution theorem**
  `𝓕(f · g)(Q) = ∫ 𝓕f(q) 𝓕g(Q − q) dq`.  Mathlib has the convolution theorem in the other
  direction (`SchwartzMap.fourier_convolution`, `SchwartzMap.convolution_apply`); this is the dual
  statement, obtained from it by Fourier inversion;
* `fourier_lineDeriv_apply` — `𝓕(∂_m u)(q) = 2π i ⟪q, m⟫ 𝓕u(q)`, the derivative as a symbol;
* `fourier_advection_convolution` — **the item's convolution theorem** for one direction:
  `ℱ[u_j ∂_m u_i](Q) = ∫ 2π i ⟪q, m⟫ Û_i(q) Û_j(Q − q) dq`;
* `fourier_advection_sum` — the full advection `∑_j u_j ∂_{w_j} u_i` of a velocity field with
  respect to a finite family of directions, as the corresponding sum of convolutions.

The normalization is Mathlib's, `𝓕 f (ξ) = ∫ e^{−2π i ⟪x, ξ⟫} f(x) dx`, in which the convolution
theorem carries no `(2π)^{−d/2}` factors; the factor `2π i q_j` of the statement above is the exact
symbol of `∂_j` in that normalization.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.NsAdvectionConvolution

open MeasureTheory SchwartzMap FourierTransform Convolution LineDeriv

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

/-! ## 1. The double transform and the product-to-convolution theorem -/

/-- The Fourier transform applied twice is the reflection. -/
theorem fourier_fourier_apply (f : 𝓢(V, ℂ)) (x : V) :
    (𝓕 (𝓕 f : 𝓢(V, ℂ)) : 𝓢(V, ℂ)) x = f (-x) := by
  have h : (𝓕⁻ (𝓕 f : 𝓢(V, ℂ)) : 𝓢(V, ℂ)) = f := FourierTransform.fourierInv_fourier_eq f
  have h2 := congrArg (fun g : 𝓢(V, ℂ) => g (-x)) h
  simp only at h2
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg] at h2
  rw [← h2, neg_neg, SchwartzMap.fourier_coe]

/-- **The product-to-convolution theorem.**  The Fourier transform of a pointwise product of
Schwartz functions is the convolution of their transforms. -/
theorem fourier_mul_eq_convolution (f g : 𝓢(V, ℂ)) (Q : V) :
    𝓕 (fun x => f x * g x) Q = ∫ q, (𝓕 (f : V → ℂ)) q * (𝓕 (g : V → ℂ)) (Q - q) := by
  set A : 𝓢(V, ℂ) := 𝓕 f with hA
  set Bg : 𝓢(V, ℂ) := 𝓕 g with hB
  set C : 𝓢(V, ℂ) := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) A Bg with hC
  have hFC : (𝓕 C : 𝓢(V, ℂ))
      = SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 A) (𝓕 Bg) :=
    SchwartzMap.fourier_convolution _ A Bg
  have hFCpt : ∀ x, (𝓕 C : 𝓢(V, ℂ)) x = f (-x) * g (-x) := by
    intro x
    rw [hFC]
    simp only [SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply']
    rw [hA, hB, fourier_fourier_apply, fourier_fourier_apply]
  have hCQ : C Q = 𝓕 (fun x => f x * g x) Q := by
    have hinv : (𝓕⁻ (𝓕 C : 𝓢(V, ℂ)) : 𝓢(V, ℂ)) = C := FourierTransform.fourierInv_fourier_eq C
    have h1 : C Q = (𝓕⁻ (((𝓕 C : 𝓢(V, ℂ)) : V → ℂ))) Q := by
      rw [← SchwartzMap.fourierInv_coe, hinv]
    have h2 : (fun x : V => ((𝓕 C : 𝓢(V, ℂ)) : V → ℂ) (-x)) = fun x => f x * g x := by
      funext y
      rw [hFCpt (-y), neg_neg]
    rw [h1, Real.fourierInv_eq_fourier_comp_neg, h2]
  have hconv : C Q = ((A : V → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (Bg : V → ℂ)) Q :=
    SchwartzMap.convolution_apply _ A Bg Q
  rw [← hCQ, hconv, MeasureTheory.convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp [hA, hB, SchwartzMap.fourier_coe]

/-! ## 2. The derivative as a symbol -/

/-- The transform of a directional derivative is multiplication by `2π i ⟪q, m⟫`. -/
theorem fourier_lineDeriv_apply (ui : 𝓢(V, ℂ)) (m : V) (q : V) :
    (𝓕 ((∂_{m} ui : 𝓢(V, ℂ)) : V → ℂ)) q
      = (2 * Real.pi * Complex.I * ((inner ℝ q m : ℝ) : ℂ)) * (𝓕 (ui : V → ℂ)) q := by
  have h2 := congrArg (fun g : 𝓢(V, ℂ) => g q) (SchwartzMap.fourier_lineDerivOp_eq ui m)
  simp only [SchwartzMap.smul_apply, smul_eq_mul] at h2
  rw [← SchwartzMap.fourier_coe, ← SchwartzMap.fourier_coe, h2]
  have hg : (inner ℝ · m : V → ℝ).HasTemperateGrowth := ((innerSL ℝ).flip m).hasTemperateGrowth
  simp only [smulLeftCLM_apply hg, Complex.real_smul]
  ring

/-! ## 3. The advection as a convolution -/

/-- **The convolution theorem for the advection.**  In momentum space the nonlinearity
`u_j ∂_m u_i` is the convolution `∫ 2π i ⟪q, m⟫ Û_i(q) Û_j(Q − q) dq` — no derivative appears, only
the symbol `2π i ⟪q, m⟫` inside the convolution integral. -/
theorem fourier_advection_convolution (uj ui : 𝓢(V, ℂ)) (m : V) (Q : V) :
    𝓕 (fun x => uj x * (∂_{m} ui : 𝓢(V, ℂ)) x) Q
      = ∫ q, (2 * Real.pi * Complex.I * ((inner ℝ q m : ℝ) : ℂ)) *
          ((𝓕 (ui : V → ℂ)) q * (𝓕 (uj : V → ℂ)) (Q - q)) := by
  have hcomm : (fun x => uj x * (∂_{m} ui : 𝓢(V, ℂ)) x)
      = fun x => (∂_{m} ui : 𝓢(V, ℂ)) x * uj x := by
    funext x
    ring
  rw [hcomm, fourier_mul_eq_convolution]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [fourier_lineDeriv_apply, mul_assoc]

/-- The full advection `∑_j u_j ∂_{w_j} u_i` of a velocity field, in momentum space. -/
theorem fourier_advection_sum (u : ι → 𝓢(V, ℂ)) (w : ι → V) (ui : 𝓢(V, ℂ)) (Q : V) :
    𝓕 (fun x => ∑ j, u j x * (∂_{w j} ui : 𝓢(V, ℂ)) x) Q
      = ∑ j, ∫ q, (2 * Real.pi * Complex.I * ((inner ℝ q (w j) : ℝ) : ℂ)) *
          ((𝓕 (ui : V → ℂ)) q * (𝓕 ((u j : 𝓢(V, ℂ)) : V → ℂ)) (Q - q)) := by
  set S : 𝓢(V, ℂ) :=
    ∑ j, SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (u j) (∂_{w j} ui) with hS
  have hSfun : (fun x => ∑ j, u j x * (∂_{w j} ui : 𝓢(V, ℂ)) x) = (S : V → ℂ) := by
    funext x
    rw [hS]
    simp [SchwartzMap.pairing_apply_apply]
  have hFS : (𝓕 S : 𝓢(V, ℂ))
      = ∑ j, (𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (u j)
          (∂_{w j} ui)) : 𝓢(V, ℂ)) := by
    rw [hS]
    exact map_sum (SchwartzMap.fourierTransformCLM ℂ) _ _
  rw [hSfun, ← SchwartzMap.fourier_coe, hFS, SchwartzMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [SchwartzMap.fourier_coe]
  have hpair : ((SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (u j)
      (∂_{w j} ui) : 𝓢(V, ℂ)) : V → ℂ) = fun x => u j x * (∂_{w j} ui : 𝓢(V, ℂ)) x := by
    funext x
    simp [SchwartzMap.pairing_apply_apply]
  rw [hpair]
  exact fourier_advection_convolution (u j) ui (w j) Q

end

end BookProof.NsAdvectionConvolution
