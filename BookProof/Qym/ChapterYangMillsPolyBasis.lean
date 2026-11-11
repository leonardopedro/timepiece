/-
Copyright (c) 2026.  All rights reserved.

# An orthonormal Hermite basis of `L²(γ dx)`

`polyOp` is diagonal on the Hermite classes with eigenvalues `n` (`polyOpH_hermiteR`), and the
Hermite polynomials are orthogonal for the Gaussian weight (`hermiteInner_eq`, in
`ChapterHermiteFunctions`).  This module moves that orthogonality to the level of `L²(γ dx)`
classes, normalizes the family, and records it as a `HilbertBasis`.

The orthogonality is where the Gaussian weight does its work: the `L²(γ)` inner product of two
polynomial classes is the Bochner integral of their product against `gaussMeasure`, which
`integral_gaussMeasure_eq_integral_gaussWeight` turns into the Lebesgue integral of
`gaussWeight · p q`; `gaussWeight` is `gaussRoot² = exp(−x²/2) = gaussW`, so the integral is
`gint (p q)`, and `hermiteInner` is by definition `gint (H_m H_n)`.

Completeness is not new: `dense_hermiteSpanSet` already says the Hermite span is dense, and
`HilbertBasis.mk` turns an orthonormal family with dense span into a Hilbert basis.  Rescaling by
the nonzero norms does not change the span, which is `span_hermiteLpR`.

The basis is the input the real-space self-adjointness argument needs: each `hermiteBasisR n` is an
eigenvector of `polyOp` with a real eigenvalue, so the closure of `polyOp` can be read off from its
action on the basis.
-/
import BookProof.Qym.ChapterYangMillsPolyAnnulus
import BookProof.Toolbox.ChapterHermiteFunctions

open MeasureTheory Polynomial
open scoped ENNReal InnerProductSpace

namespace BookProof.YangMillsPolyBasis

open BookProof.YangMillsPolyCore BookProof.YangMillsPolyGraphNorm
open BookProof.YangMillsHermiteSpectrum BookProof.YangMillsMehlerLp
open BookProof.YangMillsMehlerBridge BookProof.YangMillsGaussForm BookProof.HermiteCore

noncomputable section

/-! ## The Gaussian weight is the Hermite weight -/

/-- **`gaussWeight` is `gaussW`.**  Both are `exp(−x²/2)`: one as the square of the Mehler root
`exp(−x²/4)`, the other as `gaussRoot_sq`. -/
theorem gaussWeight_eq_gaussW (x : ℝ) : gaussWeight x = gaussW x := by
  rw [gaussWeight, gaussRoot_sq]
  rfl

/-! ## The inner product of two Hermite classes -/

/-- **The `L²(γ dx)` inner product of two Hermite classes.**  Reading the inner product as an
integral and replacing the representatives by the polynomials (`MemLp.coeFn_toLp`) leaves
`∫ p q dγ`, which is the Gaussian integral `hermiteInner p q`. -/
theorem inner_polyLp_hermiteR (m n : ℕ) :
    ⟪polyLp (hermiteR m), polyLp (hermiteR n)⟫_ℝ = hermiteInner m n := by
  have h1 : ⟪polyLp (hermiteR m), polyLp (hermiteR n)⟫_ℝ
      = ∫ x, (hermiteR m).eval x * (hermiteR n).eval x ∂gaussMeasure := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_eval (hermiteR m)),
      MemLp.coeFn_toLp (memLp_eval (hermiteR n))] with x hx hy
    simp only [polyLp] at hx hy ⊢
    rw [hx, hy, RCLike.inner_apply, starRingEnd_apply, star_trivial]
    ring
  rw [h1, integral_gaussMeasure_eq_integral_gaussWeight, hermiteInner, gint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change gaussWeight x * ((hermiteR m).eval x * (hermiteR n).eval x)
      = (hermiteR m * hermiteR n).eval x * gaussW x
  rw [gaussWeight_eq_gaussW, Polynomial.eval_mul]
  ring

/-- The Hermite classes are orthonormal up to the norms `hermiteNorm`. -/
theorem inner_polyLp_hermiteR_eq (m n : ℕ) :
    ⟪polyLp (hermiteR m), polyLp (hermiteR n)⟫_ℝ
      = if m = n then hermiteNorm n ^ 2 else 0 := by
  rw [inner_polyLp_hermiteR, hermiteInner_eq]
  by_cases h : m = n
  · rw [if_pos h, if_pos h, sq, hermiteNorm_sq]
  · rw [if_neg h, if_neg h]

/-! ## The normalized family -/

/-- **The normalized Hermite classes** `H_n / ‖H_n‖` in `L²(γ dx)`. -/
def hermiteLpR (n : ℕ) : Lp ℝ 2 gaussMeasure := (hermiteNorm n)⁻¹ • polyLp (hermiteR n)

/-- **The normalized Hermite classes are orthonormal.**  The `L²(γ)` inner product scales by the
two factors, and `hermiteNorm n⁻¹ · hermiteNorm n = 1`. -/
theorem inner_hermiteLpR (m n : ℕ) :
    ⟪hermiteLpR m, hermiteLpR n⟫_ℝ = if m = n then 1 else 0 := by
  have hm : hermiteNorm m ≠ 0 := (hermiteNorm_pos m).ne'
  have hn : hermiteNorm n ≠ 0 := (hermiteNorm_pos n).ne'
  rw [hermiteLpR, hermiteLpR, inner_smul_left, inner_smul_right, inner_polyLp_hermiteR_eq]
  by_cases h : m = n
  · subst h
    rw [if_pos rfl, if_pos rfl, sq]
    have hstar : (starRingEnd ℝ) (hermiteNorm m)⁻¹ = (hermiteNorm m)⁻¹ := by simp
    rw [hstar]
    field_simp
  · rw [if_neg h, if_neg h, mul_zero, mul_zero]

/-- **The Hermite classes, normalized, form an orthonormal family of `L²(γ dx)`.** -/
theorem orthonormal_hermiteLpR : Orthonormal ℝ hermiteLpR :=
  orthonormal_iff_ite.mpr fun m n => inner_hermiteLpR m n

/-! ## The span is unchanged by normalizing -/

/-- The normalized classes lie in the Hermite span. -/
theorem hermiteLpR_mem (n : ℕ) : hermiteLpR n ∈ hermiteSpan :=
  Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

/-- **Normalizing does not change the span**: the Hermite span is spanned by the normalized
classes as well. -/
theorem span_hermiteLpR : Submodule.span ℝ (Set.range hermiteLpR) = hermiteSpan := by
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨n, rfl⟩
    exact hermiteLpR_mem n
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨n, rfl⟩
    change polyLp (hermiteR n) ∈ Submodule.span ℝ (Set.range hermiteLpR)
    have h : polyLp (hermiteR n) = hermiteNorm n • hermiteLpR n := by
      rw [hermiteLpR, smul_inv_smul₀ (hermiteNorm_pos n).ne']
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

/-! ## The Hilbert basis -/

/-- **A Hilbert basis of `L²(γ dx)` made of Hermite classes.**  `HilbertBasis.mk` needs exactly the
two facts above: orthonormality, and density of the span, which is `dense_hermiteSpanSet` read
through `span_hermiteLpR`. -/
def hermiteBasisR : HilbertBasis ℕ ℝ (Lp ℝ 2 gaussMeasure) :=
  HilbertBasis.mk orthonormal_hermiteLpR (by
    have h := Submodule.dense_iff_topologicalClosure_eq_top.mp dense_hermiteSpanSet
    rw [span_hermiteLpR, h])

/-- The basis vectors are the normalized Hermite classes. -/
@[simp] theorem hermiteBasisR_apply (n : ℕ) : hermiteBasisR n = hermiteLpR n :=
  congrFun (HilbertBasis.coe_mk orthonormal_hermiteLpR _) n

end

end BookProof.YangMillsPolyBasis
