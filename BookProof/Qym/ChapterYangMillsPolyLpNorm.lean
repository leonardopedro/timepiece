/-
Copyright (c) 2026.  All rights reserved.

# Polynomial classes under `T`, and the `L²(γ)` norm bridge

Two facts the annulus estimate for `T(χ_R p) − T p` needs, neither of which involves the cutoff:

* **`T` acts on polynomial classes by `dirichletPoly`.**  `polyOpH_coe` reads the definition of
  `polyOpRange` through the class isomorphism: on a Hermite-span class the operator returns the
  class of `dirichletPoly p`, not just something agreeing with it a.e.  `polyOpH_coeFn` then
  identifies the *representative* of that class with `gaussDirichlet (fun x => p.eval x)`, which is
  `dirichletPoly_eval` composed with `MemLp.coeFn_toLp`.  This is what makes `T p` a polynomial on
  the class level: the annulus estimate can estimate `p`, `p'`, `p''` and `x p'` as ordinary
  functions, without ever returning to the operator.

* **The norm of a difference of classes.**  `enorm_toLp_sub` and `norm_toLp_sub_eq` say that
  `‖u − v‖` only sees the difference of representatives, and `ofReal_norm_toLp_sub_sq` turns that
  into the squared `lintegral` `∫⁻ x, ofReal ((F x − G x)²) ∂γ`.  The last form is the one that
  composes with `exists_lintegral_tail_lt`, whose conclusion is stated exactly as a bound on
  `∫⁻ y in tailSet R, ofReal ((p.eval y)²)`.

The square-integral identity avoids the `eLpNorm` `rpow` bookkeeping: for real-valued classes the
`L²` norm is `⟪u, u⟫^{1/2}` and `⟪u, u⟫ = ∫ x, u x * u x` (`L2.inner_def`), so squaring removes
the root, and `ofReal_integral_eq_lintegral_ofReal` converts the Bochner integral into the
`lintegral` of `ofReal`, which is the shape a tail bound lives in.
-/
import BookProof.Qym.ChapterYangMillsPolyGraphNorm
import BookProof.Qym.ChapterYangMillsPolyTail
import BookProof.Qym.ChapterYangMillsHermiteAnalytic
import BookProof.Qym.ChapterYangMillsGaussForm

open MeasureTheory Polynomial
open scoped InnerProductSpace

namespace BookProof.YangMillsPolyLpNorm

open BookProof.YangMillsPolyCore BookProof.YangMillsPolyGraphNorm
open BookProof.YangMillsHermiteSpectrum BookProof.YangMillsGaussForm BookProof.HermiteCore
open BookProof.YangMillsHermiteAnalytic BookProof.YangMillsMehlerLp
open BookProof.YangMillsMehlerBridge

noncomputable section

/-! ## `T` on polynomial classes -/

/-- **`polyOpRange` computes `dirichletPoly` on representatives.**  This is the definition of the
class-level operator unwound through `polyEquiv`: nothing but `LinearMap.comp_apply`. -/
theorem polyOpRange_apply (x : polyRange) :
    polyOpRange x = polyEquiv (dirichletPoly (polyEquiv.symm x)) := rfl

/-- **On a Hermite-span class of a polynomial, `T` is the class of `dirichletPoly p`.**  The
inclusion `hermiteSpan → polyRange` is the identity on representatives, and `polyEquiv_symm_mk`
recovers `p` from its class, so the statement is the definition of `polyOpH` read backwards. -/
theorem polyOpH_coe (p : Polynomial ℝ) (hp : polyLp p ∈ hermiteSpan) :
    ((polyOpH ⟨polyLp p, hp⟩ : polyRange) : Lp ℝ 2 gaussMeasure) = polyLp (dirichletPoly p) := by
  have hcoe : (Submodule.inclusion hermiteSpan_le_polyRange ⟨polyLp p, hp⟩ : polyRange)
      = ⟨polyLp p, ⟨p, rfl⟩⟩ := Subtype.ext rfl
  rw [polyOpH, LinearMap.comp_apply, hcoe, polyOpRange_apply, polyEquiv_symm_mk, polyEquiv_apply]

/-- **`T p` is, as a function, `gaussDirichlet` of the polynomial.**  The class computed by
`polyOpH_coe` is `polyLp (dirichletPoly p)`, whose representative is `(dirichletPoly p).eval`
(`MemLp.coeFn_toLp`), and `dirichletPoly_eval` rewrites that as `gaussDirichlet (p.eval)`.

This is the statement that the annulus estimate consumes: the derivative terms are evaluated on
`p` itself, not on an abstract class. -/
theorem polyOpH_coeFn (p : Polynomial ℝ) (hp : polyLp p ∈ hermiteSpan) :
    ((polyOpH ⟨polyLp p, hp⟩ : polyRange) : ℝ → ℝ)
      =ᵐ[gaussMeasure] gaussDirichlet (fun x : ℝ => p.eval x) := by
  rw [polyOpH_coe p hp]
  have htoLp : (polyLp (dirichletPoly p) : ℝ → ℝ) =ᵐ[gaussMeasure]
      fun x : ℝ => (dirichletPoly p).eval x :=
    MemLp.coeFn_toLp (memLp_eval (dirichletPoly p))
  refine htoLp.trans (Filter.EventuallyEq.of_eq ?_)
  exact dirichletPoly_eval p

/-! ## The norm bridge -/

/-- **The `e`-norm of a difference of classes is the `L²` seminorm of the difference.**  Rewrite the
subtraction as the class of `F − G` (`MemLp.toLp_sub`), then read `‖·‖ₑ` off `Lp` as `eLpNorm`
(`Lp.enorm_def`), and use that the representative of a class agrees a.e. with the function. -/
theorem enorm_toLp_sub (F G : ℝ → ℝ) (hF : MemLp F 2 gaussMeasure)
    (hG : MemLp G 2 gaussMeasure) :
    ‖hF.toLp F - hG.toLp G‖ₑ = eLpNorm (F - G) 2 gaussMeasure := by
  have hsub : hF.toLp F - hG.toLp G = (hF.sub hG).toLp (F - G) := (MemLp.toLp_sub hF hG).symm
  rw [hsub, Lp.enorm_def]
  exact eLpNorm_congr_ae (MemLp.coeFn_toLp _)

/-- **The norm form**: `‖u − v‖ = (eLpNorm (F − G) 2 γ).toReal`.  Immediate from
`enorm_toLp_sub`, since the `e`-norm of a real norm is its `ofReal`. -/
theorem norm_toLp_sub_eq (F G : ℝ → ℝ) (hF : MemLp F 2 gaussMeasure)
    (hG : MemLp G 2 gaussMeasure) :
    ‖hF.toLp F - hG.toLp G‖ = (eLpNorm (F - G) 2 gaussMeasure).toReal := by
  have hsub : hF.toLp F - hG.toLp G = (hF.sub hG).toLp (F - G) := (MemLp.toLp_sub hF hG).symm
  rw [Lp.norm_def]
  refine congrArg ENNReal.toReal (eLpNorm_congr_ae ?_)
  rw [hsub]
  exact MemLp.coeFn_toLp _

/-- **The squared `lintegral` form.**  The square of the norm of a difference of classes is the
`lintegral` of `ofReal` of the squared difference of representatives — the shape
`exists_lintegral_tail_lt` bounds.

Squaring removes the `L²` root: `⟪u, u⟫ = ‖u‖²` and `⟪u, u⟫ = ∫ x, u x * u x`
(`L2.inner_def`), so `‖u‖²` is an honest Bochner integral; a.e. replacement of `u` by `F − G`
(which is what `MemLp.coeFn_toLp` gives) moves it to the representatives, and
`ofReal_integral_eq_lintegral_ofReal` converts it to the `lintegral` of `ofReal`, using that the
integrand is a square and hence nonnegative. -/
theorem ofReal_norm_toLp_sub_sq (F G : ℝ → ℝ) (hF : MemLp F 2 gaussMeasure)
    (hG : MemLp G 2 gaussMeasure) :
    ENNReal.ofReal (‖hF.toLp F - hG.toLp G‖ ^ 2)
      = ∫⁻ x, ENNReal.ofReal ((F x - G x) ^ 2) ∂gaussMeasure := by
  have hsub : hF.toLp F - hG.toLp G = (hF.sub hG).toLp (F - G) := (MemLp.toLp_sub hF hG).symm
  have hae : ((hF.toLp F - hG.toLp G : Lp ℝ 2 gaussMeasure) : ℝ → ℝ)
      =ᵐ[gaussMeasure] F - G := by
    rw [hsub]
    exact MemLp.coeFn_toLp _
  have hnorm : ‖hF.toLp F - hG.toLp G‖ ^ 2
      = ∫ x, (F x - G x) ^ 2 ∂gaussMeasure := by
    have h1 : ‖hF.toLp F - hG.toLp G‖ ^ 2
        = ∫ x, ((hF.toLp F - hG.toLp G : Lp ℝ 2 gaussMeasure) : ℝ → ℝ) x ^ 2
            ∂gaussMeasure := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp
    rw [h1]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
    rfl
  rw [hnorm]
  exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hF.sub hG).integrable_sq)
    (Filter.Eventually.of_forall fun x => sq_nonneg (F x - G x))

end

end BookProof.YangMillsPolyLpNorm
