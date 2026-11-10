/-
Copyright (c) 2026.  All rights reserved.

# The polynomial core inside the closure of `gaussOp`

`ChapterYangMillsPolyCore` produces a `LinearPMap` on `L²(γ dx)` whose domain is the Hermite
span and which is self-adjoint in the Faris–Lavine sense there, but it is not yet known to be the
closure of `gaussOp`.  `ChapterSelfAdjointMaximal` shows that a single inclusion
`polyOp ≤ gaussOp.closure` settles the matter, and `le_closure_of_forall_approx` reduces that
inclusion to a *graph-norm approximation* of the records `(x, polyOp x)` by core records.

This module writes that reduction for the actual operators.  `polyOp` is the polynomial operator
on the class level, and the approximation it asks for is isolated as `PolyGraphApprox`: for every
Hermite-span class `x` and every `ε > 0` there is a `C²`-compactly-supported class `f` with
`‖x - f‖ < ε` and `‖polyOp x - T f‖ < ε`.

`PolyGraphApprox` splits into exactly two estimates.  The first, `‖x - f‖ < ε`, needs a smooth
cutoff equal to `p` off an annulus and nothing else — that is `exists_lintegral_tail_lt`
(`ChapterYangMillsPolyTail`), the vanishing Gaussian tail of a squared polynomial.  The second,
`‖T(χ p) - T p‖ < ε`, is the annulus estimate: `T(χ p) - χ T p` is supported where the cutoff
turns off, and there its size is governed by the tails of `p`, `p'` and `p''` times the bounds
`|χ'| ≤ C/R` and `|χ''| ≤ C/R²`.  That estimate is not carried out here.

`polyOp_eq_gaussOp_closure` is the concrete form of `closure_eq_of_le` for `polyOp` and
`gaussOp.closure`.  The complexified operators live on two *different* spaces,
`Cx (Lp ℝ 2 gaussMeasure)` and `Lp ℂ 2 gaussMeasure`; the real statement below is the one that
composes with the existing bridge lemmas, the complexification being a transport away.
-/
import BookProof.Qym.ChapterYangMillsPolyTail
import BookProof.Toolbox.ChapterSelfAdjointMaximal

open MeasureTheory Polynomial
open scoped InnerProductSpace

namespace BookProof.YangMillsPolyGraphNorm

open BookProof.YangMillsPolyCore BookProof.YangMillsMehlerLp BookProof.YangMillsHermiteSpectrum
open BookProof.YangMillsGaussForm BookProof.SelfAdjointMaximal BookProof.HermiteCore

noncomputable section

/-! ## The polynomial operator as a partial operator on `L²(γ dx)` -/

/-- **`polyOp`**: the polynomial operator on the class level, with the Hermite span as domain.
This is `polyOpH` read as a `LinearPMap`.  `ChapterYangMillsPolyCore` keeps the complexified
version `polyOpC`, but the identification with `gaussOp`'s closure is a real-space statement,
because `gaussOp` is. -/
noncomputable def polyOp : Lp ℝ 2 gaussMeasure →ₗ.[ℝ] Lp ℝ 2 gaussMeasure where
  domain := hermiteSpan
  toFun := polyRange.subtype.comp polyOpH

/-- On the `n`-th Hermite class, `polyOp` is multiplication by `n`. -/
theorem polyOp_hermiteR (n : ℕ) :
    polyOp ⟨polyLp (hermiteR n), Submodule.subset_span ⟨n, rfl⟩⟩
      = (n : ℝ) • polyLp (hermiteR n) :=
  polyOpH_hermiteR n

/-! ## The graph-norm approximation -/

/-- **The graph-norm approximation property for one span element.**  An `ε`-approximation of the
record `(x, polyOp x)` by a record `(f, T f)` of the compactly supported core `gaussCore`. -/
def Approximable (x : hermiteSpan) : Prop :=
  ∀ ε > 0, ∃ f : gaussCore,
    ‖(x : Lp ℝ 2 gaussMeasure) - (f : Lp ℝ 2 gaussMeasure)‖ < ε ∧
    ‖(polyOp x : Lp ℝ 2 gaussMeasure) - gaussOpFun f‖ < ε

/-- **The graph-norm approximation property**, for every Hermite-span element.  This is the single
analytic estimate the identification of the two cores is waiting on. -/
def PolyGraphApprox : Prop := ∀ x : hermiteSpan, Approximable x

/-- `T` kills the zero class. -/
theorem gaussOpFun_zero : gaussOpFun (0 : gaussCore) = 0 := by
  have h := gaussOpFun_add 0 0
  refine add_left_cancel (a := gaussOpFun 0) ?_
  simpa using h

/-- The approximation is additive, because both operators are and a norm is subadditive. -/
theorem approximable_add {x y : hermiteSpan} (hx : Approximable x) (hy : Approximable y) :
    Approximable (x + y) := by
  intro ε hε
  obtain ⟨f, hf1, hf2⟩ := hx (ε / 2) (by positivity)
  obtain ⟨g, hg1, hg2⟩ := hy (ε / 2) (by positivity)
  refine ⟨f + g, ?_, ?_⟩
  · calc ‖((x + y : hermiteSpan) : Lp ℝ 2 gaussMeasure) - ((f + g : gaussCore) :
          Lp ℝ 2 gaussMeasure)‖
        = ‖((x : Lp ℝ 2 gaussMeasure) - f) + ((y : Lp ℝ 2 gaussMeasure) - g)‖ := by
          rw [Submodule.coe_add, Submodule.coe_add]
          abel
      _ ≤ ‖(x : Lp ℝ 2 gaussMeasure) - (f : Lp ℝ 2 gaussMeasure)‖
            + ‖(y : Lp ℝ 2 gaussMeasure) - (g : Lp ℝ 2 gaussMeasure)‖ := norm_add_le _ _
      _ < ε := by linarith
  · calc ‖(polyOp (x + y) : Lp ℝ 2 gaussMeasure) - gaussOpFun (f + g)‖
        = ‖((polyOp x - gaussOpFun f) + (polyOp y - gaussOpFun g))‖ := by
          rw [LinearPMap.map_add polyOp x y, gaussOpFun_add]
          abel
      _ ≤ ‖(polyOp x : Lp ℝ 2 gaussMeasure) - gaussOpFun f‖
            + ‖(polyOp y : Lp ℝ 2 gaussMeasure) - gaussOpFun g‖ := norm_add_le _ _
      _ < ε := by linarith

/-- The approximation is homogeneous: scale the approximant and absorb the factor into `ε`. -/
theorem approximable_smul (c : ℝ) {x : hermiteSpan} (hx : Approximable x) :
    Approximable (c • x) := by
  intro ε hε
  have hpos : 0 < ‖c‖ + 1 := by positivity
  obtain ⟨f, hf1, hf2⟩ := hx (ε / (‖c‖ + 1)) (div_pos hε hpos)
  refine ⟨c • f, ?_, ?_⟩
  · calc ‖((c • x : hermiteSpan) : Lp ℝ 2 gaussMeasure) - ((c • f : gaussCore) :
          Lp ℝ 2 gaussMeasure)‖
        = ‖c • ((x : Lp ℝ 2 gaussMeasure) - (f : Lp ℝ 2 gaussMeasure))‖ := by
          rw [Submodule.coe_smul, Submodule.coe_smul, smul_sub]
      _ = ‖c‖ * ‖(x : Lp ℝ 2 gaussMeasure) - (f : Lp ℝ 2 gaussMeasure)‖ := norm_smul _ _
      _ < ε := by
        have hkey : ‖c‖ * (ε / (‖c‖ + 1)) < ε := by
          rw [mul_div_assoc', div_lt_iff₀ hpos]
          nlinarith [norm_nonneg c]
        nlinarith [hf1, norm_nonneg c]
  · calc ‖(polyOp (c • x) : Lp ℝ 2 gaussMeasure) - gaussOpFun (c • f)‖
        = ‖c • (polyOp x - gaussOpFun f)‖ := by
          rw [LinearPMap.map_smul polyOp c x, gaussOpFun_smul, smul_sub]
      _ = ‖c‖ * ‖(polyOp x : Lp ℝ 2 gaussMeasure) - gaussOpFun f‖ := norm_smul _ _
      _ < ε := by
        have hkey : ‖c‖ * (ε / (‖c‖ + 1)) < ε := by
          rw [mul_div_assoc', div_lt_iff₀ hpos]
          nlinarith [norm_nonneg c]
        nlinarith [hf2, norm_nonneg c]

/-- The zero class is approximable by the zero core class. -/
theorem approximable_zero : Approximable 0 := by
  intro ε hε
  refine ⟨0, ?_, ?_⟩
  · simpa using hε
  · rw [LinearPMap.map_zero polyOp, gaussOpFun_zero, sub_zero]
    simpa using hε

/-! ## The inclusion, and the identification -/

/-- **The polynomial operator sits inside the closure of `gaussOp`** as soon as the graph-norm
approximation holds.  This is `le_closure_of_forall_approx` for the actual operators, with
`gaussOp_isClosable` supplying closability. -/
theorem polyOp_le_gaussOp_closure (h : PolyGraphApprox) : polyOp ≤ gaussOp.closure :=
  le_closure_of_forall_approx (A := polyOp) (B := gaussOp) gaussOp_isClosable fun x => h x

/-- **The identification of the two cores, concretely.**  `closure_eq_of_le` instantiated at
`polyOp` and `gaussOp`: once `polyOp` is self-adjoint and `gaussOp.closure` is symmetric, the
graph-norm approximation upgrades to `polyOp = gaussOp.closure`. -/
theorem polyOp_eq_gaussOp_closure (h : PolyGraphApprox) (hsa : IsSelfAdjoint polyOp)
    (hsym : SymmetricOp gaussOp.closure) : polyOp = gaussOp.closure :=
  closure_eq_of_le (polyOp_le_gaussOp_closure h) hsa hsym

end

end BookProof.YangMillsPolyGraphNorm
