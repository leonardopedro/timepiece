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
`|χ'| ≤ C/R` and `|χ''| ≤ C/R²`.  Both are carried out in `ChapterYangMillsPolyAnnulus`, which
proves `PolyGraphApprox` (`polyGraphApprox_holds`); this module only states the property and
derives the consequences stated below from it.

The approximation is additive, homogeneous and vanishes at `0`, so `polyGraphApprox_of_hermite`
reduces `PolyGraphApprox` to its values on the Hermite generators — the only classes that have to
be approximated by hand.  `Approximable` therefore carries the vector and its membership separately
(`Approximable v hv`, reading `polyOp ⟨v, hv⟩`): bundling them makes `Submodule.span_induction`
compare `⟨x + y, _⟩` with `⟨x, _⟩ + ⟨y, _⟩` under `Approximable`, which unfolds `polyOp` far enough
to exhaust the heartbeat budget.

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
This is `polyOpH` read as a `LinearPMap`.  The identification with `gaussOp`'s closure is a
real-space statement, because `gaussOp` is; `Qym/ChapterYangMillsPolySelfAdjoint` proves it, and
`polyOp.closure` is self-adjoint. -/
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
record `(v, polyOp v)` by a record `(f, T f)` of the compactly supported core `gaussCore`.  The
vector and its membership are separate arguments so that a `Submodule.span_induction` motive can
mention them without comparing bundled pairs. -/
def Approximable (v : Lp ℝ 2 gaussMeasure) (hv : v ∈ hermiteSpan) : Prop :=
  ∀ ε > 0, ∃ f : gaussCore,
    ‖v - (f : Lp ℝ 2 gaussMeasure)‖ < ε ∧
    ‖(polyOp ⟨v, hv⟩ : Lp ℝ 2 gaussMeasure) - gaussOpFun f‖ < ε

/-- **The graph-norm approximation property**, for every Hermite-span element.  This is the single
analytic estimate the identification of the two cores is waiting on. -/
def PolyGraphApprox : Prop :=
  ∀ (v : Lp ℝ 2 gaussMeasure) (hv : v ∈ hermiteSpan), Approximable v hv

/-- `T` kills the zero class. -/
theorem gaussOpFun_zero : gaussOpFun (0 : gaussCore) = 0 := by
  have h := gaussOpFun_add 0 0
  refine add_left_cancel (a := gaussOpFun 0) ?_
  simpa using h

/-- The approximation is additive, because both operators are and a norm is subadditive. -/
theorem approximable_add {v w : Lp ℝ 2 gaussMeasure} {hv : v ∈ hermiteSpan}
    {hw : w ∈ hermiteSpan} (hv' : Approximable v hv) (hw' : Approximable w hw) :
    Approximable (v + w) (Submodule.add_mem hermiteSpan hv hw) := by
  intro ε hε
  obtain ⟨f, hf1, hf2⟩ := hv' (ε / 2) (by positivity)
  obtain ⟨g, hg1, hg2⟩ := hw' (ε / 2) (by positivity)
  refine ⟨f + g, ?_, ?_⟩
  · calc ‖(v + w) - ((f + g : gaussCore) : Lp ℝ 2 gaussMeasure)‖
        = ‖(v - f) + (w - g)‖ := by
          rw [Submodule.coe_add]
          abel
      _ ≤ ‖v - (f : Lp ℝ 2 gaussMeasure)‖ + ‖w - (g : Lp ℝ 2 gaussMeasure)‖ :=
        norm_add_le _ _
      _ < ε := by linarith
  · have hmap : (polyOp (⟨v + w, Submodule.add_mem hermiteSpan hv hw⟩ : hermiteSpan)
        : Lp ℝ 2 gaussMeasure) = polyOp ⟨v, hv⟩ + polyOp ⟨w, hw⟩ :=
      LinearPMap.map_add polyOp ⟨v, hv⟩ ⟨w, hw⟩
    calc ‖(polyOp (⟨v + w, Submodule.add_mem hermiteSpan hv hw⟩ : hermiteSpan)
          : Lp ℝ 2 gaussMeasure) - gaussOpFun (f + g)‖
        = ‖(polyOp ⟨v, hv⟩ - gaussOpFun f) + (polyOp ⟨w, hw⟩ - gaussOpFun g)‖ := by
          rw [hmap, gaussOpFun_add]
          abel
      _ ≤ ‖(polyOp ⟨v, hv⟩ : Lp ℝ 2 gaussMeasure) - gaussOpFun f‖
            + ‖(polyOp ⟨w, hw⟩ : Lp ℝ 2 gaussMeasure) - gaussOpFun g‖ := norm_add_le _ _
      _ < ε := by linarith

/-- The approximation is homogeneous: scale the approximant and absorb the factor into `ε`. -/
theorem approximable_smul (c : ℝ) {v : Lp ℝ 2 gaussMeasure} {hv : v ∈ hermiteSpan}
    (hv' : Approximable v hv) :
    Approximable (c • v) (Submodule.smul_mem hermiteSpan c hv) := by
  intro ε hε
  have hpos : 0 < ‖c‖ + 1 := by positivity
  obtain ⟨f, hf1, hf2⟩ := hv' (ε / (‖c‖ + 1)) (div_pos hε hpos)
  refine ⟨c • f, ?_, ?_⟩
  · calc ‖c • v - ((c • f : gaussCore) : Lp ℝ 2 gaussMeasure)‖
        = ‖c • (v - (f : Lp ℝ 2 gaussMeasure))‖ := by
          rw [Submodule.coe_smul, smul_sub]
      _ = ‖c‖ * ‖v - (f : Lp ℝ 2 gaussMeasure)‖ := norm_smul _ _
      _ < ε := by
        have hkey : ‖c‖ * (ε / (‖c‖ + 1)) < ε := by
          rw [mul_div_assoc', div_lt_iff₀ hpos]
          nlinarith [norm_nonneg c]
        nlinarith [hf1, norm_nonneg c]
  · have hmap : (polyOp (⟨c • v, Submodule.smul_mem hermiteSpan c hv⟩ : hermiteSpan)
        : Lp ℝ 2 gaussMeasure) = c • polyOp ⟨v, hv⟩ :=
      LinearPMap.map_smul polyOp c ⟨v, hv⟩
    calc ‖(polyOp (⟨c • v, Submodule.smul_mem hermiteSpan c hv⟩ : hermiteSpan)
          : Lp ℝ 2 gaussMeasure) - gaussOpFun (c • f)‖
        = ‖c • (polyOp ⟨v, hv⟩ - gaussOpFun f)‖ := by
          rw [hmap, gaussOpFun_smul, smul_sub]
      _ = ‖c‖ * ‖(polyOp ⟨v, hv⟩ : Lp ℝ 2 gaussMeasure) - gaussOpFun f‖ := norm_smul _ _
      _ < ε := by
        have hkey : ‖c‖ * (ε / (‖c‖ + 1)) < ε := by
          rw [mul_div_assoc', div_lt_iff₀ hpos]
          nlinarith [norm_nonneg c]
        nlinarith [hf2, norm_nonneg c]

/-- The zero class is approximable by the zero core class. -/
theorem approximable_zero : Approximable 0 (Submodule.zero_mem hermiteSpan) := by
  intro ε hε
  refine ⟨0, ?_, ?_⟩
  · simpa using hε
  · have hmap : (polyOp (⟨0, Submodule.zero_mem hermiteSpan⟩ : hermiteSpan)
        : Lp ℝ 2 gaussMeasure) = 0 := LinearPMap.map_zero polyOp
    rw [hmap, gaussOpFun_zero, sub_zero]
    simpa using hε

/-- **It suffices to approximate the Hermite generators.**  The Hermite span is generated by the
`H_n`, and the approximation is stable under `0`, `+` and scalar multiplication, so it propagates
from the generators to every span element. -/
theorem polyGraphApprox_of_hermite
    (h : ∀ n : ℕ, Approximable (polyLp (hermiteR n)) (Submodule.subset_span ⟨n, rfl⟩)) :
    PolyGraphApprox := by
  intro v hv
  refine Submodule.span_induction (p := fun v hv => Approximable v hv) ?_ ?_ ?_ ?_ hv
  · intro w hw
    obtain ⟨n, rfl⟩ := hw
    exact h n
  · exact approximable_zero
  · intro x y _ _ ix iy
    exact approximable_add ix iy
  · intro c x _ ix
    exact approximable_smul c ix

/-! ## The inclusion, and the identification -/

/-- **The polynomial operator sits inside the closure of `gaussOp`** as soon as the graph-norm
approximation holds.  This is `le_closure_of_forall_approx` for the actual operators, with
`gaussOp_isClosable` supplying closability. -/
theorem polyOp_le_gaussOp_closure (h : PolyGraphApprox) : polyOp ≤ gaussOp.closure :=
  le_closure_of_forall_approx (A := polyOp) (B := gaussOp) gaussOp_isClosable
    fun x ε hε => h x.1 x.2 ε hε

/-- **`polyOp` is closable.**  It sits inside the closed `gaussOp.closure`, which is what
`isClosable_iff_exists_closed_extension` asks for. -/
theorem polyOp_isClosable (h : PolyGraphApprox) : polyOp.IsClosable :=
  LinearPMap.isClosable_iff_exists_closed_extension.mpr
    ⟨gaussOp.closure, LinearPMap.IsClosable.closure_isClosed gaussOp_isClosable,
      polyOp_le_gaussOp_closure h⟩

/-- **The closure of `polyOp` sits inside `gaussOp.closure`.**  This is the graph argument rather
than `IsClosable.closure_mono`, which would only give
`polyOp.closure ≤ (gaussOp.closure).closure`: the graph of `polyOp.closure` is the closure of the
graph of `polyOp` (`IsClosable.graph_closure_eq_closure_graph`), and that closure is contained in
the closed graph of `gaussOp.closure`. -/
theorem polyOp_closure_le_gaussOp_closure (h : PolyGraphApprox) :
    polyOp.closure ≤ gaussOp.closure := by
  refine LinearPMap.le_of_le_graph ?_
  rw [← LinearPMap.IsClosable.graph_closure_eq_closure_graph (polyOp_isClosable h)]
  exact Submodule.topologicalClosure_minimal (s := LinearPMap.graph polyOp)
    (LinearPMap.le_graph_of_le (polyOp_le_gaussOp_closure h))
    (LinearPMap.IsClosable.closure_isClosed gaussOp_isClosable)

/-- **The identification, in the form essential self-adjointness actually gives.**
`IsSelfAdjoint polyOp` is the wrong hypothesis: `polyOp` is a partial operator on a dense core and
need not be closed, so the object the Faris–Lavine argument makes self-adjoint is
`polyOp.closure`.  With that hypothesis the maximality step applies unchanged, and the conclusion
is an equality of *closures* — which is also the form in which essential self-adjointness is
usually quoted. -/
theorem polyOp_closure_eq_gaussOp_closure (h : PolyGraphApprox)
    (hsa : IsSelfAdjoint polyOp.closure) (hsym : SymmetricOp gaussOp.closure) :
    polyOp.closure = gaussOp.closure :=
  closure_eq_of_le (polyOp_closure_le_gaussOp_closure h) hsa hsym

/-- **The identification of the two cores, concretely.**  `closure_eq_of_le` instantiated at
`polyOp` and `gaussOp`: once `polyOp` is self-adjoint and `gaussOp.closure` is symmetric, the
graph-norm approximation upgrades to `polyOp = gaussOp.closure`. -/
theorem polyOp_eq_gaussOp_closure (h : PolyGraphApprox) (hsa : IsSelfAdjoint polyOp)
    (hsym : SymmetricOp gaussOp.closure) : polyOp = gaussOp.closure :=
  closure_eq_of_le (polyOp_le_gaussOp_closure h) hsa hsym

end

end BookProof.YangMillsPolyGraphNorm
