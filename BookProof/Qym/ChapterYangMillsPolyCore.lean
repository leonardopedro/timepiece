/-
Copyright (c) 2026.  All rights reserved.

# The polynomial form core of `gaussDirichlet`, as an operator on `L²(γ dx)`

`ChapterYangMillsHermiteAnalytic` puts `T = −∂² + x∂` on polynomials and proves the growth
bounds `Tᵐ(H_n) = nᵐ H_n` there, but leaves the class level open: `gaussOp`'s domain is the
compactly supported `C²` core `gaussCore`, which contains no polynomial, so neither the
eigenvalue relation nor the density of the Hermite classes was ever stated for an operator
*on* `L²(γ dx)`.  This module closes that gap, and with it the S0 self-adjointness item.

The two inputs are:

* `polyLp_injective` — the polynomial classes inject into `L²(γ dx)`.  A polynomial class that
  vanishes is a.e. zero (`MemLp.toLp_eq_toLp_iff`), a polynomial is continuous, and
  `gaussMeasure` is an `IsOpenPosMeasure`, so a.e. zero forces zero everywhere
  (`IsOpen.eq_empty_of_measure_zero`), hence the polynomial is zero (`Polynomial.funext`).
  With this the class map is an isomorphism onto its range, and an operator on the range can
  be *defined* by prescribing it on representatives — no well-definedness obligation is left
  over.
* `mem_span_hermiteR` — the Hermite polynomials span `Polynomial ℝ`, because `hermiteR n` is
  monic of degree `n` (`coeff_hermiteR_self`, `natDegree_hermiteR`).  Combined with
  `dense_span_polyLp` this gives `dense_hermiteSpan`: the Hermite classes span a dense
  subspace of `L²(γ dx)`, which is exactly the completeness a spectral argument needs.

The operator on the span, `polyOpH`, is then extended to a global real-linear map `coreExt` by
composing with a left inverse of the inclusion.  The values off the span are irrelevant; what the
extension buys is that inner products against `coreExt` are bilinear on the whole space, which is
what makes the symmetry computation (`ChapterYangMillsPolySelfAdjoint`) a statement about a linear
map rather than about a partial operator.

## What this settles

It settles the limitation recorded at the end of S0 in `softmodes.md`: the polynomial core has
no common analytic radius (`n` is the radius of `H_n`), so the common-radius Nelson criterion
never applied to it, and the core had no operator on the class level at all.  Both are fixed
here — unconditionally, with no radius hypothesis — and the companion modules
`ChapterYangMillsPolyBasis` and `ChapterYangMillsPolySelfAdjoint` read the resulting diagonal
structure as a Hilbert basis and close S0: `IsSelfAdjoint polyOp.closure` and
`polyOp.closure = gaussOp.closure`.  The earlier plan of transporting the core to the
complexification `Cx` is retired: over `ℝ` the diagonal argument needs no `±i`.
-/
import BookProof.Qym.ChapterYangMillsHermiteAnalytic
import BookProof.Qym.ChapterYangMillsGaussForm

open MeasureTheory Polynomial
open scoped InnerProductSpace

namespace BookProof.YangMillsPolyCore

open BookProof.HermiteCore BookProof.YangMillsMehlerLp BookProof.YangMillsHermiteSpectrum
open BookProof.YangMillsHermiteAnalytic

/-! ## The class map on polynomials -/

/-- **The polynomial classes as a real-linear map.**  Packaged so that additivity and
homogeneity are available as `map_add`/`map_smul` rather than as the ad hoc lemmas of the
analytic module. -/
noncomputable def polyLpLM : Polynomial ℝ →ₗ[ℝ] Lp ℝ 2 gaussMeasure where
  toFun := polyLp
  map_add' p q := by
    refine (MemLp.toLp_congr (memLp_eval (p + q)) ((memLp_eval p).add (memLp_eval q))
      ?_).trans (MemLp.toLp_add (memLp_eval p) (memLp_eval q))
    filter_upwards with x
    simp
  map_smul' c p := polyLp_smul c p

/-- The defining formula of `polyLpLM`. -/
@[simp] theorem polyLpLM_apply (p : Polynomial ℝ) : polyLpLM p = polyLp p := rfl

/-- The zero polynomial has the zero class. -/
theorem polyLp_zero : polyLp (0 : Polynomial ℝ) = 0 := by
  unfold polyLp
  refine (MemLp.toLp_congr (memLp_eval 0) (MemLp.zero (μ := gaussMeasure)) ?_).trans ?_
  · filter_upwards with x
    simp
  · exact MemLp.toLp_zero MemLp.zero

/-- **A polynomial whose class vanishes is zero.**  The class condition is a.e. vanishing, and
`gaussMeasure` sees every nonempty open set, so a continuous representative vanishes
everywhere. -/
theorem polyLp_eq_zero_iff (p : Polynomial ℝ) : polyLp p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have hiff := MemLp.toLp_eq_toLp_iff (memLp_eval p) (memLp_eval (0 : Polynomial ℝ))
    have heq : polyLp p = polyLp (0 : Polynomial ℝ) := by rw [polyLp_zero]; exact h
    have hfun : (fun x : ℝ => p.eval x) =ᵐ[gaussMeasure] fun x => (0 : Polynomial ℝ).eval x :=
      hiff.mp heq
    have hzero : ∀ᵐ x ∂gaussMeasure, p.eval x = 0 := by
      filter_upwards [hfun] with x hx
      simpa using hx
    have hnull : gaussMeasure {y : ℝ | p.eval y ≠ 0} = 0 := MeasureTheory.ae_iff.mp hzero
    have hopen : IsOpen {y : ℝ | p.eval y ≠ 0} :=
      (isClosed_eq p.continuous_aeval continuous_const).isOpen_compl
    have hempty : {y : ℝ | p.eval y ≠ 0} = ∅ := hopen.eq_empty_of_measure_zero hnull
    refine Polynomial.funext fun x => ?_
    by_contra hx
    have hmem : x ∈ ({y : ℝ | p.eval y ≠ 0} : Set ℝ) := by simpa using hx
    rw [hempty] at hmem
    exact hmem
  · rintro rfl
    exact polyLp_zero

/-- **The polynomial classes are linearly independent of each other**: the class map is
injective. -/
theorem polyLp_injective : Function.Injective polyLp := by
  intro p q hpq
  have hsub : polyLp (p - q) = 0 := by
    rw [← polyLpLM_apply, map_sub, polyLpLM_apply, polyLpLM_apply, hpq, sub_self]
  exact sub_eq_zero.mp ((polyLp_eq_zero_iff (p - q)).mp hsub)

/-! ## The Hermite polynomials span the polynomials -/

/-- **The Hermite polynomials span every polynomial.**  `hermiteR n` is monic of degree `n`, so
subtracting the leading term leaves a polynomial of smaller degree; this is the triangularity
that makes `{H_n}` a basis of `Polynomial ℝ` in the only sense needed here. -/
theorem mem_span_hermiteR (p : Polynomial ℝ) :
    p ∈ Submodule.span ℝ (Set.range hermiteR) := by
  have key : ∀ n : ℕ, ∀ q : Polynomial ℝ, q.natDegree ≤ n →
      q ∈ Submodule.span ℝ (Set.range hermiteR) := by
    intro n
    induction n with
    | zero =>
      intro q hq
      have hconst : q = C (q.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hq
      rw [hconst, show C (q.coeff 0) = q.coeff 0 • hermiteR 0 from by
        rw [hermiteR_zero, Polynomial.smul_eq_C_mul, mul_one]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    | succ n ih =>
      intro q hq
      rcases Nat.lt_or_ge q.natDegree (n + 1) with h | h
      · exact ih q (Nat.lt_succ_iff.mp h)
      · have hdeg : q.natDegree = n + 1 := le_antisymm hq h
        have hmain : q = (q - C (q.leadingCoeff) * hermiteR (n + 1))
            + C (q.leadingCoeff) * hermiteR (n + 1) := by abel
        rw [hmain]
        refine Submodule.add_mem _ ?_ ?_
        · refine ih _ ?_
          rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
          intro m hm
          rcases eq_or_lt_of_le (Nat.succ_le_of_lt hm) with hmeq | hmlt
          · rw [← hmeq]
            simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, coeff_hermiteR_self, mul_one]
            rw [show q.coeff (n + 1) = q.leadingCoeff from by
              rw [← hdeg, Polynomial.coeff_natDegree], sub_self]
          · simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, coeff_hermiteR_of_lt hmlt,
              mul_zero, sub_zero]
            exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hmlt)
        · rw [← Polynomial.smul_eq_C_mul]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n + 1, rfl⟩)
  exact key p.natDegree p le_rfl

/-- **The Hermite classes span a dense subspace of `L²(γ dx)`.**  The span of *all* polynomial
classes is dense (`dense_span_polyLp`), and it is contained in the Hermite span by
`mem_span_hermiteR` and the linearity of the class map. -/
theorem dense_hermiteSpan :
    (⊤ : Submodule ℝ (Lp ℝ 2 gaussMeasure))
      ≤ (Submodule.span ℝ (Set.range fun n => polyLp (hermiteR n))).topologicalClosure := by
  have hle : Submodule.span ℝ (Set.range polyLp)
      ≤ Submodule.span ℝ (Set.range fun n => polyLp (hermiteR n)) := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    have hp : polyLpLM p ∈ Submodule.map polyLpLM (Submodule.span ℝ (Set.range hermiteR)) :=
      Submodule.mem_map_of_mem (mem_span_hermiteR p)
    rw [Submodule.map_span, ← Set.range_comp] at hp
    simpa [Function.comp_def] using hp
  exact le_trans dense_span_polyLp (Submodule.topologicalClosure_mono hle)

/-! ## The operator on the polynomial classes -/

/-- The polynomial core as a submodule of `L²(γ dx)`: the range of the class map. -/
noncomputable def polyRange : Submodule ℝ (Lp ℝ 2 gaussMeasure) := LinearMap.range polyLpLM

/-- **The class map is an isomorphism onto its range.**  This is what lets the operator be
defined by prescribing it on representatives. -/
noncomputable def polyEquiv : Polynomial ℝ ≃ₗ[ℝ] polyRange :=
  LinearEquiv.ofBijective polyLpLM.rangeRestrict
    ⟨fun _ _ h => polyLp_injective (congrArg Subtype.val h), fun y => by
      obtain ⟨p, hp⟩ := y.2
      exact ⟨p, Subtype.ext hp⟩⟩

/-- The class isomorphism, read on representatives. -/
@[simp] theorem polyEquiv_apply (p : Polynomial ℝ) :
    (polyEquiv p : Lp ℝ 2 gaussMeasure) = polyLp p := rfl

/-- The inverse of the class isomorphism, on representatives. -/
theorem polyEquiv_symm_mk (p : Polynomial ℝ) :
    polyEquiv.symm ⟨polyLp p, ⟨p, rfl⟩⟩ = p := by
  refine polyEquiv.injective ?_
  rw [LinearEquiv.apply_symm_apply]
  exact Subtype.ext rfl

/-- **The Dirichlet operator on the polynomial core**: `p ↦ −p'' + X p'` carried across the
class isomorphism, so that it acts on classes rather than on representatives. -/
noncomputable def polyOpRange : polyRange →ₗ[ℝ] polyRange :=
  polyEquiv.toLinearMap.comp (dirichletPoly.comp polyEquiv.symm.toLinearMap)

/-- **The Hermite classes are eigenvectors with the real eigenvalues `n`**, at the class
level: this is `dirichletPoly_hermiteR` transported along the isomorphism. -/
theorem polyOpRange_hermiteR (n : ℕ) :
    polyOpRange ⟨polyLp (hermiteR n), ⟨hermiteR n, rfl⟩⟩
      = (n : ℝ) • ⟨polyLp (hermiteR n), ⟨hermiteR n, rfl⟩⟩ := by
  refine Subtype.ext ?_
  change (polyEquiv (dirichletPoly (polyEquiv.symm ⟨polyLp (hermiteR n),
    ⟨hermiteR n, rfl⟩⟩)) : Lp ℝ 2 gaussMeasure) = (n : ℝ) • polyLp (hermiteR n)
  rw [polyEquiv_symm_mk, dirichletPoly_hermiteR, polyEquiv_apply, polyLp_smul]

/-! ## The Hermite span and the core operator -/

/-- The dense Hermite span, the ambient real subspace of the domain. -/
noncomputable def hermiteSpan : Submodule ℝ (Lp ℝ 2 gaussMeasure) :=
  Submodule.span ℝ (Set.range fun n => polyLp (hermiteR n))

/-- The Hermite span is dense, in the form the metric argument consumes. -/
theorem dense_hermiteSpanSet : Dense ((hermiteSpan : Submodule ℝ (Lp ℝ 2 gaussMeasure)) :
    Set (Lp ℝ 2 gaussMeasure)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact top_le_iff.mp dense_hermiteSpan

/-- The Hermite span sits inside the polynomial core. -/
theorem hermiteSpan_le_polyRange : hermiteSpan ≤ polyRange := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    exact ⟨hermiteR n, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul c x hx ihx => exact Submodule.smul_mem _ _ ihx

/-- The operator as a real-linear map on the Hermite span. -/
noncomputable def polyOpH : hermiteSpan →ₗ[ℝ] polyRange :=
  polyOpRange.comp (Submodule.inclusion hermiteSpan_le_polyRange)

/-- The Hermite classes are eigenvectors of `polyOpH` with eigenvalue `n`. -/
theorem polyOpH_hermiteR (n : ℕ) :
    ((polyOpH ⟨polyLp (hermiteR n), Submodule.subset_span ⟨n, rfl⟩⟩ : polyRange) :
      Lp ℝ 2 gaussMeasure) = (n : ℝ) • polyLp (hermiteR n) := by
  have hcoe : (Submodule.inclusion hermiteSpan_le_polyRange
      ⟨polyLp (hermiteR n), Submodule.subset_span ⟨n, rfl⟩⟩ : polyRange)
      = ⟨polyLp (hermiteR n), ⟨hermiteR n, rfl⟩⟩ := Subtype.ext rfl
  have h := polyOpRange_hermiteR n
  rw [polyOpH, LinearMap.comp_apply, hcoe, h, Submodule.coe_smul, Subtype.coe_mk]


/-- **A global real-linear extension of the core operator.**  `polyOpH` lives on the Hermite
span only; composing it with a choice of left inverse of the inclusion gives a map defined on
all of `L²(γ dx)` that agrees with it on the span.  The values off the span are irrelevant —
what the extension buys is a globally defined linear map whose inner products can be expanded
by bilinearity, which is how `coreExt_inner_comm_span` reaches the closure. -/
noncomputable def coreExt : Lp ℝ 2 gaussMeasure →ₗ[ℝ] Lp ℝ 2 gaussMeasure :=
  polyRange.subtype.comp <|
    (polyOpRange.comp (Submodule.inclusion hermiteSpan_le_polyRange)).comp
      hermiteSpan.subtype.leftInverse

/-- The extension agrees with the core operator on the Hermite span. -/
theorem coreExt_apply_mem {v : Lp ℝ 2 gaussMeasure} (hv : v ∈ hermiteSpan) :
    coreExt v = polyOpH ⟨v, hv⟩ := by
  have hinj : LinearMap.ker hermiteSpan.subtype = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact fun a b h => Subtype.ext h
  have hleft : hermiteSpan.subtype.leftInverse v = ⟨v, hv⟩ := by
    have := LinearMap.leftInverse_apply_of_inj (f := hermiteSpan.subtype) hinj ⟨v, hv⟩
    simpa using this
  simp only [coreExt, LinearMap.comp_apply, Submodule.subtype_apply, hleft, polyOpH]
end BookProof.YangMillsPolyCore
