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

The operator is then transported to the complexification `Cx` of `L²(γ dx)` (the corpus's
`BookProof.Complexification`, where the Faris–Lavine notions live).  Its domain is *not* a
ℂ-span of the embedded classes — that would be a spanning-family definition and would need
independence — but the pair condition `z.re, z.im ∈ span{H_n}`: `Cx` is a pair space, so the
action `⟨u, v⟩ ↦ ⟨T u, T v⟩` is automatically well defined, and the Hermite classes embed as
eigenvectors with the real eigenvalues `n`.  `polyCore_essentiallySelfAdjoint` is then
Nelson's eigenbasis criterion `essentiallySelfAdjointOn_of_dense_span_eigenvectors` applied
to it.

## What this does and does not settle

It settles the limitation recorded at the end of S0 in `softmodes.md`: the polynomial core has
no common analytic radius (`n` is the radius of `H_n`), so the common-radius Nelson criterion
never applied to it, and the core had no operator on the class level at all.  Both are fixed
here — unconditionally, with no radius hypothesis.  What is *not* proved is that this operator
is the closure of `gaussOp`; that identification needs the regularity/symmetry work on the
common core, and it is the only remaining step between `polyCore_essentiallySelfAdjoint` and
self-adjointness of `gaussDirichlet`'s closure.
-/
import BookProof.Qym.ChapterYangMillsHermiteAnalytic
import BookProof.Qym.ChapterYangMillsGaussForm
import BookProof.Realification.Complexification

open MeasureTheory Polynomial
open scoped InnerProductSpace

namespace BookProof.YangMillsPolyCore

open BookProof.HermiteCore BookProof.YangMillsMehlerLp BookProof.YangMillsHermiteSpectrum
open BookProof.YangMillsHermiteAnalytic BookProof.Complexification
open BookProof.FarisLavine BookProof.NelsonAnalytic

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

/-! ## The complexified core -/

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

/-- **The complexified polynomial core**: the pairs whose two real components lie in the
Hermite span.  This is a ℂ-submodule because the ℂ-action mixes the components with real
scalars. -/
noncomputable def polyDomC : Submodule ℂ (Cx (Lp ℝ 2 gaussMeasure)) where
  carrier := {z | z.re ∈ hermiteSpan ∧ z.im ∈ hermiteSpan}
  zero_mem' := ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
  add_mem' hx hy := ⟨Submodule.add_mem _ hx.1 hy.1, Submodule.add_mem _ hx.2 hy.2⟩
  smul_mem' c x hx := by
    refine ⟨?_, ?_⟩
    · rw [Cx.csmul_re]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hx.1) (Submodule.smul_mem _ _ hx.2)
    · rw [Cx.csmul_im]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx.2) (Submodule.smul_mem _ _ hx.1)

/-- **The complexified core is dense.**  A pair is approximated by putting approximations of
its two components in the two slots, and the norm of the complexification is the euclidean
norm of the two component norms (`Cx.norm_sq`). -/
theorem dense_polyDomC : Dense ((polyDomC : Submodule ℂ (Cx (Lp ℝ 2 gaussMeasure))) :
    Set (Cx (Lp ℝ 2 gaussMeasure))) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro z
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨a, ha, hda⟩ :=
    Metric.mem_closure_iff.mp (dense_hermiteSpanSet z.re) (ε / 2) (by linarith)
  obtain ⟨b, hb, hdb⟩ :=
    Metric.mem_closure_iff.mp (dense_hermiteSpanSet z.im) (ε / 2) (by linarith)
  refine ⟨(⟨a, b⟩ : Cx (Lp ℝ 2 gaussMeasure)), ⟨ha, hb⟩, ?_⟩
  · have hsq : ‖z - ⟨a, b⟩‖ ^ 2 = ‖z.re - a‖ ^ 2 + ‖z.im - b‖ ^ 2 := by
      rw [Cx.norm_sq]
      simp
    have hle : ‖z - ⟨a, b⟩‖ ≤ ‖z.re - a‖ + ‖z.im - b‖ := by
      have h1 : ‖z - ⟨a, b⟩‖ ^ 2 ≤ (‖z.re - a‖ + ‖z.im - b‖) ^ 2 := by
        rw [hsq]
        nlinarith [norm_nonneg (z.re - a), norm_nonneg (z.im - b)]
      nlinarith [norm_nonneg (z - ⟨a, b⟩), norm_nonneg (z.re - a), norm_nonneg (z.im - b), h1]
    have hdist : ‖z.re - a‖ + ‖z.im - b‖ < ε := by
      rw [dist_eq_norm] at hda hdb
      linarith
    rw [dist_eq_norm]
    linarith

/-- **A global real-linear extension of the core operator.**  `polyOpH` lives on the Hermite
span only; composing it with a choice of left inverse of the inclusion gives a map defined on
all of `L²(γ dx)` that agrees with it on the span.  The values off the span are irrelevant —
the only thing the extension buys is that the complexified operator below is ℂ-linear by
construction, with no proof obligations. -/
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

/-- **The operator on the complexified core.**  It is the complexification of `coreExt`, read
on the pairs whose two real components lie in the Hermite span: `⟨u, v⟩ ↦ ⟨T u, T v⟩`.
Agreement with `polyOpH` on that domain is `coreExt_apply_mem`. -/
noncomputable def polyOpC : polyDomC →ₗ[ℂ] Cx (Lp ℝ 2 gaussMeasure) :=
  (Cx.cxMapₗ coreExt).comp polyDomC.subtype

/-! ## The eigenvectors and the spectral criterion -/

/-- The Hermite classes, embedded as vectors of the complexified core with zero imaginary
part.  These are the eigenvectors the spectral criterion is applied to. -/
def eigenClasses : Set polyDomC :=
  {z | ∃ n : ℕ, z.1.re = polyLp (hermiteR n) ∧ z.1.im = 0}

/-- The embedded Hermite class `⟨H_n, 0⟩` is an eigenvector of `polyOpC` with eigenvalue `n`. -/
theorem polyOpC_eigen {z : polyDomC} (h : z ∈ eigenClasses) :
    ∃ c : ℝ, polyOpC z = (c : ℂ) • ((z : Cx (Lp ℝ 2 gaussMeasure))) := by
  obtain ⟨n, hre, him⟩ := h
  refine ⟨(n : ℝ), ?_⟩
  have hmem : polyLp (hermiteR n) ∈ hermiteSpan := Submodule.subset_span ⟨n, rfl⟩
  have hzre : coreExt z.1.re = (n : ℝ) • z.1.re := by
    rw [hre, coreExt_apply_mem hmem, polyOpH_hermiteR]
  have hzim : coreExt z.1.im = 0 := by
    rw [him, coreExt_apply_mem (Submodule.zero_mem _)]
    exact congrArg Subtype.val (map_zero polyOpH)
  refine Cx.ext ?_ ?_
  · simp only [polyOpC, LinearMap.comp_apply, Cx.cxMapₗ_re, Submodule.coe_subtype]
    rw [hzre, Cx.csmul_re, Complex.ofReal_re, Complex.ofReal_im, him]
    simp
  · simp only [polyOpC, LinearMap.comp_apply, Cx.cxMapₗ_im, Submodule.coe_subtype]
    rw [hzim, Cx.csmul_im, Complex.ofReal_re, Complex.ofReal_im, him]
    simp

/-- Every element of the complexified core lies in the ℂ-span of the Hermite classes. -/
theorem span_eigenClasses_eq_top :
    (Submodule.span ℂ eigenClasses : Submodule ℂ polyDomC) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  have hbase : ∀ (v : Lp ℝ 2 gaussMeasure) (hv : v ∈ hermiteSpan),
      (⟨⟨v, 0⟩, hv, Submodule.zero_mem _⟩ : polyDomC)
        ∈ Submodule.span ℂ eigenClasses := by
    rintro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, rfl⟩ := hx
      exact Submodule.subset_span ⟨n, rfl, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      have hxy : (⟨⟨x, 0⟩, hx, Submodule.zero_mem _⟩ : polyDomC)
          + ⟨⟨y, 0⟩, hy, Submodule.zero_mem _⟩
          = ⟨⟨x + y, 0⟩, Submodule.add_mem _ hx hy, Submodule.zero_mem _⟩ := by
        refine Subtype.ext (Cx.ext ?_ ?_) <;> simp
      rw [← hxy]
      exact Submodule.add_mem _ ihx ihy
    | smul c x hx ihx =>
      have hcx : (c : ℂ) • (⟨⟨x, 0⟩, hx, Submodule.zero_mem _⟩ : polyDomC)
          = ⟨⟨c • x, 0⟩, Submodule.smul_mem _ _ hx, Submodule.zero_mem _⟩ := by
        refine Subtype.ext (Cx.ext ?_ ?_)
        · change ((c : ℂ) • (⟨x, 0⟩ : Cx (Lp ℝ 2 gaussMeasure))).re = c • x
          rw [Cx.csmul_re]
          simp
        · change ((c : ℂ) • (⟨x, 0⟩ : Cx (Lp ℝ 2 gaussMeasure))).im = 0
          rw [Cx.csmul_im]
          simp
      rw [← hcx]
      exact Submodule.smul_mem _ _ ihx
  have hdecomp : z = (⟨⟨z.1.re, 0⟩, z.2.1, Submodule.zero_mem _⟩ : polyDomC)
      + Complex.I • ⟨⟨z.1.im, 0⟩, z.2.2, Submodule.zero_mem _⟩ := by
    refine Subtype.ext (Cx.ext ?_ ?_)
    · simp
    · simp
  rw [hdecomp]
  refine Submodule.add_mem _ (hbase _ z.2.1) ?_
  exact Submodule.smul_mem _ _ (hbase _ z.2.2)

/-- **The polynomial core of `gaussDirichlet` is essentially self-adjoint**, with no radius
hypothesis and no symmetry input: the Hermite classes are a complete eigenbasis, which is the
hypothesis of `essentiallySelfAdjointOn_of_dense_span_eigenvectors`. -/
theorem polyCore_essentiallySelfAdjoint :
    BookProof.FarisLavine.EssentiallySelfAdjointOn polyDomC polyOpC :=
  BookProof.NelsonAnalytic.essentiallySelfAdjointOn_of_dense_span_eigenvectors polyOpC
    eigenClasses (fun x hx => polyOpC_eigen hx) (by
      rw [span_eigenClasses_eq_top]
      simpa using dense_polyDomC)

end BookProof.YangMillsPolyCore
