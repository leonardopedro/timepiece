/-
# S0: the Gaussian-weighted Dirichlet form and its operator

The last open S0 acceptance item is closability: `−Δ + x·∇`, densely defined on `C_c^∞` and closable
in `L²(γ dx)`, with the Dirichlet form `∫ γ |∇f|² dx` as its closed form and `H¹(γ)` as its form
domain.  That item has three separable parts; the first and the operator half of it are done here.

**Done here.**

* `gaussWeight` is the density `γ^{1/2}² = exp(−x²/2)` of `γ dx`, and `hasDerivAt_gaussWeight` is
  `(γ^{1/2}²)' = −x γ^{1/2}²` — the identity the integration by parts consumes, and the reason the
  drift `x·∇` appears in `−Δ + x·∇` rather than `−Δ` alone.
* `gaussForm f g = ∫ x, γ^{1/2}(x)² · f'(x) · g'(x) dx` is the one-coordinate form.
* `gaussForm_comm` (symmetry) and `gaussForm_self_nonneg` (nonnegativity of the diagonal).  Both are
  statements about the integrand and `∫`, so they hold for *every* pair of functions: the Bochner
  integral is total, and a non-integrable integrand contributes `0` on both sides of the symmetry,
  while the diagonal is an integral of a nonnegative integrand.
* **`gaussForm_eq_integral_gaussDirichlet` is the operator identity**: for `f` of class `C²` with
  compact support and `g` of class `C¹`,
  `gaussForm f g = ∫ x, γ^{1/2}(x)² · (−f''(x) + x f'(x)) · g(x) dx`, the operator on the right
  being `gaussDirichlet` of the bridge chapter.  So the symmetric form is the form of `−Δ + x·∇`,
  on the compactly supported core, and not merely a quadratic functional.  The proof is one
  application of mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` (integration by
  parts, the integrability of the three products supplied by compact support) plus `deriv_mul` and
  `deriv_gaussWeight`.
* **`integral_gaussDirichlet_mul_comm` is the symmetry of the operator** in `L²(γ dx)` on that core:
  `⟨−Δf + x·∇f, g⟩_{L²(γ)} = ⟨f, −Δg + x·∇g⟩_{L²(γ)}`.  It is the form symmetry read through the
  operator identity in both orders, and it is what a closability argument actually consumes —
  symmetry of the *operator*, not only of the quadratic form.
* **The operator is defined on `L²(γ dx)` classes, not just on functions** — the three facts a
  closure argument needs from the core:
  `isOpenPosMeasure_gaussMeasure` (the density is strictly positive, so "zero a.e." implies "zero on
  a dense set"), `eq_of_ae_eq_gaussMeasure` (a continuous function that is zero `γ`-a.e. *is* zero:
  `Measure.eq_of_ae_eq` plus that open-positivity), `gaussDirichlet_eq_zero_of_ae_eq_zero` (so `T`
  is well defined on classes, not on representatives), `hasCompactSupport_gaussDirichlet` and
  `memLp_gaussDirichlet` (so `T` maps the core into `L²(γ dx)`; the proof multiplies by `γ^{1/2}`,
  uses `memLp_gaussRoot_mul` to swap the weighted norm for the Lebesgue one, and closes with
  square-integrability of a continuous compactly supported function against `volume`).
* **`gaussOp` is `T` as a `LinearPMap` on `L²(γ dx)`.**  `gaussCore` is the core as a submodule of
  `L²(γ dx)` (a class is in it when it has a `C²`-compactly-supported representative), and
  `gaussCoreRep` chooses one.  The value on a class is `gaussOpFun f = toLp (T (gaussCoreRep f))`,
  and `gaussOpFun_eq_toLp` says it computes `toLp (T F)` for *any* admissible representative `F` —
  the choice never appears in a statement.  Linearity at the function level is
  `gaussDirichlet_add`/`gaussDirichlet_smul`, the congruence `gaussDirichlet_congr_ae` upgrades a.e.
  equality of representatives to equality of images, and the one `Lp` glue lemma mathlib lacks is
  `memLp_toLp_const_smul` (for addition `MemLp.toLp_add` already exists, and is even `rfl`).
  Finally  `gaussOpFun_add`/`gaussOpFun_smul` make `gaussOpFun` a linear map on the core, and
  `gaussOp` is the resulting `LinearPMap`.
* **`gaussOp` is densely defined, symmetric as a pairing, and closable.**  Density is
  `dense_gaussCore`, and it is the only non-elementary input: `C_c` is dense in `L²(dx)`
  (`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`), a compactly supported continuous function is
  uniformly continuous, `UniformContinuous.exists_contDiff_dist_le` smooths it in the sup norm,
  and a `ContDiffBump` that is `1` on its support cuts the smooth approximation back to compact
  (`exists_contDiff_hasCompactSupport_eLpNorm_sub_lt`); the Mehler isometry then carries that dense
  family into `L²(γ dx)`, where its members are the classes of `γ^{-1/2} φ` for smooth compactly
  supported `φ` — smooth and compactly supported, so in the core
  (`mehlerMapInv_toLp_mem_gaussCore`).
  Symmetry as an inner-product identity is `gaussOp_inner_comm`: the integral symmetry
  `integral_gaussDirichlet_mul_comm` read through `inner_def` on `toLp` images, with
  `integral_gaussMeasure_eq_integral_gaussWeight` performing the density-to-weight translation.  So
  `gaussOp.IsFormalAdjoint gaussOp`, hence `gaussOp ≤ gaussOp.adjoint`; the adjoint of a densely
  defined operator is closed (`adjoint_isClosed`), and `IsClosable.leIsClosable` transfers that, so
  `gaussOp.IsClosable`.

The `99`-coordinate form is the sum of these over coordinates (`laplaceVec`/`pd` in
`ChapterYangMillsMehlerProduct`), so nothing here is coordinate-count specific.

What is *not* here: the closure `gaussOp.closure` itself, its self-adjointness, and the
identification of its domain with the form domain of `gaussForm` — those are the S0/Friedrichs
content that `ChapterYangMillsFriedrichs` consumes, not the operator bookkeeping.
-/
import BookProof.Qym.ChapterYangMillsMehlerLp

namespace BookProof.YangMillsGaussForm

open BookProof.YangMillsMehlerBridge BookProof.YangMillsMehlerLp MeasureTheory

open scoped RealInnerProductSpace

noncomputable section

/-- The density of the Gaussian measure `γ dx = gaussWeight dx`, i.e. the square of the Mehler
root: `γ^{1/2}(x)² = exp(−x²/2)`. -/
def gaussWeight (x : ℝ) : ℝ := gaussRoot x ^ 2

/-- The Gaussian density is positive. -/
theorem gaussWeight_pos (x : ℝ) : 0 < gaussWeight x := by
  unfold gaussWeight
  exact pow_pos (gaussRoot_pos x) 2

/-- **The derivative of the density.**  `(γ^{1/2}²)' = −x · γ^{1/2}²`.  This is where the drift
`x·∇` of `−Δ + x·∇` comes from: the weight carries the `x`, not the operator's second derivative. -/
theorem hasDerivAt_gaussWeight (x : ℝ) :
    HasDerivAt gaussWeight (-(x * gaussWeight x)) x := by
  have h := (hasDerivAt_gaussRoot x).pow 2
  unfold gaussWeight
  convert h using 1
  ring

/-- The Gaussian density is smooth: `γ^{1/2}² = exp(−x²/2)`. -/
theorem contDiff_gaussWeight : ContDiff ℝ ⊤ gaussWeight := by
  have h : gaussWeight = fun x : ℝ => Real.exp (-(x ^ 2) / 2) := by
    funext x
    exact gaussRoot_sq x
  rw [h]
  exact Real.contDiff_exp.comp (((contDiff_id.pow 2).neg).div_const 2)

/-- The derivative of the density, as a function. -/
theorem deriv_gaussWeight (x : ℝ) : deriv gaussWeight x = -(x * gaussWeight x) :=
  (hasDerivAt_gaussWeight x).deriv

/-- The Gaussian Dirichlet form, in one coordinate: `∫ γ^{1/2}² f' g' dx`.  It is the one-coordinate
summand of `∫ γ |∇f|² dx`; the Bochner integral makes it total, so no integrability hypothesis is
needed to state it. -/
def gaussForm (f g : ℝ → ℝ) : ℝ :=
  ∫ x, gaussWeight x * deriv f x * deriv g x

/-- **The form is symmetric.**  No integrability or differentiability hypothesis: the identity is a
pointwise `ring` identity under `∫`. -/
theorem gaussForm_comm (f g : ℝ → ℝ) : gaussForm f g = gaussForm g f := by
  unfold gaussForm
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-- **The diagonal is nonnegative.**  The integrand is the density times a square. -/
theorem gaussForm_self_nonneg (f : ℝ → ℝ) : 0 ≤ gaussForm f f := by
  unfold gaussForm
  refine integral_nonneg fun x => ?_
  have hw : 0 ≤ gaussWeight x := (gaussWeight_pos x).le
  calc (0 : ℝ) ≤ gaussWeight x * (deriv f x) ^ 2 := mul_nonneg hw (sq_nonneg _)
    _ = gaussWeight x * deriv f x * deriv f x := by ring

/-- The integrability predicate that cuts out the form's domain: the density-weighted square of
`f'` is integrable.  Naming it keeps the domain a hypothesis rather than a silent assumption. -/
def MemGaussForm (f : ℝ → ℝ) : Prop :=
  Integrable (fun x => gaussWeight x * deriv f x * deriv f x)

/-- On its domain the diagonal of the form is finite (in the sense that the Bochner integral of an
integrable function is its value, not `0` by convention) — the form's finiteness obligation,
isolated from any statement about `H¹(γ)`. -/
theorem gaussForm_self_of_mem {f : ℝ → ℝ} (hf : MemGaussForm f) :
    Integrable (fun x => gaussWeight x * deriv f x * deriv f x) ∧ 0 ≤ gaussForm f f :=
  ⟨hf, gaussForm_self_nonneg f⟩

/-! ## The operator identity: the form *is* the form of `−Δ + x·∇`

Integration by parts once, against the compactly supported factor.  The weight puts the drift in,
because `(γ^{1/2}²)' = −x γ^{1/2}²`, so

`∫ γ^{1/2}² f' g' = −∫ (γ^{1/2}² f')' g = ∫ γ^{1/2}² (−f'' + x f') g`,

and the operator on the right is `gaussDirichlet`.  The single integration-by-parts step is
mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, which needs the three products
integrable: `f` of class `C²` and `g` of class `C¹`, with `f` compactly supported, supplies exactly
that, and the boundary terms are absent because the support of `f` is, so nothing is assumed about
the growth of `g`. -/

/-- **The form of the weighted Dirichlet operator.**  For `f` of class `C²` and compactly supported
and `g` of class `C¹`, `gaussForm f g` is the `L²(dx)` pairing of `gaussDirichlet f` against `g`
with the weight `γ^{1/2}²` — the operator identity that turns the symmetric form into the operator
`−Δ + x·∇`.

The regularity is `C²`/`C¹`, not `C^∞`: the corpus's `ContDiff ℝ ⊤` is mathlib's *analytic* order
`ω`, and an analytic function with compact support on `ℝ` is identically zero, so a `ContDiff ℝ ⊤`
hypothesis here would make the statement vacuous. -/
theorem gaussForm_eq_integral_gaussDirichlet {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 1 g) :
    gaussForm f g = ∫ x, gaussWeight x * gaussDirichlet f x * g x := by
  have hws : ContDiff ℝ 1 gaussWeight := contDiff_gaussWeight.of_le (by simp)
  have hd1 : ContDiff ℝ 1 (deriv f) := ContDiff.deriv' hf
  have hF : ContDiff ℝ 1 (fun x => gaussWeight x * deriv f x) := hws.mul hd1
  have hFdiff : Differentiable ℝ (fun x => gaussWeight x * deriv f x) :=
    hF.differentiable (by simp)
  have hFc : HasCompactSupport (fun x => gaussWeight x * deriv f x) := hfc.deriv.mul_left
  have hFd : Continuous (deriv (fun x => gaussWeight x * deriv f x)) :=
    hF.continuous_deriv le_rfl
  have hg' : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hI1 : Integrable
      (fun x => deriv (fun y => gaussWeight y * deriv f y) x * g x) :=
    (hFd.mul hg.continuous).integrable_of_hasCompactSupport (hFc.deriv.mul_right)
  have hI2 : Integrable (fun x => gaussWeight x * deriv f x * deriv g x) :=
    (hF.continuous.mul hg').integrable_of_hasCompactSupport (hFc.mul_right)
  have hI3 : Integrable (fun x => gaussWeight x * deriv f x * g x) :=
    (hF.continuous.mul hg.continuous).integrable_of_hasCompactSupport (hFc.mul_right)
  have hbp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℝ)) (f := fun x => gaussWeight x * deriv f x) (g := g)
    (v := (1 : ℝ)) (by simpa only [fderiv_apply_one_eq_deriv] using hI1)
    (by simpa only [fderiv_apply_one_eq_deriv] using hI2)
    (by simpa only [fderiv_apply_one_eq_deriv] using hI3) hFdiff (hg.differentiable (by simp))
  have hderivF : ∀ x, deriv (fun y => gaussWeight y * deriv f y) x
      = -(x * gaussWeight x) * deriv f x
        + gaussWeight x * deriv (fun y => deriv f y) x := by
    intro x
    have h := deriv_mul (hasDerivAt_gaussWeight x).differentiableAt
      (hd1.differentiable (by simp) x)
    rw [deriv_gaussWeight] at h
    simpa only [Pi.mul_apply] using h
  have hleft : gaussForm f g
      = -∫ x, deriv (fun y => gaussWeight y * deriv f y) x * g x := by
    rw [gaussForm]
    simpa only [fderiv_apply_one_eq_deriv] using hbp
  rw [hleft, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hderivF x, gaussDirichlet]
  ring

/-- **The operator is symmetric in `L²(γ dx)`.**  On the compactly supported `C²` core, the pairing
`⟨−Δf + x·∇f, g⟩_{L²(γ)}` is symmetric in `f` and `g`: both sides are `gaussForm f g`, read through
the operator identity once in each order, with form symmetry `gaussForm_comm` in between.

This is the hypothesis a closability argument needs — symmetry *of the operator*, not only of the
quadratic form — so it is stated separately rather than folded into the identity. -/
theorem integral_gaussDirichlet_mul_comm {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    ∫ x, gaussWeight x * gaussDirichlet f x * g x
      = ∫ x, gaussWeight x * f x * gaussDirichlet g x := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  calc ∫ x, gaussWeight x * gaussDirichlet f x * g x
      = gaussForm f g := (gaussForm_eq_integral_gaussDirichlet hf hfc hg1).symm
    _ = gaussForm g f := gaussForm_comm f g
    _ = ∫ x, gaussWeight x * gaussDirichlet g x * f x :=
        gaussForm_eq_integral_gaussDirichlet hg hgc hf1
    _ = ∫ x, gaussWeight x * f x * gaussDirichlet g x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        ring

/-! ## The operator on classes

The form-level statements above are about *functions*.  The operator that a closure argument acts on
lives on `L²(γ dx)` *classes*, so two more things are needed, and both are here: the operator sends
the compactly supported `C²` core into `L²(γ dx)`, and it kills functions that vanish a.e., so it
descends to classes without choosing a representative. -/

/-- **`gaussMeasure` is positive on nonempty open sets.**  The density `γ^{1/2}²` is strictly
positive, and `volume ≪ gaussMeasure` (`absolutelyContinuous_volume_gaussMeasure`) already puts the
measure in `IsOpenPosMeasure` — that is what turns "zero a.e." into "zero on a dense set". -/
instance isOpenPosMeasure_gaussMeasure : Measure.IsOpenPosMeasure gaussMeasure :=
  Measure.AbsolutelyContinuous.isOpenPosMeasure absolutelyContinuous_volume_gaussMeasure

/-- **A continuous function that is zero `γ`-a.e. is zero.**  `{x | f x = 0}` is closed, so its
complement is an open null set, and `gaussMeasure` is positive on nonempty opens. -/
theorem eq_of_ae_eq_gaussMeasure {f g : ℝ → ℝ} (h : f =ᵐ[gaussMeasure] g) (hf : Continuous f)
    (hg : Continuous g) : f = g :=
  Measure.eq_of_ae_eq h hf hg

/-- **The operator vanishes on a.e.-zero functions**, so it is well defined on `L²(γ dx)` classes:
if a core function is zero `γ`-a.e. it is zero, and hence so are its derivatives and `gaussDirichlet
f`.  Without this, `T` would depend on the chosen representative of a class. -/
theorem gaussDirichlet_eq_zero_of_ae_eq_zero {f : ℝ → ℝ} (hf : Continuous f)
    (h : f =ᵐ[gaussMeasure] 0) : gaussDirichlet f = 0 := by
  have hz : f = 0 := eq_of_ae_eq_gaussMeasure h hf continuous_const
  subst hz
  funext x
  simp [gaussDirichlet]

/-- **`gaussDirichlet` preserves compact support.**  Both summands are supported in `supp f'` and
`supp f''`, so the operator never spreads a core function past the support of its second derivative.
This is what keeps `γ^{1/2}·gaussDirichlet f` compactly supported, and hence in `L²(dx)`. -/
theorem hasCompactSupport_gaussDirichlet {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (gaussDirichlet f) := by
  have h2 : HasCompactSupport (fun x => -(deriv (fun y => deriv f y) x)) :=
    (HasCompactSupport.deriv (HasCompactSupport.deriv hf)).neg
  have h1 : HasCompactSupport (fun x => x * deriv f x) :=
    (HasCompactSupport.deriv hf).mul_left (f := fun x : ℝ => x)
  have hsum := h2.add h1
  simpa only [gaussDirichlet, Pi.add_apply] using hsum

/-- **The operator maps the core into `L²(γ dx)`.**  Multiplying by `γ^{1/2}` turns the `γ`-norm
into the `volume`-norm (`memLp_gaussRoot_mul`), and `γ^{1/2}·gaussDirichlet f` is continuous with
compact support, hence square-integrable against Lebesgue measure. -/
theorem memLp_gaussDirichlet {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    MemLp (gaussDirichlet f) 2 gaussMeasure := by
  have hcont : Continuous (gaussDirichlet f) := by
    have hd2 : Continuous (fun x => deriv (fun y => deriv f y) x) :=
      (hf.deriv' : ContDiff ℝ 1 (deriv f)).continuous_deriv (le_refl 1)
    have hd1 : Continuous (deriv f) :=
      hf.continuous_deriv (by norm_num)
    exact (hd2.neg.add (continuous_id.mul hd1))
  have hgauss : Continuous gaussRoot :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_gaussRoot x).continuousAt
  have hprod : Continuous (fun x => gaussRoot x * gaussDirichlet f x) := hgauss.mul hcont
  have hcs : HasCompactSupport (fun x => gaussRoot x * gaussDirichlet f x) :=
    (hasCompactSupport_gaussDirichlet hfc).mul_left (f := gaussRoot)
  have hcsSq : HasCompactSupport (fun x => (gaussRoot x * gaussDirichlet f x) ^ 2) := by
    have h := hcs.mul_left (f := fun x => gaussRoot x * gaussDirichlet f x)
    simpa only [Pi.mul_apply, pow_two] using h
  have hsq : Integrable (fun x => (gaussRoot x * gaussDirichlet f x) ^ 2) (volume : Measure ℝ) :=
    (hprod.pow 2).integrable_of_hasCompactSupport hcsSq
  rw [← memLp_gaussRoot_mul hcont.measurable]
  exact (memLp_two_iff_integrable_sq hprod.aestronglyMeasurable).2 hsq

/-! ## The operator as a partially defined linear map

The well-definedness facts above are what let `T = −Δ + x·∇` become a `LinearPMap` on `L²(γ dx)`.
The domain is the `C²`-compactly-supported core; the value on a class is `T` of a chosen
representative, and every change of representative is an a.e. equality upgraded to pointwise
equality by `eq_of_ae_eq_gaussMeasure`, so the choice never shows up in a statement. -/

/-- The `C²`-compactly-supported core, as a submodule of `L²(γ dx)`: a class is in the core when it
has a representative of class `C²` with compact support. -/
def gaussCore : Submodule ℝ (Lp ℝ 2 gaussMeasure) where
  carrier := {f | ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧ ⇑f =ᵐ[gaussMeasure] F}
  zero_mem' := ⟨0, contDiff_const, HasCompactSupport.zero, by
    filter_upwards [Lp.coeFn_zero (μ := gaussMeasure) (p := 2) (E := ℝ)] with x hx using hx⟩
  add_mem' := by
    rintro f g ⟨F, hF, hFc, hFe⟩ ⟨G, hG, hGc, hGe⟩
    exact ⟨F + G, hF.add hG, hFc.add hGc, (Lp.coeFn_add f g).trans (hFe.add hGe)⟩
  smul_mem' := by
    rintro c f ⟨F, hF, hFc, hFe⟩
    exact ⟨c • F, hF.const_smul c, hFc.smul_left,
      (Lp.coeFn_smul c f).trans (hFe.const_smul c)⟩

/-- A chosen representative of a core class: `C²` with compact support. -/
noncomputable def gaussCoreRep (f : gaussCore) : ℝ → ℝ :=
  Classical.choose (show ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F
    ∧ ⇑(f : Lp ℝ 2 gaussMeasure) =ᵐ[gaussMeasure] F from f.2)

/-- The chosen representative has the three properties the core promises. -/
theorem gaussCoreRep_spec (f : gaussCore) :
    ContDiff ℝ 2 (gaussCoreRep f) ∧ HasCompactSupport (gaussCoreRep f)
      ∧ (f : Lp ℝ 2 gaussMeasure) =ᵐ[gaussMeasure] gaussCoreRep f :=
  Classical.choose_spec (show ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F
    ∧ ⇑(f : Lp ℝ 2 gaussMeasure) =ᵐ[gaussMeasure] F from f.2)

/-- **`gaussDirichlet` respects a.e. equality.**  Two continuous representatives of the same
`L²(γ dx)` class have the same image: `gaussMeasure` is open-positive, so a.e. equality of
continuous functions is equality (`eq_of_ae_eq_gaussMeasure`), and the operator is a function of
the function.  This is well-definedness on classes, the representative choice being isolated in
`gaussCoreRep`. -/
theorem gaussDirichlet_congr_ae {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G)
    (h : F =ᵐ[gaussMeasure] G) : gaussDirichlet F = gaussDirichlet G := by
  rw [eq_of_ae_eq_gaussMeasure h hF hG]

/-- **The operator is additive** on `C²` functions: the second derivative and the drift are each
additive, the drift because `deriv_add` is. -/
theorem gaussDirichlet_add {F G : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) :
    gaussDirichlet (F + G) = gaussDirichlet F + gaussDirichlet G := by
  have hdF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hdG : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hdF' : Differentiable ℝ (deriv F) :=
    (hF.deriv' : ContDiff ℝ 1 (deriv F)).differentiable (by norm_num)
  have hdG' : Differentiable ℝ (deriv G) :=
    (hG.deriv' : ContDiff ℝ 1 (deriv G)).differentiable (by norm_num)
  funext x
  have hd : deriv (F + G) = deriv F + deriv G :=
    funext fun y => deriv_add (hdF y) (hdG y)
  have h2 : deriv (fun y => deriv (F + G) y) x
      = deriv (fun y => deriv F y) x + deriv (fun y => deriv G y) x := by
    rw [show (fun y => deriv (F + G) y) = deriv F + deriv G from hd]
    exact deriv_add (hdF' x) (hdG' x)
  simp only [gaussDirichlet, Pi.add_apply, h2, deriv_add (hdF x) (hdG x)]
  ring

/-- **The operator is homogeneous** on `C²` functions. -/
theorem gaussDirichlet_smul {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (c : ℝ) :
    gaussDirichlet (c • F) = c • gaussDirichlet F := by
  have hdF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hdF' : Differentiable ℝ (deriv F) :=
    (hF.deriv' : ContDiff ℝ 1 (deriv F)).differentiable (by norm_num)
  have hd1 : deriv (c • F) = fun y => c * deriv F y := by
    funext y
    exact deriv_const_smul c (hdF y)
  have hd2 : (fun y => deriv (c • F) y) = fun y => c * deriv F y := hd1
  funext x
  have h1x : deriv (c • F) x = c * deriv F x := congrFun hd1 x
  have h2 : deriv (fun y => deriv (c • F) y) x = c * deriv (fun y => deriv F y) x := by
    rw [hd2]
    exact deriv_const_smul c (hdF' x)
  simp only [gaussDirichlet, Pi.smul_apply, h2, h1x, smul_eq_mul]
  ring

/-- The operator applied to a core class: `T` of the chosen representative. -/
noncomputable def gaussOpFun (f : gaussCore) : Lp ℝ 2 gaussMeasure :=
  MemLp.toLp (gaussDirichlet (gaussCoreRep f))
    (memLp_gaussDirichlet (gaussCoreRep_spec f).1 (gaussCoreRep_spec f).2.1)

/-- **`gaussOpFun` computes `T` on any admissible representative**, so the choice inside
`gaussCoreRep` is invisible: for any `C²`-compactly-supported `F` representing the class, the image
is `toLp (T F)`. -/
theorem gaussOpFun_eq_toLp {f : gaussCore} {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hFe : (f : Lp ℝ 2 gaussMeasure) =ᵐ[gaussMeasure] F) :
    gaussOpFun f = MemLp.toLp (gaussDirichlet F) (memLp_gaussDirichlet hF hFc) := by
  have hds : gaussDirichlet (gaussCoreRep f) = gaussDirichlet F :=
    gaussDirichlet_congr_ae (gaussCoreRep_spec f).1.continuous hF.continuous
      ((gaussCoreRep_spec f).2.2.symm.trans hFe)
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun hds))

/-- `toLp` commutes with scalar multiplication.  (Mathlib has the additive version
`MemLp.toLp_add` but not this one for `MemLp`.) -/
theorem memLp_toLp_const_smul (c : ℝ) {G : ℝ → ℝ} (hG : MemLp G 2 gaussMeasure)
    (h : MemLp (c • G) 2 gaussMeasure) : h.toLp (c • G) = c • hG.toLp G := by
  apply Lp.ext
  have h1 : ⇑(h.toLp (c • G)) =ᵐ[gaussMeasure] (c • G : ℝ → ℝ) := MemLp.coeFn_toLp h
  have h2 : ⇑(c • hG.toLp G) =ᵐ[gaussMeasure] c • ⇑(hG.toLp G) := Lp.coeFn_smul c _
  have h3 : c • ⇑(hG.toLp G) =ᵐ[gaussMeasure] c • G := (MemLp.coeFn_toLp hG).const_smul c
  exact h1.trans (h2.trans h3).symm

/-- **The operator is additive on the core**, hence is a linear map there.  Each step trades the
chosen representative for a concrete witness (`gaussOpFun_eq_toLp`), applies
`gaussDirichlet_add`, and reassembles with `MemLp.toLp_add`. -/
theorem gaussOpFun_add (f g : gaussCore) : gaussOpFun (f + g) = gaussOpFun f + gaussOpFun g := by
  have hf := gaussCoreRep_spec f
  have hg := gaussCoreRep_spec g
  have hsum : ((f + g : gaussCore) : Lp ℝ 2 gaussMeasure) =ᵐ[gaussMeasure]
      gaussCoreRep f + gaussCoreRep g := by
    have h1 : ((f + g : gaussCore) : Lp ℝ 2 gaussMeasure)
        = (f : Lp ℝ 2 gaussMeasure) + g := Submodule.coe_add f g
    rw [h1]
    exact (Lp.coeFn_add _ _).trans (hf.2.2.add hg.2.2)
  calc gaussOpFun (f + g)
      = MemLp.toLp (gaussDirichlet (gaussCoreRep f + gaussCoreRep g))
          (memLp_gaussDirichlet (hf.1.add hg.1) (hf.2.1.add hg.2.1)) :=
        gaussOpFun_eq_toLp (f := f + g) (F := gaussCoreRep f + gaussCoreRep g)
          (hf.1.add hg.1) (hf.2.1.add hg.2.1) hsum
    _ = MemLp.toLp (gaussDirichlet (gaussCoreRep f) + gaussDirichlet (gaussCoreRep g))
          ((memLp_gaussDirichlet hf.1 hf.2.1).add (memLp_gaussDirichlet hg.1 hg.2.1)) :=
        MemLp.toLp_congr _ _
          (Filter.Eventually.of_forall (congrFun (gaussDirichlet_add hf.1 hg.1)))
    _ = MemLp.toLp (gaussDirichlet (gaussCoreRep f)) (memLp_gaussDirichlet hf.1 hf.2.1)
          + MemLp.toLp (gaussDirichlet (gaussCoreRep g)) (memLp_gaussDirichlet hg.1 hg.2.1) :=
        MemLp.toLp_add _ _
    _ = gaussOpFun f + gaussOpFun g := by
        rw [gaussOpFun_eq_toLp (f := f) (F := gaussCoreRep f) hf.1 hf.2.1 hf.2.2,
          gaussOpFun_eq_toLp (f := g) (F := gaussCoreRep g) hg.1 hg.2.1 hg.2.2]

/-- **The operator is homogeneous on the core.** -/
theorem gaussOpFun_smul (c : ℝ) (f : gaussCore) : gaussOpFun (c • f) = c • gaussOpFun f := by
  have hf := gaussCoreRep_spec f
  have hsm : ((c • f : gaussCore) : Lp ℝ 2 gaussMeasure) =ᵐ[gaussMeasure] c • gaussCoreRep f := by
    have h1 : ((c • f : gaussCore) : Lp ℝ 2 gaussMeasure) = c • (f : Lp ℝ 2 gaussMeasure) :=
      Submodule.coe_smul c f
    rw [h1]
    exact (Lp.coeFn_smul c _).trans (hf.2.2.const_smul c)
  calc gaussOpFun (c • f)
      = MemLp.toLp (gaussDirichlet (c • gaussCoreRep f))
          (memLp_gaussDirichlet (hf.1.const_smul c) hf.2.1.smul_left) :=
        gaussOpFun_eq_toLp (f := c • f) (F := c • gaussCoreRep f)
          (hf.1.const_smul c) hf.2.1.smul_left hsm
    _ = MemLp.toLp (c • gaussDirichlet (gaussCoreRep f))
          ((memLp_gaussDirichlet hf.1 hf.2.1).const_smul c) :=
        MemLp.toLp_congr _ _
          (Filter.Eventually.of_forall (congrFun (gaussDirichlet_smul hf.1 c)))
    _ = c • MemLp.toLp (gaussDirichlet (gaussCoreRep f)) (memLp_gaussDirichlet hf.1 hf.2.1) :=
        memLp_toLp_const_smul c _ _
    _ = c • gaussOpFun f := by
        rw [gaussOpFun_eq_toLp (f := f) (F := gaussCoreRep f) hf.1 hf.2.1 hf.2.2]

/-- The operator as a linear map on its core. -/
noncomputable def gaussOpLinearMap : gaussCore →ₗ[ℝ] Lp ℝ 2 gaussMeasure where
  toFun := gaussOpFun
  map_add' := gaussOpFun_add
  map_smul' := gaussOpFun_smul

/-- **`T = −Δ + x·∇` as a partially defined operator on `L²(γ dx)`**, with the `C²`-compactly-
supported core as domain.  Closability of this `LinearPMap` is the remaining S0 content. -/
noncomputable def gaussOp : Lp ℝ 2 gaussMeasure →ₗ.[ℝ] Lp ℝ 2 gaussMeasure where
  domain := gaussCore
  toFun := gaussOpLinearMap

/-- On the core, `gaussOp` is `gaussOpFun`, by definition. -/
theorem gaussOp_apply (f : gaussCore) : gaussOp f = gaussOpFun f := rfl

/-! ## Density of the smooth core

`gaussCore` is dense in `L²(γ dx)`, and this is what makes `gaussOp` densely defined — the
hypothesis mathlib's adjoint construction and every closability statement ask for.

The proof is a chain of approximations, all of it in `L²(dx)` where density is available:

* `C_c` is dense in `L²(dx)` (`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`), so a class is
  approximated by a continuous compactly supported `g`;
* `g` is uniformly continuous (compact support plus continuity, via
  `Continuous.uniformContinuous_of_tendsto_cocompact`), so
  `UniformContinuous.exists_contDiff_dist_le` gives a smooth `u` uniformly close to it;
* multiplying by a `ContDiffBump` that is `1` on `tsupport g` makes `u` compactly supported while
  keeping it close to `g`, and the norm of the difference is bounded by the sup bound times
  `(volume (tsupport χ))^{1/2}`;
* the Mehler isometry `mehlerLpEquiv` carries the resulting dense family into `L²(γ dx)`, where its
  members are exactly the classes represented by `γ^{-1/2} φ` for smooth compactly supported `φ` —
  smooth and compactly supported, so in the core.

This section proves the metric facts; the membership in `gaussCore` and the final `Dense` statement
follow below. -/

/-- **A bounded function vanishing outside a set has small `eLpNorm`.**  The pointwise bound
`|u| ≤ c` is compared with the indicator of the supporting set `K`, whose `eLpNorm` is
`c · (volume K)^{1/2}` by `eLpNorm_indicator_const_le`.  Compactness of `K` is not used here —
it enters only once the bound is compared with a target, which needs `volume K < ∞`. -/
theorem eLpNorm_le_of_forall_notMem {u : ℝ → ℝ} {K : Set ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hzero : ∀ x, x ∉ K → u x = 0) (hsup : ∀ x, |u x| ≤ c) :
    eLpNorm u 2 (volume : Measure ℝ) ≤ ENNReal.ofReal c * (volume K) ^ (1 / 2 : ℝ) := by
  have hind : ∀ x, ‖u x‖ ≤ ‖K.indicator (fun _ => c) x‖ := by
    intro x
    by_cases hx : x ∈ K
    · simpa only [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg hc] using hsup x
    · rw [Set.indicator_of_notMem hx, hzero x hx, norm_zero]
  refine (eLpNorm_mono_ae (μ := (volume : Measure ℝ)) (p := 2)
    (Filter.Eventually.of_forall hind)).trans ?_
  have h2 : (1 : ℝ) / (2 : ENNReal).toReal = 1 / 2 := by norm_num
  have h := eLpNorm_indicator_const_le (μ := (volume : Measure ℝ)) (s := K) c (p := 2)
  rw [h2] at h
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hc] at h
  exact h

/-- **Smooth compactly supported classes are dense in `L²(dx)`.**  For a class `F` and any target
`η > 0` there is a `C²` compactly supported `φ` whose class is within `η` of `F` in `L²(dx)`.

`C_c` supplies the first approximation, uniform continuity of a compactly supported continuous
function turns it into a smooth `u` that is small in the *sup* norm, and the `ContDiffBump` that is
`1` on `tsupport g` cuts `u` down to compact support without spoiling that bound.  The sup bound is
then integrated with `eLpNorm_le_of_forall_notMem`. -/
theorem exists_contDiff_hasCompactSupport_eLpNorm_sub_lt (F : Lp ℝ 2 (volume : Measure ℝ))
    {η : ℝ} (hη : 0 < η) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      eLpNorm ((F : ℝ → ℝ) - φ) 2 (volume : Measure ℝ) < ENNReal.ofReal η := by
  -- a continuous compactly supported approximation of `F`
  obtain ⟨g, hgcpt, hgclose, hgcont, _hgmem⟩ :=
    MemLp.exists_hasCompactSupport_eLpNorm_sub_le (p := 2) (μ := (volume : Measure ℝ))
      (by norm_num) (Lp.memLp F) (ε := ENNReal.ofReal (η / 3))
      (ENNReal.ofReal_pos.mpr (by linarith : (0 : ℝ) < η / 3)).ne'
  -- it is uniformly continuous
  have hguc : UniformContinuous g :=
    hgcont.uniformContinuous_of_tendsto_cocompact hgcpt.is_zero_at_infty
  -- a radius for its support
  obtain ⟨r, hrs⟩ := hgcpt.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hRs : tsupport g ⊆ Metric.closedBall (0 : ℝ) (max r 0) :=
    hrs.trans (Metric.closedBall_subset_closedBall (le_max_left r 0))
  -- the bump that is `1` on it and vanishes outside a slightly larger ball
  have hr0 : (0 : ℝ) ≤ max r 0 := le_max_right r 0
  set b : ContDiffBump (0 : ℝ) :=
    ⟨max r 0 + 1, max r 0 + 2, by linarith, by linarith⟩ with hb
  have hχsmooth : ContDiff ℝ 2 (⇑b) := by simpa using b.contDiff (n := 2)
  have hχcpt : HasCompactSupport (⇑b) := b.hasCompactSupport
  have hχone : ∀ x ∈ tsupport g, b x = 1 := fun x hx =>
    b.one_of_mem_closedBall (hRs.trans (Metric.closedBall_subset_closedBall (by linarith)) hx)
  have hχsupport : tsupport (⇑b) = Metric.closedBall (0 : ℝ) (max r 0 + 2) := b.tsupport_eq
  set c : ℝ := (volume (tsupport (⇑b))).toReal ^ (1 / 2 : ℝ) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg ENNReal.toReal_nonneg _
  set ε' : ℝ := η / 3 / (c + 1) with hε'
  have hε'pos : 0 < ε' := by
    rw [hε']
    exact div_pos (by linarith) (by linarith)
  -- the smooth approximation, uniformly close
  obtain ⟨u, huSmooth, hudist⟩ := hguc.exists_contDiff_dist_le hε'pos
  have hu2 : ContDiff ℝ 2 u := huSmooth.of_le (WithTop.coe_le_coe.mpr le_top)
  -- cut it down to compact support
  set u' : ℝ → ℝ := fun x => b x * u x with hu'
  have hu'2 : ContDiff ℝ 2 u' := by rw [hu']; exact hχsmooth.mul hu2
  have hu'cpt : HasCompactSupport u' := by
    rw [hu']
    simpa only [Pi.mul_apply, mul_comm] using hχcpt.mul_left (f := u)
  -- the pointwise bound where `χ = 1`, and the trivial one outside `tsupport χ`
  have hbabs : ∀ x, |b x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (b.nonneg)]
    exact b.le_one
  have hu'close : ∀ x, |u' x - g x| ≤ ε' := by
    intro x
    show |b x * u x - g x| ≤ ε'
    by_cases hxg : x ∈ tsupport g
    · have hd : |u x - g x| < ε' := by
        rw [← Real.dist_eq]
        exact hudist x
      rw [hχone x hxg, one_mul]
      exact hd.le
    · have hg0 : g x = 0 := image_eq_zero_of_notMem_tsupport hxg
      have hd : |u x| < ε' := by
        have h := hudist x
        rwa [Real.dist_eq, hg0, sub_zero] at h
      calc |b x * u x - g x| = |b x * u x| := by rw [hg0, sub_zero]
        _ = |b x| * |u x| := abs_mul _ _
        _ ≤ 1 * |u x| := mul_le_mul_of_nonneg_right (hbabs x) (abs_nonneg _)
        _ = |u x| := one_mul _
        _ ≤ ε' := hd.le
  -- and the values it keeps are supported in `tsupport χ`
  have hsub : tsupport g ⊆ tsupport (⇑b) :=
    fun x hx => subset_tsupport _ (Function.mem_support.mpr (by rw [hχone x hx]; exact one_ne_zero))
  have hu'zero : ∀ x, x ∉ tsupport (⇑b) → u' x - g x = 0 := by
    intro x hx
    have hg0 : g x = 0 := by
      by_contra hne
      exact hx (hsub (subset_tsupport g (Function.mem_support.mpr hne)))
    show b x * u x - g x = 0
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, hg0, sub_zero]
  have hχfin : volume (tsupport (⇑b)) ≠ ⊤ := by
    rw [hχsupport]
    exact (isCompact_closedBall (0 : ℝ) (max r 0 + 2)).measure_lt_top.ne
  -- the sup bound integrated
  have hsmall : eLpNorm (u' - g) 2 (volume : Measure ℝ) ≤ ENNReal.ofReal (η / 3) := by
    have hpow : volume (tsupport (⇑b)) ^ (1 / 2 : ℝ) = ENNReal.ofReal c := by
      rw [← ENNReal.ofReal_toReal hχfin,
        ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
        hc]
    calc eLpNorm (u' - g) 2 (volume : Measure ℝ)
        ≤ ENNReal.ofReal ε' * volume (tsupport (⇑b)) ^ (1 / 2 : ℝ) :=
          eLpNorm_le_of_forall_notMem hε'pos.le hu'zero (fun x => by
            simpa only [Pi.sub_apply] using hu'close x)
      _ = ENNReal.ofReal ε' * ENNReal.ofReal c := by rw [hpow]
      _ = ENNReal.ofReal (ε' * c) := (ENNReal.ofReal_mul hε'pos.le).symm
      _ ≤ ENNReal.ofReal (η / 3) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hε', div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0 : ℝ) < c + 1)]
          nlinarith [hc0]
  -- the triangle inequality
  have hFmeas : AEStronglyMeasurable ((F : ℝ → ℝ) - g) (volume : Measure ℝ) :=
    ((Lp.memLp F).1).sub hgcont.aestronglyMeasurable
  have hgmeas : AEStronglyMeasurable (g - u') (volume : Measure ℝ) :=
    hgcont.aestronglyMeasurable.sub hu'2.continuous.aestronglyMeasurable
  have hsplit : ((F : ℝ → ℝ) - u') =ᵐ[volume] ((F : ℝ → ℝ) - g) + (g - u') :=
    Filter.Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
  have hsmall' : eLpNorm (g - u') 2 (volume : Measure ℝ) ≤ ENNReal.ofReal (η / 3) := by
    rw [eLpNorm_congr_ae (show (g - u') =ᵐ[volume] -(u' - g) from
      Filter.Eventually.of_forall fun x => by
        simp only [Pi.sub_apply, Pi.neg_apply]
        ring), eLpNorm_neg]
    exact hsmall
  have htri : eLpNorm ((F : ℝ → ℝ) - u') 2 (volume : Measure ℝ)
      ≤ ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) := by
    rw [eLpNorm_congr_ae hsplit]
    exact (eLpNorm_add_le hFmeas hgmeas (by norm_num)).trans (add_le_add hgclose hsmall')
  refine ⟨u', hu'2, hu'cpt, lt_of_le_of_lt htri ?_⟩
  rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
  exact ENNReal.ofReal_lt_ofReal_iff hη |>.mpr (by linarith)

/-- A continuous compactly supported real function is in `L²(dx)`. -/
theorem memLp_of_hasCompactSupport {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    MemLp f 2 (volume : Measure ℝ) := by
  have hcs : HasCompactSupport (fun x => f x ^ 2) := by
    have h := hfc.mul_left (f := f)
    simpa only [Pi.mul_apply, pow_two] using h
  exact (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
    ((hf.pow 2).integrable_of_hasCompactSupport hcs)

/-- **The smooth `γ^{-1/2}` family sits in the core.**  For smooth compactly supported `φ` the class
`toLp_γ (γ^{-1/2} φ)` has the representative `γ^{-1/2} φ` itself, which is `C²` and compactly
supported, so it is in `gaussCore`.  This is the membership half of the density statement: the
Mehler isometry's inverse sends smooth compactly supported `L²(dx)` classes into the core. -/
theorem mehlerMapInv_toLp_mem_gaussCore {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφmem : MemLp φ 2 (volume : Measure ℝ)) :
    mehlerMapInv (MemLp.toLp φ hφmem) ∈ gaussCore := by
  refine ⟨fun x => invGauss x * φ x, ?_, ?_, ?_⟩
  · have hinv : ContDiff ℝ 2 invGauss := by
      unfold invGauss
      fun_prop
    exact hinv.mul hφ
  · exact hφc.mul_left (f := invGauss)
  · refine (MemLp.coeFn_toLp (memLp_invGauss_mul_lp (MemLp.toLp φ hφmem))).trans ?_
    filter_upwards [absolutelyContinuous_gaussMeasure_volume.ae_eq
      (MemLp.coeFn_toLp hφmem)] with x hx
    rw [hx]

/-- **The smooth core is dense in `L²(γ dx)`.**  Approximate `mehlerLpEquiv F` by a smooth
compactly supported `L²(dx)` class, pull the approximation back through the Mehler isometry (an
isometry, so distances are preserved), and note that what comes back lies in `gaussCore` by
`mehlerMapInv_toLp_mem_gaussCore`. -/
theorem dense_gaussCore : Dense (gaussCore : Set (Lp ℝ 2 gaussMeasure)) := by
  intro F
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨φ, hφ2, hφc, hφclose⟩ :=
    exists_contDiff_hasCompactSupport_eLpNorm_sub_lt (mehlerLpEquiv F) (by linarith : 0 < ε / 2)
  have hφmem : MemLp φ 2 (volume : Measure ℝ) := memLp_of_hasCompactSupport hφ2.continuous hφc
  refine ⟨mehlerLpEquiv.symm (MemLp.toLp φ hφmem),
    mehlerMapInv_toLp_mem_gaussCore hφ2 hφc hφmem, ?_⟩
  have hdist : dist (mehlerLpEquiv F) (MemLp.toLp φ hφmem)
      = (eLpNorm ((mehlerLpEquiv F : ℝ → ℝ) - φ) 2 (volume : Measure ℝ)).toReal := by
    rw [Lp.dist_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hφmem] with x hx
    simp only [Pi.sub_apply, hx]
  have hlt : (eLpNorm ((mehlerLpEquiv F : ℝ → ℝ) - φ) 2 (volume : Measure ℝ)).toReal < ε := by
    have hfin : ENNReal.ofReal (ε / 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    have ha : eLpNorm ((mehlerLpEquiv F : ℝ → ℝ) - φ) 2 (volume : Measure ℝ) ≠ ⊤ :=
      ne_top_of_lt hφclose
    have h := (ENNReal.toReal_lt_toReal ha hfin).mpr hφclose
    rw [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ ε / 2)] at h
    linarith
  calc dist F (mehlerLpEquiv.symm (MemLp.toLp φ hφmem))
      = dist (mehlerLpEquiv F) (MemLp.toLp φ hφmem) := by
        rw [← LinearIsometryEquiv.dist_map mehlerLpEquiv F
            (mehlerLpEquiv.symm (MemLp.toLp φ hφmem)),
          LinearIsometryEquiv.apply_symm_apply]
    _ = (eLpNorm ((mehlerLpEquiv F : ℝ → ℝ) - φ) 2 (volume : Measure ℝ)).toReal := hdist
    _ < ε := hlt

/-- `gaussOp` is densely defined: its domain is the core, which is dense by `dense_gaussCore`. -/
theorem dense_gaussOp_domain : Dense (gaussOp.domain : Set (Lp ℝ 2 gaussMeasure)) :=
  dense_gaussCore

/-! ## Symmetry as an inner-product identity, and closability

The integral symmetry `integral_gaussDirichlet_mul_comm` is a statement about integrals over `dx`
against the weight.  Read through `inner_def` on `toLp` images it becomes
`⟪T f, g⟫ = ⟪f, T g⟫` on the core, i.e. `gaussOp.IsFormalAdjoint gaussOp`.  Mathlib's
`IsFormalAdjoint.le_adjoint` then gives `gaussOp ≤ gaussOp†`, and since the adjoint is closed
(`adjoint_isClosed`, using density) `IsClosable.leIsClosable` makes `gaussOp` closable. -/

/-- **Integration against `γ dx` is a weighted Lebesgue integral.** -/
theorem integral_gaussMeasure_eq_integral_gaussWeight (h : ℝ → ℝ) :
    ∫ x, h x ∂gaussMeasure = ∫ x, gaussWeight x * h x ∂(volume : Measure ℝ) := by
  rw [gaussMeasure, integral_withDensity_eq_integral_toReal_smul measurable_gaussDensity
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [gaussWeight, ENNReal.toReal_ofReal (sq_nonneg (gaussRoot x)), smul_eq_mul]

/-- **Symmetry of `gaussOp` on its core, as an inner-product identity.**  The left matrix element is
`∫ γ · T f · g`, the right one `∫ γ · f · T g`, and `integral_gaussDirichlet_mul_comm` identifies
them. -/
theorem gaussOp_inner_comm (f g : gaussCore) :
    ⟪gaussOp f, (g : Lp ℝ 2 gaussMeasure)⟫ = ⟪(f : Lp ℝ 2 gaussMeasure), gaussOp g⟫ := by
  have hf := gaussCoreRep_spec f
  have hg := gaussCoreRep_spec g
  have hmemf := memLp_gaussDirichlet hf.1 hf.2.1
  have hmemg := memLp_gaussDirichlet hg.1 hg.2.1
  have hL : ⟪gaussOp f, (g : Lp ℝ 2 gaussMeasure)⟫
      = ∫ x, gaussWeight x * gaussDirichlet (gaussCoreRep f) x * gaussCoreRep g x :=
    calc ⟪gaussOp f, (g : Lp ℝ 2 gaussMeasure)⟫
        = ∫ x, ⟪⇑(MemLp.toLp (gaussDirichlet (gaussCoreRep f)) hmemf) x,
            ⇑(g : Lp ℝ 2 gaussMeasure) x⟫ ∂gaussMeasure := by
          rw [gaussOp_apply,
            gaussOpFun_eq_toLp (f := f) (F := gaussCoreRep f) hf.1 hf.2.1 hf.2.2, L2.inner_def]
      _ = ∫ x, gaussWeight x * ⟪⇑(MemLp.toLp (gaussDirichlet (gaussCoreRep f)) hmemf) x,
            ⇑(g : Lp ℝ 2 gaussMeasure) x⟫ :=
          integral_gaussMeasure_eq_integral_gaussWeight _
      _ = ∫ x, gaussWeight x * gaussDirichlet (gaussCoreRep f) x * gaussCoreRep g x := by
          refine integral_congr_ae ?_
          filter_upwards [absolutelyContinuous_volume_gaussMeasure.ae_eq (MemLp.coeFn_toLp hmemf),
            absolutelyContinuous_volume_gaussMeasure.ae_eq hg.2.2] with x hx hy
          rw [hx, hy, RCLike.inner_apply', RCLike.conj_to_real, mul_assoc]
  have hR : ⟪(f : Lp ℝ 2 gaussMeasure), gaussOp g⟫
      = ∫ x, gaussWeight x * gaussCoreRep f x * gaussDirichlet (gaussCoreRep g) x :=
    calc ⟪(f : Lp ℝ 2 gaussMeasure), gaussOp g⟫
        = ∫ x, ⟪⇑(f : Lp ℝ 2 gaussMeasure) x,
            ⇑(MemLp.toLp (gaussDirichlet (gaussCoreRep g)) hmemg) x⟫ ∂gaussMeasure := by
          rw [gaussOp_apply,
            gaussOpFun_eq_toLp (f := g) (F := gaussCoreRep g) hg.1 hg.2.1 hg.2.2, L2.inner_def]
      _ = ∫ x, gaussWeight x * ⟪⇑(f : Lp ℝ 2 gaussMeasure) x,
            ⇑(MemLp.toLp (gaussDirichlet (gaussCoreRep g)) hmemg) x⟫ :=
          integral_gaussMeasure_eq_integral_gaussWeight _
      _ = ∫ x, gaussWeight x * gaussCoreRep f x * gaussDirichlet (gaussCoreRep g) x := by
          refine integral_congr_ae ?_
          filter_upwards [absolutelyContinuous_volume_gaussMeasure.ae_eq hf.2.2,
            absolutelyContinuous_volume_gaussMeasure.ae_eq (MemLp.coeFn_toLp hmemg)] with x hx hy
          rw [hx, hy, RCLike.inner_apply', RCLike.conj_to_real, mul_assoc]
  rw [hL, hR, integral_gaussDirichlet_mul_comm hf.1 hf.2.1 hg.1 hg.2.1]

/-- `gaussOp` is a formal adjoint of itself: it is symmetric on its core. -/
theorem gaussOp_isFormalAdjoint : gaussOp.IsFormalAdjoint gaussOp := gaussOp_inner_comm

/-- **`gaussOp` is contained in its adjoint.**  This is the symmetry plus density, nothing else. -/
theorem gaussOp_le_adjoint : gaussOp ≤ gaussOp.adjoint :=
  LinearPMap.IsFormalAdjoint.le_adjoint dense_gaussOp_domain gaussOp_isFormalAdjoint

/-- **`gaussOp` is closable.**  A symmetric operator contained in its adjoint is closable, since the
adjoint of a densely defined operator is closed. -/
theorem gaussOp_isClosable : gaussOp.IsClosable :=
  (LinearPMap.adjoint_isClosed dense_gaussOp_domain).isClosable.leIsClosable gaussOp_le_adjoint

/-! ### What the closure inherits, and the one statement it does not

`gaussOp.closure` is closed by construction, its domain is dense, the `C²` core is a core of it, and
it is contained in `gaussOp†` (the adjoint is a closed extension, and the closure is the smallest
closed extension).  Self-adjointness of the closure would need the *reverse* containment
`gaussOp† ≤ gaussOp.closure` — equivalently, that every element of the adjoint's domain already lies
in the closure's graph, i.e. that the `C²` core is a core for the adjoint as well as for `gaussOp`.
That is the essential-self-adjointness statement, and it is **not** proved here: it is a genuine
analytic theorem about `−Δ + x·∇` (deficiency spaces of the ODE `−f'' + x f' = ±i f`, or elliptic
regularity in `H¹(γ)`), whereas mathlib has no weak-derivative, `H¹(γ)` or deficiency-index API, and
the corpus' Hermite chapter stops at the Hermite polynomials and their ODE — it has no Hilbert-basis
or oscillator spectral theorem to lean on.  See the S0 entry of `softmodes.md`. -/

/-- The closure of a closable operator is closed. -/
theorem gaussOp_closure_isClosed : gaussOp.closure.IsClosed :=
  gaussOp_isClosable.closure_isClosed

/-- The closure is densely defined: its domain contains the core. -/
theorem dense_gaussOp_closure_domain : Dense (gaussOp.closure.domain : Set (Lp ℝ 2 gaussMeasure)) :=
  Dense.mono (LinearPMap.le_closure gaussOp).1 dense_gaussOp_domain

/-- **The `C²` core is a core of the closure**: the restriction of `gaussOp` to `gaussCore`
already has `gaussOp.closure` as its closure.  (This is the general `LinearPMap.closureHasCore`; the
only input specific to this operator is that `gaussOp.domain` is `gaussCore` by definition.) -/
theorem gaussOp_closure_hasCore : gaussOp.closure.HasCore gaussCore :=
  LinearPMap.closureHasCore gaussOp

/-- **The closure is contained in the adjoint.**  `gaussOp.adjoint` is closed and contains
`gaussOp`, so — the closure being the smallest closed extension — it contains `gaussOp.closure`. -/
theorem gaussOp_closure_le_adjoint : gaussOp.closure ≤ gaussOp.adjoint := by
  have hclosed : gaussOp.adjoint.IsClosed := LinearPMap.adjoint_isClosed dense_gaussOp_domain
  have hfix : gaussOp.adjoint.closure = gaussOp.adjoint := by
    apply LinearPMap.eq_of_eq_graph
    rw [LinearPMap.closure_def hclosed.isClosable, ← hclosed.isClosable.choose_spec,
      hclosed.submodule_topologicalClosure_eq]
  have h := LinearPMap.IsClosable.closure_mono hclosed.isClosable gaussOp_le_adjoint
  rwa [hfix] at h

end

end BookProof.YangMillsGaussForm
