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

**Not done here, and the shape of what is left.**

1. *Closability proper.*  This needs the graph norm and the identification of the form domain with
   `H¹(γ)`; mathlib has `LinearPMap.IsClosable` and `LinearPMap.closure`, but no weak-derivative or
   Sobolev-space API, so the domain is not available as a `LinearPMap` domain yet.
2. *Density.*  `C_c^∞` is dense in `L²(γ dx)`; mathlib has the `volume` version
   (`MeasureTheory.MemLp` + `ContDiff.dense`-style results) but not the density-weighted transport,
   though `ChapterYangMillsMehlerLp.absolutelyContinuous_volume_gaussMeasure` is the piece that
   makes the transport routine.

The `99`-coordinate form is the sum of these over coordinates (`laplaceVec`/`pd` in
`ChapterYangMillsMehlerProduct`), so nothing here is coordinate-count specific.
-/
import BookProof.Qym.ChapterYangMillsMehlerBridge

namespace BookProof.YangMillsGaussForm

open BookProof.YangMillsMehlerBridge MeasureTheory

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

end

end BookProof.YangMillsGaussForm
