/-
# S0 (start): the Gaussian-weighted Dirichlet form

The last open S0 acceptance item is closability: `−Δ + x·∇`, densely defined on `C_c^∞` and closable
in `L²(γ dx)`, with the Dirichlet form `∫ γ |∇f|² dx` as its closed form and `H¹(γ)` as its form
domain.  That item has three separable parts, and only the first is done here.

**Done here (no domain choice, no integrability assumption).**

* `gaussWeight` is the density `γ^{1/2}² = exp(−x²/2)` of `γ dx`, and `hasDerivAt_gaussWeight` is
  `(γ^{1/2}²)' = −x γ^{1/2}²` — the identity that the eventual integration by parts consumes, and
  the reason the drift `x·∇` appears in `−Δ + x·∇` rather than `−Δ` alone.
* `gaussForm f g = ∫ x, γ^{1/2}(x)² · f'(x) · g'(x) dx` is the one-coordinate form.
* `gaussForm_comm` (symmetry) and `gaussForm_self_nonneg` (nonnegativity of the diagonal).  Both are
  statements about the integrand and `∫`, so they hold for *every* pair of functions: the Bochner
  integral is total, and a non-integrable integrand contributes `0` on both sides of the symmetry,
  while the diagonal is an integral of a nonnegative integrand.

**Not done here, and the shape of what is left.**

1. *The operator identity.*  On `C_c^∞`, integration by parts gives
   `gaussForm f g = ∫ x, γ^{1/2}(x)² · (−f''(x) + x f'(x)) · g(x) dx`, i.e. the form of the operator
   `gaussDirichlet f = −f'' + x f'` of the bridge chapter.  The ingredients exist
   (`MeasureTheory.integral_deriv_mul_eq_sub` for the improper integral on `ℝ`,
   `Continuous.integrable_of_hasCompactSupport` for the integrability, and
   `hasDerivAt_gaussWeight` above); what is missing is the differentiability bookkeeping of `u` and
   `u'` for a `C²` compactly supported `f`.
2. *Closability proper.*  This needs the graph norm and the identification of the form domain with
   `H¹(γ)`; mathlib has `LinearPMap.IsClosable` and `LinearPMap.closure`, but no weak-derivative or
   Sobolev-space API, so the domain is not available as a `LinearPMap` domain yet.
3. *Density.*  `C_c^∞` is dense in `L²(γ dx)`; mathlib has the `volume` version
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

end

end BookProof.YangMillsGaussForm
