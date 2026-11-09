/-
# S0 (continued): the Mehler norm identity at the level of `Lp`

The bridge chapter proves the identity as an identity of Lebesgue integrals of `ofReal (· ^ 2)`,
`lintegral_norm_sq_conj`.  That is a pointwise-and-`∫⁻` statement; this module lifts it to the
`Lp`-space level:

* `eLpNorm_gaussRoot_mul` — `‖γ^{1/2} f‖_{L²(dx)} = ‖f‖_{L²(γ dx)}` with `γ dx` as
  `gaussMeasure = volume.withDensity (ofReal ∘ γ^{1/2}²)`;
* `memLp_gaussRoot_mul` — membership of `γ^{1/2} f` in `L²(dx)` is *equivalent* to membership of `f`
  in `L²(γ dx)`, so multiplication by `γ^{1/2}` really is a bijection of the two `Lp` spaces;
* `norm_toLp_mehler` — hence `‖toLp (γ^{1/2} f)‖ = ‖toLp f‖` for every `f` in `L²(γ dx)`: the map
  on `Lp` elements is isometric.

## What is *not* here: a `LinearIsometryEquiv`, and why

The plan's S0 asks for the identity as `LinearIsometryEquiv (Lp ℝ 2 gaussMeasure) (Lp ℝ 2 volume)`.
Mathlib has no such construction for a density change.  The two available routes do not apply:

* `MeasureTheory.Lp.compMeasurePreservingᵢ` (and the `compMeasurePreserving` family in
  `MeasureTheory/Function/LpSpace/`) builds an isometry `L²(ν) → L²(μ)` from a *measure-preserving
  map* `α → β`, i.e. from `ν = μ.map f`.  `gaussMeasure` is not the pushforward of Lebesgue measure
  under any map — a density is not an image measure — so nothing there unifies.
* There is no `Lp`-level `LinearMap`/`LinearIsometryEquiv` for "multiply by a function, changing the
  measure by that function's square".  Building one by hand means defining a map on the quotient
  `Lp ℝ 2 gaussMeasure = {f : ℝ →ₘ[γ] ℝ // eLpNorm f 2 γ < ∞}` through `MemLp.toLp`, proving
  well-definedness on a.e. classes, additivity (`toLp_add` after `toLp_congr`), scalar-linearity
  (there is no `MemLp.toLp_smul` in this mathlib), both inverse laws
  (`gaussRoot * (invGauss * f) = f` a.e., and symmetrically) and `norm_map'` (from `eLpNorm_gaussRoot_mul` below).  That is a bespoke
  quotient-level construction, not a one-line application, and it is not undertaken here.  The
  isometry itself is not in question: `norm_toLp_mehler` is exactly `norm_map'` for every point of
  `L²(γ dx)`, so the missing piece is the bundled equivalence, not the metric content.

## Scope

`eLpNorm_gaussRoot_mul` assumes measurability (as the integral identity does); no integrability
assumption is needed, because `eLpNorm` is allowed to be `∞` on both sides.  Nothing here is a
statement about domains, forms or spectra.
-/
import BookProof.Qym.ChapterYangMillsMehlerBridge

namespace BookProof.YangMillsMehlerLp

open BookProof.YangMillsMehlerBridge MeasureTheory
open scoped ENNReal

noncomputable section

/-- The Gaussian measure `γ dx`, as the density-weighted Lebesgue measure whose density is the
square of the Mehler root. -/
def gaussMeasure : Measure ℝ :=
  (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (gaussRoot x ^ 2))

/-- The density of `gaussMeasure` is measurable. -/
theorem measurable_gaussDensity :
    Measurable (fun x : ℝ => ENNReal.ofReal (gaussRoot x ^ 2)) := by
  have hcont : Continuous fun x : ℝ => gaussRoot x ^ 2 := by
    unfold gaussRoot
    fun_prop
  exact ENNReal.measurable_ofReal.comp hcont.measurable

/-- The squared `enorm` of a real number is its square, as an `ℝ≥0∞`: the bridge between the
integral identity of the bridge chapter and `eLpNorm`. -/
theorem enorm_sq_eq_ofReal_sq (y : ℝ) : ‖y‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (y ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two,
    ← ENNReal.ofReal_pow (abs_nonneg y) 2, sq_abs]

/-- **The Mehler norm identity at the `Lp` level.**  Multiplication by `γ^{1/2}` preserves the
`L²` seminorm when the measure is weighted by `γ`: `‖γ^{1/2} f‖_{L²(dx)} = ‖f‖_{L²(γ dx)}`.

No integrability hypothesis is needed: both sides are `∞` together. -/
theorem eLpNorm_gaussRoot_mul {f : ℝ → ℝ} (hf : Measurable f) :
    eLpNorm (fun x => gaussRoot x * f x) 2 (volume : Measure ℝ) = eLpNorm f 2 gaussMeasure := by
  have h := lintegral_norm_sq_conj hf
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, enorm_sq_eq_ofReal_sq, gaussMeasure]
  rw [h]

/-- **The isometry is a bijection.**  `γ^{1/2} f ∈ L²(dx)` if and only if `f ∈ L²(γ dx)`, because
the identity above equates the two `eLpNorm`s. -/
theorem memLp_gaussRoot_mul {f : ℝ → ℝ} (hf : Measurable f) :
    MemLp (fun x => gaussRoot x * f x) 2 (volume : Measure ℝ) ↔ MemLp f 2 gaussMeasure := by
  have hmeas : AEStronglyMeasurable (fun x => gaussRoot x * f x) (volume : Measure ℝ) := by
    have hcont : Continuous fun x : ℝ => gaussRoot x := by
      unfold gaussRoot
      fun_prop
    exact (hcont.measurable.mul hf).aestronglyMeasurable
  have hiff : eLpNorm (fun x => gaussRoot x * f x) 2 (volume : Measure ℝ)
      = eLpNorm f 2 gaussMeasure := eLpNorm_gaussRoot_mul hf
  constructor
  · intro h
    exact ⟨hf.aestronglyMeasurable (μ := gaussMeasure), by rw [← hiff]; exact h.2⟩
  · intro h
    exact ⟨hmeas, by rw [hiff]; exact h.2⟩

/-- **The Mehler identity on `Lp` elements.**  For `f ∈ L²(γ dx)`, the element
`toLp (γ^{1/2} f) ∈ L²(dx)` has the same norm as `toLp f ∈ L²(γ dx)`. -/
theorem norm_toLp_mehler {f : ℝ → ℝ} (hf : Measurable f) (hmem : MemLp f 2 gaussMeasure) :
    ‖(memLp_gaussRoot_mul hf |>.2 hmem).toLp (fun x => gaussRoot x * f x)‖
      = ‖hmem.toLp f‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_gaussRoot_mul hf]

end

end BookProof.YangMillsMehlerLp
