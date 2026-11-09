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
  on `Lp` elements is isometric;
* `mehlerLpEquiv` — the bundled `LinearIsometryEquiv (Lp ℝ 2 gaussMeasure) (Lp ℝ 2 volume)` whose
  forward map is multiplication by `γ^{1/2}` and whose inverse is multiplication by `γ^{-1/2}`.

## Why the equivalence is built by hand

Mathlib has no construction for "multiply by a function and change the measure by that function's
square".  The `Lp`-space isometry API in `MeasureTheory/Function/LpSpace/` is the
`compMeasurePreserving` family, which produces an isometry from a *measure-preserving map*
`α → β` (i.e. from `ν = μ.map f`); a density is not an image measure, so it does not apply.  The
construction below is therefore quotient-level, and every field is paid for:

* membership on `Lp` elements (`memLp_gaussRoot_mul_lp`, `memLp_invGauss_mul_lp`) goes through the
  `eLpNorm` identities in the a.e.-measurable form (`eLpNorm_gaussRoot_mul_ae`,
  `eLpNorm_invGauss_mul_ae`) — a.e. equality is transported between `volume` and `gaussMeasure` in
  both directions (`absolutelyContinuous_volume_gaussMeasure` is the positivity of the Gaussian
  density, `absolutelyContinuous_gaussMeasure_volume` is `withDensity`);
* additivity and ℝ-linearity are `Lp.ext` plus the pointwise identities, because this mathlib has no
  `MemLp.toLp_smul`;
* the inverse laws use `gaussRoot * invGauss = 1` and `invGauss * gaussRoot = 1` on the nose;
* `norm_map'` is `Lp.norm_def` twice plus `eLpNorm_gaussRoot_mul_ae` — the same identity as
  `norm_toLp_mehler`, now stated for every point of `L²(γ dx)`.

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

/-- The Mehler root is measurable. -/
theorem measurable_gaussRoot : Measurable gaussRoot := by
  have hcont : Continuous gaussRoot := by
    unfold gaussRoot
    fun_prop
  exact hcont.measurable

/-- Its reciprocal weight is measurable. -/
theorem measurable_invGauss : Measurable invGauss := by
  have hcont : Continuous invGauss := by
    unfold invGauss
    fun_prop
  exact hcont.measurable

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

/-! ### Transport between the two measures -/

/-- Since the Gaussian density is positive, Lebesgue measure is absolutely continuous with respect
to it: a `volume`-null set has `gaussMeasure`-measure zero. -/
theorem absolutelyContinuous_volume_gaussMeasure : (volume : Measure ℝ) ≪ gaussMeasure := by
  refine withDensity_absolutelyContinuous'
    measurable_gaussDensity.aemeasurable (μ := (volume : Measure ℝ)) ?_
  filter_upwards with x
  have h : 0 < gaussRoot x ^ 2 := pow_pos (gaussRoot_pos x) 2
  exact ne_of_gt (ENNReal.ofReal_pos.mpr h)

/-- The reverse absolute continuity is the defining property of a density. -/
theorem absolutelyContinuous_gaussMeasure_volume : gaussMeasure ≪ (volume : Measure ℝ) :=
  withDensity_absolutelyContinuous _ _

/-! ### The identities for a.e. strongly measurable functions -/

/-- **The Mehler norm identity, a.e. form.**  `eLpNorm_gaussRoot_mul` for functions that are only
known to be a.e. strongly measurable — the form the `Lp` membership lemmas need. -/
theorem eLpNorm_gaussRoot_mul_ae {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume : Measure ℝ)) :
    eLpNorm (fun x => gaussRoot x * f x) 2 (volume : Measure ℝ) = eLpNorm f 2 gaussMeasure := by
  obtain ⟨g, hg, hfg⟩ := hf
  have hfg' : f =ᵐ[gaussMeasure] g :=
    absolutelyContinuous_gaussMeasure_volume.ae_eq hfg
  have hmul : (fun x => gaussRoot x * f x) =ᵐ[volume] (fun x => gaussRoot x * g x) := by
    filter_upwards [hfg] with x hx
    rw [hx]
  rw [eLpNorm_congr_ae hfg']
  exact (eLpNorm_congr_ae hmul).trans (eLpNorm_gaussRoot_mul hg.measurable)

/-- **The reverse Mehler norm identity.**  Multiplication by `γ^{-1/2}` is the inverse weight:
`‖γ^{-1/2} g‖_{L²(γ dx)} = ‖g‖_{L²(dx)}`.  This is the density identity
`γ^{1/2}² · (γ^{-1/2} g)² = g²` read through `withDensity`. -/
theorem eLpNorm_invGauss_mul {g : ℝ → ℝ} (hg : Measurable g) :
    eLpNorm (fun x => invGauss x * g x) 2 gaussMeasure = eLpNorm g 2 (volume : Measure ℝ) := by
  have hpt : ∀ x : ℝ, ENNReal.ofReal (gaussRoot x ^ 2)
      * ENNReal.ofReal ((invGauss x * g x) ^ 2) = ENNReal.ofReal (g x ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ gaussRoot x ^ 2)]
    congr 1
    calc gaussRoot x ^ 2 * (invGauss x * g x) ^ 2
        = (gaussRoot x * invGauss x) ^ 2 * g x ^ 2 := by ring
      _ = g x ^ 2 := by rw [gaussRoot_mul_invGauss]; ring
  have hint : ∫⁻ x, ENNReal.ofReal ((invGauss x * g x) ^ 2) ∂gaussMeasure
      = ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂(volume : Measure ℝ) := by
    rw [gaussMeasure]
    rw [lintegral_withDensity_eq_lintegral_mul (volume : Measure ℝ) measurable_gaussDensity
      (g := fun x => ENNReal.ofReal ((invGauss x * g x) ^ 2))]
    · refine lintegral_congr fun x => ?_
      exact hpt x
    · exact ENNReal.measurable_ofReal.comp ((measurable_invGauss.mul hg).pow_const 2)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, enorm_sq_eq_ofReal_sq]
  rw [hint]

/-- The reverse identity in a.e. form. -/
theorem eLpNorm_invGauss_mul_ae {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g gaussMeasure) :
    eLpNorm (fun x => invGauss x * g x) 2 gaussMeasure = eLpNorm g 2 (volume : Measure ℝ) := by
  obtain ⟨h, hh, hgh⟩ := hg
  have hgh' : g =ᵐ[volume] h := absolutelyContinuous_volume_gaussMeasure.ae_eq hgh
  have hmul : (fun x => invGauss x * g x) =ᵐ[gaussMeasure] fun x => invGauss x * h x := by
    filter_upwards [hgh] with x hx
    rw [hx]
  rw [eLpNorm_congr_ae hmul, eLpNorm_congr_ae hgh']
  exact eLpNorm_invGauss_mul hh.measurable

/-! ### Membership on `Lp` elements -/

/-- Multiplication by `γ^{1/2}` sends `L²(γ dx)` into `L²(dx)`. -/
theorem memLp_gaussRoot_mul_lp (f : Lp ℝ 2 gaussMeasure) :
    MemLp (fun x => gaussRoot x * f x) 2 (volume : Measure ℝ) := by
  have hf : AEStronglyMeasurable (f : ℝ → ℝ) (volume : Measure ℝ) :=
    (Lp.memLp f).1.mono_ac absolutelyContinuous_volume_gaussMeasure
  have hAE : AEStronglyMeasurable (fun x : ℝ => gaussRoot x * f x) (volume : Measure ℝ) :=
    measurable_gaussRoot.aestronglyMeasurable.mul hf
  exact ⟨hAE, by rw [eLpNorm_gaussRoot_mul_ae hf]; exact (Lp.memLp f).2⟩

/-- Multiplication by `γ^{-1/2}` sends `L²(dx)` into `L²(γ dx)`. -/
theorem memLp_invGauss_mul_lp (g : Lp ℝ 2 (volume : Measure ℝ)) :
    MemLp (fun x => invGauss x * g x) 2 gaussMeasure := by
  have hg : AEStronglyMeasurable (g : ℝ → ℝ) gaussMeasure :=
    (Lp.memLp g).1.mono_ac absolutelyContinuous_gaussMeasure_volume
  have hAE : AEStronglyMeasurable (fun x : ℝ => invGauss x * g x) gaussMeasure :=
    measurable_invGauss.aestronglyMeasurable.mul hg
  exact ⟨hAE, by rw [eLpNorm_invGauss_mul_ae hg]; exact (Lp.memLp g).2⟩

/-! ### The bundled equivalence -/

/-- Multiplication by `γ^{1/2}`, as a map `L²(γ dx) → L²(dx)`. -/
def mehlerMap (f : Lp ℝ 2 gaussMeasure) : Lp ℝ 2 (volume : Measure ℝ) :=
  MemLp.toLp (fun x => gaussRoot x * f x) (memLp_gaussRoot_mul_lp f)

/-- Multiplication by `γ^{-1/2}`, the formal inverse of `mehlerMap`. -/
def mehlerMapInv (g : Lp ℝ 2 (volume : Measure ℝ)) : Lp ℝ 2 gaussMeasure :=
  MemLp.toLp (fun x => invGauss x * g x) (memLp_invGauss_mul_lp g)

/-- **The Mehler isometry, bundled.**  Multiplication by `γ^{1/2}` is a `LinearIsometryEquiv` from
`L²(γ dx)` onto `L²(γ^{1/2}² dx) = L²(dx)`, with inverse multiplication by `γ^{-1/2}`.

This is the S0 acceptance item that the unbundled `eLpNorm` identity left open. -/
def mehlerLpEquiv : Lp ℝ 2 gaussMeasure ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ) where
  toFun := mehlerMap
  invFun := mehlerMapInv
  left_inv f := by
    apply Lp.ext
    have h1 : (mehlerMapInv (mehlerMap f) : ℝ → ℝ)
        =ᵐ[gaussMeasure] fun x => invGauss x * (mehlerMap f : ℝ → ℝ) x :=
      MemLp.coeFn_toLp _
    have h2 : (mehlerMap f : ℝ → ℝ) =ᵐ[gaussMeasure]
        fun x => gaussRoot x * (f : ℝ → ℝ) x :=
      absolutelyContinuous_gaussMeasure_volume.ae_eq (MemLp.coeFn_toLp _)
    filter_upwards [h1, h2] with x h1x h2x
    rw [h1x, h2x]
    calc invGauss x * (gaussRoot x * (f : ℝ → ℝ) x)
        = (invGauss x * gaussRoot x) * (f : ℝ → ℝ) x := by ring
      _ = (f : ℝ → ℝ) x := by rw [invGauss_mul_gaussRoot, one_mul]
  right_inv g := by
    apply Lp.ext
    have h1 : (mehlerMap (mehlerMapInv g) : ℝ → ℝ)
        =ᵐ[volume] fun x => gaussRoot x * (mehlerMapInv g : ℝ → ℝ) x :=
      MemLp.coeFn_toLp _
    have h2 : (mehlerMapInv g : ℝ → ℝ) =ᵐ[volume]
        fun x => invGauss x * (g : ℝ → ℝ) x :=
      absolutelyContinuous_volume_gaussMeasure.ae_eq (MemLp.coeFn_toLp _)
    filter_upwards [h1, h2] with x h1x h2x
    rw [h1x, h2x]
    calc gaussRoot x * (invGauss x * (g : ℝ → ℝ) x)
        = (gaussRoot x * invGauss x) * (g : ℝ → ℝ) x := by ring
      _ = (g : ℝ → ℝ) x := by rw [gaussRoot_mul_invGauss, one_mul]
  map_add' f g := by
    apply Lp.ext
    have h1 : (mehlerMap (f + g) : ℝ → ℝ) =ᵐ[volume]
        fun x => gaussRoot x * (f + g : Lp ℝ 2 gaussMeasure) x := MemLp.coeFn_toLp _
    have h2 : (f + g : Lp ℝ 2 gaussMeasure) =ᵐ[volume]
        fun x => (f : ℝ → ℝ) x + (g : ℝ → ℝ) x :=
      absolutelyContinuous_volume_gaussMeasure.ae_eq (Lp.coeFn_add f g)
    have h3 : ((mehlerMap f + mehlerMap g : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ)
        =ᵐ[volume] (mehlerMap f : ℝ → ℝ) + (mehlerMap g : ℝ → ℝ) := Lp.coeFn_add _ _
    have h4 : (mehlerMap f : ℝ → ℝ) =ᵐ[volume] fun x => gaussRoot x * (f : ℝ → ℝ) x :=
      MemLp.coeFn_toLp _
    have h5 : (mehlerMap g : ℝ → ℝ) =ᵐ[volume] fun x => gaussRoot x * (g : ℝ → ℝ) x :=
      MemLp.coeFn_toLp _
    filter_upwards [h1, h2, h3, h4, h5] with x h1x h2x h3x h4x h5x
    rw [h1x, h2x, h3x]
    simp only [Pi.add_apply]
    rw [h4x, h5x]
    ring
  map_smul' c f := by
    apply Lp.ext
    have h1 : (mehlerMap (c • f) : ℝ → ℝ) =ᵐ[volume]
        fun x => gaussRoot x * (c • f : Lp ℝ 2 gaussMeasure) x := MemLp.coeFn_toLp _
    have h2 : (c • f : Lp ℝ 2 gaussMeasure) =ᵐ[volume]
        fun x => c * (f : ℝ → ℝ) x := by
      have := absolutelyContinuous_volume_gaussMeasure.ae_eq (Lp.coeFn_smul c f)
      simpa using this
    have h3 : ((c • mehlerMap f : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ)
        =ᵐ[volume] c • (mehlerMap f : ℝ → ℝ) := Lp.coeFn_smul c (mehlerMap f)
    have h4 : (mehlerMap f : ℝ → ℝ) =ᵐ[volume] fun x => gaussRoot x * (f : ℝ → ℝ) x :=
      MemLp.coeFn_toLp _
    filter_upwards [h1, h2, h3, h4] with x h1x h2x h3x h4x
    rw [h1x, h2x]
    simp only [RingHom.id_apply]
    rw [h3x]
    change gaussRoot x * (c * (f : ℝ → ℝ) x) = c * ((mehlerMap f : ℝ → ℝ) x)
    rw [h4x]
    ring
  norm_map' f := by
    have hf : AEStronglyMeasurable (f : ℝ → ℝ) (volume : Measure ℝ) :=
      (Lp.memLp f).1.mono_ac absolutelyContinuous_volume_gaussMeasure
    show ‖MemLp.toLp (fun x => gaussRoot x * (f : ℝ → ℝ) x) (memLp_gaussRoot_mul_lp f)‖ = ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_gaussRoot_mul_ae hf]

end

end BookProof.YangMillsMehlerLp
