import Mathlib
import BookProof.ChapterShannonSampling

/-!
# Sampling for band-limited functions on the line (the Paley–Wiener picture)

`BookProof/ChapterShannonSampling.lean` proves the Whittaker–Shannon sampling theorem in the
*spectral* picture: the signal is *defined* as the inverse Fourier transform `bandSignal F` of a
square-integrable spectrum `F` over the band `[-T/2, T/2]`.  That left one gap, recorded there as
an honest boundary: the identification of that class with the genuinely band-limited functions of
the line, i.e. with the functions whose *own* Fourier transform vanishes outside the band.

This file closes that gap.  A function `f : ℝ → ℂ` is `BandLimited T` when it is continuous,
integrable, and its Fourier transform `𝓕 f` vanishes outside the band `|ξ| ≤ T/2`.  Then:

* `BandLimited.integrable_fourier` — the spectrum is continuous with compact support, hence
  integrable and bounded, so Fourier inversion applies;
* **`BandLimited.eq_bandSignal`** — `f` *is* the band-limited signal of its own spectrum, that
  spectrum being viewed (`bandSpectrumLp`) as a square-integrable function on the circle of
  circumference `T`;
* **`BandLimited.hasSum_sinc`** — the classical sampling theorem on the line:
  `f x = ∑_{n ∈ ℤ} f (n/T) · sinc (T x - n)` for every real `x`, an unconditionally convergent
  series;
* **`BandLimited.eq_of_samples_eq`** — a band-limited function is determined by its samples at
  the lattice `{n/T}`;
* **`BandLimited.hasSum_sq_samples`** — Parseval for the samples: `∑_n ‖f (n/T)‖²` converges to
  `T · ∫_ℝ ‖𝓕 f‖²`.

Everything is `sorry`-free and uses only the standard axioms.
-/

namespace BookProof.ChapterPaleyWienerSampling

open MeasureTheory Complex AddCircle Set
open scoped Real FourierTransform
open BookProof.ChapterShannonSampling (sinc bandSignal exists_rep half_add_period)

/-- A *band-limited function of bandwidth `T`*: a continuous integrable function on the line
whose Fourier transform vanishes outside the band `|ξ| ≤ T/2`. -/
structure BandLimited (T : ℝ) (f : ℝ → ℂ) : Prop where
  /-- The function is continuous. -/
  continuous : Continuous f
  /-- The function is integrable, so that its Fourier transform is defined. -/
  integrable : Integrable f
  /-- The Fourier transform vanishes outside the band. -/
  spectrum_support : ∀ ξ : ℝ, T / 2 < |ξ| → 𝓕 f ξ = 0

namespace BandLimited

variable {T : ℝ} {f g : ℝ → ℂ}

/-- The Fourier transform of an integrable function is continuous. -/
theorem continuous_fourier (hf : BandLimited T f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by apply continuous_inner) hf.integrable

/-- The spectrum of a band-limited function has compact support. -/
theorem hasCompactSupport_fourier (hf : BandLimited T f) : HasCompactSupport (𝓕 f) := by
  refine HasCompactSupport.intro (K := Icc (-(T / 2)) (T / 2)) isCompact_Icc ?_
  intro ξ hξ
  refine hf.spectrum_support ξ ?_
  rcases lt_or_ge (T / 2) |ξ| with h | h
  · exact h
  · exact absurd (abs_le.mp h) (by simpa [Set.mem_Icc] using hξ)

/-- The spectrum of a band-limited function is integrable. -/
theorem integrable_fourier (hf : BandLimited T f) : Integrable (𝓕 f) :=
  hf.continuous_fourier.integrable_of_hasCompactSupport hf.hasCompactSupport_fourier

/-- The spectrum of a band-limited function is bounded. -/
theorem exists_bound_fourier (hf : BandLimited T f) : ∃ C, ∀ ξ : ℝ, ‖𝓕 f ξ‖ ≤ C :=
  hf.hasCompactSupport_fourier.exists_bound_of_continuous hf.continuous_fourier

end BandLimited

section Spectrum

variable {T : ℝ} [hT : Fact (0 < T)] {f g : ℝ → ℂ}

/-- The spectrum of `f`, viewed as a function on the circle of circumference `T`: the
`T`-periodic extension of `𝓕 f` from the band `(-T/2, T/2]`. -/
noncomputable def bandSpectrum (T : ℝ) [Fact (0 < T)] (f : ℝ → ℂ) : AddCircle T → ℂ :=
  AddCircle.liftIoc T (-(T / 2)) (𝓕 f)

theorem bandSpectrum_coe_apply {ξ : ℝ} (hξ : ξ ∈ Ioc (-(T / 2)) (-(T / 2) + T)) :
    bandSpectrum T f ξ = 𝓕 f ξ :=
  show AddCircle.liftIoc T (-(T / 2)) (𝓕 f) ξ = 𝓕 f ξ from AddCircle.liftIoc_coe_apply hξ

theorem measurable_bandSpectrum (hf : BandLimited T f) : Measurable (bandSpectrum T f) := by
  have h₁ : Measurable (equivIoc T (-(T / 2))) :=
    (AddCircle.measurePreserving_equivIoc T (a := -(T / 2))).measurable
  have h₂ : Measurable fun ξ : Ioc (-(T / 2)) (-(T / 2) + T) => 𝓕 f (ξ : ℝ) :=
    (hf.continuous_fourier.comp continuous_subtype_val).measurable
  exact show Measurable (AddCircle.liftIoc T (-(T / 2)) (𝓕 f)) from h₂.comp h₁

theorem norm_bandSpectrum_le (hf : BandLimited T f) :
    ∃ C, ∀ z : AddCircle T, ‖bandSpectrum T f z‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf.exists_bound_fourier
  refine ⟨C, fun z => ?_⟩
  obtain ⟨ξ, hξ, rfl⟩ := exists_rep (T := T) z
  rw [bandSpectrum_coe_apply hξ]
  exact hC ξ

theorem memLp_bandSpectrum (hf : BandLimited T f) :
    MemLp (bandSpectrum T f) 2 (haarAddCircle (T := T)) := by
  obtain ⟨C, hC⟩ := norm_bandSpectrum_le hf
  exact MemLp.of_bound (measurable_bandSpectrum hf).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

/-- The spectrum of a band-limited function as an element of `L²` of the circle. -/
noncomputable def bandSpectrumLp (hf : BandLimited T f) : Lp ℂ 2 (haarAddCircle (T := T)) :=
  (memLp_bandSpectrum hf).toLp _

/-- The band-limited signal only depends on the almost-everywhere class of its spectrum. -/
theorem bandSignal_congr_ae {F G : AddCircle T → ℂ} (h : F =ᵐ[haarAddCircle (T := T)] G)
    (x : ℝ) : bandSignal (T := T) F x = bandSignal (T := T) G x := by
  have hT0 : (0 : ℝ) < T := hT.out
  have hvol : F =ᵐ[(volume : Measure (AddCircle T))] G := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact Measure.ae_smul_measure h _
  have hpull : (fun ξ : ℝ => F ξ)
      =ᵐ[(volume : Measure ℝ).restrict (Ioc (-(T / 2)) (-(T / 2) + T))] fun ξ : ℝ => G ξ :=
    (AddCircle.measurePreserving_mk T (-(T / 2))).quasiMeasurePreserving.ae_eq_comp hvol
  rw [half_add_period (T := T)] at hpull
  have hle : -(T / 2) ≤ T / 2 := by linarith
  rw [bandSignal, bandSignal, intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_of_le hle]
  refine setIntegral_congr_ae measurableSet_Ioc ((ae_restrict_iff' measurableSet_Ioc).mp ?_)
  filter_upwards [hpull] with ξ hξ
  rw [hξ]

theorem bandSignal_bandSpectrumLp (hf : BandLimited T f) (x : ℝ) :
    bandSignal (T := T) ((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))) :
        AddCircle T → ℂ) x
      = bandSignal (T := T) (bandSpectrum T f) x :=
  bandSignal_congr_ae (memLp_bandSpectrum hf).coeFn_toLp x

namespace BandLimited

/-- **A band-limited function is the band-limited signal of its own spectrum.** -/
theorem eq_bandSignal (hf : BandLimited T f) (x : ℝ) :
    f x = bandSignal (T := T) (bandSpectrum T f) x := by
  have hT0 : (0 : ℝ) < T := hT.out
  have hinv : 𝓕⁻ (𝓕 f) = f :=
    hf.continuous.fourierInv_fourier_eq hf.integrable hf.integrable_fourier
  have hline : f x = ∫ ξ : ℝ, Complex.exp (2 * π * I * x * ξ) * 𝓕 f ξ := by
    conv_lhs => rw [← hinv]
    rw [Real.fourierInv_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
    congr 2
    push_cast
    ring
  have hzero : ∀ ξ : ℝ, ξ ∉ Icc (-(T / 2)) (T / 2) →
      Complex.exp (2 * π * I * x * ξ) * 𝓕 f ξ = 0 := by
    intro ξ hξ
    have hout : T / 2 < |ξ| := by
      rcases lt_or_ge (T / 2) |ξ| with hlt | hge
      · exact hlt
      · exact absurd (abs_le.mp hge) (by simpa [Set.mem_Icc] using hξ)
    simp [hf.spectrum_support ξ hout]
  have hband : (∫ ξ : ℝ, Complex.exp (2 * π * I * x * ξ) * 𝓕 f ξ)
      = ∫ ξ in (-(T / 2))..(T / 2), Complex.exp (2 * π * I * x * ξ) * 𝓕 f ξ := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hsig : (∫ ξ in (-(T / 2))..(T / 2), Complex.exp (2 * π * I * x * ξ) * 𝓕 f ξ)
      = bandSignal (T := T) (bandSpectrum T f) x := by
    rw [bandSignal]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun ξ hξ => ?_)
    have hξ' : ξ ∈ Ioc (-(T / 2)) (-(T / 2) + T) := by
      rw [Set.uIoc_of_le (by linarith)] at hξ
      exact ⟨hξ.1, by rw [half_add_period]; exact hξ.2⟩
    rw [bandSpectrum_coe_apply hξ']
  rw [hline, hband, hsig]

/-- The band-limited signal attached to the `L²` spectrum is the function itself. -/
theorem eq_bandSignal_lp (hf : BandLimited T f) (x : ℝ) :
    f x = bandSignal (T := T) ((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))) :
      AddCircle T → ℂ) x := by
  rw [bandSignal_bandSpectrumLp hf x, hf.eq_bandSignal x]

/-- **The Whittaker–Shannon sampling theorem on the line.**  A band-limited function of
bandwidth `T` is recovered from its samples at the lattice `{n/T}` by the cardinal-sine series
`f x = ∑_{n ∈ ℤ} f (n/T) · sinc (T x - n)`. -/
theorem hasSum_sinc (hf : BandLimited T f) (x : ℝ) :
    HasSum (fun n : ℤ => f ((n : ℝ) / T) * (sinc (T * x - n) : ℝ)) (f x) := by
  have hbase := ChapterShannonSampling.bandSignal_hasSum_sinc (bandSpectrumLp hf) x
  rw [← hf.eq_bandSignal_lp x] at hbase
  refine hbase.congr_fun fun n => ?_
  rw [hf.eq_bandSignal_lp ((n : ℝ) / T)]

/-- **A band-limited function is determined by its samples** at the lattice `{n/T}`. -/
theorem eq_of_samples_eq (hf : BandLimited T f) (hg : BandLimited T g)
    (h : ∀ n : ℤ, f ((n : ℝ) / T) = g ((n : ℝ) / T)) : f = g := by
  funext x
  refine HasSum.unique (hf.hasSum_sinc x) ?_
  refine (hg.hasSum_sinc x).congr_fun fun n => ?_
  rw [h n]

/-- **Parseval for the samples of a band-limited function**: the squared moduli of the samples
are summable, with sum `T · ∫_ℝ ‖𝓕 f‖²`. -/
theorem hasSum_sq_samples (hf : BandLimited T f) :
    HasSum (fun n : ℤ => ‖f ((n : ℝ) / T)‖ ^ 2) (T * ∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ 2) := by
  have hT0 : (0 : ℝ) < T := hT.out
  have hbase := ChapterShannonSampling.hasSum_sq_samples (bandSpectrumLp hf)
  have hcoe : ∀ n : ℤ,
      ‖bandSignal (T := T) ((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))) :
        AddCircle T → ℂ) ((n : ℝ) / T)‖ ^ 2 = ‖f ((n : ℝ) / T)‖ ^ 2 := by
    intro n
    rw [← hf.eq_bandSignal_lp]
  simp_rw [hcoe] at hbase
  -- identify the energy of the spectrum on the circle with the energy of `𝓕 f` on the line
  have hband : (∫ ξ in (-(T / 2))..(-(T / 2) + T),
        ‖((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))) : AddCircle T → ℂ) ξ‖ ^ 2)
      = ∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ 2 := by
    have hae : (fun ξ : ℝ =>
          ‖((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))) : AddCircle T → ℂ) ξ‖ ^ 2)
        =ᵐ[(volume : Measure ℝ).restrict (Ioc (-(T / 2)) (-(T / 2) + T))]
          fun ξ : ℝ => ‖𝓕 f ξ‖ ^ 2 := by
      have hvol : ((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))) : AddCircle T → ℂ)
          =ᵐ[(volume : Measure (AddCircle T))] bandSpectrum T f := by
        rw [AddCircle.volume_eq_smul_haarAddCircle]
        exact Measure.ae_smul_measure (memLp_bandSpectrum hf).coeFn_toLp _
      have hpull := (AddCircle.measurePreserving_mk T
        (-(T / 2))).quasiMeasurePreserving.ae_eq_comp hvol
      filter_upwards [hpull, ae_restrict_mem measurableSet_Ioc] with ξ hξ hmem
      rw [show ((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))) : AddCircle T → ℂ)
        (ξ : AddCircle T) = bandSpectrum T f (ξ : AddCircle T) from hξ,
        bandSpectrum_coe_apply hmem]
    have hzero : ∀ ξ : ℝ, ξ ∉ Icc (-(T / 2)) (T / 2) → ‖𝓕 f ξ‖ ^ 2 = 0 := by
      intro ξ hξ
      have : T / 2 < |ξ| := by
        rcases lt_or_ge (T / 2) |ξ| with hlt | hge
        · exact hlt
        · exact absurd (abs_le.mp hge) (by simpa [Set.mem_Icc] using hξ)
      simp [hf.spectrum_support ξ this]
    rw [half_add_period (T := T)] at hae ⊢
    rw [intervalIntegral.integral_of_le (by linarith),
      setIntegral_congr_ae measurableSet_Ioc ((ae_restrict_iff' measurableSet_Ioc).mp hae),
      ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  rw [hband] at hbase
  exact hbase

end BandLimited

end Spectrum

end BookProof.ChapterPaleyWienerSampling
