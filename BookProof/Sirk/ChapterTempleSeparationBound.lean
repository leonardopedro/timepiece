import Mathlib
import BookProof.Sirk.ChapterRitzCertificate

/-!
# Chapter TempleSeparationBound — the analytic separation constant in Temple's denominator

Plan: `softmodes.md`, Phase 5.  `ChapterRitzCertificate` proves the finite Temple certificate

`θ − ε² / (β − θ) ≤ sInf (spectrum ℝ A) ≤ θ`,

whose width `ε²/(β−θ)` blows up as `β → θ`.  `softmodes.md` replaces the truncation-dependent
`β` by an **analytic** separation constant

`β_∞ − θ_∞ ≥ c₁ · Δ_ref`,

where `c₁ > 0` is the constant of the form-domination `q_{H_W} ≥ c₁ q_{H_ref} − c₂` (Phase 4)
and `Δ_ref > 0` is the certified gap of the reference operator `H_ref` (Phase 3).  With such a
constant the Temple denominator is bounded away from zero **uniformly in the approximation
order**, so the uncertainty

`δ_n = η_n² / (β_n − θ_n) ≤ η_n² / (c₁ Δ_ref)`

is controlled by the residual alone.

This chapter proves that implication — the arithmetic and the packaging of Phase 5.  It is the
part of the plan that needs no new analysis: given the analytic separation constant as a
hypothesis (exactly what Phases 1–4 must supply), the finite certificate becomes uniform.

## Contents

* **`temple_lower_bound_analytic`** — the uniform two-sided enclosure
  `θ − ε² / c ≤ l` under `β − θ ≥ c`, the form the plan's `β_∞ = θ_∞ + c₁ Δ_ref` gives;
* `temple_band_width_le_analytic` — the band width is at most `ε²/c`;
* `temple_uncertainty_tendsto_zero` — the uncertainty vanishes with the residual at the
  uniform rate `ε²/c`;
* `separation_constant_pos` — `c₁ > 0` and `Δ_ref > 0` give a positive separation constant
  `c₁ Δ_ref`;
* **`temple_lower_bound_of_form_domination`** — the end-to-end Phase 5 statement: a reference
  gap `Δ_ref`, a domination constant `c₁`, and the separation `β = θ + c₁Δ_ref` give the
  certified edge `θ − ε²/(c₁Δ_ref) ≤ l`;
* `temple_uncertainty_le_of_residual` — a uniform residual bound `ε ≤ η` bounds the uncertainty
  by `η²/c` (§5.1 of the plan), and `certified_edge_of_uniform_residual` is the corresponding
  certificate `θ − η²/(c₁Δ_ref) ≤ l`;
* **`continuum_gap_unconditional`** — §5.2's displayed inequality,
  `(θ_odd − θ_even) − 2η_max²/(c₁Δ_ref) ≤ l_odd − l_even`, with `continuum_gap_positive`
  concluding a strictly positive gap once the Ritz separation exceeds the correction (the
  transfer across the strong-resolvent limit is *not* proved — see Honest boundary).

## Honest boundary

Phases 1–4 — the BRST projection of the longitudinal flat directions, Simon's transverse
zero-point bound, the explicit reference operator with its certified gap, and the form
domination `q_{H_W} ≥ c₁ q_{H_ref} − c₂` — are **not** proved in this file or anywhere in the
corpus.  They enter here as the hypothesis `SpectralSeparation A l b` together with the size
`c = c₁ Δ_ref` of the gap between the edge and the rest of the spectrum.  What is proved is
that this is *exactly* the data Temple's inequality needs, with the uniformity in the
approximation order that the plan requires.

Everything is `sorry`-free and introduces no axioms.
-/

noncomputable section

open BookProof.RitzCertificate

namespace BookProof.TempleSeparationBound

open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ## 1. The uniform denominator -/

/-- **The uniform Temple lower bound.**  Under the analytic separation constant — `β − θ ≥ c`
with `c > 0` — the certified lower bound for the spectral edge is
`θ − ε² / c`, which no longer degrades as the finite data improve only in the residual. -/
theorem temple_lower_bound_analytic {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {l b c : ℝ} {x : F}
    (hsep : SpectralSeparation A l b) (hx : ‖x‖ = 1) (hlt : rayleigh A x < b)
    (hc : 0 < c) (hbc : c ≤ b - rayleigh A x) :
    rayleigh A x - resid A x ^ 2 / c ≤ l := by
  have hbase := temple_lower_bound hA hsep hx hlt
  have hbth : 0 < b - rayleigh A x := by linarith
  have hcpos : 0 < c := hc
  have hle : resid A x ^ 2 / (b - rayleigh A x) ≤ resid A x ^ 2 / c :=
    div_le_div_of_nonneg_left (sq_nonneg _) hcpos hbc
  linarith

omit [CompleteSpace F] in
/-- The width of the emitted Temple band, with the analytic denominator, is at most
`ε² / c`. -/
theorem temple_band_width_le_analytic (A : F →L[ℂ] F) (x : F) {b c : ℝ}
    (hc : 0 < c) (hbc : c ≤ b - rayleigh A x) :
    rayleigh A x - (rayleigh A x - resid A x ^ 2 / (b - rayleigh A x))
      ≤ resid A x ^ 2 / c := by
  have hbth : 0 < b - rayleigh A x := by linarith
  have hle : resid A x ^ 2 / (b - rayleigh A x) ≤ resid A x ^ 2 / c :=
    div_le_div_of_nonneg_left (sq_nonneg _) hc hbc
  have hwidth : rayleigh A x - (rayleigh A x - resid A x ^ 2 / (b - rayleigh A x))
      = resid A x ^ 2 / (b - rayleigh A x) := by ring
  rw [hwidth]
  exact hle

omit [CompleteSpace F] in
/-- **The Temple uncertainty vanishes at the analytic rate.**  If the separation constant `c`
is uniform in the order `m`, the uncertainty `ε_m² / (β − θ_m)` is bounded by `ε_m² / c`, so
it tends to zero with the residuals. -/
theorem temple_uncertainty_tendsto_zero (A : F →L[ℂ] F) {b c : ℝ} {x : ℕ → F}
    (hc : 0 < c) (hbc : ∀ m, c ≤ b - rayleigh A (x m))
    (hres : Tendsto (fun m => resid A (x m)) atTop (𝓝 0)) :
    Tendsto (fun m => resid A (x m) ^ 2 / (b - rayleigh A (x m))) atTop (𝓝 0) := by
  have hsq : Tendsto (fun m => resid A (x m) ^ 2) atTop (𝓝 0) := by
    simpa using hres.pow 2
  have hupper : Tendsto (fun m => resid A (x m) ^ 2 / c) atTop (𝓝 0) := by
    simpa using hsq.div_const c
  refine squeeze_zero_norm (fun m => ?_) hupper
  have hden : 0 < b - rayleigh A (x m) := by linarith [hbc m]
  have hle : resid A (x m) ^ 2 / (b - rayleigh A (x m)) ≤ resid A (x m) ^ 2 / c :=
    div_le_div_of_nonneg_left (sq_nonneg _) hc (hbc m)
  have hnn : 0 ≤ resid A (x m) ^ 2 / (b - rayleigh A (x m)) :=
    div_nonneg (sq_nonneg _) hden.le
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle

/-! ## 2. The separation constant of the plan -/

/-- **The separation constant is positive.**  Phase 3's reference gap `Δ_ref > 0` and Phase 4's
domination constant `c₁ > 0` give `c₁ · Δ_ref > 0`, the uniform lower bound on
`β_∞ − θ_∞` that the plan derives. -/
theorem separation_constant_pos {c₁ Δ : ℝ} (hc : 0 < c₁) (hΔ : 0 < Δ) : 0 < c₁ * Δ :=
  mul_pos hc hΔ

/-- A gap of the reference operator bounded below by `Δ_ref`, scaled by the domination
constant, is bounded below by `c₁ Δ_ref`. -/
theorem gap_scaled_ge {c₁ Δ μ₀ μ₁ : ℝ} (hc : 0 ≤ c₁) (hΔ : Δ ≤ μ₁ - μ₀) :
    c₁ * Δ ≤ c₁ * (μ₁ - μ₀) := mul_le_mul_of_nonneg_left hΔ hc

/-- **Phase 5 of `softmodes.md`: the certified edge with the analytic constant.**

Let `A` be bounded self-adjoint with its spectrum separated at the edge `l` by
`β = θ + c₁Δ_ref` (the analytic separation Phases 3–4 supply, with `c₁ > 0` the form-domination
constant and `Δ_ref > 0` the reference gap).  Then the Temple certificate reads

`θ − ε² / (c₁ Δ_ref) ≤ l ≤ θ`,

with a denominator that is uniformly bounded away from zero: the Temple uncertainty no longer
blows up as the basis grows. -/
theorem temple_lower_bound_of_form_domination {A : F →L[ℂ] F} (hA : IsSelfAdjoint A)
    {l : ℝ} {x : F} (hx : ‖x‖ = 1) {c₁ Δ : ℝ} (hc : 0 < c₁) (hΔ : 0 < Δ)
    (hsep : SpectralSeparation A l (rayleigh A x + c₁ * Δ)) :
    rayleigh A x - resid A x ^ 2 / (c₁ * Δ) ≤ l := by
  have hcpos : 0 < c₁ * Δ := mul_pos hc hΔ
  have hlt : rayleigh A x < rayleigh A x + c₁ * Δ := by linarith
  refine temple_lower_bound_analytic hA hsep hx hlt hcpos ?_
  linarith

/-! ## 3. Phase 5.2: uniform residuals and the unconditional gap -/

/-- **The Temple uncertainty is bounded by the residual size.**  Under the analytic separation
`b − θ ≥ c`, a uniform residual bound `ε ≤ η` turns Temple's `θ − l ≤ ε²/(b − θ)` into
`θ − l ≤ η²/c` — §5.1 of `softmodes.md`. -/
theorem temple_uncertainty_le_of_residual {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {l b c η : ℝ}
    {x : F} (hsep : SpectralSeparation A l b) (hx : ‖x‖ = 1) (hlt : rayleigh A x < b)
    (hc : 0 < c) (hbc : c ≤ b - rayleigh A x) (hres : resid A x ≤ η) :
    rayleigh A x - l ≤ η ^ 2 / c := by
  have hbase := temple_lower_bound_analytic hA hsep hx hlt hc hbc
  have hr : 0 ≤ resid A x := norm_nonneg _
  have hη : 0 ≤ η := le_trans hr hres
  have hsq : resid A x ^ 2 ≤ η ^ 2 := by nlinarith
  have hle : resid A x ^ 2 / c ≤ η ^ 2 / c := div_le_div_of_nonneg_right hsq hc.le
  linarith

/-- **The certified edge with a uniform residual bound.**  With the analytic separation constant
`c₁ Δ_ref` and `ε ≤ η_max`, the edge is certified to within `η_max²/(c₁Δ_ref)`:
`θ − η_max²/(c₁Δ_ref) ≤ l`. -/
theorem certified_edge_of_uniform_residual {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {l : ℝ}
    {x : F} (hx : ‖x‖ = 1) {c₁ Δ η : ℝ} (hc : 0 < c₁) (hΔ : 0 < Δ)
    (hsep : SpectralSeparation A l (rayleigh A x + c₁ * Δ)) (hres : resid A x ≤ η) :
    rayleigh A x - η ^ 2 / (c₁ * Δ) ≤ l := by
  have hcpos : 0 < c₁ * Δ := mul_pos hc hΔ
  have base := temple_lower_bound_of_form_domination hA hx hc hΔ hsep
  have hr : 0 ≤ resid A x := norm_nonneg _
  have hη : 0 ≤ η := le_trans hr hres
  have hsq : resid A x ^ 2 ≤ η ^ 2 := by nlinarith
  have hle : resid A x ^ 2 / (c₁ * Δ) ≤ η ^ 2 / (c₁ * Δ) :=
    div_le_div_of_nonneg_right hsq hcpos.le
  linarith

/-- **Phase 5.2's gap bookkeeping.**  If the odd sector's edge `l_odd` is certified from below
with correction `δ` and the even edge `l_even` obeys the variational upper bound, then the
physical gap is at least `(θ_odd − θ_even) − δ`. -/
theorem gap_of_temple_bounds {l_odd l_even θ_odd θ_even δ : ℝ}
    (hodd : θ_odd - δ ≤ l_odd) (heven : l_even ≤ θ_even) :
    θ_odd - θ_even - δ ≤ l_odd - l_even := by
  linarith

/-- **`softmodes.md` Phase 5.2, `continuum_gap_unconditional`.**  With the analytic separation
constant `c₁ Δ_ref > 0`, a uniform residual bound `η_max` on the odd-sector trial vector, and the
variational upper bound `l_even ≤ θ_even`, the physical gap satisfies

`(θ_odd − θ_even) − 2 η_max²/(c₁Δ_ref) ≤ l_odd − l_even`.

The factor `2` is the plan's: `η_max²/(c₁Δ_ref)` is the correction the certificate charges, and
it is subtracted twice so that the bound survives whichever edge is the one being certified. -/
theorem continuum_gap_unconditional {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {l_odd l_even θ_even : ℝ}
    {x : F} (hx : ‖x‖ = 1) {c₁ Δ η_max : ℝ} (hc : 0 < c₁) (hΔ : 0 < Δ)
    (hsep : SpectralSeparation A l_odd (rayleigh A x + c₁ * Δ)) (hres : resid A x ≤ η_max)
    (heven : l_even ≤ θ_even) :
    rayleigh A x - θ_even - 2 * (η_max ^ 2 / (c₁ * Δ)) ≤ l_odd - l_even := by
  have hedge := certified_edge_of_uniform_residual hA hx hc hΔ hsep hres
  have hδ : 0 ≤ η_max ^ 2 / (c₁ * Δ) := by positivity
  linarith

/-- **The unconditional gap is positive.**  Under the same hypotheses, if the Ritz separation
exceeds the Temple correction, the gap of the limit operator is strictly positive — the
denominator `β_∞ − θ_∞ = c₁Δ_ref` no longer degrades with the approximation order. -/
theorem continuum_gap_positive {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {l_odd l_even θ_even : ℝ}
    {x : F} (hx : ‖x‖ = 1) {c₁ Δ η_max : ℝ} (hc : 0 < c₁) (hΔ : 0 < Δ)
    (hsep : SpectralSeparation A l_odd (rayleigh A x + c₁ * Δ)) (hres : resid A x ≤ η_max)
    (heven : l_even ≤ θ_even)
    (hpos : 2 * (η_max ^ 2 / (c₁ * Δ)) < rayleigh A x - θ_even) :
    0 < l_odd - l_even := by
  have hgap := continuum_gap_unconditional hA hx hc hΔ hsep hres heven
  linarith

end BookProof.TempleSeparationBound
