import Mathlib
import BookProof.ChapterH4
import BookProof.ChapterSirkSpectralGeometry

/-!
# Crouzeix's inequality for self-adjoint operators, with constant `1`

The SIRK chapters (`BookProof.ChapterH4`, `BookProof.ChapterSirkSpectralGeometry`) carry
Crouzeix's inequality `‖f(X)‖ ≤ C · sup_{Σ}|f|` as a **named hypothesis** — the general
theorem of Crouzeix (2007) and Crouzeix–Palencia, with `Σ` a convex set containing the
numerical range and `C = 2` (in general `1 + √2`), is deep.  This file proves the
inequality outright in the regime the project actually selects, namely for the
**shift-invert of a positive symmetric operator**, which is *self-adjoint*: there the
functional calculus is the continuous functional calculus of a normal operator, the
inequality holds with constant `C = 1`, and it needs no external input.

## Results

* `norm_cfc_le_of_spectrum_subset` — **Crouzeix's inequality with constant `1` for a
  normal operator**: if `spectrum ℂ a ⊆ S` and `‖f‖ ≤ C` on `S`, then `‖f(a)‖ ≤ C`, where
  `f(a)` is the continuous functional calculus.  `norm_cfc_le_of_selfAdjoint` is the
  self-adjoint form.
* `spectrum_subset_realSegment` — the spectrum of a self-adjoint operator lies in the real
  segment `[-‖a‖, ‖a‖]`, which is the `realSegment` of `ChapterSirkSpectralGeometry`; with
  a norm bound `‖a‖ ≤ ρ` (the shift-invert bound `‖R‖ ≤ γ⁻¹`) it lies in `[-ρ, ρ]`.
* `crouzeix_realSegment_of_selfAdjoint` — combining the two: for a self-adjoint operator of
  norm at most `ρ`, `‖f(a)‖ ≤ sup_{[-ρ,ρ]}|f|`.  This is exactly the Crouzeix hypothesis of
  the SIRK chapters, with `C = 1`, *proved*.
* `compress_isSelfAdjoint` — the SIRK compression `V∗ X V` of a self-adjoint operator is
  self-adjoint, so the same bound is available on the reduced side.
* **`sirk_error_bound_selfAdjoint`** — the SIRK error bound of `ChapterH4.sirk_error_bound`
  with **no Crouzeix hypothesis**: for self-adjoint `X` and `B`, functions `ψ, r` continuous
  on the spectra with `|ψ − r| ≤ D` on a set `S` containing both spectra, and the
  rational-transfer identity, one has
  `‖ψ(X) v − V ψ(B) V∗ v‖ ≤ 2 · D · ‖v‖`.

Everything is `sorry`-free and uses only the standard axioms.
-/

open ContinuousLinearMap

namespace BookProof.ChapterCrouzeixSelfAdjoint

open BookProof.ChapterSirkSpectralGeometry

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ## Crouzeix's inequality with constant `1` -/

/-- **Crouzeix's inequality with constant `1` for a normal operator.**  If the spectrum of
`a` is contained in `S` and `‖f‖ ≤ C` on `S`, then `‖f(a)‖ ≤ C`.  (For a general operator
this is Crouzeix's theorem, with `S` a convex set containing the numerical range and a
constant `C = 2`; for a normal operator it is the isometry of the continuous functional
calculus.) -/
theorem norm_cfc_le_of_spectrum_subset (a : E →L[ℂ] E) [IsStarNormal a] {f : ℂ → ℂ}
    {S : Set ℂ} (hS : spectrum ℂ a ⊆ S) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ z ∈ S, ‖f z‖ ≤ C) :
    ‖cfc f a‖ ≤ C :=
  norm_cfc_le hC fun x hx => hf x (hS hx)

/-- The self-adjoint form of `norm_cfc_le_of_spectrum_subset`. -/
theorem norm_cfc_le_of_selfAdjoint {a : E →L[ℂ] E} (ha : IsSelfAdjoint a) {f : ℂ → ℂ}
    {S : Set ℂ} (hS : spectrum ℂ a ⊆ S) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ z ∈ S, ‖f z‖ ≤ C) :
    ‖cfc f a‖ ≤ C :=
  have : IsStarNormal a := ha.isStarNormal
  norm_cfc_le_of_spectrum_subset a hS hC hf

/-! ## The spectrum of a self-adjoint operator is a real segment -/

/-- The spectrum of a self-adjoint operator of norm at most `ρ` lies in the real segment
`[-ρ, ρ]`.  For the shift-invert `R` of a positive symmetric operator at a real shift
`γ > 0` the project's bound is `‖R‖ ≤ γ⁻¹`, so the segment is `[-γ⁻¹, γ⁻¹]`. -/
theorem spectrum_subset_realSegment [Nontrivial E] {a : E →L[ℂ] E} (ha : IsSelfAdjoint a)
    {ρ : ℝ} (hρ : ‖a‖ ≤ ρ) : spectrum ℂ a ⊆ realSegment (-ρ) ρ := by
  intro z hz
  have him : z.im = 0 := ha.im_eq_zero_of_mem_spectrum hz
  have hnorm : ‖z‖ ≤ ρ := le_trans (spectrum.norm_le_norm_of_mem hz) hρ
  have habs : |z.re| ≤ ρ := le_trans (Complex.abs_re_le_norm z) hnorm
  exact ⟨him, by linarith [neg_abs_le z.re, le_abs_self z.re], by
    linarith [le_abs_self z.re]⟩

/-- **Crouzeix's inequality on the real segment of a self-adjoint operator**, with constant
`1` and no external input: this is the hypothesis that the SIRK chapters carry as the named
`Crouzeix` input, discharged in the self-adjoint (positive shift-invert) regime. -/
theorem crouzeix_realSegment_of_selfAdjoint [Nontrivial E] {a : E →L[ℂ] E}
    (ha : IsSelfAdjoint a) {ρ : ℝ} (hρ : ‖a‖ ≤ ρ) {f : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ z ∈ realSegment (-ρ) ρ, ‖f z‖ ≤ C) : ‖cfc f a‖ ≤ C :=
  norm_cfc_le_of_selfAdjoint ha (spectrum_subset_realSegment ha hρ) hC hf

/-! ## The reduced side: compressions of self-adjoint operators -/

/-- The SIRK compression `V∗ X V` of a self-adjoint operator is self-adjoint. -/
theorem compress_isSelfAdjoint (V : F →L[ℂ] E) {X : E →L[ℂ] E} (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (BookProof.ChapterH4.compress V X) := by
  have : (BookProof.ChapterH4.compress V X).adjoint = BookProof.ChapterH4.compress V X := by
    simp only [BookProof.ChapterH4.compress, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, hX.adjoint_eq]
    rw [ContinuousLinearMap.comp_assoc]
  exact this

/-- The norm of a compression does not exceed the norm of the operator, for an isometric
embedding: so the Crouzeix segment of the reduced operator is the same one. -/
theorem norm_compress_le (V : F →L[ℂ] E) (X : E →L[ℂ] E) (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖) : ‖BookProof.ChapterH4.compress V X‖ ≤ ‖X‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg X) fun x => ?_
  have h1 : ‖(BookProof.ChapterH4.compress V X) x‖ ≤ ‖X (V x)‖ := by
    simpa [BookProof.ChapterH4.compress] using hVadj (X (V x))
  have h2 : ‖X (V x)‖ ≤ ‖X‖ * ‖x‖ := by
    have := X.le_opNorm (V x)
    rwa [hViso x] at this
  exact h1.trans h2

/-! ## The SIRK error bound without the Crouzeix hypothesis -/

/-- **The SIRK error bound for self-adjoint operators, unconditional.**  This is
`ChapterH4.sirk_error_bound` with the two Crouzeix hypotheses *proved*: for self-adjoint
`X` and `B`, functions `ψ, r` continuous on the two spectra with `|ψ − r| ≤ D` on a set `S`
containing both spectra, and the rational transfer identity `r(X) v = V r(B) V∗ v`, the
error of the reduced approximation is at most `2 · D · ‖v‖` — Crouzeix's constant being
`C = 1` here. -/
theorem sirk_error_bound_selfAdjoint
    (V : F →L[ℂ] E) {X : E →L[ℂ] E} {B : F →L[ℂ] F}
    (hX : IsSelfAdjoint X) (hB : IsSelfAdjoint B)
    (psi r : ℂ → ℂ) {S : Set ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hSX : spectrum ℂ X ⊆ S) (hSB : spectrum ℂ B ⊆ S)
    (hpsiX : ContinuousOn psi (spectrum ℂ X)) (hrX : ContinuousOn r (spectrum ℂ X))
    (hpsiB : ContinuousOn psi (spectrum ℂ B)) (hrB : ContinuousOn r (spectrum ℂ B))
    (hbound : ∀ z ∈ S, ‖psi z - r z‖ ≤ D)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hrt : ∀ v : E, cfc r X v = V (cfc r B (V.adjoint v)))
    (v : E) :
    ‖cfc psi X v - V (cfc psi B (V.adjoint v))‖ ≤ 2 * D * ‖v‖ := by
  have hcx1 : ‖cfc psi X - cfc r X‖ ≤ 1 * D := by
    rw [one_mul, ← cfc_sub psi r X hpsiX hrX]
    exact norm_cfc_le_of_selfAdjoint hX hSX hD fun z hz => hbound z hz
  have hcx2 : ‖cfc psi B - cfc r B‖ ≤ 1 * D := by
    rw [one_mul, ← cfc_sub psi r B hpsiB hrB]
    exact norm_cfc_le_of_selfAdjoint hB hSB hD fun z hz => hbound z hz
  simpa using BookProof.ChapterH4.sirk_error_bound V (cfc psi X) (cfc psi X) (cfc r X)
    (cfc psi B) (cfc r B) 1 D rfl hViso hVadj hrt hcx1 hcx2 v

end BookProof.ChapterCrouzeixSelfAdjoint
