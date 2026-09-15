import Mathlib
import BookProof.ChapterSirkRitzSpectrum
import BookProof.ChapterSirkRitzMinMax.Part1

/-!
# Chapter SirkRitzMinMax — the higher Rayleigh–Ritz levels and the Ritz gap

`CONSOLIDATED_PLAN.md` §12.2 **Gap 2, QYM** asks for "the statement that the
Ritz/**gap** values converge to the spectrum of the selected extension as `m → ∞`".
`BookProof.ChapterSirkRitzSpectrum` settled the *lowest* Ritz value: it converges to
`sInf (spectrum ℝ A)`.  A gap statement needs the **second** level as well, and there
is no second Rayleigh quotient — the correct object is the Courant–Fischer min–max
level

  `minmaxLevel T k = inf { sup_{x ∈ S, ‖x‖ = 1} ⟪x, Tx⟫ : dim S = k + 1 }`.

This chapter introduces those levels for a bounded operator on a complex Hilbert
space, and proves that the **Galerkin (Rayleigh–Ritz) min–max levels of the
truncations converge to them**, hence that the computed gap converges to the
min–max gap.

## Deliverables

* `rayleighVal`, `rayleighSetOn`, `rayleighSup` — the Rayleigh quotient, its range
  over the unit sphere of a subspace, and the supremum, with the basic bounds
  (`rayleighSup_le_norm`, `rayleighSup_mono`).
* `minmaxLevel` / `minmaxLevelIn` — the Courant–Fischer levels of `T`, and the
  levels computed inside a fixed subspace `W` (the truncation the solver sees).
* `minmaxLevel_le_minmaxLevelIn` — the Ritz levels are always **upper** bounds
  (the variational principle in the direction the algorithm can certify).
* `minmaxLevel_mono` — the levels increase with `k`.
* `minmaxLevel_zero_eq_rayleighInf` and `minmaxLevel_zero_eq_sInf_spectrum` — the
  level `k = 0` is the bottom of the numerical range, hence the bottom of the
  spectrum: this chapter's ladder starts exactly where `ChapterSirkRitzSpectrum`
  stopped.
* `exists_galerkin_approx_subspace` — the approximation engine: any `(k+1)`-dimensional
  subspace can be pushed into a large enough Galerkin subspace with an arbitrarily
  small increase of its Rayleigh supremum.
* `galerkin_minmaxLevel_tendsto` — **headline**: for every `k`, the Galerkin min–max
  levels converge to `minmaxLevel T k`.
* `galerkin_gap_tendsto` — the computed **gap** `Λ₁(m) − Λ₀(m)` converges to
  `minmaxLevel T 1 − minmaxLevel T 0`, and `galerkin_gap_eventually_pos`: a positive
  min–max gap is eventually seen by the truncations.

## Honest boundary

The min–max levels are spectral quantities only below the essential spectrum;
nothing here claims that `minmaxLevel T k` is an eigenvalue for `k ≥ 1` (for
`k = 0` the identification with `sInf (spectrum ℝ T)` *is* proved).  The operator is
bounded throughout — the unbounded case is reached through the resolvent, not
directly.
-/

noncomputable section

namespace BookProof.RitzMinMax

open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
/-! ## 3. Level zero is the bottom of the numerical range -/

omit [CompleteSpace F] in
/-- The level-zero min–max values are exactly the Rayleigh quotients of unit vectors. -/
theorem minmaxSet_zero_eq_rayleighSet (T : F →L[ℂ] F) : minmaxSet T 0 = rayleighSet T := by
  ext t
  constructor
  · rintro ⟨S, hrank, rfl⟩
    have hfd : FiniteDimensional ℂ S := .of_finrank_pos (by rw [hrank]; omega)
    obtain ⟨x, hx, hx1⟩ := exists_unit_mem S (by rw [hrank]; omega)
    have hx0 : x ≠ 0 := by
      intro h
      rw [h] at hx1
      simp at hx1
    have hspan : Submodule.span ℂ {x} = S :=
      Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (by simpa using hx))
        (by rw [finrank_span_singleton hx0, hrank])
    rw [← hspan, rayleighSup_span_singleton T hx1]
    exact ⟨x, hx1, rfl⟩
  · rintro ⟨x, hx1, rfl⟩
    have hx0 : x ≠ 0 := by
      intro h
      rw [h] at hx1
      simp at hx1
    exact ⟨Submodule.span ℂ {x}, by simpa using finrank_span_singleton hx0,
      (rayleighSup_span_singleton T hx1).symm⟩

omit [CompleteSpace F] in
theorem minmaxLevel_zero_eq_rayleighInf [Nontrivial F] (T : F →L[ℂ] F) :
    minmaxLevel T 0 = rayleighInf T := by
  rw [minmaxLevel, minmaxSet_zero_eq_rayleighSet, rayleighInf]

/-- **The bottom rung of the ladder is the bottom of the spectrum.** -/
theorem minmaxLevel_zero_eq_sInf_spectrum [Nontrivial F] (T : F →L[ℂ] F)
    (hT : IsSelfAdjoint T) : minmaxLevel T 0 = sInf (spectrum ℝ T) := by
  rw [minmaxLevel_zero_eq_rayleighInf T, ← sInf_spectrum_eq_rayleighInf T hT]

/-! ## 4. The Galerkin flag: dimensions and approximation -/

omit [CompleteSpace F] in
theorem finrank_galerkinSpan (b : HilbertBasis ℕ ℂ F) (m : ℕ) :
    Module.finrank ℂ (galerkinSpan b m) = m := by
  classical
  have hrange : Set.range (fun i : Fin m => b i.val) = b '' {i | i < m} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.isLt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hli : LinearIndependent ℂ (fun i : Fin m => b i.val) :=
    b.orthonormal.linearIndependent.comp _ Fin.val_injective
  rw [galerkinSpan, ← hrange, finrank_span_eq_card hli]
  simp

omit [CompleteSpace F] in
/-- Uniform approximation of a finite-dimensional subspace by its projections. -/
theorem exists_uniform_proj_bound (b : HilbertBasis ℕ ℂ F) (S : Submodule ℂ F)
    [FiniteDimensional ℂ S] {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ x ∈ S,
      ‖(galerkinSpan b m).starProjection x - x‖ ≤ ε * ‖x‖ := by
  classical
  set d := Module.finrank ℂ S with hd
  set e := stdOrthonormalBasis ℂ S with he
  set g : ℕ → (F →L[ℂ] F) :=
    fun m => (galerkinSpan b m).starProjection - ContinuousLinearMap.id ℂ F with hg
  have hgapp : ∀ (m : ℕ) (x : F), g m x = (galerkinSpan b m).starProjection x - x := by
    intro m x
    simp [hg]
  have htend : ∀ i : Fin d, ∀ᶠ m : ℕ in atTop, ‖g m ((e i : S) : F)‖ ≤ ε / (d + 1) := by
    intro i
    have h := galerkinProj_tendsto b ((e i : S) : F)
    rw [tendsto_iff_norm_sub_tendsto_zero] at h
    have hpos : 0 < ε / (d + 1) := by positivity
    have h2 := h.eventually (eventually_le_nhds hpos)
    filter_upwards [h2] with m hm
    rw [hgapp]
    exact hm
  have hall : ∀ᶠ m : ℕ in atTop, ∀ i : Fin d, ‖g m ((e i : S) : F)‖ ≤ ε / (d + 1) :=
    eventually_all.2 htend
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp hall
  refine ⟨m₀, fun m hm x hx => ?_⟩
  have hbound := hm₀ m hm
  set y : S := ⟨x, hx⟩ with hy
  have hxsum : x = ∑ i : Fin d, (e.repr y i) • ((e i : S) : F) := by
    have h1 := e.sum_repr y
    have h2 := congrArg (fun z : S => (z : F)) h1
    simpa using h2.symm
  have hgx : g m x = ∑ i : Fin d, (e.repr y i) • (g m ((e i : S) : F)) := by
    rw [hxsum]
    simp [map_sum]
  have hcoef : ∀ i : Fin d, ‖e.repr y i‖ ≤ ‖x‖ := by
    intro i
    rw [e.repr_apply_apply]
    calc ‖(inner ℂ (e i) y : ℂ)‖ ≤ ‖(e i : S)‖ * ‖y‖ := norm_inner_le_norm _ _
      _ = ‖x‖ := by rw [e.orthonormal.1 i]; simp [hy]
  have hdd : (d : ℝ) / (d + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  calc ‖(galerkinSpan b m).starProjection x - x‖ = ‖g m x‖ := by rw [hgapp]
    _ = ‖∑ i : Fin d, (e.repr y i) • (g m ((e i : S) : F))‖ := by rw [hgx]
    _ ≤ ∑ i : Fin d, ‖(e.repr y i) • (g m ((e i : S) : F))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, ‖x‖ * (ε / (d + 1)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul]
        exact mul_le_mul (hcoef i) (hbound i) (norm_nonneg _) (norm_nonneg _)
    _ = (d : ℝ) * (‖x‖ * (ε / (d + 1))) := by simp [Finset.sum_const]
    _ = ((d : ℝ) / (d + 1)) * (ε * ‖x‖) := by field_simp
    _ ≤ 1 * (ε * ‖x‖) := mul_le_mul_of_nonneg_right hdd (by positivity)
    _ = ε * ‖x‖ := one_mul _

omit [CompleteSpace F] in
/-- **The approximation engine**: every `(k+1)`-dimensional subspace can be moved into
a large enough Galerkin subspace at an arbitrarily small cost in the Rayleigh
supremum. -/
theorem exists_galerkin_approx_subspace (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F)
    {S : Submodule ℂ F} {k : ℕ} (hrank : Module.finrank ℂ S = k + 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ S' : Submodule ℂ F, S' ≤ galerkinSpan b m ∧
      Module.finrank ℂ S' = k + 1 ∧ rayleighSup T S' ≤ rayleighSup T S + ε := by
  classical
  have hfd : FiniteDimensional ℂ S := .of_finrank_pos (by rw [hrank]; omega)
  set c : ℝ := ‖T‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  set δ : ℝ := min (1 / 2) (ε / (8 * c + 8)) with hδ
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδeps : 8 * c * δ ≤ ε := by
    have h1 : δ ≤ ε / (8 * c + 8) := min_le_right _ _
    have h2 : (0 : ℝ) < 8 * c + 8 := by linarith
    calc 8 * c * δ ≤ 8 * c * (ε / (8 * c + 8)) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ h2]
          nlinarith [hε.le]
  obtain ⟨m₀, hm₀⟩ := exists_uniform_proj_bound b S hδpos
  refine ⟨m₀, fun m hm => ?_⟩
  set P := (galerkinSpan b m).starProjection with hP
  have hbnd : ∀ x ∈ S, ‖P x - x‖ ≤ δ * ‖x‖ := hm₀ m hm
  have hinj : Function.Injective ((P : F →ₗ[ℂ] F) ∘ₗ S.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hx⟩ hzero
    have h0 : P x = 0 := by simpa using hzero
    have h2 := hbnd x hx
    rw [h0, zero_sub, norm_neg] at h2
    have hx0 : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
    ext
    simpa using hx0
  have hrk : Module.finrank ℂ (S.map (P : F →ₗ[ℂ] F)) = k + 1 := by
    have hr : LinearMap.range ((P : F →ₗ[ℂ] F) ∘ₗ S.subtype) = S.map (P : F →ₗ[ℂ] F) := by
      rw [LinearMap.range_comp]
      simp
    rw [← hr, LinearMap.finrank_range_of_inj hinj, hrank]
  refine ⟨S.map (P : F →ₗ[ℂ] F), ?_, hrk, ?_⟩
  · rintro y ⟨x, -, rfl⟩
    exact (galerkinSpan b m).starProjection_apply_mem x
  · refine csSup_le
      (rayleighSetOn_nonempty T (S := S.map (P : F →ₗ[ℂ] F)) (by rw [hrk]; omega)) ?_
    rintro t ⟨y, hy, hy1, rfl⟩
    obtain ⟨x, hxS, rfl⟩ := hy
    simp only [ContinuousLinearMap.coe_coe] at hy1 ⊢
    have hxnorm : ‖P x - x‖ ≤ δ * ‖x‖ := hbnd x hxS
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hy1
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have habs : |‖x‖ - 1| ≤ δ * ‖x‖ := by
      have h1 := abs_norm_sub_norm_le x (P x)
      rw [hy1, norm_sub_rev] at h1
      exact h1.trans hxnorm
    have hxle : ‖x‖ ≤ 2 := by
      have h2 := abs_le.mp habs
      nlinarith [h2.2]
    set u : F := (‖x‖⁻¹ : ℂ) • x with hu
    have hunorm : ‖u‖ = 1 := by
      rw [hu, norm_smul]
      simp [hxpos.ne']
    have huS : u ∈ S := S.smul_mem _ hxS
    have hxu : ‖x - u‖ = |‖x‖ - 1| := by
      have hxe : x - u = ((1 - ‖x‖⁻¹ : ℝ) : ℂ) • x := by
        rw [hu]
        push_cast
        module
      have key : (1 - ‖x‖⁻¹) * ‖x‖ = ‖x‖ - 1 := by field_simp
      rw [hxe, norm_smul]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      calc |1 - ‖x‖⁻¹| * ‖x‖ = |1 - ‖x‖⁻¹| * |‖x‖| := by rw [abs_of_pos hxpos]
        _ = |(1 - ‖x‖⁻¹) * ‖x‖| := (abs_mul _ _).symm
        _ = |‖x‖ - 1| := by rw [key]
    have hyu : ‖P x - u‖ ≤ 2 * (δ * ‖x‖) := by
      calc ‖P x - u‖ ≤ ‖P x - x‖ + ‖x - u‖ := by
            simpa using norm_sub_le_norm_sub_add_norm_sub (P x) x u
        _ ≤ δ * ‖x‖ + δ * ‖x‖ := by rw [hxu]; linarith [habs]
        _ = 2 * (δ * ‖x‖) := by ring
    have hdiff := rayleighVal_sub_le T (P x) u
    rw [hy1, hunorm] at hdiff
    have hbound2 : rayleighVal T (P x) - rayleighVal T u ≤ ε := by
      have h4 : ‖P x - u‖ ≤ 4 * δ := by nlinarith [hyu, hxle, hδpos.le]
      calc rayleighVal T (P x) - rayleighVal T u ≤ c * (1 + 1) * ‖P x - u‖ := hdiff
        _ ≤ c * (1 + 1) * (4 * δ) := mul_le_mul_of_nonneg_left h4 (by linarith)
        _ = 8 * c * δ := by ring
        _ ≤ ε := hδeps
    have hle := rayleighVal_le_rayleighSup T huS hunorm
    linarith

/-! ## 5. The headline: convergence of the Galerkin min–max levels -/

omit [CompleteSpace F] in
theorem minmaxSetIn_galerkin_nonempty (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) {k m : ℕ}
    (hm : k + 1 ≤ m) : (minmaxSetIn T (galerkinSpan b m) k).Nonempty :=
  ⟨rayleighSup T (galerkinSpan b (k + 1)), galerkinSpan b (k + 1),
    galerkinSpan_mono b hm, finrank_galerkinSpan b (k + 1), rfl⟩

omit [CompleteSpace F] in
theorem minmaxSet_nonempty (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (k : ℕ) :
    (minmaxSet T k).Nonempty :=
  (minmaxSetIn_galerkin_nonempty T b (le_refl (k + 1))).mono (minmaxSetIn_subset T _ k)

omit [CompleteSpace F] in
/-- **The Galerkin min–max levels converge to the Courant–Fischer levels.** -/
theorem galerkin_minmaxLevel_tendsto (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (k : ℕ) :
    Tendsto (fun m : ℕ => minmaxLevelIn T (galerkinSpan b m) k) atTop
      (nhds (minmaxLevel T k)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨t, ht, htlt⟩ := exists_lt_of_csInf_lt (minmaxSet_nonempty T b k)
    (show minmaxLevel T k < minmaxLevel T k + ε / 2 by linarith)
  obtain ⟨S, hrank, rfl⟩ := ht
  obtain ⟨m₀, hm₀⟩ := exists_galerkin_approx_subspace T b hrank (half_pos hε)
  refine ⟨max m₀ (k + 1), fun m hm => ?_⟩
  have hlow : minmaxLevel T k ≤ minmaxLevelIn T (galerkinSpan b m) k :=
    minmaxLevel_le_minmaxLevelIn T _ k (minmaxSetIn_galerkin_nonempty T b (le_of_max_le_right hm))
  obtain ⟨S', hS'le, hS'rank, hS'sup⟩ := hm₀ m (le_of_max_le_left hm)
  have hup : minmaxLevelIn T (galerkinSpan b m) k ≤ rayleighSup T S' :=
    csInf_le (minmaxSetIn_bddBelow T _ k) ⟨S', hS'le, hS'rank, rfl⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

omit [CompleteSpace F] in
/-- **The computed gap converges to the min–max gap.** -/
theorem galerkin_gap_tendsto (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) :
    Tendsto (fun m : ℕ => minmaxLevelIn T (galerkinSpan b m) 1
        - minmaxLevelIn T (galerkinSpan b m) 0) atTop
      (nhds (minmaxLevel T 1 - minmaxLevel T 0)) :=
  ((galerkin_minmaxLevel_tendsto T b 1).sub (galerkin_minmaxLevel_tendsto T b 0))

omit [CompleteSpace F] in
/-- **A positive min–max gap is eventually seen by the truncations.** -/
theorem galerkin_gap_eventually_pos (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F)
    (hgap : minmaxLevel T 0 < minmaxLevel T 1) :
    ∀ᶠ m : ℕ in atTop, 0 < minmaxLevelIn T (galerkinSpan b m) 1
      - minmaxLevelIn T (galerkinSpan b m) 0 :=
  (galerkin_gap_tendsto T b).eventually_const_lt (by linarith)

end BookProof.RitzMinMax
