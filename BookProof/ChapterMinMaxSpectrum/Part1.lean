import Mathlib
import BookProof.ChapterSirkRitzMinMax

/-!
# Chapter MinMaxSpectrum — every Courant–Fischer level is a point of the spectrum

`BookProof.ChapterSirkRitzMinMax` built the Courant–Fischer ladder

  `minmaxLevel T k = inf { sup_{x ∈ S, ‖x‖ = 1} ⟪x, Tx⟫ : dim S = k + 1 }`

and proved that the Galerkin (Rayleigh–Ritz) levels of the truncations converge to it,
hence that the **computed gap** converges to `minmaxLevel T 1 − minmaxLevel T 0`.  Its
recorded honest boundary was that only the bottom rung `k = 0` had been identified with
a *spectral* quantity (`minmaxLevel_zero_eq_sInf_spectrum`); nothing was claimed about
the levels `k ≥ 1`.

This chapter removes that boundary in the form that the numerics needs: **every** level
of the ladder is a point of the spectrum,

  `minmaxLevel_mem_spectrum : minmaxLevel T k ∈ spectrum ℝ T`,

for a bounded self-adjoint `T` on a complex Hilbert space (with the ladder defined, i.e.
with subspaces of dimension `k + 1` available).  Consequently the limit of the computed
Galerkin levels is a spectral value and the computed gap converges to the difference of
two spectral values — the statement `CONSOLIDATED_PLAN.md` §12.2 (Gap 2, QYM) asks for.

## The proof

The classical argument, run through the continuous functional calculus rather than a
Borel spectral measure.  If `a = minmaxLevel T k` were **not** in the spectrum, then —
the spectrum being closed — some `ε > 0` separates it: every spectral point is `≤ a − ε`
or `≥ a + ε`.  The continuous cutoff

  `cutoff a ε t = min 1 (max 0 ((a + ε − t) / (2ε)))`

is therefore `{0, 1}`-valued on the spectrum, so `P = cfc (cutoff a ε) T` is an
orthogonal projection commuting with `T`, `T ≤ a − ε` on its range and `T ≥ a + ε` on its
kernel (`rayleighVal_le_of_proj_fixed`, `le_rayleighVal_of_proj_zero`, both obtained from
the order-preservation of the functional calculus, `cfc_le_iff`).  Then:

* if the range of `P` contains a `(k+1)`-dimensional subspace, that subspace is a
  competitor with `rayleighSup ≤ a − ε`, so `a ≤ a − ε` — impossible;
* otherwise `P` is non-injective on every `(k+1)`-dimensional subspace `S`, so `S` meets
  the kernel of `P` in a unit vector and `rayleighSup T S ≥ a + ε` for **every**
  competitor, whence `a ≥ a + ε` — impossible.

## Deliverables

* `cutoff`, `cutoff_eq_one`, `cutoff_eq_zero` — the continuous `{0,1}`-valued cutoff.
* `re_inner_mono_of_le` — the operator order dominates the Rayleigh quotients.
* `rayleighVal_le_of_proj_fixed`, `le_rayleighVal_of_proj_fixed` — the two spectral
  half-space bounds, for a general `{0,1}`-valued continuous symbol.
* `minmaxLevel_mem_spectrum` — **headline**: `minmaxLevel T k ∈ spectrum ℝ T`;
  `sInf_spectrum_mem_spectrum` — in particular the bottom of the spectrum is attained.
* `galerkin_minmaxLevel_tendsto_spectrum` — the Galerkin min–max levels converge to a
  point of the spectrum; `galerkin_gap_tendsto_spectrum_sub` — the computed gap converges
  to the difference of two points of the spectrum.
* `rayleighVal_le_of_mem_range`, `exists_cfc_ne_zero`, `inner_range_eq_zero` — the
  spectral-subspace toolkit: the half-space bound on the range of `cfc p T` for an
  arbitrary continuous symbol, the non-triviality of a spectral subspace at a spectral
  point, and the orthogonality of the subspaces of disjoint symbols.
* `notMem_spectrum_of_mem_minmaxGap` / `spectrum_inter_minmaxGap_eq_empty` —
  **the computed gap is a gap of the spectrum**: no spectral point lies strictly between
  `minmaxLevel T 0` and `minmaxLevel T 1`.
* `exists_eigenvector_of_minmaxGap` — **a positive min–max gap makes the ground level an
  eigenvalue**: there is a non-zero `x` with `T x = minmaxLevel T 0 • x`.

## Honest boundary

The operator is **bounded** throughout (the unbounded case is reached through the
resolvent, not directly).  For a general level the statement is that it *lies in the
spectrum*; it is not claimed to be an eigenvalue — at or above the essential spectrum a
level is typically only a spectral point, and no essential-spectrum theory is developed
here.  What *is* proved is the eigenvalue statement for the ground level of a **positive**
min–max gap, which is the case the numerics is about.  Nothing here says that a computed
Galerkin gap is positive for the exact operator: the computed levels are upper bounds, and
that direction is the stability question of `ChapterSirkRitzPerturbation`.
-/

noncomputable section

namespace BookProof.MinMaxSpectrum

open BookProof.RitzMinMax
open Filter Topology ContinuousLinearMap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ## 1. The operator order dominates the Rayleigh quotients -/

/-- If `A ≤ B` in the C\*-order of operators then the Rayleigh quotient of `A` is
everywhere at most that of `B`. -/
theorem re_inner_mono_of_le {A B : F →L[ℂ] F} (hAB : A ≤ B) (x : F) :
    (inner ℂ x (A x) : ℂ).re ≤ (inner ℂ x (B x) : ℂ).re := by
  have h : (0 : F →L[ℂ] F) ≤ B - A := sub_nonneg.mpr hAB
  rw [nonneg_iff_isPositive] at h
  have h2 := h.2 x
  rw [ContinuousLinearMap.reApplyInnerSelf, ContinuousLinearMap.sub_apply, inner_sub_left] at h2
  have e1 : (inner ℂ (A x) x : ℂ).re = (inner ℂ x (A x) : ℂ).re := by
    rw [← inner_conj_symm x (A x), Complex.conj_re]
  have e2 : (inner ℂ (B x) x : ℂ).re = (inner ℂ x (B x) : ℂ).re := by
    rw [← inner_conj_symm x (B x), Complex.conj_re]
  simp only [RCLike.re_to_complex, Complex.sub_re, e1, e2] at h2
  linarith

/-! ## 2. The sandwich identities for a functional-calculus projection -/

/-- On a vector fixed by `cfc p T`, the Rayleigh quotient of the sandwich
`cfc p T · T · cfc p T` is the Rayleigh quotient of `T`. -/
theorem sandwich_inner_eq (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (p : ℝ → ℝ)
    (hp : Continuous p) {x : F} (hx : cfc p T x = x) :
    (inner ℂ x ((cfc (fun t => t * (p t * p t)) T) x) : ℂ) = inner ℂ x (T x) := by
  have hPsa : IsSelfAdjoint (cfc p T) := cfc_predicate p T
  have hA : cfc (fun t => t * (p t * p t)) T = cfc p T * (T * cfc p T) := by
    have h1 : cfc (fun t : ℝ => p t * (t * p t)) T = cfc p T * cfc (fun t : ℝ => t * p t) T :=
      cfc_mul _ _ T hp.continuousOn (by fun_prop)
    have h2 : cfc (fun t : ℝ => t * p t) T = T * cfc p T := by
      rw [cfc_mul _ _ T (by fun_prop) hp.continuousOn, cfc_id' ℝ T]
    rw [show (fun t : ℝ => t * (p t * p t)) = (fun t : ℝ => p t * (t * p t)) by funext t; ring,
      h1, h2]
  rw [hA]
  simp only [ContinuousLinearMap.mul_apply, hx]
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hPsa
  have h := hsym x (T x)
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [hx] at h
  exact h.symm

/-- On a vector fixed by `cfc p T`, with `p` idempotent on the spectrum, the Rayleigh
quotient of `cfc (c · p²) T` is `c‖x‖²`. -/
theorem const_inner_eq (T : F →L[ℂ] F) (p : ℝ → ℝ) (hp : Continuous p) (c : ℝ)
    (hidem : ∀ μ ∈ spectrum ℝ T, p μ * p μ = p μ) {x : F} (hx : cfc p T x = x) :
    (inner ℂ x ((cfc (fun t => c * (p t * p t)) T) x) : ℂ).re = c * ‖x‖ ^ 2 := by
  rw [cfc_const_mul _ _ T (by fun_prop), cfc_congr hidem]
  change (inner ℂ x (c • cfc p T x) : ℂ).re = _
  rw [hx]
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

/-- **The upper half-space bound.**  If `p` is idempotent on the spectrum and
`t p(t)² ≤ c p(t)²` there, then `T ≤ c` on the vectors fixed by `cfc p T`. -/
theorem rayleighVal_le_of_proj_fixed (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (p : ℝ → ℝ)
    (hp : Continuous p) (c : ℝ) (hidem : ∀ μ ∈ spectrum ℝ T, p μ * p μ = p μ)
    (hbd : ∀ μ ∈ spectrum ℝ T, μ * (p μ * p μ) ≤ c * (p μ * p μ))
    {x : F} (hx : cfc p T x = x) :
    rayleighVal T x ≤ c * ‖x‖ ^ 2 := by
  have hAB : cfc (fun t => t * (p t * p t)) T ≤ cfc (fun t => c * (p t * p t)) T :=
    (cfc_le_iff _ _ T (by fun_prop) (by fun_prop) hT).mpr hbd
  have hkey := re_inner_mono_of_le hAB x
  rw [sandwich_inner_eq T hT p hp hx, const_inner_eq T p hp c hidem hx] at hkey
  exact hkey

/-- **The lower half-space bound.**  If `p` is idempotent on the spectrum and
`c p(t)² ≤ t p(t)²` there, then `T ≥ c` on the vectors fixed by `cfc p T`. -/
theorem le_rayleighVal_of_proj_fixed (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (p : ℝ → ℝ)
    (hp : Continuous p) (c : ℝ) (hidem : ∀ μ ∈ spectrum ℝ T, p μ * p μ = p μ)
    (hbd : ∀ μ ∈ spectrum ℝ T, c * (p μ * p μ) ≤ μ * (p μ * p μ))
    {x : F} (hx : cfc p T x = x) :
    c * ‖x‖ ^ 2 ≤ rayleighVal T x := by
  have hAB : cfc (fun t => c * (p t * p t)) T ≤ cfc (fun t => t * (p t * p t)) T :=
    (cfc_le_iff _ _ T (by fun_prop) (by fun_prop) hT).mpr hbd
  have hkey := re_inner_mono_of_le hAB x
  rw [sandwich_inner_eq T hT p hp hx, const_inner_eq T p hp c hidem hx] at hkey
  exact hkey

/-! ## 3. The continuous cutoff at a spectral gap -/

/-- The continuous cutoff: `1` below `a − ε`, `0` above `a + ε`, affine in between. -/
def cutoff (a ε : ℝ) : ℝ → ℝ := fun t => min 1 (max 0 ((a + ε - t) / (2 * ε)))

theorem cutoff_continuous (a ε : ℝ) : Continuous (cutoff a ε) := by
  unfold cutoff; fun_prop

theorem cutoff_eq_one {a ε t : ℝ} (hε : 0 < ε) (h : t ≤ a - ε) : cutoff a ε t = 1 := by
  have h1 : (1 : ℝ) ≤ (a + ε - t) / (2 * ε) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have h2 : max 0 ((a + ε - t) / (2 * ε)) = (a + ε - t) / (2 * ε) :=
    max_eq_right (by linarith)
  rw [cutoff, h2, min_eq_left h1]

theorem cutoff_eq_zero {a ε t : ℝ} (hε : 0 < ε) (h : a + ε ≤ t) : cutoff a ε t = 0 := by
  have h1 : (a + ε - t) / (2 * ε) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  rw [cutoff, max_eq_left h1, min_eq_right (by norm_num)]

/-- The complementary cutoff `1 − cutoff`. -/
def cocutoff (a ε : ℝ) : ℝ → ℝ := fun t => 1 - cutoff a ε t

theorem cocutoff_continuous (a ε : ℝ) : Continuous (cocutoff a ε) := by
  unfold cocutoff; exact continuous_const.sub (cutoff_continuous a ε)

/-- The functional calculus of the complementary cutoff is the complementary projection. -/
theorem cfc_cocutoff (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (a ε : ℝ) :
    cfc (cocutoff a ε) T = 1 - cfc (cutoff a ε) T := by
  unfold cocutoff
  rw [cfc_sub _ _ T (by fun_prop) (cutoff_continuous a ε).continuousOn]
  congr 1
  exact cfc_const_one ℝ T

/-! ## 4. The two half-space bounds at a spectral gap -/

section Gap

variable (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) {a ε : ℝ}

omit [CompleteSpace F] in
/-- Below the gap the cutoff is `1`, above it `0`: it is idempotent on the spectrum. -/
theorem cutoff_idem (hε : 0 < ε) (hsep : ∀ μ ∈ spectrum ℝ T, μ ≤ a - ε ∨ a + ε ≤ μ) :
    ∀ μ ∈ spectrum ℝ T, cutoff a ε μ * cutoff a ε μ = cutoff a ε μ := by
  intro μ hμ
  rcases hsep μ hμ with h | h
  · rw [cutoff_eq_one hε h]; norm_num
  · rw [cutoff_eq_zero hε h]; norm_num

omit [CompleteSpace F] in
theorem cocutoff_idem (hε : 0 < ε) (hsep : ∀ μ ∈ spectrum ℝ T, μ ≤ a - ε ∨ a + ε ≤ μ) :
    ∀ μ ∈ spectrum ℝ T, cocutoff a ε μ * cocutoff a ε μ = cocutoff a ε μ := by
  intro μ hμ
  rcases hsep μ hμ with h | h
  · rw [cocutoff, cutoff_eq_one hε h]; norm_num
  · rw [cocutoff, cutoff_eq_zero hε h]; norm_num

include hT in
/-- **On the range of the spectral projection the operator is at most `a − ε`.** -/
theorem rayleighVal_le_of_cutoff_fixed (hε : 0 < ε)
    (hsep : ∀ μ ∈ spectrum ℝ T, μ ≤ a - ε ∨ a + ε ≤ μ)
    {x : F} (hx : cfc (cutoff a ε) T x = x) :
    rayleighVal T x ≤ (a - ε) * ‖x‖ ^ 2 := by
  refine rayleighVal_le_of_proj_fixed T hT _ (cutoff_continuous a ε) (a - ε)
    (cutoff_idem T hε hsep) ?_ hx
  intro μ hμ
  rcases hsep μ hμ with h | h
  · rw [cutoff_eq_one hε h]; nlinarith
  · rw [cutoff_eq_zero hε h]; norm_num

include hT in
/-- **On the kernel of the spectral projection the operator is at least `a + ε`.** -/
theorem le_rayleighVal_of_cutoff_zero (hε : 0 < ε)
    (hsep : ∀ μ ∈ spectrum ℝ T, μ ≤ a - ε ∨ a + ε ≤ μ)
    {x : F} (hx : cfc (cutoff a ε) T x = 0) :
    (a + ε) * ‖x‖ ^ 2 ≤ rayleighVal T x := by
  have hfix : cfc (cocutoff a ε) T x = x := by
    rw [cfc_cocutoff T hT a ε]
    simp [hx]
  refine le_rayleighVal_of_proj_fixed T hT _ (cocutoff_continuous a ε) (a + ε)
    (cocutoff_idem T hε hsep) ?_ hfix
  intro μ hμ
  rcases hsep μ hμ with h | h
  · rw [cocutoff, cutoff_eq_one hε h]; norm_num
  · rw [cocutoff, cutoff_eq_zero hε h]; nlinarith

end Gap

/-! ## 5. The headline: every min–max level is a spectral point -/

/-- **Every Courant–Fischer level of a bounded self-adjoint operator is a point of its
spectrum.** -/
theorem minmaxLevel_mem_spectrum (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (k : ℕ)
    (hne : (minmaxSet T k).Nonempty) : minmaxLevel T k ∈ spectrum ℝ T := by
  classical
  by_contra hmem
  set a : ℝ := minmaxLevel T k with ha
  -- the real spectrum is closed, so a gap of some width `ε` separates `a` from it
  have hclosed : IsClosed (spectrum ℝ T) := spectrum.isClosed T
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl a hmem
  have hsep : ∀ μ ∈ spectrum ℝ T, μ ≤ a - ε ∨ a + ε ≤ μ := by
    intro μ hμ
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    exact (hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)) hμ
  set P : F →L[ℂ] F := cfc (cutoff a ε) T with hP
  set R : Submodule ℂ F := LinearMap.ker (((1 : F →L[ℂ] F) - P : F →L[ℂ] F) : F →ₗ[ℂ] F) with hR
  have hmemR : ∀ x : F, x ∈ R ↔ P x = x := by
    intro x
    simp only [hR, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, sub_eq_zero]
    exact eq_comm
  by_cases hcase : ∃ S : Submodule ℂ F, S ≤ R ∧ Module.finrank ℂ S = k + 1
  · -- a competitor inside the range of the projection pushes the level below `a`
    obtain ⟨S, hSR, hSrank⟩ := hcase
    have hsup : rayleighSup T S ≤ a - ε := by
      refine csSup_le (rayleighSetOn_nonempty T (by rw [hSrank]; omega)) ?_
      rintro t ⟨x, hxS, hx1, rfl⟩
      have hfix : P x = x := (hmemR x).mp (hSR hxS)
      have := rayleighVal_le_of_cutoff_fixed T hT hε hsep hfix
      rwa [hx1, one_pow, mul_one] at this
    have hle : a ≤ rayleighSup T S := csInf_le (minmaxSet_bddBelow T k) ⟨S, hSrank, rfl⟩
    linarith
  · -- otherwise every competitor meets the kernel and sits above `a`
    push_neg at hcase
    have hall : ∀ t ∈ minmaxSet T k, a + ε ≤ t := by
      rintro t ⟨S, hSrank, rfl⟩
      -- `P` cannot be injective on `S`
      have hnotinj : ¬ Function.Injective ((P : F →ₗ[ℂ] F) ∘ₗ S.subtype) := by
        intro hinj
        have hrk : Module.finrank ℂ (S.map (P : F →ₗ[ℂ] F)) = k + 1 := by
          have hr : LinearMap.range ((P : F →ₗ[ℂ] F) ∘ₗ S.subtype) = S.map (P : F →ₗ[ℂ] F) := by
            rw [LinearMap.range_comp]
            simp
          rw [← hr, LinearMap.finrank_range_of_inj hinj, hSrank]
        have hsub : S.map (P : F →ₗ[ℂ] F) ≤ R := by
          rintro y ⟨x, -, rfl⟩
          refine (hmemR _).mpr ?_
          have hidem : P * P = P := by
            rw [hP, ← cfc_mul _ _ T (cutoff_continuous a ε).continuousOn
              (cutoff_continuous a ε).continuousOn, cfc_congr (cutoff_idem T hε hsep)]
          have := congrArg (fun A : F →L[ℂ] F => A x) hidem
          simpa using this
        exact absurd hrk (hcase _ hsub)
      -- hence a nonzero vector of `S` in the kernel
      obtain ⟨x, hxS, hx0, hxker⟩ : ∃ x : F, x ∈ S ∧ x ≠ 0 ∧ P x = 0 := by
        rw [← LinearMap.ker_eq_bot] at hnotinj
        obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnotinj
        refine ⟨(y : F), y.2, fun h => hy0 (Subtype.ext h), ?_⟩
        have hy2 : ((P : F →ₗ[ℂ] F) ∘ₗ S.subtype) y = 0 := hy
        simpa using hy2
      have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      set u : F := (‖x‖⁻¹ : ℂ) • x with hu
      have hunorm : ‖u‖ = 1 := by
        rw [hu, norm_smul]
        simp [hxpos.ne']
      have huS : u ∈ S := S.smul_mem _ hxS
      have huker : P u = 0 := by
        rw [hu, ContinuousLinearMap.map_smul, hxker, smul_zero]
      have hlow := le_rayleighVal_of_cutoff_zero T hT hε hsep huker
      rw [hunorm, one_pow, mul_one] at hlow
      exact hlow.trans (rayleighVal_le_rayleighSup T huS hunorm)
    have hge : a + ε ≤ a := by
      rw [ha]
      exact le_csInf hne hall
    linarith

/-- The bottom rung, restated: the min–max level `0` is a spectral point. -/
theorem minmaxLevel_zero_mem_spectrum (T : F →L[ℂ] F) (hT : IsSelfAdjoint T)
    (hne : (minmaxSet T 0).Nonempty) : minmaxLevel T 0 ∈ spectrum ℝ T :=
  minmaxLevel_mem_spectrum T hT 0 hne

/-- **The bottom of the spectrum is attained**: `sInf (spectrum ℝ T)` is itself a
spectral point.  (The `k = 0` rung, read through
`RitzMinMax.minmaxLevel_zero_eq_sInf_spectrum`.) -/
theorem sInf_spectrum_mem_spectrum [Nontrivial F] (T : F →L[ℂ] F) (hT : IsSelfAdjoint T)
    (hne : (minmaxSet T 0).Nonempty) : sInf (spectrum ℝ T) ∈ spectrum ℝ T := by
  rw [← minmaxLevel_zero_eq_sInf_spectrum T hT]
  exact minmaxLevel_mem_spectrum T hT 0 hne

/-! ## 6. What the computed Galerkin levels converge to -/

open BookProof.HermiteGalerkin in
/-- **The Galerkin min–max levels converge to a point of the spectrum.** -/
theorem galerkin_minmaxLevel_tendsto_spectrum (T : F →L[ℂ] F) (hT : IsSelfAdjoint T)
    (b : HilbertBasis ℕ ℂ F) (k : ℕ) :
    ∃ lam ∈ spectrum ℝ T,
      Tendsto (fun m : ℕ => minmaxLevelIn T (galerkinSpan b m) k) atTop (nhds lam) :=
  ⟨minmaxLevel T k, minmaxLevel_mem_spectrum T hT k (minmaxSet_nonempty T b k),
    galerkin_minmaxLevel_tendsto T b k⟩

open BookProof.HermiteGalerkin in
/-- **The computed gap converges to the difference of two spectral points.** -/
theorem galerkin_gap_tendsto_spectrum_sub (T : F →L[ℂ] F) (hT : IsSelfAdjoint T)
    (b : HilbertBasis ℕ ℂ F) :
    ∃ lam₀ ∈ spectrum ℝ T, ∃ lam₁ ∈ spectrum ℝ T,
      Tendsto (fun m : ℕ => minmaxLevelIn T (galerkinSpan b m) 1
          - minmaxLevelIn T (galerkinSpan b m) 0) atTop (nhds (lam₁ - lam₀)) :=
  ⟨minmaxLevel T 0, minmaxLevel_mem_spectrum T hT 0 (minmaxSet_nonempty T b 0),
    minmaxLevel T 1, minmaxLevel_mem_spectrum T hT 1 (minmaxSet_nonempty T b 1),
    galerkin_gap_tendsto T b⟩

/-! ## 7. Spectral subspaces: the bounds on the range of a functional calculus -/

/-- `‖cfc p T y‖²` read as a form of `cfc p²`. -/
theorem norm_range_eq (T : F →L[ℂ] F) (p : ℝ → ℝ) (hp : Continuous p) (y : F) :
    ((‖cfc p T y‖ ^ 2 : ℝ) : ℂ) = inner ℂ y ((cfc (fun t => p t * p t) T) y) := by
  have hPsa : IsSelfAdjoint (cfc p T) := cfc_predicate p T
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hPsa
  have hA : cfc (fun t => p t * p t) T = cfc p T * cfc p T :=
    cfc_mul _ _ T hp.continuousOn hp.continuousOn
  rw [hA]
  have h := hsym y (cfc p T y)
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [ContinuousLinearMap.mul_apply, ← h, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-- The Rayleigh quotient of a vector in the range of `cfc p T`, read as a form of
`cfc (t p²)`. -/
theorem inner_range_eq (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (p : ℝ → ℝ) (hp : Continuous p)
    (y : F) :
    (inner ℂ (cfc p T y) (T (cfc p T y)) : ℂ)
      = inner ℂ y ((cfc (fun t => t * (p t * p t)) T) y) := by
  have hPsa : IsSelfAdjoint (cfc p T) := cfc_predicate p T
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hPsa
  have hA : cfc (fun t => t * (p t * p t)) T = cfc p T * (T * cfc p T) := by
    have h1 : cfc (fun t : ℝ => p t * (t * p t)) T = cfc p T * cfc (fun t : ℝ => t * p t) T :=
      cfc_mul _ _ T hp.continuousOn (by fun_prop)
    have h2 : cfc (fun t : ℝ => t * p t) T = T * cfc p T := by
      rw [cfc_mul _ _ T (by fun_prop) hp.continuousOn, cfc_id' ℝ T]
    rw [show (fun t : ℝ => t * (p t * p t)) = (fun t : ℝ => p t * (t * p t)) by funext t; ring,
      h1, h2]
  rw [hA]
  have h := hsym y (T (cfc p T y))
  simp only [ContinuousLinearMap.coe_coe] at h
  simpa [ContinuousLinearMap.mul_apply] using h

/-- **The half-space bound on a spectral subspace.**  If `t p(t)² ≤ c p(t)²` on the
spectrum then the Rayleigh quotient of every vector in the range of `cfc p T` is at most
`c`.  No idempotency is required: the symbol need not be a projection. -/
theorem rayleighVal_le_of_mem_range (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (p : ℝ → ℝ)
    (hp : Continuous p) (c : ℝ)
    (hbd : ∀ μ ∈ spectrum ℝ T, μ * (p μ * p μ) ≤ c * (p μ * p μ)) (y : F) :
    rayleighVal T (cfc p T y) ≤ c * ‖cfc p T y‖ ^ 2 := by
  have hAB : cfc (fun t => t * (p t * p t)) T ≤ cfc (fun t => c * (p t * p t)) T :=
    (cfc_le_iff _ _ T (by fun_prop) (by fun_prop) hT).mpr hbd
  have hkey := re_inner_mono_of_le hAB y
  have hR : (inner ℂ y ((cfc (fun t => c * (p t * p t)) T) y) : ℂ).re = c * ‖cfc p T y‖ ^ 2 := by
    rw [cfc_const_mul _ _ T (by fun_prop)]
    have h2 : (inner ℂ y ((c • cfc (fun t => p t * p t) T) y) : ℂ)
        = (c : ℂ) * inner ℂ y ((cfc (fun t => p t * p t) T) y) := by
      simp [ContinuousLinearMap.smul_apply]
    rw [h2, ← norm_range_eq T p hp y, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hL : (inner ℂ y ((cfc (fun t => t * (p t * p t)) T) y) : ℂ).re
      = rayleighVal T (cfc p T y) := by
    rw [rayleighVal, inner_range_eq T hT p hp y]
  rw [hL, hR] at hkey
  exact hkey

/-- **A spectral subspace at a spectral point is non-trivial**: a continuous symbol that
does not vanish at a point of the spectrum has a non-zero functional calculus. -/
theorem exists_cfc_ne_zero [Nontrivial F] (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (p : ℝ → ℝ)
    (hp : Continuous p) {lam : ℝ} (hlam : lam ∈ spectrum ℝ T) (hp0 : p lam ≠ 0) :
    ∃ y : F, cfc p T y ≠ 0 := by
  by_contra h
  push_neg at h
  have hzero : cfc p T = 0 := by ext y; simp [h y]
  have hmap : spectrum ℝ (cfc p T) = p '' spectrum ℝ T :=
    cfc_map_spectrum (R := ℝ) p T (ha := hT) (hf := hp.continuousOn)
  rw [hzero] at hmap
  have hmem : p lam ∈ spectrum ℝ (0 : F →L[ℂ] F) := by rw [hmap]; exact ⟨lam, hlam, rfl⟩
  rw [spectrum.zero_eq] at hmem
  exact hp0 (by simpa using hmem)

/-- **Disjoint symbols give orthogonal spectral subspaces**, and they stay orthogonal
after `T` is applied. -/
theorem inner_range_eq_zero (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (p q : ℝ → ℝ)
    (hp : Continuous p) (hq : Continuous q) (hpq : ∀ μ ∈ spectrum ℝ T, p μ * q μ = 0) (y z : F) :
    (inner ℂ (cfc p T y) (cfc q T z) : ℂ) = 0 ∧
      (inner ℂ (cfc p T y) (T (cfc q T z)) : ℂ) = 0 := by
  have hPsa : IsSelfAdjoint (cfc p T) := cfc_predicate p T
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hPsa
  have hzero : cfc (fun t => p t * q t) T = 0 := by
    rw [cfc_congr hpq]
    exact cfc_const_zero ℝ T
  constructor
  · have h := hsym y (cfc q T z)
    simp only [ContinuousLinearMap.coe_coe] at h
    have hmul : cfc p T (cfc q T z) = (cfc (fun t => p t * q t) T) z := by
      rw [cfc_mul _ _ T hp.continuousOn hq.continuousOn]
      rfl
    rw [h, hmul, hzero]
    simp
  · have h := hsym y (T (cfc q T z))
    simp only [ContinuousLinearMap.coe_coe] at h
    have hmul : cfc p T (T (cfc q T z)) = (cfc (fun t => p t * (t * q t)) T) z := by
      rw [cfc_mul _ _ T hp.continuousOn (by fun_prop),
        cfc_mul _ _ T (by fun_prop) hq.continuousOn, cfc_id' ℝ T]
      rfl
    have hzero2 : cfc (fun t => p t * (t * q t)) T = 0 := by
      have hcongr : ∀ μ ∈ spectrum ℝ T, p μ * (μ * q μ) = 0 := by
        intro μ hμ
        have hz := hpq μ hμ
        have hmulcomm : p μ * (μ * q μ) = μ * (p μ * q μ) := by ring
        rw [hmulcomm, hz, mul_zero]
      rw [cfc_congr hcongr]
      exact cfc_const_zero ℝ T
    rw [h, hmul, hzero2]
    simp

end BookProof.MinMaxSpectrum
