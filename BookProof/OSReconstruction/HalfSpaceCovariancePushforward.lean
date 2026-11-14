import Mathlib
import BookProof.OSReconstruction.HalfSpaceFreeState

/-!
# A non-diagonal covariance pushforward

Plan: `cftproof.md`, **E3** — `HalfSpaceInfiniteVolumeGaussian` builds the infinite-volume
free-field state as a product of independent blocks, i.e. with *identity* covariance.  The next
step recorded in `E3_RECONSTRUCTION_CHAIN.md` §4.2.3 item 5 is a **non-diagonal** covariance: the
massive free field has two-point function `(−Δ+m²)⁻¹`, whose off-diagonal entries are nonzero.
This module builds that pushforward on the smallest nontrivial truncation, where the computation
is exact.

The construction is the Cholesky step: if `X`, `Z` are independent unit Gaussians and
`Y = ρ X + √(1-ρ²) Z`, the pair `(X, Y)` has unit variances and covariance `ρ`.  So the
pushforward of the product reference law along the (non-diagonal) linear map
`p ↦ (p.1, ρ p.1 + s p.2)` is a state whose covariance matrix is `[[1, ρ], [ρ, 1]]`.

## Contents

* `refPair` — the product of two unit Gaussians (the two-site reference law);
* `corrMap ρ s`, `corrLaw ρ s` — the Cholesky map and **the pushforward**;
* `cov_fst_snd_refPair`, `cov_fst_fst_refPair`, `cov_mix_refPair` — the covariance entries of the
  reference law (`0`, `1`, and `ρ`);
* `corrLaw_cov`, `corrLaw_var` — **the pushforward has covariance `ρ` and unit variances**;
* `covMatrix`, `covMatrix_hsNormSq` — the covariance matrix and its squared Hilbert–Schmidt norm
  `2 + 2ρ²` (finite rank, hence Hilbert–Schmidt);
* `lapInvMatrix`, `covMatrix_eq_lapInv` — for `ρ = 1/(1+m²)` the covariance is a positive multiple
  of the two-site `(−Δ+m²)⁻¹`.

## Boundary

* This is the two-site truncation.  The full `(−Δ+m²)⁻¹` on an infinite lattice would need the
  Hilbert–Schmidt square root of an infinite covariance applied to the product law; Mathlib has no
  multivariate Gaussian pushforward, so the chain case is not attempted.
* `covMatrix_eq_lapInv` is a matrix identity, not an operator equality: it identifies the
  covariance of the two-site state with `λ • (−Δ+m²)⁻¹` for the explicit `λ`.
* Only second moments are computed; no `IsGaussian` instance for the pushforward is claimed.
-/

namespace BookProof.OSReconstruction

open MeasureTheory ProbabilityTheory
open Matrix

noncomputable section

/-! ## The reference law and the Cholesky map -/

/-- **The two-site reference law**: two independent unit Gaussians. -/
def refPair : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

instance refPair_isProbability : IsProbabilityMeasure refPair := by
  unfold refPair
  infer_instance

/-- **The Cholesky map** `p ↦ (p.1, ρ p.1 + s p.2)`; with `s = √(1-ρ²)` it produces a pair with
unit variances and correlation `ρ`. -/
def corrMap (ρ s : ℝ) : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, ρ * p.1 + s * p.2)

theorem measurable_corrMap (ρ s : ℝ) : Measurable (corrMap ρ s) := by
  unfold corrMap
  fun_prop

/-- **The pushforward**: the pair law with non-diagonal covariance. -/
def corrLaw (ρ s : ℝ) : Measure (ℝ × ℝ) := refPair.map (corrMap ρ s)

instance corrLaw_isProbability (ρ s : ℝ) : IsProbabilityMeasure (corrLaw ρ s) := by
  unfold corrLaw
  exact Measure.isProbabilityMeasure_map (measurable_corrMap ρ s).aemeasurable

/-- The mixed second coordinate, as a function on the reference law. -/
def mixVar (ρ s : ℝ) : ℝ × ℝ → ℝ := fun p => ρ * p.1 + s * p.2

/-! ## The covariance entries of the reference law -/

/-- **The reference law has no correlation**: the two coordinates are independent. -/
theorem cov_fst_snd_refPair :
    cov[fun p : ℝ × ℝ => p.1, fun p : ℝ × ℝ => p.2; refPair] = 0 := by
  unfold refPair
  exact covariance_fst_snd_prod (memLp_id_gaussianReal 2) (memLp_id_gaussianReal 2)

/-- The mean of the first coordinate of the reference law. -/
theorem integral_fst_refPair : ∫ p : ℝ × ℝ, p.1 ∂refPair = 0 := by
  unfold refPair
  rw [integral_fun_fst (f := fun x : ℝ => x)]
  simp

/-- The second moment of one coordinate of the reference law. -/
theorem integral_sq_gaussUnit : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral
    (by fun_prop : AEMeasurable (fun x : ℝ => x) (gaussianReal 0 1)),
    integral_id_gaussianReal] at h
  simpa using h

theorem integral_sq_fst_refPair : ∫ p : ℝ × ℝ, p.1 ^ 2 ∂refPair = 1 := by
  unfold refPair
  rw [integral_fun_fst (f := fun x : ℝ => x ^ 2), integral_sq_gaussUnit]
  simp

/-- **The unit variance of one coordinate of the reference law.** -/
theorem cov_fst_fst_refPair :
    cov[fun p : ℝ × ℝ => p.1, fun p : ℝ × ℝ => p.1; refPair] = 1 := by
  rw [covariance_self (by fun_prop : AEMeasurable (fun p : ℝ × ℝ => p.1) refPair),
    variance_eq_integral (by fun_prop : AEMeasurable (fun p : ℝ × ℝ => p.1) refPair),
    integral_fst_refPair]
  simpa using integral_sq_fst_refPair

/-- **The correlation `ρ` of the mixed coordinate** with the first one. -/
theorem cov_mix_refPair (ρ s : ℝ) :
    cov[fun p : ℝ × ℝ => p.1, mixVar ρ s; refPair] = ρ := by
  have hX : MemLp (fun p : ℝ × ℝ => p.1) 2 refPair :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_fst _
  have hZ : MemLp (fun p : ℝ × ℝ => p.2) 2 refPair :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_snd _
  have hmix : mixVar ρ s
      = (fun p : ℝ × ℝ => ρ * p.1) + fun p : ℝ × ℝ => s * p.2 := rfl
  rw [hmix, covariance_add_right hX (hX.const_mul ρ) (hZ.const_mul s),
    covariance_const_mul_right, covariance_const_mul_right, cov_fst_snd_refPair,
    cov_fst_fst_refPair]
  ring

/-! ## The covariance of the pushforward -/

/-- **The pushed-forward state has the non-diagonal covariance `ρ`.** -/
theorem corrLaw_cov (ρ s : ℝ) :
    cov[fun p : ℝ × ℝ => p.1, fun p : ℝ × ℝ => p.2; corrLaw ρ s] = ρ := by
  unfold corrLaw
  rw [covariance_map (Z := corrMap ρ s)
    (Measurable.aestronglyMeasurable (by fun_prop : Measurable (fun p : ℝ × ℝ => p.1)))
    (Measurable.aestronglyMeasurable (by fun_prop : Measurable (fun p : ℝ × ℝ => p.2)))
    (measurable_corrMap ρ s).aemeasurable]
  rw [show ((fun p : ℝ × ℝ => p.1) ∘ corrMap ρ s) = fun p : ℝ × ℝ => p.1 from rfl,
    show ((fun p : ℝ × ℝ => p.2) ∘ corrMap ρ s) = mixVar ρ s from rfl]
  exact cov_mix_refPair ρ s

/-- **The pushforward has unit variances**, so with `corrLaw_cov` its covariance matrix is
`[[1, ρ], [ρ, 1]]`. -/
theorem corrLaw_var (ρ s : ℝ) :
    cov[fun p : ℝ × ℝ => p.1, fun p : ℝ × ℝ => p.1; corrLaw ρ s] = 1 := by
  unfold corrLaw
  rw [covariance_map (Z := corrMap ρ s)
    (Measurable.aestronglyMeasurable (by fun_prop : Measurable (fun p : ℝ × ℝ => p.1)))
    (Measurable.aestronglyMeasurable (by fun_prop : Measurable (fun p : ℝ × ℝ => p.1)))
    (measurable_corrMap ρ s).aemeasurable]
  rw [show ((fun p : ℝ × ℝ => p.1) ∘ corrMap ρ s) = fun p : ℝ × ℝ => p.1 from rfl]
  exact cov_fst_fst_refPair

/-! ## The covariance matrix, its Hilbert–Schmidt norm, and `(−Δ+m²)⁻¹` -/

/-- **The covariance matrix** of the pushed-forward state. -/
def covMatrix (ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, ρ; ρ, 1]

theorem covMatrix_zero_zero (ρ : ℝ) : covMatrix ρ 0 0 = 1 := by simp [covMatrix]

theorem covMatrix_zero_one (ρ : ℝ) : covMatrix ρ 0 1 = ρ := by simp [covMatrix]

theorem covMatrix_one_zero (ρ : ℝ) : covMatrix ρ 1 0 = ρ := by simp [covMatrix]

theorem covMatrix_one_one (ρ : ℝ) : covMatrix ρ 1 1 = 1 := by simp [covMatrix]

/-- **The covariance operator is Hilbert–Schmidt**: the squared Hilbert–Schmidt norm of the
`2 × 2` covariance matrix is finite, `2 + 2ρ²`. -/
theorem covMatrix_hsNormSq (ρ : ℝ) :
    ∑ i : Fin 2, ∑ j : Fin 2, covMatrix ρ i j ^ 2 = 2 + 2 * ρ ^ 2 := by
  simp [covMatrix, Fin.sum_univ_two]
  ring

/-- The two-site `(−Δ+m²)⁻¹` as a matrix: diagonal `(1+m²)/(m²(2+m²))`, off-diagonal
`1/(m²(2+m²))`. -/
def lapInvMatrix (m : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then (1 + m ^ 2) / (m ^ 2 * (2 + m ^ 2))
    else 1 / (m ^ 2 * (2 + m ^ 2))

/-- **The covariance is a positive multiple of the two-site `(−Δ+m²)⁻¹`**: for `ρ = 1/(1+m²)` the
covariance matrix is `λ • (−Δ+m²)⁻¹` with `λ = m²(2+m²)/(1+m²)`. -/
theorem covMatrix_eq_lapInv (m : ℝ) (hm : 0 < m) :
    covMatrix (1 / (1 + m ^ 2)) = (m ^ 2 * (2 + m ^ 2) / (1 + m ^ 2)) • lapInvMatrix m := by
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hm)
  have h1 : 1 + m ^ 2 ≠ 0 := by positivity
  have h2 : 2 + m ^ 2 ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [covMatrix, lapInvMatrix, Matrix.smul_apply, smul_eq_mul]
  all_goals field_simp

end

end BookProof.OSReconstruction
