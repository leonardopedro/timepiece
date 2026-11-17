import Mathlib
import BookProof.OSReconstruction.EuclideanMomentHierarchy
import BookProof.OSReconstruction.GaussianMehlerCylinderRP

/-!
# C2 ↔ C1: the free regulator reproduces the Mehler slice covariances

`cftproof.md` **C1** fixes the finite-cutoff Gaussian control in Mehler coordinates, whose
two-slice covariance in the slice coordinates `x₀ = (y₊ − y₋)/√2`, `x₁ = (y₊ + y₋)/√2` is

```text
C = [[A, B], [B, A]],   A k = (v₊ k + v₋ k)/2,   B k = (v₊ k − v₋ k)/2,
```

with `v₊ k = 1/(λ k + 1)`, `v₋ k = 1/(λ k + 3)` the Mehler variances
(`GaussianMehlerControl.variance`).  **C2** builds the Euclidean moment hierarchy from the
other direction: a reference vector and the semigroup `e^{-tK}`.

This module identifies the two at the level of the two-point function.  For one mode and a
unit time step, the free one-mode regulator `scalarK m` in the state of norm `√A`
(`Ω = √A`) has

```text
⟨Ω, Ω⟩ = A,        ⟨Ω, e^{-m} Ω⟩ = A e^{-m}.
```

Choosing the mass so that the decay factor equals the Mehler ratio `B/A`, the Euclidean
two-point function of the regulator equals the Mehler slice covariance: the diagonal is `A`,
the cross term `B`.  So the C1 slice covariance is exactly a free-regulator two-point
function, and `GaussianMehlerCylinderRP.sliceVariance_eq` (the mixture's variance bookkeeping)
is the same statement from the boundary-conditioned side.

Reflection positivity of this calibrated regulator is the general
`EuclideanMomentHierarchy.twoPoint_reflected_re_nonneg` statement, instantiated at the free
generator.

## Honest boundary

* Calibration, not equality of laws.  The identity below is a statement about the **two-point
  function** at one mode and unit separation; the scalar regulator's moments are not the
  Mehler path measure, and no field law, transfer operator or interacting claim is made.
* The mass is produced existentially from the ratio `B/A ∈ (0,1)` via `Real.log`.  It is
  the free mass that reproduces the covariance ratio; no identification with the physical
  cutoff mass is claimed.
* `A` and `B` are the C1 slice covariances of the *free* Gaussian control, not those of the
  regulated interacting state.
-/

noncomputable section

open scoped BigOperators InnerProductSpace

namespace BookProof.OSReconstruction

variable {M : ℕ}

/-! ## 1. The Euclidean two-point function in the state of norm `√A` -/

/-- **The free regulator's two-point function at variance `A`**: in the state
`Ω = √A`, the moment `⟨Ω, e^{-hK} Ω⟩` is `A e^{-h m}`. -/
theorem euclidMoment_scalarK_sqrt (m : ℝ) {A : ℝ} (hA : 0 ≤ A) (h : ℝ) :
    euclidMoment (scalarK m) ((Real.sqrt A : ℝ) : ℂ) 1 [(h, 1)]
      = ((A * Real.exp (-(h * m)) : ℝ) : ℂ) := by
  simp only [euclidMoment, euclidWord, one_mul, mul_one]
  rw [euclidEvol_scalarK, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  rw [inner_smul_right]
  have hsq : ⟪((Real.sqrt A : ℝ) : ℂ), ((Real.sqrt A : ℝ) : ℂ)⟫_ℂ = ((A : ℝ) : ℂ) := by
    have h1 : ⟪((Real.sqrt A : ℝ) : ℂ), ((Real.sqrt A : ℝ) : ℂ)⟫_ℂ
        = ((Real.sqrt A : ℝ) : ℂ) ^ 2 := by
      rw [RCLike.inner_apply, Complex.conj_ofReal]
      ring
    rw [h1]
    calc ((Real.sqrt A : ℝ) : ℂ) ^ 2 = ((Real.sqrt A ^ 2 : ℝ) : ℂ) := by
          rw [Complex.ofReal_pow]
      _ = ((A : ℝ) : ℂ) := by rw [Real.sq_sqrt hA]
  rw [hsq]
  push_cast
  ring

/-- At zero separation the regulator's two-point function is the **variance** `A`. -/
theorem euclidMoment_scalarK_sqrt_zero (m : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    euclidMoment (scalarK m) ((Real.sqrt A : ℝ) : ℂ) 1 [(0, 1)] = ((A : ℝ) : ℂ) := by
  rw [euclidMoment_scalarK_sqrt m hA 0]
  norm_num

/-! ## 2. The C1 slice covariance -/

/-- The **diagonal slice covariance** of the C1 Mehler control:
`A k = (v₊ k + v₋ k)/2`, the variance of the slice `x₁ k = (y₊ k + y₋ k)/√2`. -/
def sliceDiagonal (m0 : ℝ) (k : SpatialMode M) : ℝ :=
  (variance m0 (true, k) + variance m0 (false, k)) / 2

/-- The **cross slice covariance** of the C1 Mehler control:
`B k = (v₊ k − v₋ k)/2`, the correlation of the two slices, `E[x₁ k x₀ k]`. -/
def sliceCross (m0 : ℝ) (k : SpatialMode M) : ℝ :=
  (variance m0 (true, k) - variance m0 (false, k)) / 2

/-- The cross covariance is the shared-shift variance of the kernel state. -/
theorem sliceCross_eq_shiftVariance (m0 : ℝ) (k : SpatialMode M) :
    sliceCross m0 k = shiftVariance m0 k := rfl

/-- The diagonal is the boundary plus noise variance, i.e. the C1 slice variance. -/
theorem sliceDiagonal_eq_shiftVariance_add_noiseVariance (m0 : ℝ) (k : SpatialMode M) :
    sliceDiagonal m0 k = shiftVariance m0 k + noiseVariance m0 k := by
  have h := sliceVariance_eq m0 k
  unfold sliceDiagonal shiftVariance noiseVariance
  linarith

theorem sliceDiagonal_pos (m0 : ℝ) (k : SpatialMode M) : 0 < sliceDiagonal m0 k := by
  have h1 := variance_pos m0 (true, k)
  have h2 := variance_pos m0 (false, k)
  unfold sliceDiagonal
  linarith

/-- The cross covariance is **strictly positive**: the symmetric parity dominates.  This is
the sign that makes the reflected covariance positive in C1. -/
theorem sliceCross_pos (m0 : ℝ) (k : SpatialMode M) : 0 < sliceCross m0 k := by
  have hsym : variance m0 (true, k) = 1 / (m0 ^ 2 + spatialEigenvalue k + 1) := by
    unfold variance
    simp
  have hanti : variance m0 (false, k) = 1 / (m0 ^ 2 + spatialEigenvalue k + 3) := by
    unfold variance
    simp
  have h1 : 0 < m0 ^ 2 + spatialEigenvalue k + 1 := by
    nlinarith [sq_nonneg m0, spatialEigenvalue_nonneg k]
  have h3 : 0 < m0 ^ 2 + spatialEigenvalue k + 3 := by linarith
  have hdiff : 0 < 1 / (m0 ^ 2 + spatialEigenvalue k + 1)
      - 1 / (m0 ^ 2 + spatialEigenvalue k + 3) := by
    rw [div_sub_div _ _ h1.ne' h3.ne']
    refine div_pos (by linarith) (mul_pos h1 h3)
  unfold sliceCross
  rw [hsym, hanti]
  linarith

/-- The cross covariance is **smaller than the diagonal**: the ratio `B/A` is a decay
factor in `(0,1)`. -/
theorem sliceCross_lt_sliceDiagonal (m0 : ℝ) (k : SpatialMode M) :
    sliceCross m0 k < sliceDiagonal m0 k := by
  have h := variance_pos m0 (false, k)
  unfold sliceCross sliceDiagonal
  linarith

/-! ## 3. The calibration -/

/-- **The free regulator reproduces the Mehler slice covariances.**  There is a free mass
`m ≥ 0` such that the one-mode regulator in the state `Ω = √A` has diagonal two-point
function `A = sliceDiagonal` and, at unit separation, cross term `B = sliceCross`.  The mass
is `−log (B/A)`, the decay rate whose factor is the Mehler covariance ratio. -/
theorem free_regulator_reproduces_slice_covariance (m0 : ℝ) (k : SpatialMode M) :
    ∃ m : ℝ, 0 ≤ m ∧
      euclidMoment (scalarK m) ((Real.sqrt (sliceDiagonal m0 k) : ℝ) : ℂ) 1 [(0, 1)]
          = ((sliceDiagonal m0 k : ℝ) : ℂ) ∧
      euclidMoment (scalarK m) ((Real.sqrt (sliceDiagonal m0 k) : ℝ) : ℂ) 1 [(1, 1)]
          = ((sliceCross m0 k : ℝ) : ℂ) := by
  classical
  set A := sliceDiagonal m0 k with hAdef
  set B := sliceCross m0 k with hBdef
  have hApos : 0 < A := sliceDiagonal_pos m0 k
  have hBpos : 0 < B := sliceCross_pos m0 k
  have hlt : B < A := sliceCross_lt_sliceDiagonal m0 k
  have hrpos : 0 < B / A := div_pos hBpos hApos
  have hrle : B / A ≤ 1 := (div_le_one hApos).mpr hlt.le
  set r := B / A with hrdef
  have hlog : Real.log r ≤ 0 := Real.log_nonpos hrpos.le hrle
  refine ⟨-Real.log r, by linarith, ?_, ?_⟩
  · rw [euclidMoment_scalarK_sqrt _ hApos.le 0]
    norm_num
  · rw [euclidMoment_scalarK_sqrt _ hApos.le 1]
    have hexp : Real.exp (-(1 * -Real.log r)) = r := by
      rw [one_mul, neg_neg, Real.exp_log hrpos]
    rw [hexp]
    have hcancel : A * (B / A) = B := by
      field_simp
    rw [hcancel]

/-! ## 4. Reflection positivity of the calibrated regulator -/

/-- **Reflection positivity of the free regulator at the Mehler covariance.**  The four-term
reflected form of two insertions at separated times is nonnegative for the free one-mode
regulator — the C2 reflection-positivity statement, specialized to the generator whose
covariances calibrate against the C1 Mehler slices. -/
theorem free_regulator_twoPoint_reflected_re_nonneg (m : ℝ) (Ω : ℂ) (A B : ℂ →L[ℂ] ℂ)
    (s t : ℝ) :
    0 ≤ (euclidMoment (scalarK m) Ω (ContinuousLinearMap.adjoint A) [(s + s, A)]
        + euclidMoment (scalarK m) Ω (ContinuousLinearMap.adjoint A) [(s + t, B)]
        + euclidMoment (scalarK m) Ω (ContinuousLinearMap.adjoint B) [(t + s, A)]
        + euclidMoment (scalarK m) Ω (ContinuousLinearMap.adjoint B) [(t + t, B)]).re :=
  twoPoint_reflected_re_nonneg (scalarK m) Ω A B s t (scalarK_isSelfAdjoint m)

end BookProof.OSReconstruction
