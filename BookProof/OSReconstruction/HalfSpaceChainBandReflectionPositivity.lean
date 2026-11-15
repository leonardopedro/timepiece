import Mathlib
import BookProof.OSReconstruction.HalfSpaceChainBandHSNorm
import BookProof.OSReconstruction.HalfSpaceChainBandCovariance

/-!
# Reflection positivity of the doubled finite-volume banded chain state

Plan: `cftproof.md`, **E3**.  This is the finite-volume counterpart of
`bandedCovZ_doubled_reflectionPositive` (`HalfSpaceInfiniteBandedCovariance`), for the width-`k`
cycle covariance `bandCov` (`HalfSpaceChainBandCovariance`).  The doubled state has two halves
sharing `bandCov` and carrying independent white noise, so its blocks are
`[[C + 1, C ∘ θ], [θ ∘ C, C + 1]]`: the OS form is `doubledBandForm`, and it is nonnegative
whenever `θ` is a bijection preserving `C` (`bandCov_doubled_reflectionPositive`).  The shift
`θ = σ` is such a symmetry, which makes the statement non-vacuous
(`bandCov_doubled_reflectionPositive_shift`).  As in infinite volume, positivity comes from the
`+ 1` blocks: the reflected cross block alone is not positive.

## Contents

* `bandCov_posSemidef` — `bandCov` is positive semidefinite, being the covariance matrix of the
  probability measure `bandLaw`;
* `doubledBandForm` — the OS form of the doubled state, with reflection `θ`;
* `doubledBandForm_eq_folded` — that form is the quadratic form of `bandCov` at the folded test
  function `H p = f p + g (θ⁻¹ p)`, plus the two white-noise sums;
* `bandCov_doubled_reflectionPositive` — the doubled form is nonnegative for every pair of test
  functions;
* `bandCov_shift_apply_apply`, `bandCov_doubled_reflectionPositive_shift` — the shift instance.

## Boundary

* **A bilinear statement, not a measure-level one.**  `0 ≤ ∫ F · θF dμ` for every observable `F` of
  one half needs the measure of the coupled state; what is proved here is positivity of the
  covariance form, exactly as in the infinite-volume module.
* **The reflection is an input.**  `θ` must preserve `bandCov`.  The geometric reflection of a
  cycle (negation of the cycle coordinate, which reverses the shift) is not constructed here: only
  the abstract invariance hypothesis and the shift instance are recorded.
* **Truncation.**  `bandCov` is the width-`k` truncation of the free covariance, not the massive
  `(−Δ + m²)⁻¹`; the statement is about that truncation on the cycle.
-/

namespace BookProof.OSReconstruction

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- **`bandCov` is positive semidefinite**: it is the covariance matrix of the probability measure
`bandLaw`, so the quadratic form is a variance. -/
theorem bandCov_posSemidef {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ)
    (k : ℕ) (f : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, bandCov σ ρ k i j * f i * f j := by
  classical
  have hmem : ∀ i : ι, MemLp (fun z : ι → ℝ => z i) 2 (bandLaw σ ρ k) :=
    fun i => memLp_eval_bandLaw σ ρ k i
  have hbilin : cov[(fun z : ι → ℝ => ∑ i, f i * z i),
      (fun z : ι → ℝ => ∑ i, f i * z i); bandLaw σ ρ k]
      = ∑ i, ∑ j, bandCov σ ρ k i j * f i * f j := by
    rw [covariance_fun_sum_fun_sum (X := fun i => fun z : ι → ℝ => f i * z i)
      (Y := fun j => fun z : ι → ℝ => f j * z j)
      (fun i => (hmem i).const_mul (f i)) (fun j => (hmem j).const_mul (f j))]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [covariance_const_mul_left, covariance_const_mul_right, bandLaw_cov σ ρ k i j]
    ring
  rw [← hbilin]
  have hmeas : Measurable (fun z : ι → ℝ => ∑ i, f i * z i) := by
    fun_prop
  rw [covariance_self hmeas.aemeasurable]
  exact variance_nonneg _ _

/-- **The OS form of the doubled banded chain state**: two `C + 1` blocks and the reflected cross
block `2 · ∑_{i,j} c(i,θ j) f i g j`, for a reflection `θ`. -/
def doubledBandForm {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ)
    (θ : Equiv.Perm ι) (f g : ι → ℝ) : ℝ :=
  (∑ i, ∑ j, bandCov σ ρ k i j * f i * f j)
    + (∑ i, ∑ j, bandCov σ ρ k i j * g i * g j)
    + 2 * (∑ i, ∑ j, bandCov σ ρ k i (θ j) * f i * g j)
    + (∑ i, f i * f i) + ∑ i, g i * g i

/-- **The doubled form is the quadratic form of the kernel at the folded test function**
`H p = f p + g (θ⁻¹ p)`, plus the two white-noise sums. -/
theorem doubledBandForm_eq_folded {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι)
    (ρ : ℝ) (k : ℕ) (θ : Equiv.Perm ι)
    (hθC : ∀ i j, bandCov σ ρ k (θ i) (θ j) = bandCov σ ρ k i j) (f g : ι → ℝ) :
    doubledBandForm σ ρ k θ f g
      = (∑ p, ∑ q, bandCov σ ρ k p q * (f p + g (θ.symm p)) * (f q + g (θ.symm q)))
        + (∑ i, f i * f i) + ∑ i, g i * g i := by
  classical
  have hAB : (∑ p, ∑ q, bandCov σ ρ k p q * f p * g (θ.symm q))
      = ∑ i, ∑ j, bandCov σ ρ k i (θ j) * f i * g j := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Equiv.sum_comp θ (fun q => bandCov σ ρ k i q * f i * g (θ.symm q))]
    simp
  have hBA : (∑ p, ∑ q, bandCov σ ρ k p q * g (θ.symm p) * f q)
      = ∑ i, ∑ j, bandCov σ ρ k i (θ j) * f i * g j := by
    rw [← Equiv.sum_comp θ (fun p => ∑ q, bandCov σ ρ k p q * g (θ.symm p) * f q)]
    simp only [Equiv.symm_apply_apply]
    have h1 : (∑ a, ∑ q, bandCov σ ρ k (θ a) q * g a * f q)
        = ∑ a, ∑ q, bandCov σ ρ k q (θ a) * f q * g a := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro q _
      rw [bandCov_comm σ ρ k (θ a) q]
      ring
    rw [h1, Finset.sum_comm]
  have hBB : (∑ p, ∑ q, bandCov σ ρ k p q * g (θ.symm p) * g (θ.symm q))
      = ∑ i, ∑ j, bandCov σ ρ k i j * g i * g j := by
    rw [← Equiv.sum_comp θ
      (fun p => ∑ q, bandCov σ ρ k p q * g (θ.symm p) * g (θ.symm q))]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Equiv.sum_comp θ
      (fun q => bandCov σ ρ k (θ i) q * g (θ.symm (θ i)) * g (θ.symm q))]
    simp only [Equiv.symm_apply_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hθC i j]
  have hpt : ∀ p q : ι, bandCov σ ρ k p q * (f p + g (θ.symm p)) * (f q + g (θ.symm q))
      = bandCov σ ρ k p q * f p * f q + bandCov σ ρ k p q * f p * g (θ.symm q)
        + bandCov σ ρ k p q * g (θ.symm p) * f q
        + bandCov σ ρ k p q * g (θ.symm p) * g (θ.symm q) := by
    intro p q
    ring
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
  simp only [Finset.sum_add_distrib]
  rw [hAB, hBA, hBB]
  unfold doubledBandForm
  ring

/-- **Reflection positivity of the doubled finite-volume banded state**: for any reflection `θ`
preserving `bandCov`, the OS form of the state with blocks `[[C + 1, C ∘ θ], [θ ∘ C, C + 1]]` is
nonnegative. -/
theorem bandCov_doubled_reflectionPositive {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ) (θ : Equiv.Perm ι)
    (hθC : ∀ i j, bandCov σ ρ k (θ i) (θ j) = bandCov σ ρ k i j) (f g : ι → ℝ) :
    0 ≤ doubledBandForm σ ρ k θ f g := by
  rw [doubledBandForm_eq_folded σ ρ k θ hθC f g]
  refine add_nonneg (add_nonneg (bandCov_posSemidef σ ρ k _) ?_) ?_
  · exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (f i))
  · exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (g i))

/-- Shifting both arguments by `σ` leaves the iterated `σ^[a]`-shift structure of a band entry
unchanged. -/
theorem iterate_apply_perm_apply {ι : Type*} (σ : Equiv.Perm ι) (a : ℕ) (i : ι) :
    (σ^[a + 1]) (σ i) = σ ((σ^[a + 1]) i) := by
  simp only [Equiv.Perm.iterate_eq_pow]
  rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply]
  congr 1
  group

/-- **The shift preserves `bandCov`**: the kernel only sees shifts of the cycle. -/
theorem bandCov_shift_apply_apply {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ) (i j : ι) :
    bandCov σ ρ k (σ i) (σ j) = bandCov σ ρ k i j := by
  classical
  simp only [bandCov, iterate_apply_perm_apply, σ.injective.eq_iff]

/-- **Reflection positivity for `θ = σ`**: the concrete instance of
`bandCov_doubled_reflectionPositive`. -/
theorem bandCov_doubled_reflectionPositive_shift {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (ρ : ℝ) (k : ℕ) (f g : ι → ℝ) :
    0 ≤ doubledBandForm σ ρ k σ f g :=
  bandCov_doubled_reflectionPositive σ ρ k σ (fun i j => bandCov_shift_apply_apply σ ρ k i j) f g

end

end BookProof.OSReconstruction
