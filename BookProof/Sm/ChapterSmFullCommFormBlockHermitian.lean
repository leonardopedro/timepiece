import Mathlib
import BookProof.Sm.ChapterSmFullCommFormBlock

/-!
# The commutator form: block-diagonal operators with Hermitian block interiors

Work order: `SM_ESA_COMPLETION_PLAN.md` §20.

## 1. What §18 left open

§18's `blockOp T blk d` lets the four blocks carry four *different* operators, but the interior of
each block is still a **scalar** `d A`.  Its closing note says so: "a bound with a non-diagonal
block interior is not claimed".  The current module closes that, at the norm level, for an arbitrary
family `M a` of complex matrices — in particular for Hermitian ones, which is what the P1 Yukawa
dictionary supplies.

`blockOpMat T M = Σ_a T_a ⊗ M_a` is the operator: no block index is needed, because the support of
`M a` *is* the block.  The hypothesis that makes it block-diagonal is the support condition
`hsupp : M a A B ≠ 0 → blk A = a`, which for `M a = blockMat blk d a` is automatic
(`blockOp_eq_blockOpMat` shows `blockOp` is the special case).

## 2. Why the bound needs Schur's test

For a scalar interior the proof of §18 is componentwise: `‖(blockOp f).ofLp A‖ ≤ K c ‖N f_A + f_A‖`
and summing the squares of the *right* sides rebuilds `‖N ⊗ 1 f + f‖²` exactly, so the constant `K`
is not degraded.  With a non-diagonal interior, component `A` reads a whole row of `M`, so the
componentwise bound becomes `‖(blockOpMat f).ofLp A‖ ≤ c ∑_B |M A B| g_B` with
`g_B = ‖N f_B + f_B‖`, and the sum is controlled by Cauchy–Schwarz:

```text
(∑_B |M A B| g_B)² ≤ (∑_B |M A B|) · (∑_B |M A B| g_B²),
```

which after summing over `A` and swapping the two finite sums gives Schur's test

```text
‖blockOpMat T M f‖ ≤ c √(ρ κ) ‖N ⊗ 1 f + f‖,
ρ ≥ sup_A ∑_B |M_{blk A} A B|,      κ ≥ sup_B ∑_A |M_{blk A} A B|.
```

For a diagonal interior both Schur sums equal `sup_A |d A|`, so `√(ρ κ)` is exactly §18's `K`
(`rowSum_blockMat`, `colSum_blockMat`): the generalization degrades nothing.  A plain Cauchy–Schwarz
in `(A, B)` instead would have cost `√(96)` — the number of internal components — which is why the
bound is stated with the two Schur sums rather than a Hilbert–Schmidt norm.

## 3. What is still not claimed

The *form-level* identity of §18 (`commForm = Σ_A d_A commForm`) does not survive a non-diagonal
interior: component `A` then pairs `T f_B` with `N f_A` for `B ≠ A`, and the imaginary part of that
cross pairing is not a scalar form bound of `T`.  The commutator bound below is therefore obtained
from the norm bound through §17's engine `abs_commForm_le_of_norm_le`, which is how §18 handled the
multiplication families as well.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmFullCommFormBlockHermitian

open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.SmHamiltonian BookProof.SmOneParticle BookProof.SmFarisLavine
open BookProof.SmFullMatter BookProof.SmFullCoupledCore BookProof.SmFullYukawaCoeffs
open BookProof.SmFullFamilyBounds BookProof.SmMatter BookProof.YangMillsHermite
open BookProof.SmFullNormalFormBounds BookProof.SmFullCommFormDiagonal
open BookProof.SmFullCommFormBlock

noncomputable section

/-! ## 1. The weighted Cauchy–Schwarz step -/

/-- **Cauchy–Schwarz with weights**: `(∑ w g)² ≤ (∑ w)(∑ w g²)`.  This is the inequality behind
Schur's test; it is stated separately because both of its factors are used again. -/
theorem sq_sum_mul_le_sum_mul_sq {ι : Type*} (s : Finset ι) (w g : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * g i) ^ 2 ≤ (∑ i ∈ s, w i) * (∑ i ∈ s, w i * g i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i) * g i)
  have h1 : (∑ i ∈ s, Real.sqrt (w i) * (Real.sqrt (w i) * g i))
      = ∑ i ∈ s, w i * g i :=
    Finset.sum_congr rfl fun i hi => by
      rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  have h2 : (∑ i ∈ s, Real.sqrt (w i) ^ 2) = ∑ i ∈ s, w i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hw i hi)
  have h3 : (∑ i ∈ s, (Real.sqrt (w i) * g i) ^ 2) = ∑ i ∈ s, w i * g i ^ 2 :=
    Finset.sum_congr rfl fun i hi => by
      rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rw [h1, h2, h3] at h
  exact h

/-! ## 2. The Schur sums and the block operator -/

/-- **The `A`-th row sum of the matrix family**, with row `A` read in the matrix of `A`'s own block.
For a scalar interior this is `|d A|`. -/
def rowSum (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (blk : Finset (Fin 96) → Fin 4) (A : Finset (Fin 96)) : ℝ :=
  ∑ B, ‖M (blk A) A B‖

/-- **The `B`-th column sum of the matrix family**, the second Schur sum. -/
def colSum (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (blk : Finset (Fin 96) → Fin 4) (B : Finset (Fin 96)) : ℝ :=
  ∑ A, ‖M (blk A) A B‖

/-- **The block operator of a matrix family**: the `a`-th block acts with `T a` against the full
matrix `M a`.  The support of `M a` — not a scalar weight — is what makes this block-diagonal. -/
def blockOpMat (T : Fin 4 → polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ) :
    SmCoupledCore →ₗ[ℂ] SmCoupledSpace :=
  ∑ a : Fin 4, coupledOp (T a) (M a)

/-- **§18's block operator is the diagonal special case**: `blockOp` with weights `d` is
`blockOpMat` with the matrix family `a ↦ blockMat blk d a`. -/
theorem blockOp_eq_blockOpMat (T : Fin 4 → polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (blk : Finset (Fin 96) → Fin 4) (d : Finset (Fin 96) → ℝ) :
    blockOp T blk d = blockOpMat T fun a => blockMat blk d a := rfl

/-- **The support condition makes the block operator act blockwise**: component `A` is met only by
the matrix of its own block, so `A` sees the row `M_{blk A} A ·`. -/
theorem blockOpMat_apply_of_supp (T : Fin 4 → polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (blk : Finset (Fin 96) → Fin 4)
    (hsupp : ∀ (a : Fin 4) (A B : Finset (Fin 96)), M a A B ≠ 0 → blk A = a)
    (f : SmCoupledCore) (A : Finset (Fin 96)) :
    (blockOpMat T M f).ofLp A = ∑ B, M (blk A) A B • T (blk A) (coreComp f B) := by
  have hsum : (blockOpMat T M f).ofLp A
      = ∑ a : Fin 4, ∑ B, M a A B • T a (coreComp f B) := by
    rw [blockOpMat, LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => coupledOp_apply (T a) (M a) f A
  rw [hsum, Finset.sum_eq_single (blk A)]
  · intro a _ ha
    refine Finset.sum_eq_zero fun B _ => ?_
    by_cases h : M a A B = 0
    · rw [h, zero_smul]
    · exact absurd (hsupp a A B h) (Ne.symm ha)
  · intro h
    exact absurd (Finset.mem_univ (blk A)) h

/-- **The componentwise Schur bound**: component `A` of the block operator is bounded by the row
sum of its own block's matrix against the componentwise bounds `v B` of the operators. -/
theorem blockOpMat_component_le (T : Fin 4 → polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (blk : Finset (Fin 96) → Fin 4)
    (hsupp : ∀ (a : Fin 4) (A B : Finset (Fin 96)), M a A B ≠ 0 → blk A = a)
    (f : SmCoupledCore) (A : Finset (Fin 96)) (v : Finset (Fin 96) → ℝ)
    (hv : ∀ B, ‖T (blk A) (coreComp f B)‖ ≤ v B) :
    ‖(blockOpMat T M f).ofLp A‖ ≤ ∑ B, ‖M (blk A) A B‖ * v B := by
  rw [blockOpMat_apply_of_supp T M blk hsupp f A]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun B _ => ?_
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hv B) (norm_nonneg _)

/-! ## 3. Schur's test: the norm bound -/

set_option maxHeartbeats 1000000 in
-- the two nested sums over the internal components and their swap exceed the default budget
set_option maxRecDepth 4000 in
/-- **Schur's test for the block operator.**  The two Schur sums `ρ` and `κ` replace the scalar
weight `K` of §18, and the constant is `c √(ρ κ)`: for a diagonal interior this is exactly §18's
`c K`, so nothing is degraded by allowing a full Hermitian interior. -/
theorem blockOpMat_norm_sq_le (T : Fin 4 → polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (blk : Finset (Fin 96) → Fin 4)
    (hsupp : ∀ (a : Fin 4) (A B : Finset (Fin 96)), M a A B ≠ 0 → blk A = a)
    (N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163) {c ρ κ : ℝ} (hc : 0 ≤ c)
    (hT : ∀ (a : Fin 4) (x : polyGaussCore (d := 163)),
      ‖T a x‖ ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (hρ0 : 0 ≤ ρ)
    (hrow : ∀ A, rowSum M blk A ≤ ρ) (hcol : ∀ B, colSum M blk B ≤ κ)
    (f : SmCoupledCore) :
    ‖blockOpMat T M f‖ ^ 2
      ≤ c ^ 2 * (ρ * κ) * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ ^ 2 := by
  set g : Finset (Fin 96) → ℝ :=
    fun B => ‖N (coreComp f B) + ((coreComp f B : polyGaussCore (d := 163)) : L2d 163)‖
  -- the componentwise bound, then Cauchy–Schwarz with weights
  have hA : ∀ A : Finset (Fin 96),
      ‖(blockOpMat T M f).ofLp A‖ ^ 2
        ≤ c ^ 2 * rowSum M blk A * ∑ B, ‖M (blk A) A B‖ * g B ^ 2 := by
    intro A
    have h1 : ‖(blockOpMat T M f).ofLp A‖ ≤ c * ∑ B, ‖M (blk A) A B‖ * g B := by
      refine (blockOpMat_component_le T M blk hsupp f A (fun B => c * g B)
        (fun B => hT (blk A) (coreComp f B))).trans ?_
      rw [Finset.mul_sum]
      exact le_of_eq (Finset.sum_congr rfl fun B _ => by ring)
    have h2 : (∑ B, ‖M (blk A) A B‖ * g B) ^ 2
        ≤ (∑ B, ‖M (blk A) A B‖) * ∑ B, ‖M (blk A) A B‖ * g B ^ 2 :=
      sq_sum_mul_le_sum_mul_sq _ _ _ (fun _ _ => norm_nonneg _)
    have h3 : ‖(blockOpMat T M f).ofLp A‖ ^ 2
        ≤ (c * ∑ B, ‖M (blk A) A B‖ * g B) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    refine h3.trans ?_
    rw [rowSum]
    calc (c * ∑ B, ‖M (blk A) A B‖ * g B) ^ 2
        = c ^ 2 * (∑ B, ‖M (blk A) A B‖ * g B) ^ 2 := by ring
      _ ≤ c ^ 2 * ((∑ B, ‖M (blk A) A B‖) * ∑ B, ‖M (blk A) A B‖ * g B ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hc 2)
      _ = c ^ 2 * (∑ B, ‖M (blk A) A B‖) * ∑ B, ‖M (blk A) A B‖ * g B ^ 2 := by ring
  -- sum over the components and swap the two finite sums
  have hsum : ∑ A, ‖(blockOpMat T M f).ofLp A‖ ^ 2
      ≤ c ^ 2 * (ρ * κ) * ∑ B, g B ^ 2 := by
    calc ∑ A, ‖(blockOpMat T M f).ofLp A‖ ^ 2
        ≤ ∑ A, c ^ 2 * rowSum M blk A * ∑ B, ‖M (blk A) A B‖ * g B ^ 2 :=
          Finset.sum_le_sum fun A _ => hA A
      _ ≤ ∑ A, c ^ 2 * ρ * ∑ B, ‖M (blk A) A B‖ * g B ^ 2 := by
          refine Finset.sum_le_sum fun A _ => ?_
          refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun B _ => ?_)
          · exact mul_le_mul_of_nonneg_left (hrow A) (by positivity)
          · exact mul_nonneg (norm_nonneg _) (sq_nonneg _)
      _ = c ^ 2 * ρ * ∑ A, ∑ B, ‖M (blk A) A B‖ * g B ^ 2 := by
          rw [Finset.mul_sum]
      _ = c ^ 2 * ρ * ∑ B, (∑ A, ‖M (blk A) A B‖) * g B ^ 2 := by
          congr 1
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun B _ => by rw [Finset.sum_mul]
      _ ≤ c ^ 2 * ρ * ∑ B, κ * g B ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun B _ => ?_)
            (by positivity)
          exact mul_le_mul_of_nonneg_right (hcol B) (sq_nonneg _)
      _ = c ^ 2 * (ρ * κ) * ∑ B, g B ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun B _ => ?_
          ring
  rw [coupledSpace_norm_sq]
  have hnorm : ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ ^ 2 = ∑ B, g B ^ 2 :=
    coupledOp_one_add_norm_sq N f
  rw [hnorm]
  exact hsum

/-- **Schur's test in the form used downstream**: the square root of the product of the two Schur
sums is the constant of the relative bound. -/
theorem blockOpMat_norm_le (T : Fin 4 → polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (blk : Finset (Fin 96) → Fin 4)
    (hsupp : ∀ (a : Fin 4) (A B : Finset (Fin 96)), M a A B ≠ 0 → blk A = a)
    (N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163) {c ρ κ : ℝ} (hc : 0 ≤ c)
    (hT : ∀ (a : Fin 4) (x : polyGaussCore (d := 163)),
      ‖T a x‖ ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (hρ0 : 0 ≤ ρ) (hκ0 : 0 ≤ κ)
    (hrow : ∀ A, rowSum M blk A ≤ ρ) (hcol : ∀ B, colSum M blk B ≤ κ)
    (f : SmCoupledCore) :
    ‖blockOpMat T M f‖ ≤ c * Real.sqrt (ρ * κ)
      * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ := by
  have hsq := blockOpMat_norm_sq_le T M blk hsupp N hc hT hρ0 hrow hcol f
  have hrhs : c ^ 2 * (ρ * κ) * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ ^ 2
      = (c * Real.sqrt (ρ * κ) * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hρ0 hκ0)]
  rw [hrhs] at hsq
  have h2 : (0 : ℝ) ≤ c * Real.sqrt (ρ * κ)
      * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ := by positivity
  have := (sq_le_sq).mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg h2] at this

/-! ## 4. Recovering §18's constant in the diagonal case -/

/-- **The row sum of a scalar interior is the weight itself**, so Schur's `ρ` is §18's `K`. -/
theorem rowSum_blockMat (blk : Finset (Fin 96) → Fin 4) (d : Finset (Fin 96) → ℝ)
    (A : Finset (Fin 96)) :
    rowSum (fun a => blockMat blk d a) blk A = |d A| := by
  simp only [rowSum, blockMat, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single A]
  · simp
  · intro B _ hBA
    rw [if_neg (fun h => hBA h.symm), norm_zero]
  · intro h
    exact absurd (Finset.mem_univ A) h

/-- **The column sum of a scalar interior is the weight itself**, so Schur's `κ` is §18's `K`. -/
theorem colSum_blockMat (blk : Finset (Fin 96) → Fin 4) (d : Finset (Fin 96) → ℝ)
    (B : Finset (Fin 96)) :
    colSum (fun a => blockMat blk d a) blk B = |d B| := by
  simp only [colSum, blockMat, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single B]
  · simp
  · intro A _ hAB
    rw [if_neg hAB, norm_zero]
  · intro h
    exact absurd (Finset.mem_univ B) h

/-! ## 5. The four Higgs components with full Hermitian interiors -/

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **The relative bound of the block-diagonal Higgs family with Hermitian block interiors.**
Same statement as §18's `smPos_block_norm_le`, but the interior of each block is now a full matrix
family `M`, controlled by its two Schur sums. -/
theorem smPos_blockMat_norm_le (D : SmInternalData) (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (hpos : ∀ a : Fin 4, ∃ m : Fin 40, D.pos a = smCoord m)
    (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (blk : Finset (Fin 96) → Fin 4)
    (hsupp : ∀ (a : Fin 4) (A B : Finset (Fin 96)), M a A B ≠ 0 → blk A = a)
    {ρ κ : ℝ} (hρ0 : 0 ≤ ρ) (hκ0 : 0 ≤ κ)
    (hrow : ∀ A, rowSum M blk A ≤ ρ) (hcol : ∀ B, colSum M blk B ≤ κ)
    (f : SmCoupledCore) :
    ‖blockOpMat (fun a => (polyGaussCore (d := 163)).subtype.comp (smPos (D.pos a))) M f‖
      ≤ 1 * Real.sqrt (ρ * κ) * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ :=
  blockOpMat_norm_le _ M blk hsupp _ (by norm_num) (fun a x => by
      obtain ⟨m, hm⟩ := hpos a
      rw [hm]
      simpa only [LinearMap.comp_apply, Submodule.subtype_apply, one_mul] using
        smPos_smCoord_norm_le_shift P hc0 m x)
    hρ0 hκ0 hrow hcol f

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **The commutator-form bound of the block-diagonal Higgs family with Hermitian interiors**,
through §17's engine `abs_commForm_le_of_norm_le`.  This is the bound §18 could not reach for a
non-diagonal interior, and the form in which the P1 coefficient matrices enter. -/
theorem smPos_blockMat_commForm_le (D : SmInternalData) (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (hpos : ∀ a : Fin 4, ∃ m : Fin 40, D.pos a = smCoord m)
    (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (blk : Finset (Fin 96) → Fin 4)
    (hsupp : ∀ (a : Fin 4) (A B : Finset (Fin 96)), M a A B ≠ 0 → blk A = a)
    {ρ κ : ℝ} (hρ0 : 0 ≤ ρ) (hκ0 : 0 ≤ κ)
    (hrow : ∀ A, rowSum M blk A ≤ ρ) (hcol : ∀ B, colSum M blk B ≤ κ)
    (f : SmCoupledCore) :
    |commForm (blockOpMat (fun a => (polyGaussCore (d := 163)).subtype.comp (smPos (D.pos a))) M)
        (coupledOp (smFlN P c0) 1) f|
      ≤ 4 * (1 * Real.sqrt (ρ * κ))
        * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ ^ 2 :=
  abs_commForm_le_of_norm_le _ (smFlN P c0) (smFlN_quadForm_nonneg P hc0)
    (by positivity)
    (fun f => smPos_blockMat_norm_le D P hc0 hpos M blk hsupp hρ0 hκ0 hrow hcol f) f

/-- **The same bound at the canonical placement `smCanonicalPos`** — for the P1 dictionary, whose
Higgs components sit on the canonical harmonic coordinates. -/
theorem smCanonical_smPos_blockMat_commForm_le (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (blk : Finset (Fin 96) → Fin 4)
    (hsupp : ∀ (a : Fin 4) (A B : Finset (Fin 96)), M a A B ≠ 0 → blk A = a)
    {ρ κ : ℝ} (hρ0 : 0 ≤ ρ) (hκ0 : 0 ≤ κ)
    (hrow : ∀ A, rowSum M blk A ≤ ρ) (hcol : ∀ B, colSum M blk B ≤ κ)
    (f : SmCoupledCore) :
    |commForm (blockOpMat (fun a => (polyGaussCore (d := 163)).subtype.comp
        (smPos (smCanonicalPos a))) M) (coupledOp (smFlN P c0) 1) f|
      ≤ 4 * (1 * Real.sqrt (ρ * κ))
        * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ ^ 2 :=
  smPos_blockMat_commForm_le smCanonicalInternalData P hc0 smCanonicalPos_harmonic M blk hsupp
    hρ0 hκ0 hrow hcol f

end

end BookProof.SmFullCommFormBlockHermitian
