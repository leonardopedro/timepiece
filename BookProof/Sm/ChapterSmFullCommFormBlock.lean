import Mathlib
import BookProof.Sm.ChapterSmFullCommFormDiagonal

/-!
# The commutator form: block-diagonal coefficient matrices of the four Higgs components

Work order: `SM_ESA_COMPLETION_PLAN.md` §18.

## 1. Why block-diagonal, and what "block" means here

§17's `coupledOp_diagonal_commForm_eq` treats a **diagonal** coefficient matrix: every internal
component `A` sees the *same* bosonic operator `T`, and only the scalar weight `d A` varies.  The
physical coefficient matrices of the P2 normal form are sums `Σⱼ uⱼ ⊗ Mⱼ` with `Mⱼ` supported on
the four Higgs components, so the more faithful finite-dimensional shape is a **block-diagonal**
matrix *whose blocks carry different operators*: the `a`-th block acts with the `a`-th Higgs
coordinate `u_{pos a}`.

`blockMat blk d a` is the `a`-th block of a diagonal matrix cut out by the block index
`blk : Finset (Fin 96) → Fin 4`, and `blockOp T blk d = Σ_a T_a ⊗ blockMat blk d a`.  The
decomposition is honest — `sum_blockMat` shows the four blocks reassemble into the plain diagonal
matrix `diag d`, and `blockOp_apply` shows that component `A` is `d A • T_{blk A} f_A`, i.e. the
operator acting on a component is selected by its block.

## 2. What survives of §17's identity

The identity survives in full: because each block acts diagonally *inside itself*, component `A` of
the block operator still pairs with its own comparison `N f_A`, so

```text
commForm (Σ_a T_a ⊗ blk_a) (N ⊗ 1) f = Σ_A d_A commForm (T_{blk A}) N f_A,
```

and the quadratic-form-level bound `blockOp_commForm_le` follows with the same constant as the
diagonal case.  The hypothesis there is the scalar form bound `|commForm T_a N y| ≤ c quadForm N y`
of each block's operator; for multiplication families the corpus has no such scalar bound, so the
second half of the module works at the norm level instead (`blockOp_norm_le`, fed to
`abs_commForm_le_of_norm_le`), which is how §17 discharged the Higgs placement as well.

## 3. The four Higgs components

`smPos_block_norm_le` instantiates the block operator with `T_a = u_{pos a}` — the four Higgs
coordinates of `SmInternalData` — against the SM comparison `smFlN`, and
`smCanonical_smPos_block_commForm_le` fixes the canonical placement `smCanonicalPos`, so the
commutator bound of the block-diagonal Higgs family needs **no** hypothesis on the placement.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmFullCommFormBlock

open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.SmHamiltonian BookProof.SmOneParticle BookProof.SmFarisLavine
open BookProof.QgOuterFockFL
open BookProof.SmFullMatter BookProof.SmFullCoupledCore BookProof.SmFullYukawaCoeffs
open BookProof.SmFullFamilyBounds BookProof.SmMatter BookProof.YangMillsHermite
open BookProof.SmFullNormalFormBounds
open BookProof.SmFullCommFormDiagonal

noncomputable section

/-! ## 1. The block-diagonal matrix and the block operator -/

/-- **The `a`-th block of a block-diagonal coefficient matrix**: the diagonal entries of the
components whose block index is `a`, and zero elsewhere. -/
def blockMat (blk : Finset (Fin 96) → Fin 4) (d : Finset (Fin 96) → ℝ) (a : Fin 4) :
    Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ :=
  Matrix.diagonal fun A => if blk A = a then (d A : ℂ) else 0

/-- **The four blocks reassemble into the diagonal matrix** `diag d`: the block decomposition is a
partition of the diagonal entries, not an additional hypothesis. -/
theorem sum_blockMat (blk : Finset (Fin 96) → Fin 4) (d : Finset (Fin 96) → ℝ) :
    (∑ a : Fin 4, blockMat blk d a) = Matrix.diagonal fun A => (d A : ℂ) := by
  ext A B
  rw [Matrix.sum_apply]
  by_cases hAB : A = B
  · subst hAB
    rw [Matrix.diagonal_apply, if_pos rfl, Finset.sum_eq_single (blk A)]
    · simp only [blockMat, Matrix.diagonal_apply, if_true]
    · intro a _ ha
      rw [blockMat, Matrix.diagonal_apply, if_pos rfl, if_neg (Ne.symm ha)]
    · intro h
      exact absurd (Finset.mem_univ (blk A)) h
  · rw [Matrix.diagonal_apply, if_neg hAB]
    exact Finset.sum_eq_zero fun a _ => by
      rw [blockMat, Matrix.diagonal_apply, if_neg hAB]

/-- **The block-diagonal operator of a component family**: the `a`-th block acts with the `a`-th
member of the family `T` on the components of that block. -/
def blockOp (T : Fin 4 → polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (blk : Finset (Fin 96) → Fin 4) (d : Finset (Fin 96) → ℝ) :
    SmCoupledCore →ₗ[ℂ] SmCoupledSpace :=
  ∑ a : Fin 4, coupledOp (T a) (blockMat blk d a)

set_option maxHeartbeats 1000000 in
-- the double internal sum and the two inner products need more `isDefEq` work than the default
-- heartbeat budget allows
/-- **The action of the block operator**: component `A` sees the operator of its own block,
`d A • T_{blk A} f_A`. -/
theorem blockOp_apply (T : Fin 4 → polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (blk : Finset (Fin 96) → Fin 4) (d : Finset (Fin 96) → ℝ) (f : SmCoupledCore)
    (A : Finset (Fin 96)) :
    (blockOp T blk d f).ofLp A = (d A : ℂ) • T (blk A) (coreComp f A) := by
  have hsum : (blockOp T blk d f).ofLp A
      = ∑ a : Fin 4, (coupledOp (T a) (blockMat blk d a) f).ofLp A := by
    rw [blockOp, LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  rw [hsum, Finset.sum_eq_single (blk A)]
  · rw [coupledOp_apply, Finset.sum_eq_single A]
    · rw [blockMat, Matrix.diagonal_apply, if_pos rfl, if_pos rfl]
    · intro B _ hBA
      rw [blockMat, Matrix.diagonal_apply, if_neg (Ne.symm hBA), zero_smul]
    · intro h
      exact absurd (Finset.mem_univ A) h
  · intro a _ ha
    rw [coupledOp_apply]
    refine Finset.sum_eq_zero fun C _ => ?_
    by_cases hCA : A = C
    · subst hCA
      rw [blockMat, Matrix.diagonal_apply, if_pos rfl, if_neg (Ne.symm ha), zero_smul]
    · rw [blockMat, Matrix.diagonal_apply, if_neg hCA, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ (blk A)) h

/-! ## 2. The commutator form at the quadratic-form level -/

set_option maxHeartbeats 1000000 in
-- the double internal sum and the two inner products need more `isDefEq` work than the default
-- heartbeat budget allows
/-- **The commutator form of a block-diagonal operator is the sum of the blockwise scalar forms.**
Only the operator of a component's own block meets that component, so no `T a` is paired with the
comparison of a different component — the exact analogue of §17's diagonal identity. -/
theorem blockOp_commForm_eq (T : Fin 4 → polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163) (blk : Finset (Fin 96) → Fin 4)
    (d : Finset (Fin 96) → ℝ) (f : SmCoupledCore) :
    commForm (blockOp T blk d) (coupledOp N 1) f
      = ∑ A, d A * commForm (T (blk A)) N (coreComp f A) := by
  have hinner : (inner ℂ (blockOp T blk d f) (coupledOp N 1 f) : ℂ)
      = ∑ A, (d A : ℂ) * inner ℂ (T (blk A) (coreComp f A)) (N (coreComp f A)) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [blockOp_apply, coupledOp_one_apply, inner_smul_left]
    simp
  rw [commForm_eq, hinner, Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [commForm_eq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  ring

set_option maxHeartbeats 1000000 in
-- the componentwise sums and their rearrangement exceed the default heartbeat budget
/-- **The commutator bound at the quadratic-form level for a block-diagonal coefficient matrix.**
Each block contributes its own scalar form bound and its own weight sum, and the blockwise
quadratic forms are dominated by the coupled one, so no shifted-graph-norm-squared factor
remains. -/
theorem blockOp_commForm_le (T : Fin 4 → polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163) {c : ℝ} (hc : 0 ≤ c)
    (hT : ∀ (a : Fin 4) (y : polyGaussCore (d := 163)), |commForm (T a) N y| ≤ c * quadForm N y)
    (hposN : ∀ y : polyGaussCore (d := 163), 0 ≤ quadForm N y)
    (blk : Finset (Fin 96) → Fin 4) (d : Finset (Fin 96) → ℝ) (hdiag : ∀ A, 0 ≤ d A)
    (f : SmCoupledCore) :
    |commForm (blockOp T blk d) (coupledOp N 1) f|
      ≤ c * (∑ A, d A) * quadForm (coupledOp N 1) f := by
  have hsingle : ∀ A : Finset (Fin 96),
      quadForm N (coreComp f A) ≤ ∑ B, quadForm N (coreComp f B) := fun A =>
    Finset.single_le_sum (f := fun B => quadForm N (coreComp f B))
      (fun B _ => hposN (coreComp f B)) (Finset.mem_univ A)
  rw [blockOp_commForm_eq]
  calc |∑ A, d A * commForm (T (blk A)) N (coreComp f A)|
      ≤ ∑ A, |d A * commForm (T (blk A)) N (coreComp f A)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ A, d A * |commForm (T (blk A)) N (coreComp f A)| := by
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [abs_mul, abs_of_nonneg (hdiag A)]
    _ ≤ ∑ A, d A * (c * quadForm N (coreComp f A)) :=
        Finset.sum_le_sum fun A _ =>
          mul_le_mul_of_nonneg_left (hT (blk A) (coreComp f A)) (hdiag A)
    _ = c * ∑ A, d A * quadForm N (coreComp f A) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun A _ => by ring
    _ ≤ c * ((∑ A, d A) * ∑ A, quadForm N (coreComp f A)) := by
        refine mul_le_mul_of_nonneg_left ?_ hc
        calc ∑ A, d A * quadForm N (coreComp f A)
            ≤ ∑ A, d A * ∑ B, quadForm N (coreComp f B) :=
              Finset.sum_le_sum fun A _ => mul_le_mul_of_nonneg_left (hsingle A) (hdiag A)
          _ = (∑ A, d A) * ∑ B, quadForm N (coreComp f B) := by rw [Finset.sum_mul]
    _ = c * (∑ A, d A) * quadForm (coupledOp N 1) f := by
        rw [coupledOp_one_quadForm]
        ring

/-! ## 3. The norm level: multiplication families carry no scalar form bound -/

set_option maxHeartbeats 1000000 in
-- the `ℓ²` reassembly of the coupled norm and the componentwise sums exceed the default budget
/-- **The relative bound of a block-diagonal operator** from the relative bound of each block's
operator, with the block weights entering through `K ≥ |d A|`.  This is the norm-level sibling of
`blockOp_commForm_le`, and the form in which the Higgs coordinates can be fed in. -/
theorem blockOp_norm_le (T : Fin 4 → polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163) {c K : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hT : ∀ (a : Fin 4) (x : polyGaussCore (d := 163)),
      ‖T a x‖ ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (blk : Finset (Fin 96) → Fin 4) (d : Finset (Fin 96) → ℝ) (hbd : ∀ A, |d A| ≤ K)
    (f : SmCoupledCore) :
    ‖blockOp T blk d f‖ ≤ c * K * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ := by
  have hsq : ‖blockOp T blk d f‖ ^ 2
      ≤ (c * K * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖) ^ 2 := by
    rw [coupledSpace_norm_sq, mul_pow, coupledOp_one_add_norm_sq, Finset.mul_sum]
    refine Finset.sum_le_sum fun A _ => ?_
    have h1 : |d A| * ‖T (blk A) (coreComp f A)‖
        ≤ K * (c * ‖N (coreComp f A)
          + ((coreComp f A : polyGaussCore (d := 163)) : L2d 163)‖) :=
      mul_le_mul (hbd A) (hT (blk A) (coreComp f A)) (norm_nonneg _) hK
    calc ‖(blockOp T blk d f).ofLp A‖ ^ 2
        = (|d A| * ‖T (blk A) (coreComp f A)‖) ^ 2 := by
          rw [blockOp_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
      _ ≤ (K * (c * ‖N (coreComp f A)
            + ((coreComp f A : polyGaussCore (d := 163)) : L2d 163)‖)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = (c * K) ^ 2 * ‖N (coreComp f A)
            + ((coreComp f A : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 := by ring
  have h2 : (0 : ℝ) ≤ c * K * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ :=
    mul_nonneg (mul_nonneg hc hK) (norm_nonneg _)
  have := (sq_le_sq).mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg h2] at this

/-! ## 4. The four Higgs components -/

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **The relative bound of the block-diagonal Higgs family.**  The `a`-th block acts with the
`a`-th Higgs coordinate `u_{pos a}`, whose relative bound is §15's
`smPos_smCoord_norm_le_shift` with constant `1`; the only requirement on the blocks is that every
Higgs component sits on one of the `40` harmonic coordinates. -/
theorem smPos_block_norm_le (D : SmInternalData) (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (hpos : ∀ a : Fin 4, ∃ m : Fin 40, D.pos a = smCoord m)
    (blk : Finset (Fin 96) → Fin 4) (d : Finset (Fin 96) → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hbd : ∀ A, |d A| ≤ K) (f : SmCoupledCore) :
    ‖blockOp (fun a => (polyGaussCore (d := 163)).subtype.comp (smPos (D.pos a))) blk d f‖
      ≤ 1 * K * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ :=
  blockOp_norm_le _ _ (by norm_num) hK
    (fun a x => by
      obtain ⟨m, hm⟩ := hpos a
      rw [hm]
      simpa only [LinearMap.comp_apply, Submodule.subtype_apply, one_mul] using
        smPos_smCoord_norm_le_shift P hc0 m x)
    blk d hbd f

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **The commutator-form bound of the block-diagonal Higgs family**, through §17's engine
`abs_commForm_le_of_norm_le`: the block weights enter only through `K`. -/
theorem smPos_block_commForm_le (D : SmInternalData) (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (hpos : ∀ a : Fin 4, ∃ m : Fin 40, D.pos a = smCoord m)
    (blk : Finset (Fin 96) → Fin 4) (d : Finset (Fin 96) → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hbd : ∀ A, |d A| ≤ K) (f : SmCoupledCore) :
    |commForm (blockOp (fun a => (polyGaussCore (d := 163)).subtype.comp (smPos (D.pos a)))
        blk d) (coupledOp (smFlN P c0) 1) f|
      ≤ 4 * (1 * K) * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ ^ 2 :=
  abs_commForm_le_of_norm_le _ (smFlN P c0) (smFlN_quadForm_nonneg P hc0)
    (by simpa using hK) (fun f => smPos_block_norm_le D P hc0 hpos blk d hK hbd f) f

/-- The internal data with only the canonical placement fixed: the block operator of
`smCanonical_smPos_block_commForm_le` reads `pos` and no coefficient matrix. -/
def smCanonicalInternalData : SmInternalData where
  pos := smCanonicalPos
  higgs := fun _ => 0
  mass := 0
  higgsHermitian := fun _ => by
    ext i j
    simp
  massHermitian := by
    ext i j
    simp

/-- **The commutator-form bound of the block-diagonal Higgs family at the canonical placement —
with no hypothesis left.**  `smCanonicalPos` places the `a`-th Higgs component on a harmonic
coordinate by construction, so `smPos_block_commForm_le` applies with its placement hypothesis
discharged. -/
theorem smCanonical_smPos_block_commForm_le (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (blk : Finset (Fin 96) → Fin 4) (d : Finset (Fin 96) → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hbd : ∀ A, |d A| ≤ K) (f : SmCoupledCore) :
    |commForm (blockOp (fun a => (polyGaussCore (d := 163)).subtype.comp
        (smPos (smCanonicalPos a))) blk d) (coupledOp (smFlN P c0) 1) f|
      ≤ 4 * (1 * K) * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ ^ 2 :=
  smPos_block_commForm_le smCanonicalInternalData P hc0 smCanonicalPos_harmonic blk d hK hbd f

end

end BookProof.SmFullCommFormBlock
