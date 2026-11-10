import Mathlib
import BookProof.Sm.ChapterSmFullCommFormBlockP1Schur

/-!
# The operator-valued Schur test: no block-diagonal support condition

Work order: `SM_ESA_COMPLETION_PLAN.md` §25.

## 1. What §20 still assumed

§20's block operator `blockOpMat T M = Σ_a T_a ⊗ M_a` was bounded under
`hsupp : M a A B ≠ 0 → blk A = a`: the `a`-th matrix may only reach the block `a`.  That covers
block-diagonal coefficient family — in particular the P1 dictionary of §21 — but not a family that
mixes blocks, and the SM's Yukawa couplings do mix them (the Higgs generator carries both the
component index and the internal mode index).

This section removes the condition.  The component formula is no longer `A`'s own row, but the full
double sum

```text
(Σ_a T_a ⊗ M_a f).ofLp A = Σ_a Σ_B (M_a)_{A B} • T_a f_B,
```

and the Schur weight is the *sum* over the components,

```text
w A B = Σ_a ‖(M_a)_{A B}‖,
```

with the two Schur sums `rowSumGen M A = Σ_B w A B` and `colSumGen M B = Σ_A w A B`.  The rest of
Schur's test is unchanged, so the constant is again `c √(ρ κ)`.

## 2. Consistency with §20

`weightSum_eq_of_supp` proves that under §20's `hsupp` the weight collapses to a single term,
`w A B = ‖(M_{blk A})_{A B}‖`, so `rowSumGen`/`colSumGen` reduce to §20's `rowSum`/`colSum`.  The
general bound is therefore a strict extension and not a weaker parallel theory: nothing is lost by
using it, and the constant of the diagonal case is recovered exactly.

## 3. Why the extension is worth the factor

`w` sums `4` absolute values instead of one, so for the P1 dictionary §24's radii acquire exactly
one factor `card (Fin 4) = 4` (`p1HiggsGeneralRowRadius`), and the column count stays as in §24.  In
exchange the coefficient family is free: any `M : Fin 4 → Matrix _ _ ℂ` whatsoever, no support
condition, no `blk`.  `smCanonical_p1Higgs_commForm_le_unconditional` is the payoff — the commutator
bound for the P1 Higgs dictionary with **no hypothesis at all** beyond `0 ≤ c₀`, since the support
condition is gone and the Schur data is the explicit radius.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmFullCommFormBlockGeneral

open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.SmHamiltonian BookProof.SmOneParticle BookProof.SmFarisLavine
open BookProof.SmFullMatter BookProof.SmFullCoupledCore BookProof.SmFullYukawaCoeffs
open BookProof.SmFullFamilyBounds BookProof.SmMatter BookProof.SmFullNormalFormBounds
open BookProof.SmFullCommFormDiagonal BookProof.SmFullCommFormBlock
open BookProof.SmFullCommFormBlockHermitian
open BookProof.SmFullCommFormBlockHermitianP1 BookProof.SmFullCommFormBlockHermitianP1Schur

noncomputable section

/-! ## 1. The Schur weight and the two general Schur sums -/

/-- **The Schur weight**: the total size of the coefficient of `T_a f_B` in component `A`, summed
over the four internal components. -/
def weightSum (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (A B : Finset (Fin 96)) : ℝ :=
  ∑ a : Fin 4, ‖M a A B‖

/-- **The general row sum**: the sum of the Schur weight over `B`. -/
def rowSumGen (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (A : Finset (Fin 96)) : ℝ :=
  ∑ B, weightSum M A B

/-- **The general column sum**. -/
def colSumGen (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (B : Finset (Fin 96)) : ℝ :=
  ∑ A, weightSum M A B

theorem weightSum_nonneg (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (A B : Finset (Fin 96)) : 0 ≤ weightSum M A B :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- **The weighted sum is the double sum over the components**: the form in which the general Schur
step is carried out. -/
theorem sum_weightSum_mul (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (A : Finset (Fin 96)) (v : Finset (Fin 96) → ℝ) :
    (∑ B, weightSum M A B * v B) = ∑ a : Fin 4, ∑ B, ‖M a A B‖ * v B := by
  have h : ∑ B, weightSum M A B * v B = ∑ B, ∑ a : Fin 4, ‖M a A B‖ * v B := by
    refine Finset.sum_congr rfl fun B _ => ?_
    simp only [weightSum, Finset.sum_mul]
  rw [h, Finset.sum_comm]

/-- **The swap of the two component sums**, in the form the Schur estimate needs. -/
theorem sum_sum_weightSum_mul_sq (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (g : Finset (Fin 96) → ℝ) :
    ∑ A : Finset (Fin 96), ∑ B, weightSum M A B * g B ^ 2
      = ∑ B, (∑ A : Finset (Fin 96), weightSum M A B) * g B ^ 2 := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun B _ => by rw [Finset.sum_mul]

/-- **Under §20's support condition the general weight collapses to §20's row**: only the term of
`A`'s own block survives, so `rowSumGen`/`colSumGen` are §20's `rowSum`/`colSum`. -/
theorem weightSum_eq_of_supp (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (blk : Finset (Fin 96) → Fin 4)
    (hsupp : ∀ (a : Fin 4) (A B : Finset (Fin 96)), M a A B ≠ 0 → blk A = a)
    (A B : Finset (Fin 96)) :
    weightSum M A B = ‖M (blk A) A B‖ := by
  rw [weightSum, Finset.sum_eq_single (blk A)]
  · intro a _ ha
    rw [norm_eq_zero]
    have hzero : ¬(M a A B ≠ 0) := fun hne => (Ne.symm ha) (hsupp a A B hne)
    exact not_not.mp hzero
  · intro h
    exact absurd (Finset.mem_univ (blk A)) h

/-! ## 2. The component formula, with no support condition -/

/-- **Componentwise form of the block operator**: component `A` sees the whole double sum, because
`M_a` need not vanish off the block `a`. -/
theorem blockOpMat_apply_general (T : Fin 4 → polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (f : SmCoupledCore) (A : Finset (Fin 96)) :
    (blockOpMat T M f).ofLp A = ∑ a : Fin 4, ∑ B, M a A B • T a (coreComp f B) := by
  rw [blockOpMat, LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => coupledOp_apply (T a) (M a) f A

/-- **The componentwise bound with the general weight**: component `A` is bounded by the weighted
sum of the componentwise bounds `v B` of the operators, with the weight `w A B`. -/
theorem blockOpMat_component_le_general (T : Fin 4 → polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (f : SmCoupledCore) (A : Finset (Fin 96)) (v : Finset (Fin 96) → ℝ)
    (hv : ∀ (a : Fin 4) (B : Finset (Fin 96)), ‖T a (coreComp f B)‖ ≤ v B) :
    ‖(blockOpMat T M f).ofLp A‖ ≤ ∑ B, weightSum M A B * v B := by
  have hblock : ∀ a : Fin 4,
      ‖∑ B, M a A B • T a (coreComp f B)‖ ≤ ∑ B, ‖M a A B‖ * v B := by
    intro a
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum fun B _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hv a B) (norm_nonneg _)
  rw [blockOpMat_apply_general T M f A]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun a _ => hblock a).trans ?_
  exact le_of_eq (sum_weightSum_mul M A v).symm

/-! ## 3. Schur's test without the support condition -/

set_option maxHeartbeats 1000000 in
-- the three nested sums over the internal components and their swaps exceed the default budget
/-- **Schur's test for an operator-valued coefficient family**, with no block-diagonal condition:
the constant is `c √(ρ κ)` from the two general Schur sums. -/
theorem blockOpMat_norm_sq_le_general (T : Fin 4 → polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163) {c ρ κ : ℝ} (hc : 0 ≤ c)
    (hT : ∀ (a : Fin 4) (x : polyGaussCore (d := 163)),
      ‖T a x‖ ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (hρ0 : 0 ≤ ρ) (hrow : ∀ A, rowSumGen M A ≤ ρ) (hcol : ∀ B, colSumGen M B ≤ κ)
    (f : SmCoupledCore) :
    ‖blockOpMat T M f‖ ^ 2
      ≤ c ^ 2 * (ρ * κ) * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ ^ 2 := by
  set g : Finset (Fin 96) → ℝ :=
    fun B => ‖N (coreComp f B) + ((coreComp f B : polyGaussCore (d := 163)) : L2d 163)‖
  have hA : ∀ A : Finset (Fin 96),
      ‖(blockOpMat T M f).ofLp A‖ ^ 2
        ≤ c ^ 2 * rowSumGen M A * ∑ B, weightSum M A B * g B ^ 2 := by
    intro A
    have h1 : ‖(blockOpMat T M f).ofLp A‖ ≤ c * ∑ B, weightSum M A B * g B := by
      refine (blockOpMat_component_le_general T M f A (fun B => c * g B)
        (fun a B => hT a (coreComp f B))).trans ?_
      rw [Finset.mul_sum]
      exact le_of_eq (Finset.sum_congr rfl fun B _ => by ring)
    have h2 : (∑ B, weightSum M A B * g B) ^ 2
        ≤ (∑ B, weightSum M A B) * ∑ B, weightSum M A B * g B ^ 2 :=
      sq_sum_mul_le_sum_mul_sq _ _ _ (fun _ _ => weightSum_nonneg M A _)
    have h3 : ‖(blockOpMat T M f).ofLp A‖ ^ 2
        ≤ (c * ∑ B, weightSum M A B * g B) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    refine h3.trans ?_
    rw [rowSumGen]
    calc (c * ∑ B, weightSum M A B * g B) ^ 2
        = c ^ 2 * (∑ B, weightSum M A B * g B) ^ 2 := by ring
      _ ≤ c ^ 2 * ((∑ B, weightSum M A B) * ∑ B, weightSum M A B * g B ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hc 2)
      _ = c ^ 2 * (∑ B, weightSum M A B) * ∑ B, weightSum M A B * g B ^ 2 := by ring
  have hsum : ∑ A, ‖(blockOpMat T M f).ofLp A‖ ^ 2
      ≤ c ^ 2 * (ρ * κ) * ∑ B, g B ^ 2 := by
    calc ∑ A, ‖(blockOpMat T M f).ofLp A‖ ^ 2
        ≤ ∑ A, c ^ 2 * rowSumGen M A * ∑ B, weightSum M A B * g B ^ 2 :=
          Finset.sum_le_sum fun A _ => hA A
      _ ≤ ∑ A, c ^ 2 * ρ * ∑ B, weightSum M A B * g B ^ 2 := by
          refine Finset.sum_le_sum fun A _ => ?_
          refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun B _ => ?_)
          · exact mul_le_mul_of_nonneg_left (hrow A) (by positivity)
          · exact mul_nonneg (weightSum_nonneg M A B) (sq_nonneg _)
      _ = c ^ 2 * ρ * ∑ A, ∑ B, weightSum M A B * g B ^ 2 := by
          rw [Finset.mul_sum]
      _ = c ^ 2 * ρ * ∑ B, (∑ A, weightSum M A B) * g B ^ 2 := by
          rw [sum_sum_weightSum_mul_sq M g]
      _ ≤ c ^ 2 * ρ * ∑ B, κ * g B ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun B _ => ?_) (by positivity)
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

/-- **Schur's test in the form used downstream**, with the square root of the product of the two
general Schur sums as the constant. -/
theorem blockOpMat_norm_le_general (T : Fin 4 → polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163) {c ρ κ : ℝ} (hc : 0 ≤ c)
    (hT : ∀ (a : Fin 4) (x : polyGaussCore (d := 163)),
      ‖T a x‖ ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (hρ0 : 0 ≤ ρ) (hκ0 : 0 ≤ κ)
    (hrow : ∀ A, rowSumGen M A ≤ ρ) (hcol : ∀ B, colSumGen M B ≤ κ)
    (f : SmCoupledCore) :
    ‖blockOpMat T M f‖ ≤ c * Real.sqrt (ρ * κ)
      * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ := by
  have hsq := blockOpMat_norm_sq_le_general T M N hc hT hρ0 hrow hcol f
  have hrhs : c ^ 2 * (ρ * κ) * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ ^ 2
      = (c * Real.sqrt (ρ * κ) * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hρ0 hκ0)]
  rw [hrhs] at hsq
  have h2 : (0 : ℝ) ≤ c * Real.sqrt (ρ * κ)
      * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ := by positivity
  have := (sq_le_sq).mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg h2] at this

/-! ## 4. The SM Higgs family with a coefficient family that may mix blocks -/

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **The relative bound of the Higgs family for an arbitrary coefficient family** — no support
condition on `M`, so the four components may mix their blocks arbitrarily. -/
theorem smPos_blockMat_norm_le_general (D : SmInternalData) (P : SmParams) {c0 : ℝ}
    (hc0 : 0 ≤ c0) (hpos : ∀ a : Fin 4, ∃ m : Fin 40, D.pos a = smCoord m)
    (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    {ρ κ : ℝ} (hρ0 : 0 ≤ ρ) (hκ0 : 0 ≤ κ)
    (hrow : ∀ A, rowSumGen M A ≤ ρ) (hcol : ∀ B, colSumGen M B ≤ κ)
    (f : SmCoupledCore) :
    ‖blockOpMat (fun a => (polyGaussCore (d := 163)).subtype.comp (smPos (D.pos a))) M f‖
      ≤ 1 * Real.sqrt (ρ * κ) * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ :=
  blockOpMat_norm_le_general _ M _ (by norm_num) (fun a x => by
      obtain ⟨m, hm⟩ := hpos a
      rw [hm]
      simpa only [LinearMap.comp_apply, Submodule.subtype_apply, one_mul] using
        smPos_smCoord_norm_le_shift P hc0 m x)
    hρ0 hκ0 hrow hcol f

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **The commutator-form bound for an arbitrary coefficient family**, through §17's engine
`abs_commForm_le_of_norm_le`.  This is §20's bound with the block-support condition removed. -/
theorem smPos_blockMat_commForm_le_general (D : SmInternalData) (P : SmParams) {c0 : ℝ}
    (hc0 : 0 ≤ c0) (hpos : ∀ a : Fin 4, ∃ m : Fin 40, D.pos a = smCoord m)
    (M : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    {ρ κ : ℝ} (hρ0 : 0 ≤ ρ) (hκ0 : 0 ≤ κ)
    (hrow : ∀ A, rowSumGen M A ≤ ρ) (hcol : ∀ B, colSumGen M B ≤ κ)
    (f : SmCoupledCore) :
    |commForm (blockOpMat (fun a => (polyGaussCore (d := 163)).subtype.comp
        (smPos (D.pos a))) M) (coupledOp (smFlN P c0) 1) f|
      ≤ 4 * (1 * Real.sqrt (ρ * κ))
        * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ ^ 2 :=
  abs_commForm_le_of_norm_le _ (smFlN P c0) (smFlN_quadForm_nonneg P hc0)
    (by positivity)
    (fun f => smPos_blockMat_norm_le_general D P hc0 hpos M hρ0 hκ0 hrow hcol f) f

/-! ## 5. The P1 dictionary with no hypothesis at all -/

/-- **The general row radius of the P1 matrices**: §24's radius with the one factor the mixing
costs — the cardinality of the component index `Fin 4`. -/
def p1HiggsGeneralRowRadius (D : SmInternalData) : ℝ :=
  (Fintype.card (Fin 4) : ℝ) * p1HiggsRowRadius D

/-- **The general column radius** of the P1 matrices. -/
def p1HiggsGeneralColRadius (D : SmInternalData) : ℝ :=
  (Fintype.card (Finset (Fin 96)) : ℝ) * p1HiggsGeneralRowRadius D

theorem p1HiggsGeneralRowRadius_nonneg (D : SmInternalData) :
    0 ≤ p1HiggsGeneralRowRadius D :=
  mul_nonneg (by positivity) (p1HiggsRowRadius_nonneg D)

theorem p1HiggsGeneralColRadius_nonneg (D : SmInternalData) :
    0 ≤ p1HiggsGeneralColRadius D :=
  mul_nonneg (by positivity) (p1HiggsGeneralRowRadius_nonneg D)

/-- **The general row sums of the four P1 matrices are bounded by `p1HiggsGeneralRowRadius`**, with
no support condition and no placement hypothesis. -/
theorem rowSumGen_p1Higgs_le (D : SmInternalData) (A : Finset (Fin 96)) :
    rowSumGen (p1HiggsMat D) A ≤ p1HiggsGeneralRowRadius D := by
  have hterm : ∀ a : Fin 4, ∑ B, ‖p1HiggsMat D a A B‖ ≤ p1HiggsRowRadius D := by
    intro a
    calc ∑ B, ‖p1HiggsMat D a A B‖
        ≤ ∑ B : Finset (Fin 96), p1HiggsMassTotal D * ‖fockBasis B‖ :=
          Finset.sum_le_sum fun B _ => p1Higgs_entry_le D a A B
      _ = p1HiggsRowRadius D := by
          simp only [p1HiggsRowRadius, fockMass, Finset.mul_sum]
  calc rowSumGen (p1HiggsMat D) A
      = ∑ a : Fin 4, ∑ B, ‖p1HiggsMat D a A B‖ := by
        simp only [rowSumGen, weightSum]
        exact Finset.sum_comm
    _ ≤ ∑ _a : Fin 4, p1HiggsRowRadius D := Finset.sum_le_sum fun a _ => hterm a
    _ = p1HiggsGeneralRowRadius D := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [p1HiggsGeneralRowRadius]

/-- **The general column sums of the four P1 matrices are bounded by `p1HiggsGeneralColRadius`.** -/
theorem colSumGen_p1Higgs_le (D : SmInternalData) (B : Finset (Fin 96)) :
    colSumGen (p1HiggsMat D) B ≤ p1HiggsGeneralColRadius D := by
  have hterm : ∀ (a : Fin 4) (A : Finset (Fin 96)),
      ‖p1HiggsMat D a A B‖ ≤ p1HiggsMassTotal D * ‖fockBasis B‖ :=
    fun a A => p1Higgs_entry_le D a A B
  have hinner : ∀ A : Finset (Fin 96),
      weightSum (p1HiggsMat D) A B ≤ (Fintype.card (Fin 4) : ℝ) * p1HiggsMassTotal D
        * ‖fockBasis B‖ := by
    intro A
    have h1 : weightSum (p1HiggsMat D) A B
        ≤ ∑ _a : Fin 4, p1HiggsMassTotal D * ‖fockBasis B‖ :=
      Finset.sum_le_sum fun a _ => hterm a A
    calc weightSum (p1HiggsMat D) A B
        ≤ ∑ _a : Fin 4, p1HiggsMassTotal D * ‖fockBasis B‖ := h1
      _ = (Fintype.card (Fin 4) : ℝ) * (p1HiggsMassTotal D * ‖fockBasis B‖) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Fintype.card (Fin 4) : ℝ) * p1HiggsMassTotal D * ‖fockBasis B‖ := by ring_nf
  calc colSumGen (p1HiggsMat D) B
      = ∑ A : Finset (Fin 96), weightSum (p1HiggsMat D) A B := rfl
    _ ≤ ∑ _A : Finset (Fin 96), (Fintype.card (Fin 4) : ℝ) * p1HiggsMassTotal D
          * ‖fockBasis B‖ := Finset.sum_le_sum fun A _ => hinner A
    _ = (Fintype.card (Finset (Fin 96)) : ℝ) * ((Fintype.card (Fin 4) : ℝ)
          * p1HiggsMassTotal D * ‖fockBasis B‖) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ p1HiggsGeneralColRadius D := by
        rw [p1HiggsGeneralColRadius, p1HiggsGeneralRowRadius, p1HiggsRowRadius, fockMass]
        have hcard : (0 : ℝ) ≤ (Fintype.card (Finset (Fin 96)) : ℝ) := by positivity
        have hm : (0 : ℝ) ≤ (Fintype.card (Fin 4) : ℝ) * p1HiggsMassTotal D :=
          mul_nonneg (by positivity) (p1HiggsMassTotal_nonneg D)
        have hkey := mul_le_mul_of_nonneg_left (fockBasis_norm_le_mass B) hm
        refine (mul_le_mul_of_nonneg_left hkey hcard).trans (le_of_eq ?_)
        simp only [fockMass]
        ring

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **The commutator bound for the P1 Yukawa dictionary with no hypothesis left**: no block-support
condition (this section), no Schur data (§24's explicit radii), no placement hypothesis (the
canonical placement).  Only `0 ≤ c₀` remains. -/
theorem smCanonical_p1Higgs_commForm_le_unconditional (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (f : SmCoupledCore) :
    |commForm (blockOpMat (fun a => (polyGaussCore (d := 163)).subtype.comp
        (smPos (smCanonicalPos a))) (p1HiggsMat smCanonicalInternalData))
        (coupledOp (smFlN P c0) 1) f|
      ≤ 4 * Real.sqrt (p1HiggsGeneralRowRadius smCanonicalInternalData
          * p1HiggsGeneralColRadius smCanonicalInternalData)
        * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ ^ 2 :=
  by
  simpa only [one_mul] using
    smPos_blockMat_commForm_le_general smCanonicalInternalData P hc0 smCanonicalPos_harmonic
      (p1HiggsMat smCanonicalInternalData)
      (p1HiggsGeneralRowRadius_nonneg smCanonicalInternalData)
      (p1HiggsGeneralColRadius_nonneg smCanonicalInternalData)
      (rowSumGen_p1Higgs_le smCanonicalInternalData)
      (colSumGen_p1Higgs_le smCanonicalInternalData) f

end

end BookProof.SmFullCommFormBlockGeneral
