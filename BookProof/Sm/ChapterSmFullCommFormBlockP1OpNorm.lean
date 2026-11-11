import Mathlib
import BookProof.Sm.ChapterSmFullCommFormBlockGeneral

/-!
# The P1 Schur radii as operator norms

Work order: `SM_ESA_COMPLETION_PLAN.md` §27.

## 1. What §24 and §25 charged

§24 replaced §21's abstract Schur data by explicit numbers, but it built them from the `ℓ¹` mass of
the internal matrices: `p1HiggsMass D a = ∑_{i j} ‖D.higgs a i j‖`, times
`fockMass = ∑_T ‖fockBasis T‖`.
That is a *sum over every entry* of the coefficient matrix, and a sum over every row is exactly what
a Schur row bound does not need: Schur's test asks for a bound on **each row**, uniformly in the
row.

This section uses the norm the row bound actually calls for.  On a finite matrix the `L^∞` operator
norm of Mathlib is the supremum of the row sums,

```text
‖M‖ = sup_A ∑_T ‖M A T‖,
```

(`Matrix.linfty_opNorm_def`), so one matrix norm bounds every row at once:

* `row_le_opNorm` — `∑_T ‖M A T‖ ≤ ‖M‖` for each row `A`;
* `norm_le_of_row_le` — conversely, a uniform row bound bounds the norm.

The radii are then

* `p1HiggsOpMass D a = ‖p1HiggsMat D a‖` — the operator norm of the `a`-th coefficient matrix;
* `p1HiggsOpRowRadius D = ∑_a p1HiggsOpMass D a`;
* `p1HiggsOpColRadius D = card (Finset (Fin 96)) * p1HiggsOpRowRadius D`;

with `rowSum_p1Higgs_le_opRadius` and `colSum_p1Higgs_le_opRadius` supplying the Schur data, and
`smPos_p1Higgs_commForm_le_opRadius`, `smCanonical_p1Higgs_commForm_le_opRadius` the commutator
bound.  §25's mixing-block test gets the same treatment in
`smCanonical_p1Higgs_commForm_le_opRadius_unconditional`.

## 2. That these are sharper

`p1HiggsOpMass_le_mass`, `p1HiggsOpRowRadius_le_rowRadius` and
`p1HiggsOpColRadius_le_colRadius` show the new constants are at most §24's, and hence §25's: the
operator norm is the sup of row sums while the `ℓ¹` mass sums every entry, and no `fockMass` factor
is left at all — the `L^∞` norm is defined on the entries, so the normalisation of `fockBasis` no
longer enters.  The constants are still not the exact Schur sums of the dictionary; that remains a
computation, as §24 said.

Everything here is `sorry`-free and `axiom`-free.
-/

open scoped Matrix.Norms.Operator

namespace BookProof.SmFullCommFormBlockHermitianP1OpNorm

open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.SmHamiltonian BookProof.SmOneParticle BookProof.SmFarisLavine
open BookProof.SmFullMatter BookProof.SmFullCoupledCore BookProof.SmFullYukawaCoeffs
open BookProof.SmFullFamilyBounds BookProof.SmMatter BookProof.SmFullNormalFormBounds
open BookProof.SmFullCommFormDiagonal BookProof.SmFullCommFormBlock
open BookProof.SmFullCommFormBlockHermitian BookProof.SmFullCommFormBlockHermitianP1
open BookProof.SmFullCommFormBlockHermitianP1Schur BookProof.SmFullCommFormBlockGeneral

noncomputable section

/-! ## 1. The `L^∞` operator norm against the row sums -/

/-- **Each row sum is bounded by the operator norm**: on a finite matrix the `L^∞` norm is the
supremum of the row sums of the entry norms, so every single row is below it. -/
theorem row_le_opNorm {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) (A : m) :
    (∑ B, ‖M A B‖) ≤ ‖M‖ := by
  have h := Finset.le_sup (s := Finset.univ)
    (f := fun i : m => ∑ j, ‖M i j‖₊) (Finset.mem_univ A)
  have h2 : (((∑ j : n, ‖M A j‖₊) : NNReal) : ℝ) = ∑ j : n, ‖M A j‖ := by
    push_cast
    rfl
  have h3 : ((‖M‖₊ : NNReal) : ℝ) = ‖M‖ := rfl
  rw [← h2, Matrix.linfty_opNorm_def]
  exact_mod_cast h

/-- **A single row is bounded by the operator norm**: the sup norm of the row is at most the sum of
its entries, which the operator norm bounds. -/
theorem row_norm_le_opNorm {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) (A : m) :
    ‖M A‖ ≤ ‖M‖ := by
  have h1 : ‖M A‖ ≤ ∑ B, ‖M A B‖ := by
    have hcast : (((∑ B : n, ‖M A B‖₊) : NNReal) : ℝ) = ∑ B : n, ‖M A B‖ := by
      push_cast
      rfl
    have hsup : (Finset.univ.sup fun b : n => ‖M A b‖₊) ≤ ∑ B, ‖M A B‖₊ :=
      Finset.sup_le fun b _ =>
        Finset.single_le_sum (f := fun B => ‖M A B‖₊) (fun _ _ => zero_le _)
          (Finset.mem_univ b)
    rw [Pi.norm_def, ← hcast]
    exact_mod_cast hsup
  exact h1.trans (row_le_opNorm M A)

/-- **Every entry is bounded by the operator norm.** -/
theorem entry_le_opNorm {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) (A : m)
    (B : n) : ‖M A B‖ ≤ ‖M‖ :=
  (norm_le_pi_norm (M A) B).trans (row_norm_le_opNorm M A)

/-- **A uniform row bound bounds the operator norm**, the converse direction used to compare
constants. -/
theorem norm_le_of_row_le {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) {b : ℝ}
    (hb : 0 ≤ b) (h : ∀ A : m, (∑ B, ‖M A B‖) ≤ b) : ‖M‖ ≤ b := by
  have hnn : ∀ i : m, (∑ j : n, ‖M i j‖₊) ≤ (⟨b, hb⟩ : NNReal) := by
    intro i
    rw [← NNReal.coe_le_coe, NNReal.coe_sum]
    push_cast
    exact h i
  have hsup : (Finset.univ.sup fun i : m => ∑ j : n, ‖M i j‖₊) ≤ (⟨b, hb⟩ : NNReal) :=
    Finset.sup_le fun i _ => hnn i
  have hb' : ‖M‖₊ ≤ (⟨b, hb⟩ : NNReal) := by
    rw [Matrix.linfty_opNNNorm_def]
    exact hsup
  exact_mod_cast hb'

/-! ## 2. The operator-norm radii -/

/-- **The operator norm of the `a`-th P1 Higgs coefficient matrix.** -/
def p1HiggsOpMass (D : SmInternalData) (a : Fin 4) : ℝ := ‖p1HiggsMat D a‖

/-- **The total operator-norm mass of the four P1 matrices**: the uniform row radius. -/
def p1HiggsOpRowRadius (D : SmInternalData) : ℝ := ∑ a : Fin 4, p1HiggsOpMass D a

/-- **The column radius**: the row radius times the number of internal components. -/
def p1HiggsOpColRadius (D : SmInternalData) : ℝ :=
  (Fintype.card (Finset (Fin 96)) : ℝ) * p1HiggsOpRowRadius D

theorem p1HiggsOpMass_nonneg (D : SmInternalData) (a : Fin 4) : 0 ≤ p1HiggsOpMass D a :=
  norm_nonneg _

theorem p1HiggsOpRowRadius_nonneg (D : SmInternalData) : 0 ≤ p1HiggsOpRowRadius D :=
  Finset.sum_nonneg fun _ _ => p1HiggsOpMass_nonneg D _

theorem p1HiggsOpColRadius_nonneg (D : SmInternalData) : 0 ≤ p1HiggsOpColRadius D :=
  mul_nonneg (by positivity) (p1HiggsOpRowRadius_nonneg D)

/-! ## 3. The two Schur sums from the operator norms -/

set_option maxRecDepth 10000 in
-- instantiating the row-sum lemma at `Finset (Fin 96)`-indexed matrices exceeds the default depth
/-- **The row sums of the four P1 matrices are bounded by the operator-norm row radius**: the
`blk`-th matrix's own operator norm bounds the row, and the component sum is the radius. -/
theorem rowSum_p1Higgs_le_opRadius (D : SmInternalData) (blk : Finset (Fin 96) → Fin 4)
    (A : Finset (Fin 96)) :
    rowSum (p1HiggsMat D) blk A ≤ p1HiggsOpRowRadius D := by
  have hrow : rowSum (p1HiggsMat D) blk A ≤ p1HiggsOpMass D (blk A) :=
    row_le_opNorm (p1HiggsMat D (blk A)) A
  refine hrow.trans (Finset.single_le_sum (f := fun a : Fin 4 => p1HiggsOpMass D a)
    (fun b _ => p1HiggsOpMass_nonneg D b) (Finset.mem_univ (blk A)))

/-- **The column sums of the four P1 matrices are bounded by the operator-norm column radius.** -/
theorem colSum_p1Higgs_le_opRadius (D : SmInternalData) (blk : Finset (Fin 96) → Fin 4)
    (B : Finset (Fin 96)) :
    colSum (p1HiggsMat D) blk B ≤ p1HiggsOpColRadius D := by
  have hterm : ∀ A : Finset (Fin 96), ‖p1HiggsMat D (blk A) A B‖ ≤ p1HiggsOpRowRadius D := by
    intro A
    exact (entry_le_opNorm (p1HiggsMat D (blk A)) A B).trans
      (Finset.single_le_sum (f := fun a : Fin 4 => p1HiggsOpMass D a)
        (fun b _ => p1HiggsOpMass_nonneg D b) (Finset.mem_univ (blk A)))
  have hcol : colSum (p1HiggsMat D) blk B = ∑ A, ‖p1HiggsMat D (blk A) A B‖ := rfl
  rw [hcol]
  calc ∑ A, ‖p1HiggsMat D (blk A) A B‖
      ≤ ∑ _A : Finset (Fin 96), p1HiggsOpRowRadius D := Finset.sum_le_sum fun A _ => hterm A
    _ = p1HiggsOpColRadius D := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rfl

/-! ## 4. The operator-norm radii are sharper than the `ℓ¹` radii -/

/-- **Each P1 matrix obeys its own entrywise bound**: the `ℓ¹` mass of the `a`-th internal matrix
controls its own coefficient matrix, without passing through the total. -/
theorem p1Higgs_entry_le_own (D : SmInternalData) (a : Fin 4) (S T : Finset (Fin 96)) :
    ‖p1HiggsMat D a S T‖ ≤ p1HiggsMass D a * ‖fockBasis T‖ :=
  fockMatrix_entry_norm_le (D.higgs a) S T

/-- **The operator norm is at most the `ℓ¹` mass times the basis mass.**  Every row sum is bounded
by the entrywise bound, and the operator norm is the supremum of the row sums. -/
theorem p1HiggsOpMass_le_mass (D : SmInternalData) (a : Fin 4) :
    p1HiggsOpMass D a ≤ p1HiggsMass D a * fockMass := by
  have hrow : ∀ A : Finset (Fin 96),
      (∑ T, ‖p1HiggsMat D a A T‖) ≤ p1HiggsMass D a * fockMass := by
    intro A
    have h : ∑ T, ‖p1HiggsMat D a A T‖ ≤ ∑ T : Finset (Fin 96), p1HiggsMass D a * ‖fockBasis T‖ :=
      Finset.sum_le_sum fun T _ => p1Higgs_entry_le_own D a A T
    refine h.trans ?_
    rw [← Finset.mul_sum]
    exact le_of_eq (by simp only [fockMass])
  have hb : (0 : ℝ) ≤ p1HiggsMass D a * fockMass :=
    mul_nonneg (p1HiggsMass_nonneg D a) fockMass_nonneg
  exact norm_le_of_row_le (p1HiggsMat D a) hb hrow

/-- **The operator-norm row radius is at most §24's `ℓ¹` row radius.** -/
theorem p1HiggsOpRowRadius_le_rowRadius (D : SmInternalData) :
    p1HiggsOpRowRadius D ≤ p1HiggsRowRadius D := by
  have h : p1HiggsOpRowRadius D ≤ ∑ a : Fin 4, p1HiggsMass D a * fockMass :=
    Finset.sum_le_sum fun a _ => p1HiggsOpMass_le_mass D a
  calc p1HiggsOpRowRadius D ≤ ∑ a : Fin 4, p1HiggsMass D a * fockMass := h
    _ = p1HiggsRowRadius D := by
        simp only [p1HiggsRowRadius, p1HiggsMassTotal, ← Finset.sum_mul]

/-- **The operator-norm column radius is at most §24's `ℓ¹` column radius.** -/
theorem p1HiggsOpColRadius_le_colRadius (D : SmInternalData) :
    p1HiggsOpColRadius D ≤ p1HiggsColRadius D :=
  mul_le_mul_of_nonneg_left (p1HiggsOpRowRadius_le_rowRadius D) (by positivity)

/-! ## 5. The commutator bounds with the operator-norm radii -/

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **§21's commutator bound with the operator-norm radii**: no Schur data left, and only the
block-support condition on the coefficient family. -/
theorem smPos_p1Higgs_commForm_le_opRadius (D : SmInternalData) (P : SmParams) {c0 : ℝ}
    (hc0 : 0 ≤ c0) (hpos : ∀ a : Fin 4, ∃ m : Fin 40, D.pos a = smCoord m)
    (blk : Finset (Fin 96) → Fin 4)
    (hsupp : ∀ (a : Fin 4) (A B : Finset (Fin 96)),
      p1HiggsMat D a A B ≠ 0 → blk A = a)
    (f : SmCoupledCore) :
    |commForm (blockOpMat (fun a => (polyGaussCore (d := 163)).subtype.comp
        (smPos (D.pos a))) (p1HiggsMat D)) (coupledOp (smFlN P c0) 1) f|
      ≤ 4 * Real.sqrt (p1HiggsOpRowRadius D * p1HiggsOpColRadius D)
        * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ ^ 2 :=
  by
  simpa only [one_mul] using
    smPos_p1Higgs_commForm_le D P hc0 hpos blk hsupp
      (p1HiggsOpRowRadius_nonneg D) (p1HiggsOpColRadius_nonneg D)
      (rowSum_p1Higgs_le_opRadius D blk) (colSum_p1Higgs_le_opRadius D blk) f

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **The same at the canonical placement**, with the operator-norm radii. -/
theorem smCanonical_p1Higgs_commForm_le_opRadius (D : SmInternalData) (P : SmParams) {c0 : ℝ}
    (hc0 : 0 ≤ c0) (blk : Finset (Fin 96) → Fin 4)
    (hsupp : ∀ (a : Fin 4) (A B : Finset (Fin 96)),
      p1HiggsMat D a A B ≠ 0 → blk A = a)
    (f : SmCoupledCore) :
    |commForm (blockOpMat (fun a => (polyGaussCore (d := 163)).subtype.comp
        (smPos (smCanonicalPos a))) (p1HiggsMat D)) (coupledOp (smFlN P c0) 1) f|
      ≤ 4 * Real.sqrt (p1HiggsOpRowRadius D * p1HiggsOpColRadius D)
        * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ ^ 2 :=  by
  simpa only [one_mul] using
    smCanonical_smPos_p1Higgs_commForm_le P hc0 (p1HiggsMat D) blk hsupp
      (p1HiggsOpRowRadius_nonneg D) (p1HiggsOpColRadius_nonneg D)
      (rowSum_p1Higgs_le_opRadius D blk) (colSum_p1Higgs_le_opRadius D blk) f


/-! ## 6. The mixing-block test with the operator-norm radii -/

/-- **The general row radius with operator norms**: mixing costs the cardinality of the component
index, as in §25. -/
def p1HiggsGeneralOpRowRadius (D : SmInternalData) : ℝ :=
  (Fintype.card (Fin 4) : ℝ) * p1HiggsOpRowRadius D

/-- **The general column radius with operator norms.** -/
def p1HiggsGeneralOpColRadius (D : SmInternalData) : ℝ :=
  (Fintype.card (Finset (Fin 96)) : ℝ) * p1HiggsGeneralOpRowRadius D

theorem p1HiggsGeneralOpRowRadius_nonneg (D : SmInternalData) :
    0 ≤ p1HiggsGeneralOpRowRadius D :=
  mul_nonneg (by positivity) (p1HiggsOpRowRadius_nonneg D)

theorem p1HiggsGeneralOpColRadius_nonneg (D : SmInternalData) :
    0 ≤ p1HiggsGeneralOpColRadius D :=
  mul_nonneg (by positivity) (p1HiggsGeneralOpRowRadius_nonneg D)

/-- **The general row sums from operator norms**: the sum over the components of the row sums of the
four matrices is at most the sum of their operator norms, with no support condition. -/
theorem rowSumGen_p1Higgs_le_opRowRadius (D : SmInternalData) (A : Finset (Fin 96)) :
    rowSumGen (p1HiggsMat D) A ≤ p1HiggsGeneralOpRowRadius D := by
  have hterm : rowSumGen (p1HiggsMat D) A ≤ p1HiggsOpRowRadius D := by
    have hcomm : rowSumGen (p1HiggsMat D) A = ∑ a : Fin 4, ∑ B, ‖p1HiggsMat D a A B‖ := by
      simp only [rowSumGen, weightSum]
      exact Finset.sum_comm
    rw [hcomm]
    calc ∑ a : Fin 4, ∑ B, ‖p1HiggsMat D a A B‖
        ≤ ∑ a : Fin 4, p1HiggsOpMass D a :=
          Finset.sum_le_sum fun a _ => row_le_opNorm (p1HiggsMat D a) A
      _ = p1HiggsOpRowRadius D := rfl
  refine hterm.trans ?_
  rw [p1HiggsGeneralOpRowRadius]
  refine le_mul_of_one_le_left (p1HiggsOpRowRadius_nonneg D) ?_
  exact_mod_cast Finset.one_le_card.mpr ⟨0, Finset.mem_univ 0⟩

set_option maxRecDepth 4000 in
-- instantiating the entry bound at `Finset (Fin 96)`-indexed matrices exceeds the default depth
/-- **The general column sums from operator norms**, with the column count. -/
theorem colSumGen_p1Higgs_le_opColRadius (D : SmInternalData) (B : Finset (Fin 96)) :
    colSumGen (p1HiggsMat D) B ≤ p1HiggsGeneralOpColRadius D := by
  have hinner : ∀ A : Finset (Fin 96),
      weightSum (p1HiggsMat D) A B ≤ p1HiggsOpRowRadius D := by
    intro A
    have hcomm : weightSum (p1HiggsMat D) A B = ∑ a : Fin 4, ‖p1HiggsMat D a A B‖ := rfl
    rw [hcomm]
    calc ∑ a : Fin 4, ‖p1HiggsMat D a A B‖
        ≤ ∑ a : Fin 4, p1HiggsOpMass D a := by
          exact Finset.sum_le_sum fun a _ => entry_le_opNorm (p1HiggsMat D a) A B
      _ = p1HiggsOpRowRadius D := rfl
  have hcol : colSumGen (p1HiggsMat D) B = ∑ A, weightSum (p1HiggsMat D) A B := rfl
  rw [hcol]
  calc ∑ A : Finset (Fin 96), weightSum (p1HiggsMat D) A B
      ≤ ∑ _A : Finset (Fin 96), p1HiggsOpRowRadius D := Finset.sum_le_sum fun A _ => hinner A
    _ ≤ p1HiggsGeneralOpColRadius D := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, p1HiggsGeneralOpColRadius,
          p1HiggsGeneralOpRowRadius]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_mul_of_one_le_left (p1HiggsOpRowRadius_nonneg D) ?_
        exact_mod_cast Finset.one_le_card.mpr ⟨0, Finset.mem_univ 0⟩

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **The commutator bound for the P1 dictionary with no hypothesis at all**, with the operator-norm
radii: §25's mixing-block Schur test and this section's constants. -/
theorem smCanonical_p1Higgs_commForm_le_opRadius_unconditional (P : SmParams) {c0 : ℝ}
    (hc0 : 0 ≤ c0) (f : SmCoupledCore) :
    |commForm (blockOpMat (fun a => (polyGaussCore (d := 163)).subtype.comp
        (smPos (smCanonicalPos a))) (p1HiggsMat smCanonicalInternalData))
        (coupledOp (smFlN P c0) 1) f|
      ≤ 4 * Real.sqrt (p1HiggsGeneralOpRowRadius smCanonicalInternalData
          * p1HiggsGeneralOpColRadius smCanonicalInternalData)
        * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ ^ 2 :=
  by
  simpa only [one_mul] using
    smPos_blockMat_commForm_le_general smCanonicalInternalData P hc0 smCanonicalPos_harmonic
      (p1HiggsMat smCanonicalInternalData)
      (p1HiggsGeneralOpRowRadius_nonneg smCanonicalInternalData)
      (p1HiggsGeneralOpColRadius_nonneg smCanonicalInternalData)
      (rowSumGen_p1Higgs_le_opRowRadius smCanonicalInternalData)
      (colSumGen_p1Higgs_le_opColRadius smCanonicalInternalData) f

end

end BookProof.SmFullCommFormBlockHermitianP1OpNorm
