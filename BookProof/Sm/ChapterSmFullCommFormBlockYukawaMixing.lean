import Mathlib
import BookProof.Sm.ChapterSmFullCommFormBlockP1OpNorm

/-!
# A Yukawa family that mixes blocks, and what the general Schur test charges for it

Work order: `SM_ESA_COMPLETION_PLAN.md` §28.

## 1. Why a model family

§25 removed §20's block-support condition `M a A B ≠ 0 → blk A = a`, but its example was the P1
dictionary itself, and there the mixing is a property of the second-quantized Higgs generators that
the corpus does not compute entrywise.  This section supplies a Yukawa coefficient family whose
mixing is **provable**, so that §25's test is applied to a family that §20 provably cannot accept,
and the price of mixing is visible as an explicit constant.

The family is the degenerate number-conserving Yukawa

```text
mixYuk 0 = 1,   mixYuk 1 = 1,   mixYuk 2 = 0,   mixYuk 3 = 0
```

on the occupation basis: two of the four internal components couple every occupation to itself with
unit strength — a Yukawa that conserves the internal mode, with two degenerate components, which is
exactly the situation in which a Higgs doublet's two members share a coupling pattern.

* `mixYuk_unsupported` — **no** `blk : Finset (Fin 96) → Fin 4` satisfies §20's condition, because
  row `∅` has a nonzero entry for component `0` **and** for component `1`, forcing `blk ∅ = 0` and
  `blk ∅ = 1`.  So §20's theorem cannot be instantiated, and §25's is needed.
* `rowSumGen_mixYuk_le`, `colSumGen_mixYuk_le` — both general Schur sums are `2`, so §25's constant
  is `4 √(2 · 2) = 8`.
* `mixYuk_commForm_le` — the resulting commutator bound for this family.

## 2. The same mixing on the real dictionary

`p1HiggsMix D a = p1HiggsMat D a + mixYuk a` is the P1 Higgs matrix with the degenerate pair added
to each component.  It mixes blocks for the same reason, and §27's operator-norm radius charges the
mixing exactly one additive `2`:

* `rowSumGen_p1HiggsMix_le` — `rowSumGen ≤ p1HiggsOpRowRadius D + 2`;
* `colSumGen_p1HiggsMix_le` — `colSumGen ≤ card (Finset (Fin 96)) * (p1HiggsOpRowRadius D + 2)`;
* `p1HiggsMix_commForm_le` — the commutator bound for the mixed dictionary.

The two models are a *demonstration* of the method, not a claim about the SM's Yukawa matrices: the
actual couplings are `p1HiggsMat D a` (§21), whose block structure is not computed here.  What is
proved is that when mixing is present, §25's test still gives a finite constant, and that the price
is one additive term per degenerate component — not a loss of the bound.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmFullCommFormBlockYukawaMixing

open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.SmHamiltonian BookProof.SmOneParticle BookProof.SmFarisLavine
open BookProof.SmFullMatter BookProof.SmFullCoupledCore BookProof.SmFullYukawaCoeffs
open BookProof.SmFullFamilyBounds BookProof.SmMatter BookProof.SmFullNormalFormBounds
open BookProof.SmFullCommFormDiagonal BookProof.SmFullCommFormBlock
open BookProof.SmFullCommFormBlockHermitian BookProof.SmFullCommFormBlockHermitianP1
open BookProof.SmFullCommFormBlockHermitianP1Schur BookProof.SmFullCommFormBlockGeneral
open BookProof.SmFullCommFormBlockHermitianP1OpNorm

noncomputable section

/-! ## 1. The family -/

/-- **The occupation-diagonal unit**: the coefficient matrix of the identity Yukawa coupling. -/
def occDiag : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ :=
  fun A B => if A = B then 1 else 0

/-- **The degenerate number-conserving Yukawa family**: components `0` and `1` both couple the
occupation diagonal with unit strength, components `2` and `3` vanish.  This is the family §20's
support condition cannot describe, see `mixYuk_unsupported`. -/
def mixYuk (a : Fin 4) : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ :=
  if a = 0 then occDiag else if a = 1 then occDiag else 0

/-- **The P1 Higgs dictionary with the degenerate pair added to each component**: a Yukawa family
that contains the dictionary's own matrices and mixes blocks as well. -/
def p1HiggsMix (D : SmInternalData) : Fin 4 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ :=
  fun a => p1HiggsMat D a + mixYuk a

/-! ## 2. The family is not block-supported -/

/-- **§20's support condition fails for `mixYuk`**: the empty occupation is reached by both
components `0` and `1`, so no `blk` can assign it a single block.  §25's general test is therefore
not merely convenient here — it is the only one that applies. -/
theorem mixYuk_unsupported :
    ¬ ∃ blk : Finset (Fin 96) → Fin 4,
        ∀ (a : Fin 4) (A B : Finset (Fin 96)), mixYuk a A B ≠ 0 → blk A = a := by
  rintro ⟨blk, hblk⟩
  have h0 : blk ∅ = 0 := hblk 0 ∅ ∅ (by simp [mixYuk, occDiag])
  have h1 : blk ∅ = 1 := hblk 1 ∅ ∅ (by simp [mixYuk, occDiag])
  rw [h0] at h1
  exact absurd h1 (by decide)

/-! ## 3. The two general Schur sums of `mixYuk` -/

/-- **The Schur weight of the degenerate family**: the two live components contribute the same unit
diagonal entry. -/
theorem weightSum_mixYuk (A B : Finset (Fin 96)) :
    weightSum mixYuk A B = ‖occDiag A B‖ + ‖occDiag A B‖ := by
  rw [weightSum, Fin.sum_univ_four]
  simp [mixYuk, Fin.isValue]

/-- **The row sum of the degenerate family is `2`**: only the diagonal occupation contributes, and
both live components contribute `1`. -/
theorem rowSumGen_mixYuk (A : Finset (Fin 96)) : rowSumGen mixYuk A = 2 := by
  have h : rowSumGen mixYuk A = 2 * ∑ B, ‖occDiag A B‖ := by
    rw [rowSumGen]
    rw [Finset.sum_congr rfl fun B _ => weightSum_mixYuk A B, Finset.mul_sum]
    exact Finset.sum_congr rfl fun B _ => by ring
  have hdiag : ∑ B, ‖occDiag A B‖ = 1 := by
    rw [Finset.sum_eq_single A]
    · simp [occDiag]
    · intro B _ hBA
      rw [occDiag]
      simp [Ne.symm hBA]
    · intro h
      exact absurd (Finset.mem_univ A) h
  rw [h, hdiag]
  norm_num

/-- **The column sum of the degenerate family is `2`** as well, since the diagonal is symmetric. -/
theorem colSumGen_mixYuk (B : Finset (Fin 96)) : colSumGen mixYuk B = 2 := by
  have h : colSumGen mixYuk B = 2 * ∑ A, ‖occDiag A B‖ := by
    rw [colSumGen]
    rw [Finset.sum_congr rfl fun A _ => weightSum_mixYuk A B, Finset.mul_sum]
    exact Finset.sum_congr rfl fun A _ => by ring
  have hdiag : ∑ A, ‖occDiag A B‖ = 1 := by
    rw [Finset.sum_eq_single B]
    · simp [occDiag]
    · intro A _ hAB
      rw [occDiag]
      simp [hAB]
    · intro h
      exact absurd (Finset.mem_univ B) h
  rw [h, hdiag]
  norm_num

theorem rowSumGen_mixYuk_le (A : Finset (Fin 96)) : rowSumGen mixYuk A ≤ 2 :=
  le_of_eq (rowSumGen_mixYuk A)

theorem colSumGen_mixYuk_le (B : Finset (Fin 96)) : colSumGen mixYuk B ≤ 2 :=
  le_of_eq (colSumGen_mixYuk B)

/-! ## 4. The commutator bound for the mixing family -/

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **§25's Schur test on the mixing family**: no block-support condition, and the constant is the
explicit `4 √(2 · 2) = 8` of `rowSumGen_mixYuk`/`colSumGen_mixYuk`. -/
theorem mixYuk_commForm_le (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0) (f : SmCoupledCore) :
    |commForm (blockOpMat (fun a => (polyGaussCore (d := 163)).subtype.comp
        (smPos (smCanonicalPos a))) mixYuk) (coupledOp (smFlN P c0) 1) f|
      ≤ 4 * Real.sqrt (2 * 2)
        * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ ^ 2 := by
  simpa only [one_mul] using
    smPos_blockMat_commForm_le_general smCanonicalInternalData P hc0 smCanonicalPos_harmonic
      mixYuk (by norm_num) (by norm_num) rowSumGen_mixYuk_le colSumGen_mixYuk_le f

/-! ## 5. The same mixing on the P1 dictionary -/

/-- **The Schur weight of the mixed dictionary is at most the sum of the two weights.** -/
theorem weightSum_p1HiggsMix_le (D : SmInternalData) (A B : Finset (Fin 96)) :
    weightSum (p1HiggsMix D) A B ≤ weightSum (p1HiggsMat D) A B + weightSum mixYuk A B := by
  rw [weightSum, weightSum, weightSum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ => norm_add_le _ _

/-- **The row sums of the mixed dictionary**: §25's general radius of the dictionary plus the `2`
that the two degenerate components cost. -/
theorem rowSumGen_p1HiggsMix_le (D : SmInternalData) (A : Finset (Fin 96)) :
    rowSumGen (p1HiggsMix D) A ≤ p1HiggsGeneralOpRowRadius D + 2 := by
  calc rowSumGen (p1HiggsMix D) A
      ≤ ∑ B, (weightSum (p1HiggsMat D) A B + weightSum mixYuk A B) :=
        Finset.sum_le_sum fun B _ => weightSum_p1HiggsMix_le D A B
    _ = rowSumGen (p1HiggsMat D) A + rowSumGen mixYuk A := by
        rw [rowSumGen, rowSumGen, Finset.sum_add_distrib]
    _ ≤ p1HiggsGeneralOpRowRadius D + 2 := by
        have h1 := rowSumGen_p1Higgs_le_opRowRadius D A
        have h2 := rowSumGen_mixYuk_le A
        linarith

/-- **The column sums of the mixed dictionary**, with the column count of §27. -/
theorem colSumGen_p1HiggsMix_le (D : SmInternalData) (B : Finset (Fin 96)) :
    colSumGen (p1HiggsMix D) B
      ≤ (Fintype.card (Finset (Fin 96)) : ℝ) * (p1HiggsGeneralOpRowRadius D + 2) := by
  have h : colSumGen (p1HiggsMix D) B
      ≤ colSumGen (p1HiggsMat D) B + colSumGen mixYuk B := by
    calc colSumGen (p1HiggsMix D) B
        ≤ ∑ A, (weightSum (p1HiggsMat D) A B + weightSum mixYuk A B) :=
          Finset.sum_le_sum fun A _ => weightSum_p1HiggsMix_le D A B
      _ = colSumGen (p1HiggsMat D) B + colSumGen mixYuk B := by
          rw [colSumGen, colSumGen, Finset.sum_add_distrib]
  have h1 := colSumGen_p1Higgs_le_opColRadius D B
  simp only [p1HiggsGeneralOpColRadius] at h1
  have h2 := colSumGen_mixYuk_le B
  have hcard : (1 : ℝ) ≤ (Fintype.card (Finset (Fin 96)) : ℝ) := by
    exact_mod_cast Finset.one_le_card.mpr ⟨∅, Finset.mem_univ ∅⟩
  have hR := p1HiggsGeneralOpRowRadius_nonneg D
  nlinarith [h, h1, h2, hcard, hR]

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **The commutator bound for the mixed P1 dictionary**: the dictionary's own operator-norm radius
plus the mixing term `2`, through §25's test.  This is the bound §20 cannot produce, because
`p1HiggsMix` inherits the mixing of `mixYuk`. -/
theorem p1HiggsMix_commForm_le (D : SmInternalData) (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (f : SmCoupledCore) :
    |commForm (blockOpMat (fun a => (polyGaussCore (d := 163)).subtype.comp
        (smPos (smCanonicalPos a))) (p1HiggsMix D)) (coupledOp (smFlN P c0) 1) f|
      ≤ 4 * Real.sqrt ((p1HiggsGeneralOpRowRadius D + 2)
          * ((Fintype.card (Finset (Fin 96)) : ℝ) * (p1HiggsGeneralOpRowRadius D + 2)))
        * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ ^ 2 := by
  have hρ : (0 : ℝ) ≤ p1HiggsGeneralOpRowRadius D + 2 := by
    have := p1HiggsGeneralOpRowRadius_nonneg D
    linarith
  have hκ : (0 : ℝ) ≤ (Fintype.card (Finset (Fin 96)) : ℝ)
      * (p1HiggsGeneralOpRowRadius D + 2) :=
    mul_nonneg (by positivity) hρ
  simpa only [one_mul] using
    smPos_blockMat_commForm_le_general smCanonicalInternalData P hc0 smCanonicalPos_harmonic
      (p1HiggsMix D) hρ hκ (rowSumGen_p1HiggsMix_le D) (colSumGen_p1HiggsMix_le D) f

end

end BookProof.SmFullCommFormBlockYukawaMixing
