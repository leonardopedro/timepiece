import Mathlib
import BookProof.Sm.ChapterSmFullCommFormBlockHermitian

/-!
# The commutator form: the P1 Yukawa dictionary's four Higgs coefficient matrices

Work order: `SM_ESA_COMPLETION_PLAN.md` §21.

## 1. Which matrices

The P1 dictionary `SmInternalData` carries four second-quantized Higgs generators
`D.higgs a : Matrix SmMatterIndex SmMatterIndex ℂ`; read in the occupation basis their coefficient
matrices are `p1HiggsMat D a = fockMatrix (matterBilin (D.higgs a))`, exactly the matrices that the
normal form's coordinate family `D.toNormalForm.coord` is built from
(`SmInternalData.toNormalForm_coord_eq`), one per Higgs component
(`toNormalForm_coord_eq_p1HiggsMat`, for an injective placement).

## 2. What is proved here

* `p1HiggsMat_hermitian` — the four matrices are Hermitian, from `D.higgsHermitian` through
  `matterBilin_symmetric` and `fockMatrix_star`.  This is the hypothesis §20 was written for: the
  interiors are genuinely non-diagonal, since `matterBilin` sums over the `96²` mode pairs.
* `smPos_p1Higgs_commForm_le` / `smCanonical_smPos_p1Higgs_commForm_le` — the §20 commutator bound
  with the block operator `Σ_a u_{pos a} ⊗ p1HiggsMat D a`, i.e. the four Higgs components each
  acting with their own P1 coefficient matrix.  At the canonical placement no hypothesis on the
  placement remains.

## 3. The constant, and why it is data

The Schur data `ρ`, `κ` are the row and column sums of the four coefficient matrices; they are
finite (each `p1HiggsMat D a` is a fixed finite matrix) but their values are *data* of the
dictionary, not a uniform constant — the four matrices are not diagonal, so no analogue of §15's
constant `1` exists.  The module therefore keeps them as hypotheses of the concrete bound instead of
inventing a number.  `fockMatrix_entry_norm_le` records the only general bound available, the `ℓ¹`
bound of `matterBilin`, to make the finiteness explicit.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmFullCommFormBlockHermitianP1

open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.SmHamiltonian BookProof.SmOneParticle BookProof.SmFarisLavine
open BookProof.SmFullMatter BookProof.SmFullCoupledCore BookProof.SmFullYukawaCoeffs
open BookProof.SmFullFamilyBounds BookProof.SmMatter BookProof.SmFullNormalFormBounds
open BookProof.SmFullCommFormDiagonal BookProof.SmFullCommFormBlock
open BookProof.SmFullCommFormBlockHermitian

noncomputable section

/-! ## 1. The four coefficient matrices of the P1 dictionary -/

/-- **The `a`-th Higgs coefficient matrix of the P1 Yukawa dictionary**: the second-quantized Higgs
generator in the occupation basis.  These are the interiors §18 had to leave as scalars. -/
def p1HiggsMat (D : SmInternalData) (a : Fin 4) :
    Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ :=
  fockMatrix (matterBilin (D.higgs a))

/-- **The normal form's coordinate family is built from exactly these four matrices.** -/
theorem SmInternalData.toNormalForm_coord_eq (D : SmInternalData) (j : Fin 163) :
    D.toNormalForm.coord j = ∑ a : Fin 4, if D.pos a = j then p1HiggsMat D a else 0 := rfl

/-- **One matrix per occupied coordinate**: for an injective placement, the coefficient matrix of
the coordinate `D.pos a` is the `a`-th Higgs matrix, undiluted by the other three. -/
theorem toNormalForm_coord_eq_p1HiggsMat (D : SmInternalData)
    (hinj : ∀ a b : Fin 4, D.pos a = D.pos b → a = b) (a : Fin 4) :
    D.toNormalForm.coord (D.pos a) = p1HiggsMat D a := by
  rw [SmInternalData.toNormalForm_coord_eq]
  rw [Finset.sum_eq_single a]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg (fun h => hb (hinj b a h))]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- **The P1 Higgs coefficient matrices are Hermitian** — the property §20's bound was written for.
It holds entrywise, from the Hermiticity of the one-particle generators. -/
theorem p1HiggsMat_hermitian (D : SmInternalData) (a : Fin 4)
    (S T : Finset (Fin 96)) :
    star (p1HiggsMat D a S T) = p1HiggsMat D a T S :=
  fockMatrix_star _ (matterBilin_symmetric (D.higgsHermitian a)) S T

/-- **The only uniform entry bound available for the P1 matrices**: the `ℓ¹` bound of the second
quantization of an internal matrix, applied to the occupation basis.  This is what makes the Schur
sums finite; it is not sharp, and the sharp values are data of the dictionary. -/
theorem fockMatrix_entry_norm_le (M : Matrix SmMatterIndex SmMatterIndex ℂ)
    (S T : Finset (Fin 96)) :
    ‖fockMatrix (matterBilin M) S T‖
      ≤ (∑ i : Fin 96, ∑ j : Fin 96,
          ‖M (smMatterMode.symm i) (smMatterMode.symm j)‖) * ‖fockBasis T‖ := by
  have h1 : ‖matterBilin M (fockBasis T)‖
      ≤ (∑ i : Fin 96, ∑ j : Fin 96,
          ‖M (smMatterMode.symm i) (smMatterMode.symm j)‖) * ‖fockBasis T‖ :=
    matterBilin_norm_le M (fockBasis T)
  refine le_trans ?_ h1
  have h2 : ‖fockMatrix (matterBilin M) S T‖
      ≤ ‖matterBilin M (fockBasis T)‖ := by
    rw [fockMatrix]
    exact PiLp.norm_apply_le (matterBilin M (fockBasis T)) S
  exact h2

/-! ## 2. The block operator of the four P1 matrices -/

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **The commutator bound for the four P1 Higgs coefficient matrices.**  This is §20's bound with
`sM a := p1HiggsMat D a`: the four Higgs components act with their own second-quantized generators,
one per block, and `D.higgsHermitian` is what makes the interiors admissible. -/
theorem smPos_p1Higgs_commForm_le (D : SmInternalData) (P : SmParams) {c0 : ℝ}
    (hc0 : 0 ≤ c0) (hpos : ∀ a : Fin 4, ∃ m : Fin 40, D.pos a = smCoord m)
    (blk : Finset (Fin 96) → Fin 4)
    (hsupp : ∀ (a : Fin 4) (A B : Finset (Fin 96)),
      p1HiggsMat D a A B ≠ 0 → blk A = a)
    {ρ κ : ℝ} (hρ0 : 0 ≤ ρ) (hκ0 : 0 ≤ κ)
    (hrow : ∀ A, rowSum (p1HiggsMat D) blk A ≤ ρ)
    (hcol : ∀ B, colSum (p1HiggsMat D) blk B ≤ κ)
    (f : SmCoupledCore) :
    |commForm (blockOpMat (fun a => (polyGaussCore (d := 163)).subtype.comp
        (smPos (D.pos a))) (p1HiggsMat D)) (coupledOp (smFlN P c0) 1) f|
      ≤ 4 * (1 * Real.sqrt (ρ * κ))
        * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ ^ 2 :=
  smPos_blockMat_commForm_le D P hc0 hpos (p1HiggsMat D) blk hsupp hρ0 hκ0 hrow hcol f

/-- **The same bound at the canonical placement**, so for the canonical P1 dictionary no hypothesis
on the placement is left. -/
theorem smCanonical_smPos_p1Higgs_commForm_le (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
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
  smCanonical_smPos_blockMat_commForm_le P hc0 M blk hsupp hρ0 hκ0 hrow hcol f

end

end BookProof.SmFullCommFormBlockHermitianP1
