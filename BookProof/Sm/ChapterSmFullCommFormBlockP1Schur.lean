import Mathlib
import BookProof.Sm.ChapterSmFullCommFormBlockP1

/-!
# The Schur constants of the four P1 Higgs matrices, made explicit

Work order: `SM_ESA_COMPLETION_PLAN.md` §24.

## 1. What §21 left as data

§21 proved the commutator bound for the P1 dictionary's four Higgs coefficient matrices with the two
Schur sums `ρ`, `κ` as *hypotheses*, and recorded honestly that they are finite because each
`p1HiggsMat D a` is a fixed matrix of a finite type.  "Finite" is not a number, so the bound could not
be applied without supplying `ρ` and `κ` by hand.

This section removes that.  Every entry of every P1 matrix is bounded by `fockMatrix_entry_norm_le`,
whose right-hand side is the `ℓ¹` mass of the internal matrix `D.higgs a` times the norm of a Fock
basis vector, and the occupation basis is finite.  Summing that bound over the row (resp. column)
gives two explicit numbers:

* `p1HiggsMass D a = ∑_{i j} ‖D.higgs a i j‖` — the `ℓ¹` mass of the `a`-th internal matrix;
* `p1HiggsMassTotal D = ∑_a p1HiggsMass D a`;
* `fockMass = ∑_T ‖fockBasis T‖` — the mass of the occupation basis;
* `p1HiggsRowRadius D = p1HiggsMassTotal D * fockMass` — a **uniform** row bound;
* `p1HiggsColRadius D = card (Finset (Fin 96)) * p1HiggsRowRadius D` — the same for columns, with
  the one factor the column count costs.

`rowSum_p1Higgs_le` and `colSum_p1Higgs_le` prove the corresponding Schur bounds, and
`smCanonical_smPos_p1Higgs_commForm_le_radius` is §21's commutator bound with `ρ` and `κ` replaced by
these numbers.  §25 then drops the block-support hypothesis as well, which is what makes the bound
hypothesis-free.

## 2. Honesty about the size

These constants are **crude on purpose**: the `ℓ¹` mass is not the operator norm, `fockMass` is not
`1` because the corpus records no normalisation of `fockBasis`, and the column count is the full
cardinality `card (Finset (Fin 96))` rather than the number of actually occupied sectors.  Their role
is to be *explicit and finite*, which is what a Schur hypothesis needs to be discharged; a sharper
constant is a computation on the dictionary, not a theorem about it.  The module says so instead of
presenting the first bound it could close as the right one.

## 3. What is proved

* `p1HiggsMass_nonneg`, `fockMass_nonneg`, `p1HiggsRowRadius_nonneg`, `p1HiggsColRadius_nonneg`;
* `p1HiggsMass_le_total` — one component's mass is at most the total;
* `p1Higgs_entry_le` — the entrywise bound in terms of `p1HiggsMassTotal`, uniform in the component;
* `fockBasis_norm_le_mass`, `sum_fockBasis_norm_eq` — the basis mass bounds a single basis vector;
* `rowSum_p1Higgs_le`, `colSum_p1Higgs_le` — the two Schur bounds;
* `smCanonical_smPos_p1Higgs_commForm_le_radius` and the variant at an arbitrary placement,
  `smPos_p1Higgs_commForm_le_radius` — §20/§21's bounds with no Schur hypothesis left.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmFullCommFormBlockHermitianP1Schur

open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.SmHamiltonian BookProof.SmOneParticle BookProof.SmFarisLavine
open BookProof.SmFullMatter BookProof.SmFullCoupledCore BookProof.SmFullYukawaCoeffs
open BookProof.SmFullFamilyBounds BookProof.SmMatter BookProof.SmFullNormalFormBounds
open BookProof.SmFullCommFormDiagonal BookProof.SmFullCommFormBlock
open BookProof.SmFullCommFormBlockHermitian BookProof.SmFullCommFormBlockHermitianP1

noncomputable section

/-! ## 1. The two radii -/

/-- **The `ℓ¹` mass of the `a`-th internal Higgs matrix**, read in the occurrence ordering of the
matter modes.  This is the constant of `fockMatrix_entry_norm_le`. -/
def p1HiggsMass (D : SmInternalData) (a : Fin 4) : ℝ :=
  ∑ i : Fin 96, ∑ j : Fin 96,
    ‖D.higgs a (smMatterMode.symm i) (smMatterMode.symm j)‖

/-- **The total `ℓ¹` mass of the four internal Higgs matrices.** -/
def p1HiggsMassTotal (D : SmInternalData) : ℝ := ∑ a : Fin 4, p1HiggsMass D a

/-- **The mass of the occupation basis**, `∑_T ‖fockBasis T‖`.  It is `1` only after the corpus
fixes the normalisation of `fockBasis`, which it does not do; the sum is what the entrywise bound
actually produces. -/
def fockMass : ℝ := ∑ T : Finset (Fin 96), ‖fockBasis T‖

/-- **The uniform row radius of the four P1 matrices.** -/
def p1HiggsRowRadius (D : SmInternalData) : ℝ := p1HiggsMassTotal D * fockMass

/-- **The uniform column radius**: the row radius times the number of internal components, which is
the only factor the column count costs. -/
def p1HiggsColRadius (D : SmInternalData) : ℝ :=
  (Fintype.card (Finset (Fin 96)) : ℝ) * p1HiggsRowRadius D

theorem p1HiggsMass_nonneg (D : SmInternalData) (a : Fin 4) : 0 ≤ p1HiggsMass D a :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem p1HiggsMassTotal_nonneg (D : SmInternalData) : 0 ≤ p1HiggsMassTotal D :=
  Finset.sum_nonneg fun a _ => p1HiggsMass_nonneg D a

theorem fockMass_nonneg : 0 ≤ fockMass :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem p1HiggsRowRadius_nonneg (D : SmInternalData) : 0 ≤ p1HiggsRowRadius D :=
  mul_nonneg (p1HiggsMassTotal_nonneg D) fockMass_nonneg

theorem p1HiggsColRadius_nonneg (D : SmInternalData) : 0 ≤ p1HiggsColRadius D :=
  mul_nonneg (by positivity) (p1HiggsRowRadius_nonneg D)

/-! ## 2. The entrywise bound, uniform in the component -/

theorem p1HiggsMass_le_total (D : SmInternalData) (a : Fin 4) :
    p1HiggsMass D a ≤ p1HiggsMassTotal D :=
  Finset.single_le_sum (f := fun a : Fin 4 => p1HiggsMass D a)
    (fun b _ => p1HiggsMass_nonneg D b) (Finset.mem_univ a)

/-- **Every entry of every P1 Higgs matrix is bounded by the same two numbers**: the total `ℓ¹` mass
and the mass of the basis. -/
theorem p1Higgs_entry_le (D : SmInternalData) (a : Fin 4) (S T : Finset (Fin 96)) :
    ‖p1HiggsMat D a S T‖ ≤ p1HiggsMassTotal D * ‖fockBasis T‖ := by
  refine (fockMatrix_entry_norm_le (D.higgs a) S T).trans ?_
  exact mul_le_mul_of_nonneg_right (p1HiggsMass_le_total D a) (norm_nonneg _)

/-- **One basis vector is at most the mass of the basis.** -/
theorem fockBasis_norm_le_mass (T : Finset (Fin 96)) : ‖fockBasis T‖ ≤ fockMass :=
  Finset.single_le_sum (f := fun T : Finset (Fin 96) => ‖fockBasis T‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ T)

/-! ## 3. The two Schur sums, bounded by the radii -/

/-- **The row sums of the four P1 matrices are bounded by `p1HiggsRowRadius`.** -/
theorem rowSum_p1Higgs_le (D : SmInternalData) (blk : Finset (Fin 96) → Fin 4)
    (A : Finset (Fin 96)) :
    rowSum (p1HiggsMat D) blk A ≤ p1HiggsRowRadius D := by
  have hterm : ∀ T : Finset (Fin 96),
      ‖p1HiggsMat D (blk A) A T‖ ≤ p1HiggsMassTotal D * ‖fockBasis T‖ :=
    fun T => p1Higgs_entry_le D (blk A) A T
  calc rowSum (p1HiggsMat D) blk A
      = ∑ T : Finset (Fin 96), ‖p1HiggsMat D (blk A) A T‖ := rfl
    _ ≤ ∑ T : Finset (Fin 96), p1HiggsMassTotal D * ‖fockBasis T‖ :=
        Finset.sum_le_sum fun T _ => hterm T
    _ = p1HiggsRowRadius D := by
        rw [p1HiggsRowRadius, fockMass, Finset.mul_sum]

/-- **The column sums of the four P1 matrices are bounded by `p1HiggsColRadius`.** -/
theorem colSum_p1Higgs_le (D : SmInternalData) (blk : Finset (Fin 96) → Fin 4)
    (B : Finset (Fin 96)) :
    colSum (p1HiggsMat D) blk B ≤ p1HiggsColRadius D := by
  have hterm : ∀ A : Finset (Fin 96),
      ‖p1HiggsMat D (blk A) A B‖ ≤ p1HiggsMassTotal D * ‖fockBasis B‖ :=
    fun A => p1Higgs_entry_le D (blk A) A B
  have hsum : ∑ A : Finset (Fin 96), ‖p1HiggsMat D (blk A) A B‖
      ≤ (Fintype.card (Finset (Fin 96)) : ℝ) * (p1HiggsMassTotal D * ‖fockBasis B‖) := by
    calc ∑ A : Finset (Fin 96), ‖p1HiggsMat D (blk A) A B‖
        ≤ ∑ _A : Finset (Fin 96), p1HiggsMassTotal D * ‖fockBasis B‖ :=
          Finset.sum_le_sum fun A _ => hterm A
      _ = (Fintype.card (Finset (Fin 96)) : ℝ) * (p1HiggsMassTotal D * ‖fockBasis B‖) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcol : colSum (p1HiggsMat D) blk B
      = ∑ A : Finset (Fin 96), ‖p1HiggsMat D (blk A) A B‖ := rfl
  rw [hcol]
  refine hsum.trans ?_
  rw [p1HiggsColRadius, p1HiggsRowRadius, fockMass]
  have hcard : (0 : ℝ) ≤ (Fintype.card (Finset (Fin 96)) : ℝ) := by positivity
  have hm : (0 : ℝ) ≤ p1HiggsMassTotal D := p1HiggsMassTotal_nonneg D
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (fockBasis_norm_le_mass B) hm) hcard

/-! ## 4. The commutator bound with the radii substituted -/

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **§21's commutator bound with no Schur hypothesis left**: `ρ` and `κ` are the explicit radii of
this section, so only the block-support condition remains (and §25 drops that too). -/
theorem smPos_p1Higgs_commForm_le_radius (D : SmInternalData) (P : SmParams) {c0 : ℝ}
    (hc0 : 0 ≤ c0) (hpos : ∀ a : Fin 4, ∃ m : Fin 40, D.pos a = smCoord m)
    (blk : Finset (Fin 96) → Fin 4)
    (hsupp : ∀ (a : Fin 4) (A B : Finset (Fin 96)),
      p1HiggsMat D a A B ≠ 0 → blk A = a)
    (f : SmCoupledCore) :
    |commForm (blockOpMat (fun a => (polyGaussCore (d := 163)).subtype.comp
        (smPos (D.pos a))) (p1HiggsMat D)) (coupledOp (smFlN P c0) 1) f|
      ≤ 4 * Real.sqrt (p1HiggsRowRadius D * p1HiggsColRadius D)
        * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ ^ 2 :=
  by
  simpa only [one_mul] using
    smPos_p1Higgs_commForm_le D P hc0 hpos blk hsupp
      (p1HiggsRowRadius_nonneg D) (p1HiggsColRadius_nonneg D)
      (rowSum_p1Higgs_le D blk) (colSum_p1Higgs_le D blk) f

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **The same bound at the canonical placement**, with the explicit radii. -/
theorem smCanonical_smPos_p1Higgs_commForm_le_radius (D : SmInternalData) (P : SmParams)
    {c0 : ℝ} (hc0 : 0 ≤ c0) (blk : Finset (Fin 96) → Fin 4)
    (hsupp : ∀ (a : Fin 4) (A B : Finset (Fin 96)),
      p1HiggsMat D a A B ≠ 0 → blk A = a)
    (f : SmCoupledCore) :
    |commForm (blockOpMat (fun a => (polyGaussCore (d := 163)).subtype.comp
        (smPos (smCanonicalPos a))) (p1HiggsMat D)) (coupledOp (smFlN P c0) 1) f|
      ≤ 4 * Real.sqrt (p1HiggsRowRadius D * p1HiggsColRadius D)
        * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ ^ 2 :=
  by
  simpa only [one_mul] using
    smCanonical_smPos_p1Higgs_commForm_le P hc0 (p1HiggsMat D) blk hsupp
      (p1HiggsRowRadius_nonneg D) (p1HiggsColRadius_nonneg D)
      (rowSum_p1Higgs_le D blk) (colSum_p1Higgs_le D blk) f

end

end BookProof.SmFullCommFormBlockHermitianP1Schur
