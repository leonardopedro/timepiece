import Mathlib
import BookProof.Sm.ChapterSmHarmonicReverseEstimate
import BookProof.Sm.ChapterSmP1BlockStructure
import BookProof.Sm.ChapterSmFullCommFormBlockGeneral

/-!
# The degenerate doublet's Schur sums, evaluated

Work order: `SM_ESA_COMPLETION_PLAN.md` §34.

## 1. What was left as "the general test applies"

§30 showed that the fully degenerate dictionary `degHiggsData` — four equal identity internal
matrices — admits **no** per-component block function, so §20's test cannot be applied and §25's
general Schur test is the one that is.  What it did not do is evaluate that test: the general test
still needs `rowSumGen ≤ ρ`, `colSumGen ≤ κ`, and §28's `8` was the constant for a hand-written
family, not for this dictionary.

This section evaluates them.  The degenerate dictionary is the number operator,

```text
p1HiggsMat degHiggsData a A B = (A.card : ℂ) * (if A = B then 1 else 0),
```

so it is diagonal and the four components coincide:

* `weightSum_degHiggs` — `weightSum M A B = 4 * A.card` on the diagonal and `0` off it;
* `rowSumGen_degHiggs`, `colSumGen_degHiggs` — both equal `4 * A.card` / `4 * B.card`;
* `rowSumGen_degHiggs_le`, `colSumGen_degHiggs_le` — both at most
  `4 * 96 = 384`, the four components times the `96` occupied modes;
* `degHiggs_commForm_le` — §25's commutator bound at `ρ = κ = 384`, i.e. constant
  `4 √(384 · 384) = 1536`, stated as `degHiggs_constant`.

So the price of the mixing in this dictionary is a concrete number, and it is the expected one: the
row sum of the number operator is the occupation number, bounded by the mode count, times the number
of degenerate components.

## 2. What the number is worth

`1536` is a *bound*, not the sharp Schur constant: it uses `A.card ≤ 96` for every sector, while the
number operator's rows are concentrated on one sector each.  Making it sharp is a computation on the
dictionary (the sector sizes), not a theorem about the method; §27's operator-norm radii are the
sharper route for the physical matrices, and the point of the number here is that the support-free
test of §25 is not merely applicable but *quantified* on a dictionary where §20 provably cannot be
used.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmDegenerateDoubletConstant

open BookProof.FarisLavine BookProof.HermiteProductCore
open BookProof.SmCar BookProof.SmMatter BookProof.SmFullMatter BookProof.SmFullYukawaCoeffs
open BookProof.SmHamiltonian BookProof.SmOneParticle BookProof.SmFarisLavine
open BookProof.SmFullCoupledCore BookProof.SmFullFamilyBounds BookProof.SmFullNormalFormBounds
open BookProof.SmFullCommFormDiagonal BookProof.SmFullCommFormBlock
open BookProof.SmFullCommFormBlockHermitian BookProof.SmFullCommFormBlockHermitianP1
open BookProof.SmFullCommFormBlockHermitianP1Schur BookProof.SmFullCommFormBlockGeneral
open BookProof.SmFullCommFormBlockHermitianP1BlockStructure

noncomputable section

/-! ## 1. The degenerate data at the canonical placement -/

/-- **The fully degenerate P1 dictionary at the canonical placement.**  The placement is the only
thing `degHiggsData` left unconstrained; it does not enter `p1HiggsMat`, and fixing it here lets
§25's general test be applied without a hypothesis on `pos`. -/
def degHiggsCanonical : SmInternalData :=
  SmInternalData.canonical (fun _ => 1) (fun _ => by
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm])
    1 (by
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm])

/-- The two degenerate dictionaries carry the same coefficient matrices: `p1HiggsMat` depends
only on the internal matrices, and both carry the identity in all four components. -/
theorem p1HiggsMat_degHiggsCanonical : p1HiggsMat degHiggsCanonical = p1HiggsMat degHiggsData :=
  rfl

/-- The entries of the canonical degenerate dictionary. -/
theorem p1HiggsMat_degHiggsCanonical_apply (a : Fin 4) (A B : Finset (Fin 96)) :
    p1HiggsMat degHiggsCanonical a A B = (A.card : ℂ) * (if A = B then 1 else 0) := by
  rw [show p1HiggsMat degHiggsCanonical a = p1HiggsMat degHiggsData a from
    congrFun p1HiggsMat_degHiggsCanonical a]
  exact p1HiggsMat_degHiggs_apply a A B

/-! ## 2. The Schur weight and the two general sums -/

/-- **The Schur weight of the degenerate dictionary**: four equal entries of modulus `A.card` on the
diagonal, zero off it. -/
theorem weightSum_degHiggs (A B : Finset (Fin 96)) :
    weightSum (p1HiggsMat degHiggsData) A B
      = if A = B then 4 * (A.card : ℝ) else 0 := by
  rw [weightSum]
  by_cases hAB : A = B
  · subst hAB
    have hterm : ∀ a : Fin 4, ‖p1HiggsMat degHiggsData a A A‖ = (A.card : ℝ) := by
      intro a
      rw [p1HiggsMat_degHiggs_apply]
      simp
    rw [Finset.sum_congr rfl fun a _ => hterm a, if_pos rfl, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  · have hterm : ∀ a : Fin 4, ‖p1HiggsMat degHiggsData a A B‖ = 0 := by
      intro a
      rw [p1HiggsMat_degHiggs_apply, if_neg hAB]
      simp
    rw [Finset.sum_congr rfl fun a _ => hterm a, if_neg hAB, Finset.sum_const_zero]

/-- **The general row sum of the degenerate dictionary** is `4 * A.card`. -/
theorem rowSumGen_degHiggs (A : Finset (Fin 96)) :
    rowSumGen (p1HiggsMat degHiggsData) A = 4 * (A.card : ℝ) := by
  rw [rowSumGen, Finset.sum_congr rfl fun B _ => weightSum_degHiggs A B]
  rw [Finset.sum_eq_single A]
  · simp
  · intro b _ hb
    exact if_neg (fun h : A = b => hb h.symm)
  · intro h
    exact absurd (Finset.mem_univ A) h

/-- **The general column sum of the degenerate dictionary** is `4 * B.card`. -/
theorem colSumGen_degHiggs (B : Finset (Fin 96)) :
    colSumGen (p1HiggsMat degHiggsData) B = 4 * (B.card : ℝ) := by
  rw [colSumGen]
  have hswap : ∑ A : Finset (Fin 96), weightSum (p1HiggsMat degHiggsData) A B
      = ∑ A : Finset (Fin 96), (if B = A then 4 * (B.card : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [weightSum_degHiggs]
    by_cases h : A = B
    · subst h
      simp
    · rw [if_neg h, if_neg (fun h' : B = A => h h'.symm)]
  rw [hswap, Finset.sum_eq_single B]
  · simp
  · intro b _ hb
    exact if_neg (fun h : B = b => hb h.symm)
  · intro h
    exact absurd (Finset.mem_univ B) h

/-! ## 3. The two bounds, and the constant -/

/-- An occupied set has at most `96` modes. -/
theorem card_le_96 (A : Finset (Fin 96)) : A.card ≤ 96 := by
  simpa using Finset.card_le_univ A

/-- **The row sums are at most `384 = 4 * 96`.** -/
theorem rowSumGen_degHiggs_le (A : Finset (Fin 96)) :
    rowSumGen (p1HiggsMat degHiggsData) A ≤ 384 := by
  rw [rowSumGen_degHiggs]
  have h : (A.card : ℝ) ≤ 96 := by exact_mod_cast card_le_96 A
  linarith

/-- **The column sums are at most `384`.** -/
theorem colSumGen_degHiggs_le (B : Finset (Fin 96)) :
    colSumGen (p1HiggsMat degHiggsData) B ≤ 384 := by
  rw [colSumGen_degHiggs]
  have h : (B.card : ℝ) ≤ 96 := by exact_mod_cast card_le_96 B
  linarith

/-- **The constant of the degenerate doublet**: `4 √(384 · 384) = 1536`. -/
theorem degHiggs_constant : 4 * (1 * Real.sqrt (384 * 384)) = 1536 := by
  rw [show (384 : ℝ) * 384 = 384 ^ 2 by ring, Real.sqrt_sq (by norm_num)]
  norm_num

/-- **§25's commutator bound for the degenerate doublet**, with `ρ = κ = 384`: the mixing costs the
constant `1536`, and no block-support hypothesis appears because §30 showed there is none to be had.
-/
theorem degHiggs_commForm_le (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0) (f : SmCoupledCore) :
    |commForm (blockOpMat (fun a => (polyGaussCore (d := 163)).subtype.comp
        (smPos (smCanonicalPos a))) (p1HiggsMat degHiggsCanonical))
        (coupledOp (smFlN P c0) 1) f|
      ≤ 4 * (1 * Real.sqrt (384 * 384))
        * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ ^ 2 := by
  exact smPos_blockMat_commForm_le_general degHiggsCanonical P hc0 smCanonicalPos_harmonic
    (p1HiggsMat degHiggsData) (by norm_num) (by norm_num)
    rowSumGen_degHiggs_le colSumGen_degHiggs_le f

end

end BookProof.SmDegenerateDoubletConstant
