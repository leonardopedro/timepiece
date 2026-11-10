import Mathlib
import BookProof.Sm.ChapterSmQuarticUncertainty

/-!
# The degenerate doublet's Schur radius is sharp

Work order: `SM_ESA_COMPLETION_PLAN.md` §36.

## 1. The sector-size distribution

§34 evaluated the general Schur sums of the degenerate doublet: `rowSumGen A = colSumGen A =
4 * A.card`.  The Schur radius is therefore a function of the sector sizes alone, and the
distribution of those sizes is the binomial one: value `4 k` with multiplicity `Nat.choose 96 k`.
Nothing about the matrix enters beyond `card`, which is why the radius can be read off the
distribution.

## 2. The bound of §34 is attained

§34 bounded both sums by `4 * 96 = 384`.  This section shows that the bound cannot be improved:

* `rowSumGen_degHiggs_univ` — the full sector `univ` has row sum exactly `384`;
* `colSumGen_degHiggs_univ` — and column sum `384`;
* `degHiggs_rowRadius_sharp` / `degHiggs_colRadius_sharp` — every uniform Schur radius `ρ` must
  satisfy `384 ≤ ρ`.

So `384` is the **exact** uniform Schur radius of this dictionary, and the commForm constant `1536`
of §34 is what the Schur test gives at that radius.  A smaller commutator constant for this family
would have to come from something other than a uniform row/column bound — a cancellation argument,
not a sharper Schur radius.  Recording this matters because "sharpen the constant" and "sharpen the
method" are different tasks, and only the second is available here.

## 3. What a general `blk`-free family would need

The observation generalises: for any diagonal family, `rowSumGen A = ∑_a |M_a A A|`, so the radius
is `max_A ∑_a |M_a A A|`, attained or not depending on the diagonal.  The degenerate doublet is the
case where the diagonal is `4 · card`, hence maximal at the full sector.  §27's operator-norm radii
are the sharper tool for the physical (non-diagonal) matrices, where the row bound is not the whole
story.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmDegenerateDoubletSharp

open BookProof.FarisLavine BookProof.HermiteProductCore
open BookProof.SmCar BookProof.SmMatter BookProof.SmFullMatter BookProof.SmFullYukawaCoeffs
open BookProof.SmFullCommFormBlockHermitianP1 BookProof.SmFullCommFormBlockHermitianP1Schur
open BookProof.SmFullCommFormBlockGeneral BookProof.SmFullCommFormBlockHermitianP1BlockStructure
open BookProof.SmDegenerateDoubletConstant

noncomputable section

/-! ## 1. The radius is attained at the full sector -/

/-- **The full occupation sector saturates the row bound**: `4 * card univ = 4 * 96 = 384`. -/
theorem rowSumGen_degHiggs_univ :
    rowSumGen (p1HiggsMat degHiggsData) Finset.univ = 384 := by
  rw [rowSumGen_degHiggs]
  have hcard : (Finset.univ : Finset (Fin 96)).card = 96 := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [hcard]
  norm_num

/-- **The full sector saturates the column bound.** -/
theorem colSumGen_degHiggs_univ :
    colSumGen (p1HiggsMat degHiggsData) Finset.univ = 384 := by
  rw [colSumGen_degHiggs]
  have hcard : (Finset.univ : Finset (Fin 96)).card = 96 := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [hcard]
  norm_num

/-! ## 2. No uniform radius is smaller -/

/-- **The row radius is sharp**: every uniform bound on the general row sums is at least `384`. -/
theorem degHiggs_rowRadius_sharp (ρ : ℝ)
    (h : ∀ A : Finset (Fin 96), rowSumGen (p1HiggsMat degHiggsData) A ≤ ρ) : 384 ≤ ρ := by
  have := h Finset.univ
  rwa [rowSumGen_degHiggs_univ] at this

/-- **The column radius is sharp**: every uniform bound on the general column sums is at least
`384`. -/
theorem degHiggs_colRadius_sharp (ρ : ℝ)
    (h : ∀ B : Finset (Fin 96), colSumGen (p1HiggsMat degHiggsData) B ≤ ρ) : 384 ≤ ρ := by
  have := h Finset.univ
  rwa [colSumGen_degHiggs_univ] at this

/-- **The row radius is a value of the sector-size distribution, not just a bound**: the rows are
`4 * A.card`, so the maximum is `4 * 96`, attained at the full sector.  Together with
`degHiggs_rowRadius_sharp` this identifies `384` as the exact uniform Schur radius. -/
theorem degHiggs_rowRadius_eq_card_max :
    rowSumGen (p1HiggsMat degHiggsData) Finset.univ = 4 * 96 := by
  rw [rowSumGen_degHiggs_univ]
  norm_num

end

end BookProof.SmDegenerateDoubletSharp
