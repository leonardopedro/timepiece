import Mathlib
import BookProof.Sm.ChapterSmFullCommFormBlockP1Schur

/-!
# The occupation basis is orthonormal: `fockMass` is a pure cardinality

Work order: `SM_ESA_COMPLETION_PLAN.md` §29.

## 1. What §24 left open

§24 bounded every entry of every P1 Higgs matrix by the `ℓ¹` mass of the internal matrix times
`‖fockBasis T‖`, and summed that over the row to the radius

```text
p1HiggsRowRadius D = p1HiggsMassTotal D * fockMass,      fockMass = ∑_T ‖fockBasis T‖.
```

It recorded honestly that `fockMass` is *not* known to be `1`: the corpus never states the
normalisation of `fockBasis`.  That is the one open factor, and it is a trivial computation: the
occupation basis is defined as a delta function,

```text
fockBasis S T = if T = S then 1 else 0,
```

so `‖fockBasis S‖ = 1` and `fockMass` is the **cardinality** of `Finset (Fin 96)`, i.e. `2 ^ 96`.
This section proves both, so §24's radii become

```text
p1HiggsRowRadius D = p1HiggsMassTotal D * 2 ^ 96,
p1HiggsColRadius D = p1HiggsMassTotal D * (2 ^ 96) ^ 2,
```

with no unknown factor left.

## 2. What this does and does not sharpen

The remaining size of §24's constant is the two factors the `ℓ¹` route itself costs: the mass
`p1HiggsMassTotal` is not an operator norm, and the column count is the full cardinality rather than
the number of occupied sectors.  Those are properties of the *route*, not of the basis, and §27
removed both by switching to `L^∞` operator norms.  What is settled here is the third factor — the
basis mass — which was the only one §24 described as an open normalisation question:

* `fockBasis_norm` — `‖fockBasis S‖ = 1` (so the basis is orthonormal, not merely orthogonal);
* `fockMass_eq_card` — `fockMass = card (Finset (Fin 96))`;
* `fockMass_eq_two_pow` — `fockMass = 2 ^ 96`, the `2 ^ 96`-dimensional Fock space;
* `p1HiggsRowRadius_eq`, `p1HiggsColRadius_eq` and the `2 ^ 96` forms — §24's radii with the basis
  mass evaluated;
* `rowSum_p1Higgs_le_mass_card`, `colSum_p1Higgs_le_mass_card_sq` — §24's two Schur bounds at the
  evaluated radii.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmFullCommFormBlockHermitianP1BasisNorm

open BookProof.SmCar BookProof.SmMatter BookProof.SmFullMatter BookProof.SmFullYukawaCoeffs
open BookProof.SmFullCommFormBlockHermitian BookProof.SmFullCommFormBlockHermitianP1
open BookProof.SmFullCommFormBlockHermitianP1Schur

noncomputable section

/-! ## 1. The basis is orthonormal -/

/-- **The occupation basis vector has norm one**: `fockBasis S` is the delta function at `S`, so its
squared norm is the sum of one nonzero entry of modulus one. -/
theorem fockBasis_norm (S : Finset (Fin 96)) : ‖fockBasis S‖ = 1 := by
  have h2 : ‖fockBasis S‖ ^ 2 = 1 := by
    rw [normSq_eq_sum]
    rw [Finset.sum_eq_single S]
    · simp [fockBasis]
    · intro b _ hb
      simp [fockBasis, hb]
    · intro h
      exact absurd (Finset.mem_univ S) h
  nlinarith [norm_nonneg (fockBasis S), sq_nonneg (‖fockBasis S‖ - 1)]

/-- **The mass of the occupation basis is its cardinality.** -/
theorem fockMass_eq_card : fockMass = (Fintype.card (Finset (Fin 96)) : ℝ) := by
  simp [fockMass, fockBasis_norm]

/-- **`fockMass = 2 ^ 96`**: the matter Fock space over the `96` complex modes has `2 ^ 96`
dimensions, so the basis mass is that number. -/
theorem fockMass_eq_two_pow : fockMass = ((2 ^ 96 : ℕ) : ℝ) := by
  rw [fockMass_eq_card, Fintype.card_finset, Fintype.card_fin]

/-- The basis mass is positive. -/
theorem fockMass_pos : 0 < fockMass := by
  rw [fockMass_eq_two_pow]
  exact_mod_cast (by norm_num : (0 : ℕ) < 2 ^ 96)

/-! ## 2. §24's radii with the basis mass evaluated -/

/-- **The row radius is the total internal mass times the dimension of the Fock space.** -/
theorem p1HiggsRowRadius_eq (D : SmInternalData) :
    p1HiggsRowRadius D = p1HiggsMassTotal D * (Fintype.card (Finset (Fin 96)) : ℝ) := by
  simp [p1HiggsRowRadius, fockMass_eq_card]

/-- The row radius in the `2 ^ 96` form. -/
theorem p1HiggsRowRadius_eq_two_pow (D : SmInternalData) :
    p1HiggsRowRadius D = p1HiggsMassTotal D * ((2 ^ 96 : ℕ) : ℝ) := by
  rw [p1HiggsRowRadius_eq, Fintype.card_finset, Fintype.card_fin]

/-- **The column radius is the row radius times the dimension** — the full column count, which is
what §24's `ℓ¹` route costs. -/
theorem p1HiggsColRadius_eq (D : SmInternalData) :
    p1HiggsColRadius D
      = (Fintype.card (Finset (Fin 96)) : ℝ) ^ 2 * p1HiggsMassTotal D := by
  rw [p1HiggsColRadius, p1HiggsRowRadius_eq]
  ring

/-- The column radius in the `2 ^ 96` form. -/
theorem p1HiggsColRadius_eq_two_pow (D : SmInternalData) :
    p1HiggsColRadius D = ((2 ^ 96 : ℕ) : ℝ) ^ 2 * p1HiggsMassTotal D := by
  rw [p1HiggsColRadius_eq, Fintype.card_finset, Fintype.card_fin]

/-! ## 3. The Schur bounds at the evaluated radii -/

/-- **The row Schur bound without the basis mass**: `p1HiggsMassTotal D * 2 ^ 96`. -/
theorem rowSum_p1Higgs_le_mass_card (D : SmInternalData)
    (blk : Finset (Fin 96) → Fin 4) (A : Finset (Fin 96)) :
    rowSum (p1HiggsMat D) blk A ≤ p1HiggsMassTotal D * ((2 ^ 96 : ℕ) : ℝ) := by
  refine (rowSum_p1Higgs_le D blk A).trans_eq ?_
  exact p1HiggsRowRadius_eq_two_pow D

/-- **The column Schur bound without the basis mass**: `p1HiggsMassTotal D * (2 ^ 96) ^ 2`. -/
theorem colSum_p1Higgs_le_mass_card_sq (D : SmInternalData)
    (blk : Finset (Fin 96) → Fin 4) (B : Finset (Fin 96)) :
    colSum (p1HiggsMat D) blk B ≤ ((2 ^ 96 : ℕ) : ℝ) ^ 2 * p1HiggsMassTotal D := by
  refine (colSum_p1Higgs_le D blk B).trans_eq ?_
  exact p1HiggsColRadius_eq_two_pow D

end

end BookProof.SmFullCommFormBlockHermitianP1BasisNorm
