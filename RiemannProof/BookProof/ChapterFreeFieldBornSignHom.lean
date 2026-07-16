import Mathlib
import BookProof.ChapterFreeFieldBornSignAction

/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# the diagonal sign gauge as a homomorphism with parity character

Source: `book.tex`, Introduction, section *"Wave-function collapse versus Euler's
formula"* (`book.tex` line ~805) together with the free-field construction of §5
(`book.tex` ~line 1706).

Wave 158 (`ChapterFreeFieldBornSignAction`) recorded the diagonal `{±1}ⁿ` sign
gauge as an *action* of the elementary abelian 2-group `(Fin n → Bool, ⊕)`: the
sign flip `boolFlip b` (flip coordinate `k` iff `b k = true`) satisfies the
action laws (identity, `xor` composition, involution), preserves the unit sphere,
and fixes the Born image.

This wave records the underlying `±1` **sign vector** `flipVec b` as a *group
homomorphism*: `flipVec` sends the all-`false` vector to the pointwise unit `1`,
turns coordinate-wise `xor` into the pointwise product, is self-inverse, and is
injective (distinct boolean choices give distinct sign vectors, so the diagonal
gauge really has `2ⁿ` elements).  Finally we compute the **parity character**
`∏ k, flipVec b k = (-1) ^ (#flipped coordinates)` — the one-dimensional sign
representation `b ↦ (-1)^{|b|}` of the elementary abelian 2-group.

## Main results

* `flipVec_false` — `flipVec` sends the all-`false` vector to the pointwise `1`.
* `flipVec_xor` — `flipVec` turns coordinate-wise `xor` into the pointwise
  product (the homomorphism law).
* `flipVec_mul_self` — each `flipVec b` is self-inverse: `flipVec b * flipVec b = 1`.
* `flipVec_injective` — distinct boolean choices give distinct sign vectors.
* **headline** `flipVec_prod` — the parity character:
  `∏ k, flipVec b k = (-1) ^ (flipCount b)`.

Everything is intended to be `sorry`-free and axiom-clean.
-/

open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornSignAction

namespace BookProof.ChapterFreeFieldBornSignHom

variable {n : ℕ}

/-- The number of *flipped* coordinates of a boolean flip choice `b` — the
Hamming weight `|b|`.  The parity character below is `(-1)` to this power. -/
def flipCount (b : Fin n → Bool) : ℕ := (Finset.univ.filter (fun k => b k = true)).card

/-
`flipVec` sends the all-`false` vector to the pointwise multiplicative unit.
-/
theorem flipVec_false : flipVec (fun _ => false : Fin n → Bool) = (1 : Fin n → ℝ) := by
  ext k; simp [flipVec]

/-
**Homomorphism law.** `flipVec` turns coordinate-wise `xor` into the
pointwise product of sign vectors, exhibiting it as a group homomorphism from
`(Fin n → Bool, ⊕)` to the pointwise `±1` sign vectors.
-/
theorem flipVec_xor (b₁ b₂ : Fin n → Bool) :
    flipVec (fun k => xor (b₁ k) (b₂ k)) = flipVec b₁ * flipVec b₂ := by
  ext k; unfold flipVec; by_cases h₁ : b₁ k <;> by_cases h₂ : b₂ k <;> simp +decide [h₁, h₂]

/-
Each sign vector is self-inverse (the group is 2-torsion).
-/
theorem flipVec_mul_self (b : Fin n → Bool) :
    flipVec b * flipVec b = (1 : Fin n → ℝ) := by
  ext k; unfold flipVec; by_cases h : b k <;> simp +decide [h]

/-
Distinct boolean flip choices give distinct sign vectors: `flipVec` is
injective, so the diagonal gauge group really has `2ⁿ` elements.
-/
theorem flipVec_injective : Function.Injective (flipVec : (Fin n → Bool) → (Fin n → ℝ)) := by
  intro b₁ b₂ h; ext k; replace h := congr_fun h k; simp_all +decide [flipVec]
  grind

/-
**Headline (parity character).** The product of the coordinates of a sign
vector is `(-1)` to the number of flipped coordinates — the one-dimensional sign
representation `b ↦ (-1)^{|b|}` of the elementary abelian 2-group.
-/
theorem flipVec_prod (b : Fin n → Bool) :
    (∏ k, flipVec b k) = (-1 : ℝ) ^ flipCount b := by
  norm_num [Finset.prod_ite, flipVec]
  rfl

end BookProof.ChapterFreeFieldBornSignHom
