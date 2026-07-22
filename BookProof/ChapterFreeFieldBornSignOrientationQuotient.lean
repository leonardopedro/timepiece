import Mathlib
import BookProof.ChapterFreeFieldBornSignOrientationSubgroup

/-!
# The orientation character and the two-element quotient

This file realizes the index-two result structurally. Summing the boolean flip
coordinates gives a homomorphism to `Bool`; it is the parity/orientation
character. Its kernel is exactly the orientation-preserving sign subgroup, and
in positive dimension the first isomorphism theorem identifies the quotient
with `Bool`.
-/

open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignOrientationSubgroup

namespace BookProof.ChapterFreeFieldBornSignOrientationQuotient

/-- The parity character of a boolean sign choice. Addition on `Bool` is xor. -/
def orientationCharacter (n : ℕ) : (Fin n → Bool) →+ Bool where
  toFun b := ∑ k, b k
  map_zero' := by simp
  map_add' := by
    intro b₁ b₂
    simp [Finset.sum_add_distrib]

@[simp] theorem orientationCharacter_apply {n : ℕ} (b : Fin n → Bool) :
    orientationCharacter n b = ∑ k, b k :=
  rfl

/-
The boolean parity sum vanishes exactly when the Hamming weight is even.
-/
theorem orientationCharacter_eq_false_iff_even {n : ℕ} (b : Fin n → Bool) :
    orientationCharacter n b = false ↔ Even (flipCount b) := by
  induction n <;> simp_all +decide [ Fin.sum_univ_succ, orientationCharacter, flipCount ];
  rename_i n ih;
  by_cases h : b 0 <;> simp_all +decide [ Finset.filter_insert, parity_simps ];
  · rw [ show ( Finset.univ.filter fun k => b k = true ) = Finset.image ( fun k => Fin.succ k ) ( Finset.univ.filter fun k => b ( Fin.succ k ) = true ) ∪ { 0 } from ?_, Finset.card_union ] <;> norm_num [ Finset.card_image_of_injective, Function.Injective, h ];
    · cases Nat.mod_two_eq_zero_or_one ( Finset.card ( Finset.filter ( fun k => b ( Fin.succ k ) = true ) Finset.univ ) ) <;> simp_all +decide [ Nat.even_iff, Nat.add_mod ];
      · convert ih _ |>.2 ‹_› using 1;
      · specialize ih ( fun k => b k.succ ) ; aesop;
    · ext ( _ | k ) <;> simp +decide [ h ];
      exact ⟨ fun hk => ⟨ ⟨ k, by linarith ⟩, hk, rfl ⟩, by rintro ⟨ a, ha, ha' ⟩ ; cases a ; aesop ⟩;
  · convert ih ( fun i => b i.succ ) using 1;
    rw [ Finset.card_filter, Finset.card_filter ];
    rw [ Fin.sum_univ_succ ] ; aesop

/-
The orientation-preserving sign subgroup is the kernel of the parity
character.
-/
theorem orientationCharacter_ker (n : ℕ) :
    (orientationCharacter n).ker = orientationPreservingSigns n := by
  ext b
  rw [AddMonoidHom.mem_ker]
  change orientationCharacter n b = false ↔ b ∈ orientationPreservingSigns n
  rw [orientationCharacter_eq_false_iff_even,
    mem_orientationPreservingSigns_iff_even]

/-
In positive dimension the orientation character is onto: flipping the first
coordinate represents the orientation-reversing class.
-/
theorem orientationCharacter_surjective (n : ℕ) :
    Function.Surjective (orientationCharacter (n + 1)) := by
  intro x
  use fun k => if k = 0 then x else 0
  aesop

/-- The quotient of all boolean sign choices by the orientation-preserving
subgroup is the two-element group `Bool`. -/
noncomputable def orientationQuotientEquiv (n : ℕ) :
    ((Fin (n + 1) → Bool) ⧸ orientationPreservingSigns (n + 1)) ≃+ Bool :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (orientationCharacter_ker (n + 1)).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (orientationCharacter (n + 1)) (orientationCharacter_surjective n))

/-
The quotient equivalence sends the class of a sign choice to its parity
character.
-/
theorem orientationQuotientEquiv_mk (n : ℕ) (b : Fin (n + 1) → Bool) :
    orientationQuotientEquiv n (QuotientAddGroup.mk b) =
      orientationCharacter (n + 1) b := by
  convert QuotientAddGroup.kerLift_mk (orientationCharacter (n + 1)) b using 1

end BookProof.ChapterFreeFieldBornSignOrientationQuotient
