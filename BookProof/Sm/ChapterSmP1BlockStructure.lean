import Mathlib
import BookProof.Sm.ChapterSmFockBasisNormalised

/-!
# The block structure of the P1 coefficient matrices: occupation number, and nothing finer

Work order: `SM_ESA_COMPLETION_PLAN.md` §30.

## 1. The question

§20's commutator bound needs a block decomposition: a function `blk : Finset (Fin 96) → Fin 4`
assigning every occupation sector to one of the four Higgs components, with the support condition

```text
p1HiggsMat D a A B ≠ 0  →  blk A = a.
```

§21 instantiated that condition as a hypothesis, §24/§27 made the Schur data explicit, and §25/§28
dropped it.  What none of them asked is whether the *P1 dictionary itself* has such a `blk`.  This
section answers that question for the matrices as defined, `p1HiggsMat D a = fockMatrix (matterBilin
(D.higgs a))`.

## 2. The one block structure the dictionary does have

`matterBilin M` is `Σ_{i j} M_{i j} a†_i a_j`, and every term `a†_i a_j` moves one electron from
mode `j` to mode `i`: it conserves the occupation number.  Hence

```text
p1HiggsMat D a S T ≠ 0  →  S.card = T.card,
```

proved as `p1HiggsMat_card_eq`.  The blocks are therefore the `97` occupation numbers, and — this is
the point — they are the **same** blocks for all four components `a`.  A per-component `blk` needs
blocks that separate the four Higgs matrices from each other, and occupation number cannot do that:
it does not refer to `a` at all.

So the answer to the question is: the dictionary's structural block decomposition is occupation
number (equivalently, its parity shadow `fockSign`), and it is too coarse to be §20's `blk`.

## 3. A dictionary for which no `blk` exists at all

That is not yet a counterexample, because with four *distinct* matrices a per-component `blk` may
still happen to exist.  The second half of the section supplies one where it provably cannot:
`degHiggsData`, the fully degenerate doublet, whose four Higgs components are all the identity
internal matrix `1`.  Then

* `p1HiggsMat_degHiggs_eq` — the four coefficient matrices are literally equal;
* `p1HiggsMat_degHiggs_apply` — and equal to the number operator, `(S.card : ℂ)` on the diagonal of
  the occupation basis, so they are nonzero;
* `degHiggs_no_support` — **no** `blk` satisfies §20's support condition, because a single row
  `{0}` is shared by all four components and would have to be mapped to `0`, `1`, `2` and `3`.

The general criterion is `no_support_of_shared_entry`: whenever two components agree as internal
matrices, any nonzero entry of theirs rules out a per-component block function.  §28 built the same
conclusion for a hand-written mixing family; here it is reached from the dictionary's own
definition.

The consequence for the corpus is that §25's support-free Schur test — and §27's operator-norm
radii for it — is **necessary** for the P1 dictionary and not merely convenient: the block-diagonal
test of §20/§21 cannot be instantiated on data of this kind, degenerate doublets being exactly the
physically natural case (two members of a Higgs doublet with the same coupling pattern).

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmFullCommFormBlockHermitianP1BlockStructure

open BookProof.SmCar BookProof.SmMatter BookProof.SmFullMatter BookProof.SmFullYukawaCoeffs
open BookProof.SmFullCommFormBlockHermitianP1

noncomputable section

/-! ## 1. Occupation number is conserved by every P1 coefficient matrix -/

/-- **One second-quantized transition conserves the occupation number**: `a†_i a_j` applied to a
basis vector `|T⟩` can only produce a vector whose occupied set has the cardinality of `T`, because
it removes one mode and inserts one. -/
theorem creat_annih_basis_of_card_ne (i j : Fin 96) (S T : Finset (Fin 96))
    (h : S.card ≠ T.card) : (creat i (annih j (fockBasis T))) S = 0 := by
  rw [creat_apply]
  split_ifs with hi
  · rw [annih_apply]
    split_ifs with hj
    · simp
    · by_cases heq : insert j (S.erase i) = T
      · exfalso
        have h1 : (S.erase i).card = S.card - 1 := Finset.card_erase_of_mem hi
        have h2 : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
        have h3 : T.card = S.card := by
          rw [← heq, Finset.card_insert_of_notMem hj, h1, Nat.sub_add_cancel (by omega)]
        exact h h3.symm
      · rw [fockBasis_of_ne heq]
        simp
  · simp

/-- **Every P1 coefficient matrix is occupation-number diagonal in the block sense**: the entry at
`(S, T)` vanishes whenever `S` and `T` are occupied sets of different cardinality. -/
theorem p1HiggsMat_of_card_ne (D : SmInternalData) (a : Fin 4) (S T : Finset (Fin 96))
    (h : S.card ≠ T.card) : p1HiggsMat D a S T = 0 := by
  rw [p1HiggsMat, fockMatrix]
  simp only [matterBilin_apply]
  rw [sum_apply_fock]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [sum_apply_fock]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [smul_apply_fock, matterCreat, matterAnnih]
  simp only [smMatterMode.apply_symm_apply]
  rw [creat_annih_basis_of_card_ne i j S T h, mul_zero]

/-- **The blocks of the P1 dictionary are the occupation numbers**, and they are shared by all four
components: a nonzero entry forces `S.card = T.card`. -/
theorem p1HiggsMat_card_eq (D : SmInternalData) (a : Fin 4) (S T : Finset (Fin 96))
    (h : p1HiggsMat D a S T ≠ 0) : S.card = T.card := by
  by_contra hne
  exact h (p1HiggsMat_of_card_ne D a S T hne)

/-! ## 2. A degenerate doublet, for which no per-component block function exists -/

/-- **The fully degenerate P1 dictionary**: all four real Higgs components carry the identity
internal matrix, i.e. the same coupling pattern — the extreme case of a degenerate doublet.  The
placement `pos` is immaterial here, since the theorems below concern `p1HiggsMat`, not the
coordinate family. -/
def degHiggsData : SmInternalData where
  pos := fun _ => 0
  higgs := fun _ => 1
  mass := 1
  higgsHermitian := fun _ => by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]
  massHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]

/-- The second quantization of the identity is the free (number) operator `Σ_i a†_i a_i`. -/
theorem matterBilin_one_eq_fermiEnergy :
    matterBilin (1 : Matrix SmMatterIndex SmMatterIndex ℂ) =
      fermiEnergy (fun _ : Fin 96 => (1 : ℝ)) := by
  rw [matterBilin, fermiEnergy]
  congr 1
  ext i j
  simp [Matrix.submatrix, Matrix.one_apply]

/-- **The four coefficient matrices of the degenerate dictionary coincide.** -/
theorem p1HiggsMat_degHiggs_eq (a b : Fin 4) :
    p1HiggsMat degHiggsData a = p1HiggsMat degHiggsData b := rfl

/-- **The degenerate dictionary is the number operator**: its entries are `S.card` on the diagonal
of the occupation basis and zero off it. -/
theorem p1HiggsMat_degHiggs_apply (a : Fin 4) (S T : Finset (Fin 96)) :
    p1HiggsMat degHiggsData a S T = (S.card : ℂ) * (if S = T then 1 else 0) := by
  rw [p1HiggsMat, fockMatrix,
    show degHiggsData.higgs a = 1 from rfl, matterBilin_one_eq_fermiEnergy, fermiEnergy_apply]
  congr 1
  simp

/-- **The degenerate dictionary has a nonzero entry**: every occupied sector is an eigenvector with
eigenvalue its occupation number. -/
theorem p1HiggsMat_degHiggs_entry_ne_zero (a : Fin 4) :
    p1HiggsMat degHiggsData a {0} {0} ≠ 0 := by
  rw [p1HiggsMat_degHiggs_apply]
  norm_num

/-- **No per-component block function exists for the degenerate dictionary**: the row `{0}` carries
nonzero entries for every component, so §20's support condition would force `blk {0}` to be all four
values at once. -/
theorem degHiggs_no_support :
    ¬ ∃ blk : Finset (Fin 96) → Fin 4,
      ∀ (a : Fin 4) (A B : Finset (Fin 96)), p1HiggsMat degHiggsData a A B ≠ 0 → blk A = a := by
  rintro ⟨blk, hblk⟩
  have h0 : blk {0} = 0 := hblk 0 {0} {0} (p1HiggsMat_degHiggs_entry_ne_zero 0)
  have h1 : blk {0} = 1 := hblk 1 {0} {0} (p1HiggsMat_degHiggs_entry_ne_zero 1)
  rw [h0] at h1
  exact absurd h1 (by norm_num)

/-- **The general criterion**: if two components of the dictionary agree as internal matrices and
one of them has a nonzero entry, no per-component block function exists.  This is what makes
`degHiggs_no_support` an instance of a structural fact rather than an accident of the identity. -/
theorem no_support_of_shared_entry (D : SmInternalData) (h : D.higgs 0 = D.higgs 1)
    (A B : Finset (Fin 96)) (hne : p1HiggsMat D 0 A B ≠ 0) :
    ¬ ∃ blk : Finset (Fin 96) → Fin 4,
      ∀ (a : Fin 4) (A' B' : Finset (Fin 96)), p1HiggsMat D a A' B' ≠ 0 → blk A' = a := by
  rintro ⟨blk, hblk⟩
  have h0 : blk A = 0 := hblk 0 A B hne
  have hsame : p1HiggsMat D 1 A B = p1HiggsMat D 0 A B := by
    rw [p1HiggsMat, p1HiggsMat, h]
  have h1 : blk A = 1 := hblk 1 A B (by rw [hsame]; exact hne)
  rw [h0] at h1
  exact absurd h1 (by norm_num)

end

end BookProof.SmFullCommFormBlockHermitianP1BlockStructure
