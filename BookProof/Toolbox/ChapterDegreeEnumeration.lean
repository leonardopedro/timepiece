import Mathlib
import BookProof.Toolbox.ChapterHermiteBridgePhases

/-!
# A degree-compatible enumeration of the multi-indices

`BookProof.HermiteBridgePhases` proves the `coreBasis` ↔ `hermBasisN` bridge from a hypothesis on
the enumeration: `DegreeCompatible e` says the enumeration lists the multi-indices in nondecreasing
total degree.  This module *constructs* such an enumeration, so the bridge becomes unconditional for
`0 < d`.

## Design

The enumeration is built block by block.  `blockCard m` counts the multi-indices of total degree
`m` — no closed formula is needed, only that the type is finite (`Fintype.ofInjective` into the
bounded functions `Fin d → Fin (m + 1)`) and nonempty (`Finsupp.single i₀ m`).  `offset m` is the
number of multi-indices of degree `< m`, and

`rank b := offset (totalDeg b) + blockIdx b`

is the position of `b` in the degree-first order, `blockIdx b` being its position inside its own
degree block.  `rank` is a bijection `(Fin d →₀ ℕ) → ℕ`: injective because the blocks are
consecutive (`offset (m + 1) = offset m + blockCard m`, with `blockCard m > 0`), and surjective
because the blocks cover `ℕ` (`offset m ≥ m`).  The enumeration is the inverse of `rank`, and
`DegreeCompatible` is then a short estimate: a multi-index of smaller degree has smaller rank.

Nothing here uses analysis, Hermite functions or the dimension `99`: the statements are for a
general finite coordinate set `Fin d` with `0 < d`.

## Contents

* `totalDeg`, `le_totalDeg`, `totalDeg_single` — the total degree and its two basic estimates;
* `instFintypeDegBlock`, `blockCard`, `blockCard_pos` — the degree blocks are finite and nonempty;
* `blockIdx`, `blockIdx_val`, `eq_of_blockIdx_eq` — position inside a block;
* `offset`, `offset_succ`, `offset_mono`, `offset_le`, `offset_lt_succ` — the block boundaries;
* `rank`, `rank_lt`, `rank_val`, `rank_injective`, `rank_surjective` — the position is a bijection;
* `degreeEnum`, `degreeEnum_rank`, `degreeEnum_degreeCompatible`, `exists_degreeCompatible` — the
  enumeration and its compatibility proof.
-/

namespace BookProof.DegreeEnumeration

noncomputable section

open Finsupp (single)

variable {d : ℕ}

/-! ## The total degree -/

/-- Total degree of a multi-index, `∑ i, b i`. -/
def totalDeg (b : Fin d →₀ ℕ) : ℕ := ∑ i, b i

/-- A single coordinate never exceeds the total degree. -/
theorem le_totalDeg (b : Fin d →₀ ℕ) (i : Fin d) : b i ≤ totalDeg b :=
  Finset.single_le_sum (f := fun j => b j) (fun j _ => Nat.zero_le (b j)) (Finset.mem_univ i)

/-- A single-coordinate multi-index has degree that coordinate. -/
theorem totalDeg_single (i : Fin d) (m : ℕ) : totalDeg (single i m) = m := by
  rw [totalDeg, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    exact Finsupp.single_eq_of_ne hj
  · intro hi
    simp at hi

theorem totalDeg_eq_sum (b : Fin d →₀ ℕ) : totalDeg b = ∑ i, b i := rfl

/-! ## The degree blocks -/

/-- A multi-index of total degree `m`, read as a bounded function. -/
def toFun (m : ℕ) (b : {b : Fin d →₀ ℕ // totalDeg b = m}) : Fin d → Fin (m + 1) :=
  fun i => ⟨b.1 i, Nat.lt_succ_of_le (le_trans (le_totalDeg b.1 i) (le_of_eq b.2))⟩

theorem toFun_injective (m : ℕ) : Function.Injective (toFun (d := d) m) := by
  rintro ⟨b, hb⟩ ⟨c, hc⟩ h
  simp only [Subtype.mk.injEq]
  ext i
  have hi := congrFun h i
  simpa [toFun] using hi

/-- The multi-indices of a fixed total degree form a finite type. -/
noncomputable instance instFintypeDegBlock (m : ℕ) :
    Fintype {b : Fin d →₀ ℕ // totalDeg b = m} :=
  Fintype.ofInjective (toFun (d := d) m) (toFun_injective m)

/-- The number of multi-indices of total degree `m`. -/
noncomputable def blockCard (d : ℕ) (m : ℕ) : ℕ :=
  Fintype.card {b : Fin d →₀ ℕ // totalDeg b = m}

/-- Every degree block is nonempty, `m • e_{i₀}` being an element of it. -/
theorem blockCard_pos (hd : 0 < d) (m : ℕ) : 0 < blockCard d m := by
  haveI : Nonempty {b : Fin d →₀ ℕ // totalDeg b = m} :=
    ⟨⟨single ⟨0, hd⟩ m, totalDeg_single ⟨0, hd⟩ m⟩⟩
  exact Fintype.card_pos_iff.mpr ‹Nonempty _›

/-- Position of a multi-index inside its own degree block. -/
noncomputable def blockIdx (b : Fin d →₀ ℕ) : ℕ :=
  ((Fintype.equivFin {b' : Fin d →₀ ℕ // totalDeg b' = totalDeg b}) ⟨b, rfl⟩ : ℕ)

theorem blockIdx_lt (b : Fin d →₀ ℕ) : blockIdx b < blockCard d (totalDeg b) :=
  Fin.isLt _

/-- The block position, stated at an explicit block degree. -/
theorem blockIdx_val (b : Fin d →₀ ℕ) (m : ℕ) (hm : totalDeg b = m) :
    blockIdx b = ((Fintype.equivFin {b' : Fin d →₀ ℕ // totalDeg b' = m}) ⟨b, hm⟩ : ℕ) := by
  subst hm
  rfl

/-- Equal block positions in the same block mean equal multi-indices. -/
theorem eq_of_blockIdx_eq {b c : Fin d →₀ ℕ} (hd : totalDeg b = totalDeg c)
    (hi : blockIdx b = blockIdx c) : b = c := by
  have h1 := blockIdx_val b (totalDeg c) hd
  have h2 := blockIdx_val c (totalDeg c) rfl
  rw [h1, h2] at hi
  have hfin : (Fintype.equivFin {b' : Fin d →₀ ℕ // totalDeg b' = totalDeg c}) ⟨b, hd⟩
      = (Fintype.equivFin _) ⟨c, rfl⟩ := Fin.ext hi
  have hval := (Fintype.equivFin _).injective hfin
  simpa using hval

/-! ## The block boundaries -/

/-- The number of multi-indices of total degree `< m`. -/
noncomputable def offset (d : ℕ) (m : ℕ) : ℕ := (Finset.range m).sum (fun m' => blockCard d m')

theorem offset_zero : offset d 0 = 0 := by
  simp [offset]

theorem offset_succ (m : ℕ) : offset d (m + 1) = offset d m + blockCard d m := by
  simp [offset, Finset.sum_range_succ]

/-- The block boundaries are monotone. -/
theorem offset_mono : Monotone (offset d) := by
  intro a b hab
  simp only [offset]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hab)
    (fun x _ _ => Nat.zero_le _)

/-- They are strictly increasing, because no block is empty. -/
theorem offset_lt_succ (hd : 0 < d) (m : ℕ) : offset d m < offset d (m + 1) := by
  rw [offset_succ]
  exact Nat.lt_add_of_pos_right (blockCard_pos hd m)

/-- In particular the `m`-th boundary is at least `m`: the blocks cover everything. -/
theorem offset_le (hd : 0 < d) (m : ℕ) : m ≤ offset d m := by
  induction m with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (offset_lt_succ hd k))

/-! ## The position function -/

/-- The position of `b` in the degree-first order. -/
noncomputable def rank (b : Fin d →₀ ℕ) : ℕ := offset d (totalDeg b) + blockIdx b

/-- A multi-index sits strictly before the next block boundary. -/
theorem rank_lt (b : Fin d →₀ ℕ) : rank b < offset d (totalDeg b + 1) := by
  rw [rank, offset_succ]
  exact Nat.add_lt_add_left (blockIdx_lt b) _

/-- The position, stated at an explicit block degree. -/
theorem rank_val (b : Fin d →₀ ℕ) (m : ℕ) (hm : totalDeg b = m) :
    rank b = offset d m + ((Fintype.equivFin {b' : Fin d →₀ ℕ // totalDeg b' = m})
      ⟨b, hm⟩ : ℕ) := by
  rw [rank, blockIdx_val b m hm, hm]

/-- Two distinct degrees give distinct positions. -/
theorem rank_ne_of_totalDeg_lt {b c : Fin d →₀ ℕ}
    (hlt : totalDeg b < totalDeg c) : rank b ≠ rank c := by
  intro h
  have hb := blockIdx_lt b
  have hle : offset d (totalDeg b) + blockCard d (totalDeg b) ≤ offset d (totalDeg c) := by
    rw [← offset_succ]
    exact offset_mono (Nat.succ_le_of_lt hlt)
  simp only [rank] at h
  omega

/-- The position function is injective. -/
theorem rank_injective : Function.Injective (rank (d := d)) := by
  intro b c h
  have hdeg : totalDeg b = totalDeg c := by
    rcases lt_trichotomy (totalDeg b) (totalDeg c) with hlt | heq | hgt
    · exact absurd h (rank_ne_of_totalDeg_lt hlt)
    · exact heq
    · exact absurd h.symm (rank_ne_of_totalDeg_lt hgt)
  refine eq_of_blockIdx_eq hdeg ?_
  simp only [rank] at h
  rw [hdeg] at h
  omega

/-- The position function is surjective: take the block containing `k` and the local index. -/
theorem rank_surjective (hd : 0 < d) : Function.Surjective (rank (d := d)) := by
  intro k
  have hex : ∃ m, k < offset d (m + 1) := by
    have h := offset_le hd (k + 1)
    exact ⟨k, by omega⟩
  set m := Nat.find hex with hm
  have hspec : k < offset d (m + 1) := Nat.find_spec hex
  have hmin : offset d m ≤ k := by
    by_contra hcon
    push_neg at hcon
    rcases Nat.eq_zero_or_pos m with hzero | hpos
    · rw [hzero, offset_zero] at hcon
      omega
    · obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hlt : k < offset d m'.succ := by rw [← hm']; exact hcon
      have hfind := Nat.find_min' hex hlt
      omega
  have ht : k - offset d m < blockCard d m := by
    have h := offset_succ (d := d) m
    omega
  set x : {b : Fin d →₀ ℕ // totalDeg b = m} :=
    (Fintype.equivFin _).symm ⟨k - offset d m, ht⟩ with hx
  have hxe : (Fintype.equivFin _) x = ⟨k - offset d m, ht⟩ := by
    rw [hx]
    exact Equiv.apply_symm_apply _ _
  refine ⟨x.1, ?_⟩
  rw [rank_val x.1 m x.2, hxe]
  change offset d m + (k - offset d m) = k
  omega

/-! ## The enumeration -/

/-- **A degree-compatible enumeration of the multi-indices**, for a nonempty coordinate set. -/
noncomputable def degreeEnum (hd : 0 < d) : ℕ ≃ (Fin d →₀ ℕ) :=
  (Equiv.ofBijective (rank (d := d)) ⟨rank_injective, rank_surjective hd⟩).symm

/-- The enumeration is the inverse of the position function. -/
theorem degreeEnum_rank (hd : 0 < d) (k : ℕ) : rank (degreeEnum hd k) = k := by
  have h : (Equiv.ofBijective (rank (d := d)) ⟨rank_injective, rank_surjective hd⟩)
      ((Equiv.ofBijective (rank (d := d)) ⟨rank_injective,
        rank_surjective hd⟩).symm k) = k :=
    Equiv.apply_symm_apply _ k
  exact h

/-- Its inverse property: the position of a multi-index enumerates it. -/
theorem degreeEnum_apply_rank (hd : 0 < d) (b : Fin d →₀ ℕ) : degreeEnum hd (rank b) = b :=
  Equiv.symm_apply_apply _ b

/-- **The constructed enumeration is degree-compatible.** -/
theorem degreeEnum_degreeCompatible (hd : 0 < d) :
    BookProof.HermiteBridgePhases.DegreeCompatible (degreeEnum hd) := by
  intro k b hb
  have hdeg : totalDeg b < totalDeg (degreeEnum hd k) := by
    simpa only [totalDeg_eq_sum] using hb
  refine ⟨rank b, ?_, degreeEnum_apply_rank hd b⟩
  have h1 : rank b < offset d (totalDeg b + 1) := rank_lt b
  have h2 : offset d (totalDeg b + 1) ≤ offset d (totalDeg (degreeEnum hd k)) :=
    offset_mono (Nat.succ_le_of_lt hdeg)
  have h3 : offset d (totalDeg (degreeEnum hd k)) ≤ rank (degreeEnum hd k) := by
    rw [rank]
    exact Nat.le_add_right _ _
  rw [← degreeEnum_rank hd k]
  exact lt_of_lt_of_le (lt_of_lt_of_le h1 h2) h3

/-- **There is a degree-compatible enumeration of `Fin d →₀ ℕ`** whenever `d` is nonempty. -/
theorem exists_degreeCompatible (hd : 0 < d) :
    ∃ e : ℕ ≃ (Fin d →₀ ℕ), BookProof.HermiteBridgePhases.DegreeCompatible e :=
  ⟨degreeEnum hd, degreeEnum_degreeCompatible hd⟩

end

end BookProof.DegreeEnumeration
