import Mathlib
import BookProof.ChapterMarkovEntropy
import BookProof.ChapterReconstruct

/-!
# Symmetries as irreversible processes: a non-deterministic symmetry raises the entropy

Source: `book.tex`, chapter *"Reconstructing the classical trajectory of any isolated
quantum system"*, §*"Symmetries as irreversible processes"* (`book.tex` line ~2678):

> *"A non-deterministic symmetry transformation, when acting on a deterministic ensemble
> increases the entropy of the ensemble after the wave-function collapse and therefore must
> be an irreversible transformation."*

We formalize exactly that statement in the finite-dimensional Born model already used by
`BookProof.ChapterReconstruct` (which proves that a symmetry acts on probability
distributions iff it is *deterministic*, i.e. each column of `U` has at most one nonzero
entry) and with the Shannon entropy of `BookProof.ChapterMarkovEntropy`.

A *deterministic ensemble* is a point mass `δ_a`: the system is known to be in the basis
state `a`.  Acting with the symmetry `U` and collapsing the wave-function produces the Born
distribution of the `a`-th column,

```
bornCol U a k = ‖U k a‖² ,
```

a probability vector because the column of a unitary matrix is a unit vector.  The initial
entropy is `0` (`entropy_pointMass`), so "the entropy increases" means exactly
`0 < entropy (bornCol U a)`, and the theorem is that this happens **iff** the symmetry is
non-deterministic in that column.

## Main results

* `entropy_nonneg` — the Shannon entropy of a sub-probability vector is nonnegative.
* `entropy_eq_zero_iff` — it vanishes iff every entry is `0` or `1`.
* `entropy_pointMass` — a deterministic ensemble has zero entropy.
* `isDeterministicCol_iff_entropy_eq_zero` — for a unit column, determinism of the symmetry
  is equivalent to the collapsed ensemble still having zero entropy.
* `entropy_bornCol_pos_iff_not_isDeterministicCol` — **the headline**: the entropy strictly
  increases iff the symmetry is non-deterministic.
-/

namespace BookProof.SymmetryEntropy

open Finset
open BookProof.ChapterMarkovEntropy (entropy)
open BookProof.ChapterReconstruct (IsDeterministicCol)

variable {n : ℕ}

/-! ## Elementary facts about the Shannon entropy -/

theorem negMulLog_eq_zero_iff {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.negMulLog x = 0 ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    rcases eq_or_lt_of_le h0 with h0' | h0'
    · exact Or.inl h0'.symm
    rcases eq_or_lt_of_le h1 with h1' | h1'
    · exact Or.inr h1'
    · exfalso
      have hlog : Real.log x < 0 := Real.log_neg h0' h1'
      have : 0 < Real.negMulLog x := by
        simp only [Real.negMulLog, neg_mul]
        nlinarith
      exact absurd h (ne_of_gt this)
  · rintro (rfl | rfl) <;> simp [Real.negMulLog]

/-- The Shannon entropy of a vector with entries in `[0, 1]` is nonnegative. -/
theorem entropy_nonneg {p : Fin n → ℝ} (h0 : ∀ k, 0 ≤ p k) (h1 : ∀ k, p k ≤ 1) :
    0 ≤ entropy p :=
  Finset.sum_nonneg fun k _ => Real.negMulLog_nonneg (h0 k) (h1 k)

/-- The entropy of a vector with entries in `[0, 1]` vanishes iff each entry is `0` or
`1` — that is, iff the ensemble carries no uncertainty. -/
theorem entropy_eq_zero_iff {p : Fin n → ℝ} (h0 : ∀ k, 0 ≤ p k) (h1 : ∀ k, p k ≤ 1) :
    entropy p = 0 ↔ ∀ k, p k = 0 ∨ p k = 1 := by
  constructor
  · intro h k
    have hterm : ∀ j ∈ (univ : Finset (Fin n)), 0 ≤ Real.negMulLog (p j) := fun j _ =>
      Real.negMulLog_nonneg (h0 j) (h1 j)
    have := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp h k (mem_univ k)
    exact (negMulLog_eq_zero_iff (h0 k) (h1 k)).mp this
  · intro h
    refine Finset.sum_eq_zero fun k _ => ?_
    exact (negMulLog_eq_zero_iff (h0 k) (h1 k)).mpr (h k)

/-- A deterministic ensemble — a point mass — has zero entropy. -/
theorem entropy_pointMass (a : Fin n) :
    entropy (fun k => if k = a then (1 : ℝ) else 0) = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = a <;> simp [hk, Real.negMulLog]

/-! ## The Born distribution of a column -/

/-- The distribution obtained by letting the symmetry `U` act on the deterministic
ensemble `δ_a` and collapsing the wave-function: the Born law of the `a`-th column. -/
noncomputable def bornCol (U : Fin n → Fin n → ℂ) (a : Fin n) : Fin n → ℝ :=
  fun k => ‖U k a‖ ^ 2

theorem bornCol_nonneg (U : Fin n → Fin n → ℂ) (a : Fin n) (k : Fin n) :
    0 ≤ bornCol U a k := by
  simp only [bornCol]
  positivity

theorem bornCol_le_one {U : Fin n → Fin n → ℂ} {a : Fin n}
    (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) (k : Fin n) : bornCol U a k ≤ 1 := by
  have := Finset.single_le_sum (f := fun j => ‖U j a‖ ^ 2)
    (fun j _ => by positivity : ∀ j ∈ (univ : Finset (Fin n)), 0 ≤ ‖U j a‖ ^ 2) (mem_univ k)
  rw [hcol] at this
  exact this

theorem bornCol_eq_zero_iff (U : Fin n → Fin n → ℂ) (a k : Fin n) :
    bornCol U a k = 0 ↔ U k a = 0 := by
  simp [bornCol, pow_eq_zero_iff]

/-! ## Determinism versus entropy -/

/-- A symmetry that is deterministic in column `a` sends the deterministic ensemble `δ_a`
to a deterministic ensemble: the collapsed law is again a point mass. -/
theorem exists_eq_one_of_isDeterministicCol {U : Fin n → Fin n → ℂ} {a : Fin n}
    (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) (hdet : IsDeterministicCol U a) :
    ∃ k, bornCol U a k = 1 ∧ ∀ l, l ≠ k → bornCol U a l = 0 := by
  have hne : ∃ k, U k a ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hz : ∑ k, ‖U k a‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hall k]
      simp
    rw [hz] at hcol
    norm_num at hcol
  obtain ⟨k, hk⟩ := hne
  have hzero : ∀ l, l ≠ k → U l a = 0 := by
    intro l hl
    have := hdet l k hl
    rcases mul_eq_zero.mp this with h | h
    · exact absurd ((starRingEnd ℂ).injective (by simpa using h)) hk
    · exact h
  refine ⟨k, ?_, fun l hl => by simp [bornCol, hzero l hl]⟩
  have : ∑ j, ‖U j a‖ ^ 2 = ‖U k a‖ ^ 2 := by
    refine Finset.sum_eq_single k (fun j _ hj => by rw [hzero j hj]; simp) (by simp)
  rw [this] at hcol
  simpa [bornCol] using hcol

/-- Conversely, if the collapsed law is a point mass then the symmetry is deterministic in
that column. -/
theorem isDeterministicCol_of_entropy_eq_zero {U : Fin n → Fin n → ℂ} {a : Fin n}
    (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) (h : entropy (bornCol U a) = 0) :
    IsDeterministicCol U a := by
  have hzeroone := (entropy_eq_zero_iff (bornCol_nonneg U a) (bornCol_le_one hcol)).mp h
  -- at most one index can carry the value `1`
  have hsum : ∑ k, bornCol U a k = 1 := hcol
  have hunique : ∀ l m : Fin n, l ≠ m → bornCol U a l = 0 ∨ bornCol U a m = 0 := by
    intro l m hlm
    rcases hzeroone l with hl | hl
    · exact Or.inl hl
    rcases hzeroone m with hm | hm
    · exact Or.inr hm
    · exfalso
      have hle : bornCol U a l + bornCol U a m ≤ ∑ k, bornCol U a k := by
        have := Finset.sum_le_sum_of_subset_of_nonneg
          (s := ({l, m} : Finset (Fin n))) (t := (univ : Finset (Fin n)))
          (f := bornCol U a) (Finset.subset_univ _)
          (fun k _ _ => bornCol_nonneg U a k)
        rwa [Finset.sum_pair hlm] at this
      rw [hsum, hl, hm] at hle
      norm_num at hle
  intro l m hlm
  rcases hunique l m hlm with h' | h'
  · rw [(bornCol_eq_zero_iff U a l).mp h']
    simp
  · rw [(bornCol_eq_zero_iff U a m).mp h']
    simp

/-- **Determinism is exactly the absence of entropy production.** -/
theorem isDeterministicCol_iff_entropy_eq_zero {U : Fin n → Fin n → ℂ} {a : Fin n}
    (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) :
    IsDeterministicCol U a ↔ entropy (bornCol U a) = 0 := by
  constructor
  · intro hdet
    obtain ⟨k, hk1, hk0⟩ := exists_eq_one_of_isDeterministicCol hcol hdet
    refine (entropy_eq_zero_iff (bornCol_nonneg U a) (bornCol_le_one hcol)).mpr fun l => ?_
    by_cases hl : l = k
    · exact Or.inr (hl ▸ hk1)
    · exact Or.inl (hk0 l hl)
  · exact isDeterministicCol_of_entropy_eq_zero hcol

/-- **The headline.**  Acting with the symmetry `U` on the deterministic ensemble `δ_a`
(entropy `0`, by `entropy_pointMass`) and collapsing the wave-function strictly increases
the entropy **iff** the symmetry is non-deterministic in that column; a deterministic
symmetry leaves the entropy at `0` and is therefore reversible. -/
theorem entropy_bornCol_pos_iff_not_isDeterministicCol {U : Fin n → Fin n → ℂ} {a : Fin n}
    (hcol : ∑ k, ‖U k a‖ ^ 2 = 1) :
    0 < entropy (bornCol U a) ↔ ¬ IsDeterministicCol U a := by
  have hnn : 0 ≤ entropy (bornCol U a) :=
    entropy_nonneg (bornCol_nonneg U a) (bornCol_le_one hcol)
  rw [isDeterministicCol_iff_entropy_eq_zero hcol]
  constructor
  · intro hpos hzero
    exact absurd hzero (ne_of_gt hpos)
  · intro hne
    exact lt_of_le_of_ne hnn (fun h => hne h.symm)

end BookProof.SymmetryEntropy
