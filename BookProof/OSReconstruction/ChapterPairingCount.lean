import Mathlib
import BookProof.OSReconstruction.GaussianMoments

/-!
# Chapter PairingCount — counting pairings from the Wick recursion

The seventeenth C3 slice (`cftproof.md`) derives the five- and six-point moments uniformly in
the number of fields and records that no closed form for the number of pairings at arbitrary
`M` is extracted on `shellLaw`.  This chapter takes the counting step: specializing the existing
`wickSum_rec` bijection to the constant weight one gives a recursion for `pairingSet s` by the
partner of its least element.

The recursion is then iterated by strong induction on the cardinality to give the closed form
`(2m−1)‼` for an even-cardinality set, and in particular for `pairings (2m)`.  Odd-cardinality sets
carry no pairings, proved from `Equiv.Perm.two_dvd_card_support`.  This is a count of the
`GaussianMoments` pairing set, not an `M`-uniform δ-form algorithm on `shellLaw`.
-/

noncomputable section

namespace BookProof.PairingCount

open BookProof.OSReconstruction
open scoped Nat

/-- With all edge weights one, the Wick sum is exactly the number of pairings of `s`. -/
theorem wickSum_one_eq_card {M : ℕ} (s : Finset (Fin M)) :
    wickSum (fun _ _ : Fin M => (1 : ℝ)) s = (pairingSet s).card := by
  simp [wickSum]

/-- Counting recursion: pick the least site, sum over its possible partners, and count the
    pairings of the remaining sites.  This is `wickSum_rec` at the constant weight one. -/
theorem card_pairingSet_rec {M : ℕ} {s : Finset (Fin M)} (hs : s.Nonempty) :
    (pairingSet s).card = ∑ b ∈ s.erase (s.min' hs),
      (pairingSet ((s.erase (s.min' hs)).erase b)).card := by
  have h := wickSum_rec (fun _ _ : Fin M => (1 : ℝ)) hs
  have h' : ((pairingSet s).card : ℝ) =
      ∑ b ∈ s.erase (s.min' hs), ((pairingSet ((s.erase (s.min' hs)).erase b)).card : ℝ) := by
    simpa [wickSum] using h
  exact_mod_cast h'

/-- A set of odd cardinality has no pairings: an involution partitions its support into pairs. -/
theorem pairingSet_eq_empty_of_odd_card {M : ℕ} {s : Finset (Fin M)} (h : Odd s.card) :
    pairingSet s = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro σ hσ
  rw [mem_pairingSet] at hσ
  have h2 := Equiv.Perm.two_dvd_card_support (σ := σ) (by simpa [pow_two] using hσ.1)
  rw [hσ.2] at h2
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h2
  omega

/-- The number of pairings of an even-cardinality set is `(s.card − 1)‼`, the double factorial
    of the number of remaining partners of the least site. -/
theorem card_pairingSet_eq_doubleFactorial {M : ℕ} (s : Finset (Fin M))
    (he : Even s.card) : (pairingSet s).card = (s.card - 1)‼ := by
  classical
  generalize hn : s.card = n
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases hs0 : s = ∅
    · subst s
      subst n
      simp [pairingSet_empty]
    · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.2 hs0
      rw [card_pairingSet_rec hsne]
      have hcard_univ : (s.card - 1) = (s.erase (s.min' hsne)).card := by
        rw [Finset.card_erase_of_mem (Finset.min'_mem s hsne)]
      have hterm : ∀ b ∈ s.erase (s.min' hsne),
          (pairingSet ((s.erase (s.min' hsne)).erase b)).card =
            (((s.erase (s.min' hsne)).erase b).card - 1)‼ := by
        intro b hb
        have hpos : 0 < s.card := Finset.card_pos.2 hsne
        have hlt : ((s.erase (s.min' hsne)).erase b).card < s.card := by
          rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.min'_mem s hsne)]
          omega
        have hsub : ((s.erase (s.min' hsne)).erase b).card = s.card - 2 := by
          rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.min'_mem s hsne)]
          simp [Nat.sub_sub]
        have heven_small : Even ((s.erase (s.min' hsne)).erase b).card := by
          rw [hsub]
          obtain ⟨k, hk⟩ := he
          refine ⟨k - 1, ?_⟩
          omega
        have hlt' : ((s.erase (s.min' hsne)).erase b).card < n := by
          rw [← hn]
          exact hlt
        exact ih _ hlt' _ heven_small rfl
      have hsum : (∑ b ∈ s.erase (s.min' hsne),
          (pairingSet ((s.erase (s.min' hsne)).erase b)).card) =
          (s.erase (s.min' hsne)).card * (s.card - 3)‼ := by
        calc
          (∑ b ∈ s.erase (s.min' hsne),
              (pairingSet ((s.erase (s.min' hsne)).erase b)).card) =
              ∑ b ∈ s.erase (s.min' hsne), (s.card - 3)‼ := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [hterm b hb]
            congr 1
            rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.min'_mem s hsne)]
            omega
          _ = (s.erase (s.min' hsne)).card * (s.card - 3)‼ := by simp
      rw [hsum, ← hcard_univ, ← hn]
      by_cases hsmall : s.card ≤ 2
      · have hpos' : 0 < s.card := Finset.card_pos.2 hsne
        have hs2 : s.card = 2 := by
          have hne1 : s.card ≠ 1 := by
            intro h1
            obtain ⟨k, hk⟩ := he
            omega
          omega
        rw [hs2]
        norm_num [Nat.doubleFactorial]
      · have hge : 3 ≤ s.card := by omega
        have hdf : (s.card - 1)‼ = (s.card - 1) * (s.card - 3)‼ := by
          calc
            (s.card - 1)‼ = (s.card - 3 + 2)‼ := by
              rw [show s.card - 3 + 2 = s.card - 1 by omega]
            _ = (s.card - 3 + 2) * (s.card - 3)‼ := Nat.doubleFactorial_add_two (s.card - 3)
            _ = (s.card - 1) * (s.card - 3)‼ := by
              rw [show s.card - 3 + 2 = s.card - 1 by omega]
        rw [hdf]

/-- Closed form on the full even index set: the number of perfect matchings of `2m` sites is
    `(2m − 1)‼`. -/
theorem card_pairings_even (m : ℕ) : (pairings (2 * m)).card = (2 * m - 1)‼ := by
  rw [← pairingSet_univ_even]
  have h := card_pairingSet_eq_doubleFactorial (Finset.univ : Finset (Fin (2 * m)))
    (by refine ⟨m, ?_⟩; simp [two_mul])
  simpa using h

end BookProof.PairingCount
