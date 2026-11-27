import Mathlib
import BookProof.OSReconstruction.GaussianMoments

/-!
# Chapter PairingCount — counting pairings from the Wick recursion

The seventeenth C3 slice (`cftproof.md`) derives the five- and six-point moments uniformly in
the number of fields and records that no closed form for the number of pairings at arbitrary
`M` is extracted on `shellLaw`.  This chapter takes the counting step: specializing the existing
`wickSum_rec` bijection to the constant weight one gives a recursion for `pairingSet s` by the
partner of its least element.

This is a recursion for the count, not the closed form `(2m−1)‼` itself, and it is on the
`GaussianMoments` pairing set rather than on a new `shellLaw` algorithm.
-/

noncomputable section

namespace BookProof.PairingCount

open BookProof.OSReconstruction

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

end BookProof.PairingCount
