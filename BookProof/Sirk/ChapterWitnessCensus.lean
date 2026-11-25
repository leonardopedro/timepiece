import Mathlib
import BookProof.Sirk.ChapterStrongCouplingWitness

/-!
# Chapter WitnessCensus — the U5 search over the recorded `unfer` campaign

U5 asks for **one** strong coupling whose certified mass exceeds its whole error budget.
This module records the search actually performed by `../unfer`: the gauge-fixed campaign
`fock_sirk/tests/fixtures/mass_gap_campaign/` emits 20 rows (10 distinct solves at
`g ∈ {0, 1/2, 1, 2, 3}`, `m ∈ {10, 12}`, each cross-checked at `N = 6, 8`), and **every**
row has `certified_positive: false`.  The numbers below are transcribed verbatim from the
`certified_mass_gap` lines; `gap = θᵒ − θᵉ`, `delta = δᵒ + δᵉ`, `lo = gap − delta`.

* `census_lo_le_zero` — every row's certified lower end is ≤ 0, so neither the T6
  stopping rule `lo > 0` nor the U5 margin `η ≤ Mhat − E_gap` is met by a single row.
* `no_positive_margin` — no positive `η` can be justified from any row's margin.
* `latticeEraDiagnostic` — the one positive window `[1.932, 2.043]` is the `g = 2, m = 4`
  lattice-era solve (`qcdG2M4Row` in `ChapterSirkGapTable`), emitted with
  `physical: false`; `diagnostic_not_in_campaign` keeps it separate from the census.

**This is a search result, not a no-gap theorem.**  The campaign's exact truncated gaps are
positive and grow with `g` (≈ 0.09 at `g = 1`, ≈ 1.24 at `g = 2`); what fails is the
*certificate*: the squeezed ground makes the Parlett residuals large, so the assembled
window is far too wide to certify positivity at these Krylov orders.  U5's answer is
therefore still open — it needs a solve whose budget is smaller than its signal — and
this module only rules out the rows already on record.  It credits no physical witness
and makes no claim about the continuum operator.
-/

noncomputable section

namespace BookProof.WitnessCensus

/-- One emitted campaign row: coupling, Krylov order, assembled T6 numbers. -/
structure CampaignRow where
  g : ℝ
  m : ℕ
  gap : ℝ
  lo : ℝ
  hi : ℝ
  delta : ℝ

/-- The ten distinct solves of the campaign.  Each appears twice in the manifest, once
    for `N = 6` and once for `N = 8`, with identical certified numbers. -/
def campaignRows : Fin 10 → CampaignRow := ![
  { g := 0, m := 10, gap := -3.942061121975371e-9,
    lo := -1.580887418330829, hi := 1.5808874104467068, delta := 1.580887414388768 },
  { g := 0, m := 12, gap := -9.335289854472961e-7,
    lo := -1.4700256140284982, hi := 1.4700237469705273, delta := 1.4700246804995127 },
  { g := 0.5, m := 10, gap := -0.1312633945350936,
    lo := -3.6235624133252284, hi := 3.361035624255041, delta := 3.492299018790135 },
  { g := 0.5, m := 12, gap := -0.13593681325871088,
    lo := -3.6565441397880427, hi := 3.3846705132706205, delta := 3.5206073265293316 },
  { g := 1, m := 10, gap := -0.5332198516728923,
    lo := -7.484695182649809, hi := 6.418255479304025, delta := 6.951475330976917 },
  { g := 1, m := 12, gap := -0.5714596360669375,
    lo := -8.009312275650972, hi := 6.866393003517097, delta := 7.437852639584035 },
  { g := 2, m := 10, gap := -2.118387437764381,
    lo := -24.862480747282433, hi := 20.625705871753674, delta := 22.744093309518053 },
  { g := 2, m := 12, gap := -2.2811234468912938,
    lo := -27.703393111214584, hi := 23.141146217432, delta := 25.42226966432329 },
  { g := 3, m := 10, gap := -4.093112781274366,
    lo := -56.19181526790159, hi := 48.00558970535286, delta := 52.098702486627225 },
  { g := 3, m := 12, gap := -4.330055047862283,
    lo := -61.98781961662932, hi := 53.327709520904754, delta := 57.657764568767035 }
]

/-- The U5 margin `Mhat − E_gap` is the campaign's `gap − delta`.  It is strictly negative
    on every row: the measured Ritz difference is already ≤ 0 and the width is positive.
    (The emitter's `lo` is the f64 rounding of this difference, so the transcribed decimal
    `lo` is not exactly equal to the exact real subtraction; only the sign is needed.) -/
theorem row_margin_le_zero (i : Fin 10) : (campaignRows i).gap - (campaignRows i).delta ≤ 0 := by
  fin_cases i <;> norm_num [campaignRows]

/-- Every assembled width is nonnegative. -/
theorem row_delta_nonneg (i : Fin 10) : 0 ≤ (campaignRows i).delta := by
  fin_cases i <;> norm_num [campaignRows]

/-- **Census.** No recorded gauge-fixed campaign row has a positive certified lower end. -/
theorem census_lo_le_zero (i : Fin 10) : (campaignRows i).lo ≤ 0 := by
  fin_cases i <;> norm_num [campaignRows]

/-- The measured Ritz differences themselves are not positive at these orders. -/
theorem census_gap_le_zero (i : Fin 10) : (campaignRows i).gap ≤ 0 := by
  fin_cases i <;> norm_num [campaignRows]

/-- **No U5 margin from the campaign.**  The witness field
    `η ≤ Mhat − Ebar_gap` is the campaign's `η ≤ gap − delta`; no positive rational margin
    can meet it on any recorded row. -/
theorem no_positive_margin (i : Fin 10) (η : ℝ) (hη : 0 < η)
    (h : η ≤ (campaignRows i).gap - (campaignRows i).delta) : False := by
  have hmargin := row_margin_le_zero i
  linarith

/-- The one positive window on record is the lattice-era `g = 2, m = 4` solve of
    `ChapterSirkGapTable.qcdG2M4Row`, emitted with `physical: false`. -/
def latticeEraDiagnostic : CampaignRow :=
  { g := 2, m := 4, gap := 1.9875, lo := 1.932, hi := 2.043, delta := 0.0555 }

/-- Its lower end *is* positive — which is why it must not be confused with a census row. -/
theorem diagnostic_lo_pos : 0 < latticeEraDiagnostic.lo := by
  norm_num [latticeEraDiagnostic]

/-- The diagnostic is not one of the gauge-fixed campaign rows. -/
theorem diagnostic_not_in_campaign (i : Fin 10) : campaignRows i ≠ latticeEraDiagnostic := by
  intro h
  fin_cases i <;> norm_num [campaignRows, latticeEraDiagnostic] at h

/-- The diagnostic's own window is valid arithmetic (`lo = gap − delta`), but positivity
    of a *truncated, non-physical* window is not a U5 witness. -/
theorem diagnostic_row_lo_eq : latticeEraDiagnostic.gap - latticeEraDiagnostic.delta =
    latticeEraDiagnostic.lo := by
  norm_num [latticeEraDiagnostic]

end BookProof.WitnessCensus
