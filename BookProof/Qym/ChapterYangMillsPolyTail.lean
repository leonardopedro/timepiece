/-
Copyright (c) 2026.  All rights reserved.

# The Gaussian tail of a squared polynomial vanishes

The graph-norm approximation of a polynomial class by the compactly supported core
`gaussCore` splits into two estimates: a *cutoff* term, controlled by smoothness on the
annulus where the cutoff turns off, and a *tail* term, controlled by nothing but the decay of
`γ` at infinity.  This module supplies the second one, which is the estimate the corpus was
missing.

The statement is that the `γ`-integral of `p²` over `{y | R ≤ |y|}` is arbitrarily small.
The proof is the natural one and uses no special structure of `p` beyond square-integrability:
the tails are nested, so their indicator integrals are antitone in `R`; `lintegral_iInf`
commutes the infimum past the integral, and the pointwise infimum is `0` because every point
is eventually outside the tail.  Square-integrability of `p` (`memLp_eval`) is what makes the
total integral finite, which is the hypothesis `lintegral_iInf` needs.
-/
import BookProof.Qym.ChapterYangMillsPolyCore

open MeasureTheory Polynomial
open scoped ENNReal

namespace BookProof.YangMillsPolyTail

open BookProof.YangMillsMehlerLp BookProof.YangMillsHermiteSpectrum

noncomputable section

/-! ## Tails of the real line -/

/-- The outer tail `{y | R ≤ |y|}` of the real line beyond radius `R`. -/
def tailSet (R : ℝ) : Set ℝ := {y : ℝ | R ≤ |y|}

/-- A tail is measurable: it is the preimage of a closed ray under `|·|`. -/
theorem measurableSet_tailSet (R : ℝ) : MeasurableSet (tailSet R) :=
  measurableSet_le measurable_const continuous_abs.measurable

/-- Tails shrink as the radius grows. -/
theorem tailSet_antitone : Antitone tailSet :=
  fun _ _ hRS _ hy => le_trans hRS hy

/-! ## The vanishing tail integral -/

/-- **The `γ`-mass of a squared polynomial on a tail is arbitrarily small.**

For every `ε > 0` there is a radius beyond which the Gaussian integral of `p²` is below `ε`.
The square-integrability of `p` against `gaussMeasure` is the only input; the argument is the
antitone-indicator one, with `lintegral_iInf` supplying the exchange of `⨅` and `∫⁻`. -/
theorem exists_lintegral_tail_lt (p : Polynomial ℝ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ R : ℝ, ∫⁻ y in tailSet R, ENNReal.ofReal ((p.eval y) ^ 2) ∂gaussMeasure < ε := by
  set g : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal ((p.eval y) ^ 2) with hg
  have hgmeas : Measurable g :=
    ENNReal.measurable_ofReal.comp ((Polynomial.continuous p).pow 2).measurable
  have htot : ∫⁻ y, g y ∂gaussMeasure ≠ ∞ := by
    have hfin : ∫⁻ y, ‖p.eval y‖ₑ ^ (2 : ℝ) ∂gaussMeasure < ∞ := by
      simpa using lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2)
        (f := fun y => p.eval y) (μ := gaussMeasure) (by norm_num) (by norm_num)
        (memLp_eval p).2
    rw [show ∫⁻ y, ‖p.eval y‖ₑ ^ (2 : ℝ) ∂gaussMeasure
        = ∫⁻ y, g y ∂gaussMeasure from lintegral_congr fun y => enorm_sq_eq_ofReal_sq _]
      at hfin
    exact hfin.ne
  have hanti : Antitone fun n : ℕ => (tailSet (n : ℝ)).indicator g := by
    intro m n hmn y
    change (tailSet (n : ℝ)).indicator g y ≤ (tailSet (m : ℝ)).indicator g y
    have hsub : tailSet (n : ℝ) ⊆ tailSet (m : ℝ) :=
      tailSet_antitone (by exact_mod_cast hmn)
    by_cases hy : y ∈ tailSet (n : ℝ)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hsub hy)]
    · rw [Set.indicator_of_notMem hy]
      exact zero_le _
  have hpoint : ∀ y : ℝ, ⨅ n : ℕ, (tailSet (n : ℝ)).indicator g y = 0 := by
    intro y
    obtain ⟨n, hn⟩ := exists_nat_gt |y|
    have hnot : y ∉ tailSet (n : ℝ) := by
      simp only [tailSet, Set.mem_setOf_eq, not_le]
      exact_mod_cast hn
    refine le_antisymm ?_ (zero_le _)
    calc ⨅ k : ℕ, (tailSet (k : ℝ)).indicator g y
        ≤ (tailSet (n : ℝ)).indicator g y := iInf_le _ n
      _ = 0 := Set.indicator_of_notMem hnot g
  have hexchange := lintegral_iInf
    (f := fun n : ℕ => (tailSet (n : ℝ)).indicator g)
    (fun n => hgmeas.indicator (measurableSet_tailSet _)) hanti
    (by simpa [tailSet] using htot)
  have hzero : ∫⁻ y, (⨅ n : ℕ, (tailSet (n : ℝ)).indicator g y) ∂gaussMeasure = 0 := by
    rw [lintegral_congr hpoint]
    simp
  have hlt : ⨅ n : ℕ, ∫⁻ y, (tailSet (n : ℝ)).indicator g y ∂gaussMeasure < ε := by
    rw [← hexchange, hzero]
    exact hε
  obtain ⟨n, hn⟩ := iInf_lt_iff.mp hlt
  refine ⟨(n : ℝ), ?_⟩
  rw [← lintegral_indicator (measurableSet_tailSet (n : ℝ)) g]
  exact hn

end

end BookProof.YangMillsPolyTail
