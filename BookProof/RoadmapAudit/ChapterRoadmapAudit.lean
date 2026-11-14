/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle
-/
import BookProof.RoadmapAudit.ChapterRoadmapAuditImports
import BookProof.RoadmapAudit.ChapterRoadmapAuditPart1
import BookProof.RoadmapAudit.ChapterRoadmapAuditPart2
import BookProof.RoadmapAudit.ChapterRoadmapAuditPart3
import BookProof.RoadmapAudit.ChapterRoadmapAuditPart4
import BookProof.RoadmapAudit.ChapterRoadmapAuditPart5
import BookProof.RoadmapAudit.ChapterRoadmapAuditPart6
import BookProof.RoadmapAudit.ChapterRoadmapAuditPart7
import BookProof.RoadmapAudit.ChapterRoadmapAuditPart8

/-!
# Roadmap headline certificate

This module turns the roadmap's final prose-only hygiene audit into a checked
Lean artifact.  The aggregate theorem below simultaneously exposes three
representative mathematical headlines from independent work packages:

* the two-dimensional pure-state obstruction from the Gleason chapter;
* the Cauchy–Riemann characterization of holomorphicity on open sets;
* unitarity of the concrete Majorana–Fourier boost block.

The imported Count-Sketch, Misra–Gries, and SIRK headlines are also checked by the
`#audit_axioms` commands in `ChapterRoadmapAuditPart1`–`Part8` (the ledger is sliced so that
Lake elaborates the eight slices in parallel; the split is mechanical and the directive order is
unchanged).  The command is a memoized `#print axioms` (see
`BookProof/RoadmapAudit/AxiomAudit.lean`): the stock command re-walks the shared dependency
closure on every call, which is what made the unsliced file take ~25 minutes to build.
-/

namespace BookProof.ChapterRoadmapAudit

open BookProof.AxiomAudit

open Matrix

/-
A single kernel-checked certificate collecting representative headline
results whose final roadmap audit had previously only been recorded in prose.
-/
theorem roadmap_headline_certificate :
    (¬ ∃ ρ, BookProof.ChapterB4.IsPureState ρ ∧
      Matrix.trace (ρ * BookProof.ChapterB4.P1) = 1 / 2 ∧
      Matrix.trace (ρ * BookProof.ChapterB4.P2) = 1 / 2) ∧
    (∀ (f : ℂ → ℂ) (s : Set ℂ), IsOpen s →
      (∀ z ∈ s, DifferentiableAt ℝ f z) →
      ((∀ z ∈ s, fderiv ℝ f z Complex.I =
          Complex.I • fderiv ℝ f z 1) ↔ AnalyticOn ℂ f s)) ∧
    (∀ (m q : ℝ), 0 ≤ m → 0 < q →
      ∀ n : Fin 3 → ℝ, (∑ i, (n i) ^ 2) = 1 →
      (BookProof.ChapterMajoranaFourier.boostBlock
          (BookProof.ChapterMajoranaFourier.boostC m q)
          (BookProof.ChapterMajoranaFourier.boostS m q)
          (BookProof.ChapterMajoranaFourier.Aop n))ᴴ *
        BookProof.ChapterMajoranaFourier.boostBlock
          (BookProof.ChapterMajoranaFourier.boostC m q)
          (BookProof.ChapterMajoranaFourier.boostS m q)
          (BookProof.ChapterMajoranaFourier.Aop n) = 1) := by
  refine ⟨BookProof.ChapterB4.no_pure_state_satisfies_both, ?_, ?_⟩
  · exact fun _ _ hs hf ↦
      BookProof.ChapterHolomorphic.cauchyRiemann_iff_analyticOn hs hf
  · exact fun m q hm hq n hn ↦
      BookProof.ChapterMajoranaFourier.majoranaFourier_boostBlock_unitary
        m q hm hq n hn

/-
A second checked certificate covers the final finite Born-fiber and sign-gauge
integration wave.  It records both the complete spectrum of possible fiber
cardinalities and the index-two parity law for the orientation character.
-/
theorem roadmap_finite_born_certificate :
    (∀ (n c : ℕ),
      (∃ p : ↥(stdSimplex ℝ (Fin n)),
          Nat.card ↥(BookProof.ChapterFreeFieldBornQuotient.bornMapSphere n ⁻¹' {p}) = c) ↔
        ∃ k, 1 ≤ k ∧ k ≤ n ∧ c = 2 ^ k) ∧
    (∀ (n : ℕ) (b₁ b₂ : Fin n → Bool),
      BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix
          (fun k => xor (b₁ k) (b₂ k)) ∈
          Matrix.specialOrthogonalGroup (Fin n) ℝ ↔
        (BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix b₁ ∈
            Matrix.specialOrthogonalGroup (Fin n) ℝ ↔
         BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix b₂ ∈
            Matrix.specialOrthogonalGroup (Fin n) ℝ)) := by
  constructor
  · intro n c
    exact BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_achievable_iff
  · intro n b₁ b₂
    exact
      BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_xor_iff
        b₁ b₂

-- The two aggregate theorems above, audited here because they are declared in this module.
#audit_axioms roadmap_headline_certificate
#audit_axioms roadmap_finite_born_certificate

end BookProof.ChapterRoadmapAudit
