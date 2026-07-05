import Mathlib
import BookProof.ChapterB
import PnpProof.Kopperman

/-!
# §0 substrate glue — instantiating Chapter B at the Kopperman substrate

Work-package **N5** of `FORMALIZATION_ROADMAP.md`.  The Kopperman/Mehler
formalism is already formalized in `PnpProof` (`Kopperman.lean` substrate bundle,
`SphereGaussian.lean` Mehler chain, `FunctionSpace.lean` L²/√p layer).  Here we
discharge the §0 S2 reuse mandate by specializing Chapter B's generic Born
parametrization results to the concrete substrate measure `unitMeasure`
(= `volume.restrict (Icc 0 1)`), whose L² space is the Kopperman `Substrate`.
-/

open MeasureTheory

namespace BookProof.Substrate

/-- **Chapter B.1 at the substrate.** Every probability density on the Kopperman
substrate measure `unitMeasure` is the Born rule `|Ψ|²` of a unit wave-function
`Ψ` in the complex L² space over the substrate. -/
theorem substrate_born_forward (p : ℝ → ℝ) (hmeas : Measurable p)
    (hnonneg : ∀ x, 0 ≤ p x) (hint : ∫ x, p x ∂PnpProof.unitMeasure = 1) :
    ∃ Ψ : Lp ℂ 2 PnpProof.unitMeasure,
      ‖Ψ‖ = 1 ∧ ∀ᵐ x ∂PnpProof.unitMeasure, ‖(Ψ : ℝ → ℂ) x‖ ^ 2 = p x :=
  BookProof.ChapterB.born_forward PnpProof.unitMeasure p hmeas hnonneg hint

/-- **Chapter B.1 backward at the substrate.** Conversely, `|Ψ|²` of a unit
wave-function over the substrate is a probability density. -/
theorem substrate_born_backward (Ψ : Lp ℂ 2 PnpProof.unitMeasure) (hΨ : ‖Ψ‖ = 1) :
    (∀ x, 0 ≤ ‖(Ψ : ℝ → ℂ) x‖ ^ 2) ∧
      ∫ x, ‖(Ψ : ℝ → ℂ) x‖ ^ 2 ∂PnpProof.unitMeasure = 1 :=
  BookProof.ChapterB.born_backward PnpProof.unitMeasure Ψ hΨ

/-- **Chapter B.2 at the substrate.** Every unit wave-function over the substrate
is a member of a Hilbert basis — the book's `Ψ = 𝒰 e₀`. -/
theorem substrate_unit_vector_extends (Ψ : Lp ℂ 2 PnpProof.unitMeasure) (hΨ : ‖Ψ‖ = 1) :
    ∃ (ι : Type) (b : HilbertBasis ι ℂ (Lp ℂ 2 PnpProof.unitMeasure)) (i : ι), b i = Ψ :=
  BookProof.ChapterB.unit_vector_extends Ψ hΨ

end BookProof.Substrate
