/-
prove2.me platform library module `Definitions.Def_TeschlQM_MinMax_essentialSpectrum`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_MinMax_essentialSpectrum.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_MinMax_spectrum
import Definitions.Def_TeschlQM_MinMax_eigenspace

namespace TeschlQM.MinMax

/-- Teschl, p. 145: the **discrete spectrum** `σ_d(A)`, the set of all eigenvalues of `A` which
are discrete (isolated) points of the spectrum `σ(A)` and whose eigenspace is finite
dimensional. -/
def discreteSpectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  {z | z ∈ spectrum A ∧ eigenspace A z ≠ ⊥ ∧
    (∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ spectrum A, ‖w - z‖ < ε → w = z) ∧
    FiniteDimensional ℂ (eigenspace A z)}

/-- Teschl, p. 145: the **essential spectrum** `σ_ess(A) = σ(A) \ σ_d(A)`. -/
def essentialSpectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  spectrum A \ discreteSpectrum A

end TeschlQM.MinMax
