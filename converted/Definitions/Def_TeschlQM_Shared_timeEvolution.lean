/-
prove2.me platform library module `Definitions.Def_TeschlQM_Shared_timeEvolution`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Shared_timeEvolution.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_Shared_spectralMeasure

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TeschlQM.Shared

open Classical in
/-- Teschl, p. 90, (3.17), (3.20): for a bounded Borel function `f`, `P(f) = ∫_ℝ f(λ) dP(λ)` as a
bounded operator on `ℌ`: the bounded operator `T` with `⟨ψ, Tψ⟩ = ∫_ℝ f(λ) dμ_ψ(λ)` for all
`ψ ∈ ℌ` (over `ℂ` a bounded operator is determined by its quadratic form, so there is at most
one); the zero operator if there is none, which never happens for a projection-valued measure
and a bounded Borel `f`. -/
noncomputable def boundedSpectralIntegral {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) : H →L[ℂ] H :=
  if h : ∃ T : H →L[ℂ] H, ∀ ψ : H, ⟪ψ, T ψ⟫_ℂ = ∫ x, f x ∂spectralMeasure P ψ then h.choose
  else 0

/-- Teschl, p. 123, Sec. 5.1: the **time evolution** `U(t) = exp(−itA)` of the self-adjoint
operator `A = ∫ λ dP(λ)`, defined by the functional calculus as `P(f_t)` with the bounded
continuous function `f_t(λ) = e^{−itλ}`. In particular `e^{itA} = timeEvolution P (−t)`. -/
noncomputable def timeEvolution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : Set ℝ → (H →L[ℂ] H)) (t : ℝ) : H →L[ℂ] H :=
  boundedSpectralIntegral P (fun x : ℝ => Complex.exp (-(Complex.I * (t : ℂ) * (x : ℂ))))

end TeschlQM.Shared
