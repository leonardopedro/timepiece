/-
prove2.me platform library module `Definitions.Def_TeschlQM_Algebraic_IsHarmonicOscillator`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Algebraic_IsHarmonicOscillator.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_Algebraic_gaussCore

namespace TeschlQM.Algebraic

open MeasureTheory

/-- The Laplacian `Δf(x) = Σⱼ ∂²f/∂xⱼ²(x)` of `f : ℝⁿ → ℂ`, the sum of the second (real) partial
derivatives along the standard unit vectors `eⱼ`. -/
noncomputable def laplacian {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∑ j : Fin n, iteratedFDeriv ℝ 2 f x (fun _ => EuclideanSpace.single j (1 : ℝ))

/-- Teschl (8.33), p. 178, with `H₀ = −Δ` (units `ℏ = 1`, `m = 1/2`, p. 167): the differential
expression of the harmonic oscillator, `(H f)(x) = −Δf(x) + ω²|x|² f(x)`. -/
noncomputable def oscillatorAction {n : ℕ} (ω : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  fun x => -laplacian f x + ((ω ^ 2 * ‖x‖ ^ 2 : ℝ) : ℂ) * f x

/-- Teschl (8.33)–(8.34), p. 178: `H` is the three-dimensional **harmonic oscillator**
`H = H₀ + ω²x²` on the domain `𝔇_ω = span{x^α e^{−ω|x|²/2} | α ∈ ℕ₀³} ⊆ L²(ℝ³)`: its domain is
`𝔇_ω`, and every `ψ ∈ 𝔇(H)` is (the class of) a function `f` in the span of the
`x^α e^{−ω|x|²/2}` with `Hψ` the class of `−Δf + ω²|x|²f`. This determines `H` uniquely. -/
def IsHarmonicOscillator (ω : ℝ)
    (H : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) →ₗ.[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))) : Prop :=
  H.domain = core 3 ω ∧
    ∀ ψ : H.domain, ∃ f ∈ coreFun 3 ω,
      ((ψ : Lp ℂ 2 volume) : EuclideanSpace ℝ (Fin 3) → ℂ) =ᵐ[volume] f ∧
        ((H ψ : Lp ℂ 2 volume) : EuclideanSpace ℝ (Fin 3) → ℂ) =ᵐ[volume] oscillatorAction ω f

end TeschlQM.Algebraic
