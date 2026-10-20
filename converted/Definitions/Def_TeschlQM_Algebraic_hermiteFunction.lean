/-
prove2.me platform library module `Definitions.Def_TeschlQM_Algebraic_hermiteFunction`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Algebraic_hermiteFunction.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlQM.Algebraic

/-- Teschl (8.42), p. 179: the (physicists') **Hermite polynomial**
`Hₙ(x) = (−1)ⁿ e^{x²} dⁿ/dxⁿ e^{−x²}`. (Mathlib's `Polynomial.hermite` is the probabilists'
family and is not used.) -/
noncomputable def physHermite (n : ℕ) (x : ℝ) : ℝ :=
  (-1) ^ n * Real.exp (x ^ 2) * iteratedDeriv n (fun y : ℝ => Real.exp (-y ^ 2)) x

/-- Teschl (8.41), p. 179: the one-dimensional **Hermite function**
`ψₙ(x) = (2ⁿ n!)^{−1/2} (ω/π)^{1/4} Hₙ(√ω x) e^{−ωx²/2}`. -/
noncomputable def hermiteFunction (ω : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ((1 / Real.sqrt (2 ^ n * n.factorial)) * (ω / Real.pi) ^ (1 / 4 : ℝ) *
    physHermite n (Real.sqrt ω * x) * Real.exp (-(ω * x ^ 2) / 2) : ℝ)

/-- Teschl (8.43), p. 179: the product
`ψ_{n₁,n₂,n₃}(x) = ψ_{n₁}(x₁) ψ_{n₂}(x₂) ψ_{n₃}(x₃)` on `ℝ³`, `n ∈ ℕ₀³`. -/
noncomputable def hermiteProduct (ω : ℝ) (n : Fin 3 → ℕ) (x : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  ∏ j : Fin 3, hermiteFunction ω (n j) (x j)

end TeschlQM.Algebraic
