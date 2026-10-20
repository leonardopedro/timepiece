/-
prove2.me platform library module `Definitions.Def_Feynman1948_WaveEquation`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_Feynman1948_WaveEquation.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

/-!
# Feynman (1948), Section 6: definitions for the one-dimensional wave equation

R. P. Feynman, Space-Time Approach to Non-Relativistic Quantum Mechanics,
Rev. Mod. Phys. 20, 367 (1948), pp. 374–376, Eqs. (18), (22), (23), (26), (28), (30).
-/

namespace Feynman1948

open Complex MeasureTheory

/-- Eq. (28): the normalizing constant `A = (2πħεi/m)^{1/2}` (principal branch). -/
noncomputable def normalizingFactor (ħ m ε : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * ħ * ε * I / m) ^ (1 / 2 : ℂ)

/-- Eq. (22): the short-time action `S(x_{k+1}, x_k) = (mε/2)((x_{k+1}-x_k)/ε)^2 - ε V(x_{k+1})`
for a particle of mass `m` in the potential `V`, with `x = x_{k+1}` and `y = x_k`. -/
noncomputable def shortTimeAction (m : ℝ) (V : ℝ → ℝ) (ε x y : ℝ) : ℝ :=
  m * ε / 2 * ((x - y) / ε) ^ 2 - ε * V x

/-- Eqs. (18)/(23): one time step of length `ε` of the path-integral evolution,
`ψ(x, t+ε) = ∫ exp((i/ħ) S(x, y)) ψ(y, t) dy / A`. -/
noncomputable def stepEvolution (ħ m : ℝ) (V : ℝ → ℝ) (ε : ℝ) (ψ : ℝ → ℂ) (x : ℝ) : ℂ :=
  (normalizingFactor ħ m ε)⁻¹ *
    ∫ y : ℝ, exp (I * (shortTimeAction m V ε x y : ℂ) / ħ) * ψ y

/-- Right-hand side of Eq. (30): `Hψ = (1/2m)(ħ/i · d/dx)^2 ψ + V ψ = -(ħ²/2m) ψ'' + V ψ`. -/
noncomputable def hamiltonian (ħ m : ℝ) (V : ℝ → ℝ) (ψ : ℝ → ℂ) (x : ℝ) : ℂ :=
  -((ħ : ℂ) ^ 2 / (2 * m)) * deriv (deriv ψ) x + (V x : ℂ) * ψ x

/-- Footnote 13 regularization of the Gaussian moments of Eq. (26): `ħ` is replaced by
`ħ(1 - iδ)`, giving `∫ ξⁿ exp(i m ξ² / (2 ħ (1 - iδ) ε)) dξ`. -/
noncomputable def regularizedMoment (ħ m ε δ : ℝ) (n : ℕ) : ℂ :=
  ∫ ξ : ℝ, (ξ : ℂ) ^ n * exp (I * m * (ξ : ℂ) ^ 2 / (2 * (ħ * (1 - I * δ)) * ε))

end Feynman1948
