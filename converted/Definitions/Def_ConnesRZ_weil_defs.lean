/-
prove2.me platform library module `Definitions.Def_ConnesRZ_weil_defs`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_ConnesRZ_weil_defs.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

open Complex MeasureTheory

noncomputable section

namespace ConnesRZ

/-- Test functions on the idele class group component `ℝ*₊`, written additively via
`u = e^t`: smooth, compactly supported, complex valued functions on `ℝ`. -/
def IsTest (g : ℝ → ℂ) : Prop := ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g

/-- Connes (12): `ĥ(z) = ∫_{C_k} h(u) |u|^z d*u`, written in the coordinate `u = e^t`
and shifted by `1/2` so that `z` is the variable of the zeta function:
`ĝ(z) = ∫_ℝ g(t) e^{(z - 1/2) t} dt`. -/
def mellinHat (g : ℝ → ℂ) (z : ℂ) : ℂ := ∫ t : ℝ, g t * Complex.exp ((z - 1 / 2) * t)

/-- The involution `h*(u) = conj (h (u⁻¹))`, written additively. -/
def starInv (g : ℝ → ℂ) : ℝ → ℂ := fun t => starRingEnd ℂ (g (-t))

/-- Convolution on the group `ℝ*₊ ≃ ℝ`. -/
def conv (g₁ g₂ : ℝ → ℂ) : ℝ → ℂ := fun t => ∫ s : ℝ, g₁ s * g₂ (t - s)

/-- A zero of the Riemann zeta function in the critical strip. -/
def IsCriticalZero (s : ℂ) : Prop := riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1

/-- The multiplicity of `s` as a zero of the Riemann zeta function. -/
def zeroMult (s : ℂ) : ℕ := analyticOrderNatAt riemannZeta s

/-- The finite (non archimedean) part of the Weil distribution: the sum over prime powers
`Σ_{n ≥ 2} Λ(n) n^{-1/2} (g (log n) + g (-log n))`. -/
def primeSum (g : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
    (g (Real.log n) + g (-Real.log n))

/-- The archimedean local term of the Weil distribution:
`(1/2π) ∫_ℝ ĝ(1/2 + i r) (Re ψ(1/4 + i r/2) - log π) dr`, where `ψ = Γ'/Γ`. -/
def archTerm (g : ℝ → ℂ) : ℂ :=
  ((1 : ℂ) / (2 * Real.pi)) * ∫ r : ℝ, mellinHat g (1 / 2 + I * r) *
    ((((logDeriv Complex.Gamma (1 / 4 + I * r / 2)).re - Real.log Real.pi : ℝ) : ℂ))

/-- The Weil distribution evaluated at a test function `g`: the arithmetic side of the
explicit formula, namely the two pole terms, minus the prime powers term, plus the
archimedean term. -/
def weilDistribution (g : ℝ → ℂ) : ℂ :=
  mellinHat g 0 + mellinHat g 1 - primeSum g + archTerm g

/-- The spectral side: the sum of `ĝ(ρ)` over the zeros `ρ` of zeta in the critical strip,
each counted with its multiplicity. -/
def zeroSum (g : ℝ → ℂ) : ℂ :=
  ∑' ρ : {s : ℂ // IsCriticalZero s}, (zeroMult ρ.1 : ℂ) * mellinHat g ρ.1

end ConnesRZ
