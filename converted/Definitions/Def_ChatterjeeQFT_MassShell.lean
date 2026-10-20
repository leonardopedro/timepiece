/-
prove2.me platform library module `Definitions.Def_ChatterjeeQFT_MassShell`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_ChatterjeeQFT_MassShell.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_ChatterjeeQFT_Minkowski

/-!
# The mass shell, the Lorentz-invariant measure, and the one-particle boson space

Following S. Chatterjee, *Lectures on Quantum Field Theory*, Lectures 9-11.
-/

open MeasureTheory Matrix

namespace ChatterjeeQFT

/-- The relativistic energy `ω_q = √(m² + |q|²)` of a three-momentum `q`. -/
noncomputable def omega (m : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (m ^ 2 + (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2))

/-- The parametrisation of the mass shell by three-momentum: `q ↦ (ω_q, q)`. -/
noncomputable def massShellEmb (m : ℝ) (q : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![omega m q, q 0, q 1, q 2]

/-- The mass shell `X_m = {p ∈ R^{1,3} : p² = m², p⁰ ≥ 0}`. -/
def massShell (m : ℝ) : Set (Fin 4 → ℝ) :=
  {p | minkowskiSq p = m ^ 2 ∧ 0 ≤ p 0}

/-- The Lorentz-invariant measure `λ_m` on the mass shell `X_m`, viewed as a Borel measure on
`R^{1,3}` carried by `X_m`.  It is the push-forward under `q ↦ (ω_q, q)` of the measure
`d³q / ((2π)³ 2ω_q)` on `R³`, so that
`∫_{X_m} f dλ_m = ∫_{R³} f(ω_q, q) d³q / ((2π)³ 2ω_q)`. -/
noncomputable def massShellMeasure (m : ℝ) : Measure (Fin 4 → ℝ) :=
  Measure.map (massShellEmb m)
    ((volume : Measure (Fin 3 → ℝ)).withDensity fun q =>
      ENNReal.ofReal (1 / ((2 * Real.pi) ^ 3 * (2 * omega m q))))

/-- The one-particle Hilbert space of a massive scalar boson of mass `m`:
`H = L²(X_m, dλ_m)`. -/
noncomputable abbrev bosonSpace (m : ℝ) : Type := Lp ℂ 2 (massShellMeasure m)

/-- The Poincaré action on scalar wave functions on the mass shell:
`(U(a, L)ψ)(p) = e^{i(a,p)} ψ(L⁻¹p)`. -/
noncomputable def bosonAction (a : Fin 4 → ℝ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (ψ : (Fin 4 → ℝ) → ℂ) : (Fin 4 → ℝ) → ℂ :=
  fun p => Complex.exp (Complex.I * (minkowskiInner a p : ℂ)) * ψ (L⁻¹ *ᵥ p)

end ChatterjeeQFT
