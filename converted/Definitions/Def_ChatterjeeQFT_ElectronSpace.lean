/-
prove2.me platform library module `Definitions.Def_ChatterjeeQFT_ElectronSpace`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_ChatterjeeQFT_ElectronSpace.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_ChatterjeeQFT_MassShell
import Definitions.Def_ChatterjeeQFT_SL2C

/-!
# The one-particle Hilbert space of an electron

Following S. Chatterjee, *Lectures on Quantum Field Theory*, Lecture 25.
-/

open MeasureTheory Matrix

namespace ChatterjeeQFT

/-- The matrix weight `V_p^{-2}` occurring in the electron inner product. -/
noncomputable def electronWeight (m : ℝ) (p : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (pureBoost m p * pureBoost m p)⁻¹

/-- The pointwise pairing `ψ(p)† V_p^{-2} φ(p)` of two spinor wave functions. -/
noncomputable def electronPairing (m : ℝ) (ψ φ : (Fin 4 → ℝ) → (Fin 2 → ℂ))
    (p : Fin 4 → ℝ) : ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2, (starRingEnd ℂ) (ψ p i) * electronWeight m p i j * φ p j

/-- The electron inner product `(ψ, φ) = ∫_{X_m} dλ_m(p) ψ(p)† V_p^{-2} φ(p)`. -/
noncomputable def electronInner (m : ℝ) (ψ φ : (Fin 4 → ℝ) → (Fin 2 → ℂ)) : ℂ :=
  ∫ p, electronPairing m ψ φ p ∂(massShellMeasure m)

/-- The one-particle state space of an electron of mass `m`: the `C²`-valued functions on the
mass shell that are measurable and have finite norm for the weighted inner product,
`∫_{X_m} dλ_m(p) ψ(p)† V_p^{-2} ψ(p) < ∞`.  The Hilbert space `H = L²(X_m, dλ_m, C²)` is this
space with functions agreeing `λ_m`-almost everywhere identified. -/
noncomputable def ElectronL2 (m : ℝ) : Set ((Fin 4 → ℝ) → (Fin 2 → ℂ)) :=
  {ψ | AEStronglyMeasurable ψ (massShellMeasure m) ∧
    ∫⁻ p, ENNReal.ofReal (electronPairing m ψ ψ p).re ∂(massShellMeasure m) < ⊤}

/-- The action of the Poincaré group on electron wave functions:
`(U(a, A)ψ)(p) = e^{i(a,p)} A ψ(κ(A)⁻¹ p)` for `A ∈ SL(2,C)`. -/
noncomputable def electronAction (a : Fin 4 → ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (ψ : (Fin 4 → ℝ) → (Fin 2 → ℂ)) : (Fin 4 → ℝ) → (Fin 2 → ℂ) :=
  fun p => Complex.exp (Complex.I * (minkowskiInner a p : ℂ)) • (A *ᵥ ψ (kappa A⁻¹ p))

end ChatterjeeQFT
