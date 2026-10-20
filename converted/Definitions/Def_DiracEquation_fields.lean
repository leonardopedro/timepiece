/-
prove2.me platform library module `Definitions.Def_DiracEquation_fields`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_DiracEquation_fields.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_DiracAlgebra_core

namespace DiracEquation

open Matrix

/-- The partial derivative `∂_μ ψ` of a four-component spinor field on `ℝ⁴`, taken in the
direction of the `μ`-th coordinate axis. -/
noncomputable def pd (psi : (Fin 4 → ℝ) → (Fin 4 → ℂ)) (mu : Fin 4) (x : Fin 4 → ℝ) :
    Fin 4 → ℂ :=
  fderiv ℝ psi x (Pi.single mu 1)

/-- The second partial derivative `∂_ν ∂_μ ψ`. -/
noncomputable def pd2 (psi : (Fin 4 → ℝ) → (Fin 4 → ℂ)) (mu nu : Fin 4) (x : Fin 4 → ℝ) :
    Fin 4 → ℂ :=
  pd (fun y => pd psi mu y) nu x

/-- `IsDiracSolution g m ψ` says that `ψ` satisfies the Dirac equation `(i γ^μ ∂_μ - m) ψ = 0`
for the gamma matrices `g` and mass `m`, in natural units `ħ = c = 1`. -/
def IsDiracSolution (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (m : ℝ)
    (psi : (Fin 4 → ℝ) → (Fin 4 → ℂ)) : Prop :=
  ∀ x, ∑ mu, Complex.I • (g mu).mulVec (pd psi mu x) = (m : ℂ) • psi x

/-- `IsKleinGordonSolution m ψ` says that every component of `ψ` satisfies the Klein–Gordon
equation `(∂_μ ∂^μ + m²) ψ = 0`, where `∂_μ ∂^μ = η^{μν} ∂_μ ∂_ν`. -/
def IsKleinGordonSolution (m : ℝ) (psi : (Fin 4 → ℝ) → (Fin 4 → ℂ)) : Prop :=
  ∀ x, (∑ mu, eta mu mu • pd2 psi mu mu x) + ((m : ℂ) ^ 2) • psi x = 0

/-- The positive-frequency plane wave `ψ(x) = u e^{i p_μ x^μ}` with polarization `u`. -/
noncomputable def planeWave (p : Fin 4 → ℝ) (u : Fin 4 → ℂ) : (Fin 4 → ℝ) → (Fin 4 → ℂ) :=
  fun x => Complex.exp (Complex.I * ∑ mu, (p mu : ℂ) * (x mu : ℂ)) • u

end DiracEquation
