/-
prove2.me platform library module `Definitions.Def_QED_fields`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_QED_fields.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_QED_dirac_algebra

namespace QED

/-- A gauge field (electromagnetic four-potential): `A x μ` is the covariant
component `A_μ(x)`. -/
abbrev GaugeField : Type := Spacetime → Fin 4 → ℝ

/-- A Dirac spinor field: `ψ x` is a four-component complex spinor at `x`. -/
abbrev SpinorField : Type := Spacetime → Fin 4 → ℂ

/-- The covariant components `A^ν = η^{νβ} A_β` of the four-potential. -/
noncomputable def gaugeUp (A : GaugeField) (ν : Fin 4) (x : Spacetime) : ℝ :=
  ∑ β : Fin 4, minkowski ν β * A x β

/-- The electromagnetic field tensor `F_{μν} = ∂_μ A_ν - ∂_ν A_μ`. -/
noncomputable def fieldStrength (A : GaugeField) (μ ν : Fin 4) (x : Spacetime) : ℝ :=
  partialD μ (fun y => A y ν) x - partialD ν (fun y => A y μ) x

/-- The field tensor with both indices raised, `F^{μν} = η^{μα} η^{νβ} F_{αβ}`. -/
noncomputable def fieldStrengthUp (A : GaugeField) (μ ν : Fin 4) (x : Spacetime) : ℝ :=
  ∑ α : Fin 4, ∑ β : Fin 4, minkowski μ α * minkowski ν β * fieldStrength A α β x

/-- The gauge covariant derivative `D_μ ψ = ∂_μ ψ + i e A_μ ψ`, where `e` is the
coupling constant (the electric charge of the spinor field). -/
noncomputable def covariantD (e : ℝ) (A : GaugeField) (ψ : SpinorField) (μ : Fin 4)
    (x : Spacetime) : Fin 4 → ℂ :=
  partialD μ ψ x + ((Complex.I * (e : ℂ) * (A x μ : ℂ)) • ψ x)

/-- The Dirac current `J^μ = ψ̄ γ^μ ψ`, taken as a real number via its real part.
(Its imaginary part vanishes for any Dirac representation; see
`QED.current_isReal`.) -/
noncomputable def current (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (ψ : SpinorField)
    (μ : Fin 4) (x : Spacetime) : ℝ :=
  (diracPairing γ (γ μ) (ψ x) (ψ x)).re

/-- The QED Lagrangian density
`L = ψ̄ (i γ^μ D_μ - m) ψ - (1/4) F_{μν} F^{μν}`. -/
noncomputable def lagrangian (m e : ℝ) (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (A : GaugeField) (ψ : SpinorField) (x : Spacetime) : ℂ :=
  (∑ μ : Fin 4, Complex.I * diracPairing γ (γ μ) (ψ x) (covariantD e A ψ μ x))
    - (m : ℂ) * diracPairing γ 1 (ψ x) (ψ x)
    - (1 / 4 : ℂ) *
        ((∑ μ : Fin 4, ∑ ν : Fin 4, fieldStrength A μ ν x * fieldStrengthUp A μ ν x : ℝ) : ℂ)

/-- The Dirac equation `(i γ^μ D_μ - m) ψ = 0` in the external gauge field `A`. -/
def IsDiracSolution (m e : ℝ) (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (A : GaugeField) (ψ : SpinorField) : Prop :=
  ∀ x : Spacetime,
    ∑ μ : Fin 4, Complex.I • (γ μ).mulVec (covariantD e A ψ μ x) = (m : ℂ) • ψ x

/-- The Maxwell equation of motion `∂_μ F^{μν} = e J^ν` sourced by the Dirac
current. -/
noncomputable def IsMaxwellSolution (e : ℝ) (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (A : GaugeField) (ψ : SpinorField) : Prop :=
  ∀ (ν : Fin 4) (x : Spacetime),
    (∑ μ : Fin 4, partialD μ (fun y => fieldStrengthUp A μ ν y) x) = e * current γ ψ ν x

/-- The Lorenz gauge condition `∂^μ A_μ = η^{μν} ∂_μ A_ν = 0`. -/
noncomputable def LorenzGauge (A : GaugeField) : Prop :=
  ∀ x : Spacetime,
    (∑ μ : Fin 4, ∑ ν : Fin 4, minkowski μ ν * partialD μ (fun y => A y ν) x) = 0

/-- The gauge transform `A_μ ↦ A_μ + ∂_μ χ` of the four-potential by a real
scalar function `χ`. -/
noncomputable def gaugeShift (χ : Spacetime → ℝ) (A : GaugeField) : GaugeField :=
  fun x μ => A x μ + partialD μ χ x

/-- The accompanying phase rotation `ψ ↦ exp (-i e χ) ψ` of the spinor field. -/
noncomputable def gaugePhase (e : ℝ) (χ : Spacetime → ℝ) (ψ : SpinorField) : SpinorField :=
  fun x => Complex.exp (-(Complex.I * (e : ℂ) * (χ x : ℂ))) • ψ x

end QED
