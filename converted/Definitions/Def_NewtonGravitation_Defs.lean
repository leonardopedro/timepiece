/-
prove2.me platform library module `Definitions.Def_NewtonGravitation_Defs`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_NewtonGravitation_Defs.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

open MeasureTheory

namespace NewtonGravitation

/-- Physical space: three-dimensional Euclidean space. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The Newtonian constant of gravitation, `G = 6.67430 × 10⁻¹¹ m³ kg⁻¹ s⁻²` (CODATA 2022). -/
noncomputable def G : ℝ := 6.67430e-11

/-- Vector form of Newton's law: the force `F₂₁` applied on body 2 (mass `m₂`, position `r₂`)
exerted by body 1 (mass `m₁`, position `r₁`):
`F₂₁ = -G m₁ m₂ / ‖r₂₁‖² • r̂₂₁`, with `r₂₁ = r₂ - r₁` and `r̂₂₁ = r₂₁ / ‖r₂₁‖`. -/
noncomputable def pointForce (m₁ m₂ : ℝ) (r₁ r₂ : Space) : Space :=
  -(G * m₁ * m₂ / ‖r₂ - r₁‖ ^ 2) • (‖r₂ - r₁‖⁻¹ • (r₂ - r₁))

/-- Gravitational field at `x` of a point mass `M` located at `c`:
`g(x) = -G M / ‖x - c‖³ • (x - c)`. -/
noncomputable def pointField (M : ℝ) (c x : Space) : Space :=
  -(G * M / ‖x - c‖ ^ 3) • (x - c)

/-- Gravitational potential at `x` of a point mass `M` located at `c`: `V(x) = -G M / ‖x - c‖`. -/
noncomputable def pointPotential (M : ℝ) (c x : Space) : ℝ :=
  -(G * M / ‖x - c‖)

/-- Gravitational field at `x` produced by a mass distribution `μ` (a measure on space, giving the
mass of each region): the superposition (integral) of the point-mass fields of its elements,
`g_μ(x) = ∫ -G / ‖x - y‖³ • (x - y) dμ(y)`. -/
noncomputable def gravField (μ : Measure Space) (x : Space) : Space :=
  ∫ y, -(G / ‖x - y‖ ^ 3) • (x - y) ∂μ

/-- A mass distribution is spherically symmetric about the origin if it is invariant under every
linear isometry of space (every rotation and reflection fixing the origin). -/
def IsSphericallySymmetric (μ : Measure Space) : Prop :=
  ∀ A : Space ≃ₗᵢ[ℝ] Space, μ.map A = μ

/-- A uniform spherical shell of total mass `M` and radius `a`, centred at the origin: the surface
measure of the unit sphere, transported to the sphere of radius `a`, normalised to total mass `M`. -/
noncomputable def uniformShell (M : NNReal) (a : ℝ) : Measure Space :=
  ((M : ENNReal) / (volume : Measure Space).toSphere Set.univ) •
    ((volume : Measure Space).toSphere.map (fun u : Metric.sphere (0 : Space) 1 => a • (u : Space)))

/-- A uniform solid ball of total mass `M` and radius `R`, centred at the origin: Lebesgue measure
restricted to the open ball, normalised to total mass `M`. -/
noncomputable def uniformBall (M : NNReal) (R : ℝ) : Measure Space :=
  ((M : ENNReal) / volume (Metric.ball (0 : Space) R)) • volume.restrict (Metric.ball (0 : Space) R)

end NewtonGravitation
