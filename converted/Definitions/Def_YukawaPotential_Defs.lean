/-
prove2.me platform library module `Definitions.Def_YukawaPotential_Defs`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_YukawaPotential_Defs.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace YukawaPotential

open MeasureTheory

/-- The Yukawa (screened Coulomb) potential
`V(r) = -g^2 * exp(-α m r) / r`, with coupling `g`, scaling constant `α`,
mass `m` and radial distance `r`. -/
noncomputable def yukawaPotential (g α m r : ℝ) : ℝ :=
  -g ^ 2 * Real.exp (-(α * m * r)) / r

/-- Potential at the point `x ∈ ℝ³` felt by a point of scaling constant `g`, produced by an
infinitesimally thin uniform spherical shell of radius `R` centred at the origin with total
scaling constant `G`, where each pair interacts through `G g exp(-α m d) / d` at distance `d`:
`G g` times the average of `exp(-α m ‖x - R u‖) / ‖x - R u‖` over the unit sphere `u ∈ S²`
(with respect to the uniform surface measure). -/
noncomputable def yukawaShellPotential (G g α m R : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  G * g * ⨍ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
    Real.exp (-(α * m * ‖x - R • (u : EuclideanSpace ℝ (Fin 3))‖)) /
      ‖x - R • (u : EuclideanSpace ℝ (Fin 3))‖ ∂(volume.toSphere)

end YukawaPotential
