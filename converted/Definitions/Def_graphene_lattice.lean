/-
prove2.me platform library module `Definitions.Def_graphene_lattice`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_graphene_lattice.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

/-!
# Graphene: honeycomb lattice geometry

Geometric data of the honeycomb lattice of graphene, following
F. Utermohlen, *Tight-Binding Model for Graphene* (September 12, 2018), Eq. (1).

Positions and momenta are elements of `ℝ × ℝ`.  Note that the norm carried by the
product type `ℝ × ℝ` is the sup norm, so the Euclidean norm is introduced here
explicitly as `euclidNorm`.
-/

namespace GrapheneTightBinding

/-- Euclidean inner product of two vectors of the plane `ℝ × ℝ`. -/
def dotp (p q : ℝ × ℝ) : ℝ := p.1 * q.1 + p.2 * q.2

/-- The Euclidean norm `√(q₁² + q₂²)` of a vector of the plane `ℝ × ℝ`.
(The product type `ℝ × ℝ` carries the sup norm, hence this explicit definition.) -/
noncomputable def euclidNorm (q : ℝ × ℝ) : ℝ := Real.sqrt (q.1 ^ 2 + q.2 ^ 2)

/-- The first lattice unit vector `a₁ = (a/2)(3, √3)`. -/
noncomputable def latticeVecOne (a : ℝ) : ℝ × ℝ := (3 * a / 2, Real.sqrt 3 * a / 2)

/-- The second lattice unit vector `a₂ = (a/2)(3, -√3)`. -/
noncomputable def latticeVecTwo (a : ℝ) : ℝ × ℝ := (3 * a / 2, -(Real.sqrt 3 * a / 2))

/-- The three nearest-neighbour vectors
`δ₁ = (a/2)(1, √3)`, `δ₂ = (a/2)(1, -√3)`, `δ₃ = -a(1, 0)`. -/
noncomputable def nnVec (a : ℝ) : Fin 3 → ℝ × ℝ
  | 0 => (a / 2, Real.sqrt 3 * a / 2)
  | 1 => (a / 2, -(Real.sqrt 3 * a / 2))
  | 2 => (-a, 0)

/-- The Dirac point `K = (2π/(3√3 a))(√3, 1)`. -/
noncomputable def diracK (a : ℝ) : ℝ × ℝ :=
  (2 * Real.pi / (3 * a), 2 * Real.pi / (3 * Real.sqrt 3 * a))

/-- The Dirac point `K' = (2π/(3√3 a))(√3, -1)`. -/
noncomputable def diracKp (a : ℝ) : ℝ × ℝ :=
  (2 * Real.pi / (3 * a), -(2 * Real.pi / (3 * Real.sqrt 3 * a)))

end GrapheneTightBinding
