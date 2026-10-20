/-
prove2.me platform library module `Definitions.Def_QED_minkowski_spacetime`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_QED_minkowski_spacetime.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace QED

/-- Minkowski spacetime in coordinates: a point `x` is the quadruple of its
contravariant coordinates `x⁰, x¹, x², x³`. -/
abbrev Spacetime : Type := Fin 4 → ℝ

/-- The Minkowski metric `η` with signature `(+, -, -, -)`:
`η 0 0 = 1`, `η i i = -1` for `i = 1, 2, 3`, and `η μ ν = 0` for `μ ≠ ν`.
Since `η` is its own inverse, the same function is used for the contravariant
metric `η^{μν}` used to raise indices. -/
def minkowski (μ ν : Fin 4) : ℝ :=
  if μ = ν then (if μ = 0 then 1 else -1) else 0

/-- The partial derivative `∂_μ f` of a field `f` on Minkowski spacetime with
values in a real normed space, i.e. the Fréchet derivative of `f` evaluated on
the `μ`-th coordinate direction. If `f` is not differentiable at `x`, this is
`0` by the junk-value convention for `fderiv`. -/
noncomputable def partialD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Fin 4) (f : Spacetime → E) (x : Spacetime) : E :=
  fderiv ℝ f x (Pi.single μ 1)

/-- The d'Alembert wave operator `□ f = η^{μν} ∂_μ ∂_ν f`. -/
noncomputable def dAlembert {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Spacetime → E) (x : Spacetime) : E :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, minkowski μ ν • partialD μ (partialD ν f) x

end QED
