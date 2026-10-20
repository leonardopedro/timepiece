/-
prove2.me platform library module `Definitions.Def_ChatterjeeQFT_Minkowski`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_ChatterjeeQFT_Minkowski.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

/-!
# Minkowski space `R^{1,3}`, Lorentz transformations, and the restricted Lorentz group

Following S. Chatterjee, *Lectures on Quantum Field Theory*, Lecture 9.
-/

open Matrix

namespace ChatterjeeQFT

/-- The Minkowski inner product on `R^{1,3}`, with signature `(+,-,-,-)`:
`(x, y) = x⁰y⁰ - (x¹y¹ + x²y² + x³y³)`. -/
def minkowskiInner (x y : Fin 4 → ℝ) : ℝ :=
  x 0 * y 0 - (x 1 * y 1 + x 2 * y 2 + x 3 * y 3)

/-- The Minkowski square `x² = (x, x)`. -/
def minkowskiSq (x : Fin 4 → ℝ) : ℝ := minkowskiInner x x

/-- A Lorentz transformation: a linear map of `R^{1,3}` preserving the Minkowski inner
product. -/
def IsLorentz (L : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ x y : Fin 4 → ℝ, minkowskiInner (L *ᵥ x) (L *ᵥ y) = minkowskiInner x y

/-- The restricted Lorentz group `SO↑(1,3)`: Lorentz transformations with determinant `1`
that are orthochronous (`L⁰₀ > 0`). -/
def IsRestrictedLorentz (L : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  IsLorentz L ∧ L.det = 1 ∧ 0 < L 0 0

end ChatterjeeQFT
