/-
prove2.me platform library module `Definitions.Def_HeathcoteUnbounded_Psi`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_HeathcoteUnbounded_Psi.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace HeathcoteUnbounded

/-- Heathcote's wave function, eq. (4): `ψ(x) = x⁻¹` for `x ≥ 1` and `ψ(x) = 0` for `x < 1`. -/
noncomputable def psi : ℝ → ℂ := fun x => if 1 ≤ x then ((x : ℂ))⁻¹ else 0

end HeathcoteUnbounded
