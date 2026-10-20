/-
prove2.me platform library module `Definitions.Def_CircleMethod_genfun`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_CircleMethod_genfun.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CircleMethod_char
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace CircleMethod

/-- The exponential generating function of a finite set `A` of integers:
`f A θ = ∑_{a ∈ A} e(aθ)`. -/
noncomputable def f (A : Finset ℤ) (θ : ℝ) : ℂ := ∑ a ∈ A, e ((a : ℝ) * θ)

end CircleMethod
