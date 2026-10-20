/-
prove2.me platform library module `Definitions.Def_CircleMethod_char`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_CircleMethod_char.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Order.Round

namespace CircleMethod

/-- The standard additive character `e(θ) = exp(2πiθ)` of `ℝ/ℤ`. -/
noncomputable def e (θ : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * θ)

/-- `nrm θ` is the distance from `θ` to the nearest integer, written `‖θ‖` in the
analytic number theory literature. -/
noncomputable def nrm (θ : ℝ) : ℝ := |θ - round θ|

end CircleMethod
