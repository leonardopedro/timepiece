/-
prove2.me platform library module `Definitions.Def_TeschlODE_HigherDim_IsIntegralCurve`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlODE_HigherDim_IsIntegralCurve.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlODE.HigherDim

/-- Teschl, §6.2, p. 189: an integral curve (solution) of the autonomous system `ẋ = f(x)`
(6.7) in `M`, defined on the time set `J`. `J` is an open interval (open and order-connected,
possibly empty or unbounded), `φ` maps `J` into `M`, and `φ` has derivative `f (φ t)` at every
`t ∈ J`. The state space `E` is a real normed space (in this mission `ℝⁿ` or the phase space
`ℝⁿ × ℝⁿ`). Only the values of `φ` on `J` matter. -/
def IsIntegralCurve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → E)
    (M : Set E) (J : Set ℝ) (φ : ℝ → E) : Prop :=
  IsOpen J ∧ J.OrdConnected ∧ (∀ t ∈ J, φ t ∈ M) ∧ ∀ t ∈ J, HasDerivAt φ (f (φ t)) t

end TeschlODE.HigherDim
