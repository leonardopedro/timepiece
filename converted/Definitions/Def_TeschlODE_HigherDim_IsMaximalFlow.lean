/-
prove2.me platform library module `Definitions.Def_TeschlODE_HigherDim_IsMaximalFlow`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlODE_HigherDim_IsMaximalFlow.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlODE_HigherDim_IsIntegralCurve

namespace TeschlODE.HigherDim

/-- Teschl, §6.2, p. 189, (6.8)–(6.9): `Φ` is the (local) flow of `ẋ = f(x)` on `M`, with
maximal time intervals `I x = (T₋(x), T₊(x))`. For every `x ∈ M`, the curve `t ↦ Φ t x` on
`I x` is an integral curve with `0 ∈ I x` and `Φ 0 x = x`, and it is the unique maximal one:
every integral curve `ψ` on an interval `J ∋ 0` with `ψ 0 = x` satisfies `J ⊆ I x` and agrees
with `Φ · x` on `J`. Values of `Φ t x` and `I x` for `x ∉ M` or `t ∉ I x` carry no meaning. -/
def IsMaximalFlow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → E)
    (M : Set E) (I : E → Set ℝ) (Φ : ℝ → E → E) : Prop :=
  ∀ x ∈ M,
    IsIntegralCurve f M (I x) (fun t => Φ t x) ∧ (0 : ℝ) ∈ I x ∧ Φ 0 x = x ∧
    ∀ (J : Set ℝ) (ψ : ℝ → E),
      IsIntegralCurve f M J ψ → (0 : ℝ) ∈ J → ψ 0 = x → J ⊆ I x ∧ ∀ t ∈ J, ψ t = Φ t x

end TeschlODE.HigherDim
