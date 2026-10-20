/-
prove2.me platform library module `Definitions.Def_TeschlODE_SturmLiouville_RegularSL`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlODE_SturmLiouville_RegularSL.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlODE.SturmLiouville

/-- Teschl §5.3, p. 153, (5.45), the standing assumption for the rest of Chapter 5: on the
compact interval `[a, b]` (with `a < b`) the coefficients satisfy `r, q ∈ C⁰([a, b], ℝ)`,
`p ∈ C¹([a, b], ℝ)` and `p(x), r(x) > 0` for `x ∈ [a, b]`; the Sturm–Liouville equation (5.43)
is then called *regular*. Only the values of `p, q, r` on `[a, b]` matter. -/
def RegularSL (p q r : ℝ → ℝ) (a b : ℝ) : Prop :=
  a < b ∧ ContinuousOn r (Set.Icc a b) ∧ ContinuousOn q (Set.Icc a b) ∧
    ContDiffOn ℝ 1 p (Set.Icc a b) ∧ ∀ x ∈ Set.Icc a b, 0 < p x ∧ 0 < r x

end TeschlODE.SturmLiouville
