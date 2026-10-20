/-
prove2.me platform library module `Definitions.Def_TeschlODE_SturmLiouville_SLOp`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlODE_SturmLiouville_SLOp.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlODE.SturmLiouville

/-- Teschl §5.4, p. 155, (5.53): the Sturm–Liouville differential expression
`L f = r⁻¹ (−(p f′)′ + q f)` applied to `f : [a, b] → ℂ`, evaluated at `x`. Derivatives are taken
within `[a, b]` (one-sided at the endpoints). Only the values at `x ∈ [a, b]` are meaningful. -/
noncomputable def SLOp (p q r : ℝ → ℝ) (a b : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((r x : ℂ))⁻¹ *
    (-derivWithin (fun y => (p y : ℂ) * derivWithin f (Set.Icc a b) y) (Set.Icc a b) x +
      (q x : ℂ) * f x)

end TeschlODE.SturmLiouville
