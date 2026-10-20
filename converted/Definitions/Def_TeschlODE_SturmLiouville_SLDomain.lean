/-
prove2.me platform library module `Definitions.Def_TeschlODE_SturmLiouville_SLDomain`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlODE_SturmLiouville_SLDomain.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlODE.SturmLiouville

/-- Teschl §5.4, p. 156, (5.54)–(5.55): the domain `D(L)` of the Sturm–Liouville operator,
`f ∈ C²([a, b], ℂ)` with `BC_a(f) = cos(α) f(a) − sin(α) p(a) f′(a) = 0` and
`BC_b(f) = cos(β) f(b) − sin(β) p(b) f′(b) = 0`. Derivatives are taken within `[a, b]`. -/
def SLDomain (p : ℝ → ℝ) (a b α β : ℝ) (f : ℝ → ℂ) : Prop :=
  ContDiffOn ℝ 2 f (Set.Icc a b) ∧
    (Real.cos α : ℂ) * f a - (Real.sin α : ℂ) * (p a : ℂ) * derivWithin f (Set.Icc a b) a = 0 ∧
    (Real.cos β : ℂ) * f b - (Real.sin β : ℂ) * (p b : ℂ) * derivWithin f (Set.Icc a b) b = 0

end TeschlODE.SturmLiouville
