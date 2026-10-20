/-
prove2.me platform library module `Definitions.Def_TeschlQM_SturmLiouville_IsLimitCircle`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_SturmLiouville_IsLimitCircle.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_maxDomain
import Definitions.Def_TeschlQM_SturmLiouville_wronskian

namespace TeschlQM.SturmLiouville

/-- Teschl, p. 187: `τ` is *limit circle* (l.c.) at `a` if there is a `v ∈ D(τ)` with
`W_a(v*, v) = 0` such that `W_a(v, f) ≠ 0` for at least one `f ∈ D(τ)`. Here `v* = conj ∘ v`.
Otherwise `τ` is *limit point* (l.p.) at `a`, i.e. `¬ IsLimitCircleLeft L`. -/
def IsLimitCircleLeft (L : SLData) : Prop :=
  ∃ v : ℝ → ℂ, InMaxDomain L v ∧
    wronskianLeft L (fun x => starRingEnd ℂ (v x)) v = 0 ∧
    ∃ f : ℝ → ℂ, InMaxDomain L f ∧ wronskianLeft L v f ≠ 0

/-- Teschl, p. 187: `τ` is limit circle at `b` ("similarly for `b`"). Otherwise it is limit point
at `b`. -/
def IsLimitCircleRight (L : SLData) : Prop :=
  ∃ v : ℝ → ℂ, InMaxDomain L v ∧
    wronskianRight L (fun x => starRingEnd ℂ (v x)) v = 0 ∧
    ∃ f : ℝ → ℂ, InMaxDomain L f ∧ wronskianRight L v f ≠ 0

end TeschlQM.SturmLiouville
