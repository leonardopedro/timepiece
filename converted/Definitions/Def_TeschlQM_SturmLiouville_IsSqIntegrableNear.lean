/-
prove2.me platform library module `Definitions.Def_TeschlQM_SturmLiouville_IsSqIntegrableNear`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_SturmLiouville_IsSqIntegrableNear.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_SLData

namespace TeschlQM.SturmLiouville

open MeasureTheory

/-- Teschl, pp. 188, 191: `u` is *square integrable near `a`*, i.e. `u ∈ L²((a, c), r dx)` for
some `c ∈ I`: `∫_a^c |u(x)|² r(x) dx < ∞` (with `u` a.e.-strongly measurable there). -/
def IsSqIntegrableNearLeft (L : SLData) (u : ℝ → ℂ) : Prop :=
  ∃ c ∈ L.I, MemLp u 2 ((volume.restrict {x : ℝ | L.a < (x : EReal) ∧ x < c}).withDensity
    (fun x => ENNReal.ofReal (L.r x)))

/-- Teschl, pp. 188, 191: `u` is square integrable near `b`, i.e. `u ∈ L²((c, b), r dx)` for some
`c ∈ I`. -/
def IsSqIntegrableNearRight (L : SLData) (u : ℝ → ℂ) : Prop :=
  ∃ c ∈ L.I, MemLp u 2 ((volume.restrict {x : ℝ | c < x ∧ (x : EReal) < L.b}).withDensity
    (fun x => ENNReal.ofReal (L.r x)))

end TeschlQM.SturmLiouville
