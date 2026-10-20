/-
prove2.me platform library module `Definitions.Def_TeschlQM_SturmLiouville_quasiDeriv`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_SturmLiouville_quasiDeriv.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_SLData
import Definitions.Def_TeschlQM_SturmLiouville_IsACloc

namespace TeschlQM.SturmLiouville

open MeasureTheory

/-- Teschl (9.1), p. 181: `f, p f′ ∈ AC_loc(I)` with `f1 = p f′`. That is, `f1` is locally
absolutely continuous on `I`, `f1 / p` is locally integrable on `I`, and `f` is its integral:
`f(y) − f(x) = ∫_x^y f1(t)/p(t) dt` for `x, y ∈ I` (so `f ∈ AC_loc(I)` and `f′ = f1/p` a.e.).
`f1` is the continuous representative of `p f′` used in `(p f′)(c)` and in the Wronskian. -/
def IsQuasiDerivative (L : SLData) (f f1 : ℝ → ℂ) : Prop :=
  IsACloc L.I f1 ∧ LocallyIntegrableOn (fun t => f1 t / (L.p t : ℂ)) L.I ∧
    ∀ x ∈ L.I, ∀ y ∈ L.I, f y - f x = ∫ t in x..y, f1 t / (L.p t : ℂ)

/-- The quasi-derivative `p f′` of `f` (Teschl writes `(p f′)(x)`). On `I` it is uniquely
determined by `f` whenever `f, p f′ ∈ AC_loc(I)` (two continuous functions equal a.e. on `I`
agree on `I`); it is chosen by `Classical.choose`. It is `0` if `f` has no locally absolutely
continuous quasi-derivative; every statement of the mission applies it only to such `f`. -/
noncomputable def quasiDeriv (L : SLData) (f : ℝ → ℂ) : ℝ → ℂ :=
  open Classical in
  if h : ∃ f1, IsQuasiDerivative L f f1 then h.choose else 0

end TeschlQM.SturmLiouville
