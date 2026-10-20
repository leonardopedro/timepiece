/-
prove2.me platform library module `Definitions.Def_TeschlQM_SturmLiouville_SolvesTau`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_SturmLiouville_SolvesTau.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_quasiDeriv

namespace TeschlQM.SturmLiouville

open MeasureTheory

/-- Teschl (9.1), p. 181: `f, p f′ ∈ AC_loc(I)` and `τ f = g` a.e. on `I`, where
`τ f = (1/r)(−(p f′)′ + q f)`. Since `r > 0` this says `(p f′)′ = q f − r g` a.e., encoded as:
`q f − r g ∈ L¹_loc(I)` and `(p f′)(y) − (p f′)(x) = ∫_x^y (q f − r g)(t) dt` for `x, y ∈ I`. -/
def SolvesTau (L : SLData) (f g : ℝ → ℂ) : Prop :=
  IsQuasiDerivative L f (quasiDeriv L f) ∧
    LocallyIntegrableOn (fun t => (L.q t : ℂ) * f t - (L.r t : ℂ) * g t) L.I ∧
    ∀ x ∈ L.I, ∀ y ∈ L.I, quasiDeriv L f y - quasiDeriv L f x =
      ∫ t in x..y, ((L.q t : ℂ) * f t - (L.r t : ℂ) * g t)

/-- Teschl (9.8), p. 182: `f` is a solution of `(τ − z) f = g`, i.e. `τ f = z f + g`, with
`f, p f′ ∈ AC_loc(I)`. For `g = 0` this is `τ u = z u`. -/
def IsSolution (L : SLData) (z : ℂ) (g f : ℝ → ℂ) : Prop :=
  SolvesTau L f (fun x => z * f x + g x)

end TeschlQM.SturmLiouville
