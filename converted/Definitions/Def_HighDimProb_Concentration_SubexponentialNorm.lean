/-
prove2.me platform library module `Definitions.Def_HighDimProb_Concentration_SubexponentialNorm`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_HighDimProb_Concentration_SubexponentialNorm.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

open MeasureTheory

namespace HighDimProb.Concentration

/-- The sub-exponential (Orlicz `ψ₁`) norm of a real random variable `X` on a probability
space `(Ω, P)`. Vershynin, *High-Dimensional Probability* (2018), Definition 2.7.5 /
Eq. (2.21): the smallest `t > 0` such that the exponential moment `E[exp(|X| / t)]` is
*finite* and `≤ 2`, i.e.

`‖X‖_{ψ₁} := inf {t > 0 : exp(|X| / t) is integrable and E exp(|X| / t) ≤ 2}`.

The `Integrable` conjunct is essential: Mathlib's Bochner integral of a non-integrable
function is `0` by convention, so without it every `t` for which the moment is actually
infinite would vacuously satisfy `∫ … ≤ 2` and enter the infimum, collapsing the norm of
genuinely non-sub-exponential (and even sub-exponential) variables to `0`. If no `t` exists
with both conjuncts holding (`X` is not sub-exponential), `sInf` of the empty set defaults
to `0`, Mathlib's usual junk value for an unbounded-below or empty set. -/
noncomputable def subexponentialNorm {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ Integrable (fun ω => Real.exp (|X ω| / t)) P ∧
                ∫ ω, Real.exp (|X ω| / t) ∂P ≤ 2}

end HighDimProb.Concentration
