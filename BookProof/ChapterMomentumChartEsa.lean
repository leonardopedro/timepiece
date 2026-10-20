import Mathlib
import BookProof.ChapterFourierMultiplierEsa

/-!
# ODE-C.1 — the momentum operator `−i d/dw` of the reciprocal chart is essentially
self-adjoint

`CONSOLIDATED_PLAN.md` §"2026-10-15b", row ODE-C.1.  In the reciprocal chart `w = −1/x` of
the singular vector field `ẋ = x²` the quantum evolution is the translation group
`ψ ↦ ψ(· − t)` (`BookProof.OdeUnitaryFlow.odeKoop_chartW`), whose generator is the momentum
operator `P = −i d/dw` on `L²(ℝ, dw)`.  This module records that `P` is essentially
self-adjoint on the Schwartz core `𝓢(ℝ)` of `L²(ℝ)` — a dense, translation-stable core.

The core is the specialist's choice (the plan allows Schwartz or `C_c^∞`); the closing route
used here is the Fourier-multiplier instrument
`BookProof.FourierMultiplierEsa.momentumOp_essentiallySelfAdjoint` (under Plancherel `P` is
multiplication by the real symbol `2πξ`), instantiated at `V = ℝ` and the unit direction.
The plan's alternative route (Nelson's criterion in orbit form along the translation orbit,
`BookProof.FlowDGamma.deficiencyTrivialAt_of_orbits`) would reach the same statement.

## Main results

* `chartMomentum` — `P = −i d/dw` on `𝓢(ℝ, ℂ)`, and `chartMomentum_apply` (it really is
  `−i` times the derivative);
* `chartMomentum_symmetricOn` — `P` is symmetric on the Schwartz core of `L²(ℝ)`;
* **`momentum_essentiallySelfAdjointOn`** — `P` is essentially self-adjoint there.
-/

namespace BookProof.MomentumChart

open MeasureTheory SchwartzMap
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa

/-- **The momentum operator of the reciprocal chart**, `P = −i d/dw`, on `𝓢(ℝ, ℂ)`. -/
noncomputable def chartMomentum : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := momentumOp (1 : ℝ)

/-- `P ψ = −i ψ'`. -/
theorem chartMomentum_apply (ψ : 𝓢(ℝ, ℂ)) (w : ℝ) :
    chartMomentum ψ w = -Complex.I * deriv ψ w := by
  simp [chartMomentum, momentumOp, SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- `P` is symmetric on the Schwartz core of `L²(ℝ)`. -/
theorem chartMomentum_symmetricOn :
    BookProof.FarisLavine.SymmetricOn (schwartzDomain ℝ) (opL2 chartMomentum) := by
  have h : chartMomentum = firstOrderOp (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
    simp [chartMomentum, firstOrderOp]
  rw [h]
  exact firstOrderOp_symmetric _ _

/-- **ODE-C.1.**  The momentum operator `−i d/dw` of the reciprocal chart is essentially
self-adjoint on the Schwartz core of `L²(ℝ, dw)`. -/
theorem momentum_essentiallySelfAdjointOn :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain ℝ) (opL2 chartMomentum) :=
  momentumOp_essentiallySelfAdjoint (1 : ℝ)

end BookProof.MomentumChart
