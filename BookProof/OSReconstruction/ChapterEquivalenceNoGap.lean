import Mathlib
import BookProof.OSReconstruction.MultiplierSelfAdjoint

/-!
# Chapter EquivalenceNoGap — H7/C9 negative control

H7 keeps nontriviality and the mass gap separate from the Hamiltonian ↔ Euclidean
equivalence.  This module records the sharp form of that separation in the multiplier model:
the norm criterion for the transfer semigroup is equivalent to a **positive lower bound on the
density off its zero set**.  Consequently, the equivalence machinery (reflection positivity,
the OS bridge, the resolvent law, strong resolvent convergence) can hold while the floor fails —
and then the semigroup does not converge to the ground projection, so there is no gap.

No gap theorem is claimed; this is the negative control.
-/

noncomputable section

namespace BookProof.EquivalenceNoGap

open Filter Topology
open BookProof.OSReconstruction

variable {X : Type*} [MeasurableSpace X] {ν : MeasureTheory.Measure X}
variable {Λ : OSState} {T : TimeTranslation}

/-- Without a positive floor on the density the transfer semigroup does not converge in norm to
    the ground projection: the equivalence data alone cannot certify a mass gap. -/
theorem no_norm_convergence_of_no_floor (D : MulModel X ν Λ T)
    [MeasureTheory.SigmaFinite ν]
    (hno : ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ x ∂ν, D.f x ≠ 0 → δ ≤ D.f x) :
    ¬ Tendsto (fun τ : ℝ => ‖flowOfHCLM D τ - limitProjection D‖) atTop (𝓝 0) := by
  intro hconv
  exact hno ((tendsto_opNorm_flowOfHCLM_sub_limitProjection_iff_gap D).1 hconv)

end BookProof.EquivalenceNoGap
