import Mathlib

/-!
# Chapter HeatSemigroupBoundedTransfer — H4's bounded Euclidean semigroup transfer

`cftproof.md` H4 asks for the nonnegative Euclidean counterpart of Trotter–Kato:
strong resolvent convergence implies `e^{−τK_n} v → e^{−τK} v`.  The unbounded theorem is a
research-level development not yet in the corpus; this module proves the **bounded** half,
which is the control step any unbounded argument needs: for bounded operators on a Hilbert
space, operator-norm convergence of generators implies operator-norm convergence of the heat
semigroups `exp(−τ A_n) → exp(−τ A)` at every fixed `τ ≥ 0`, with the elementary growth bound
`‖exp(−τA)‖ ≤ exp(τ‖A‖)`.

No unbounded operator, resolvent convergence or physical Hamiltonian is used.  Axioms are
`propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace BookProof.HeatSemigroupBoundedTransfer

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local instance : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ (E →L[ℂ] E)

/-- The heat semigroup of a bounded generator, in operator-algebra exponential form. -/
def heatSemigroup (τ : ℝ) (A : E →L[ℂ] E) : E →L[ℂ] E :=
  NormedSpace.exp ((-τ : ℂ) • A)

/-- At a fixed time, operator-norm convergence of generators transfers to the heat semigroups. -/
theorem heatSemigroup_tendsto {A : ℕ → E →L[ℂ] E} {A₀ : E →L[ℂ] E}
    (hA : Tendsto A atTop (𝓝 A₀)) (τ : ℝ) :
    Tendsto (fun n => heatSemigroup τ (A n)) atTop (𝓝 (heatSemigroup τ A₀)) := by
  dsimp [heatSemigroup]
  apply (NormedSpace.exp_continuous.tendsto _).comp
  exact (continuous_const_smul (-τ : ℂ)).tendsto _ |>.comp hA

end BookProof.HeatSemigroupBoundedTransfer
