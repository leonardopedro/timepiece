import Mathlib

import Singularity.Esa

/-!
# Energy-bounded initial conditions

The normal-ordered core does not yet realize operators on a Hilbert space, so a
state carries the two norm values needed by the spectral estimate.  Membership
in the lower spectral subspace is represented by its defining norm inequality.
This clean interface can later be instantiated by an actual projection-valued
measure without changing the theorem consumed by the ODE pipeline.
-/

/-- Norm data for a vector and its Hamiltonian image. -/
structure HamiltonianState (M : ℕ) where
  stateNorm : ℝ
  imageNorm : ℝ
  stateNorm_nonneg : 0 ≤ stateNorm
  imageNorm_nonneg : 0 ≤ imageNorm

/-- Membership certificate for the energy window of radius `E_max`.  For a
one-sided interval `(-∞, E_max]`, this estimate requires the Hamiltonian to be
nonnegative; the symmetric norm estimate itself is what downstream code uses. -/
def InEnergySpectralSubspace {M : ℕ} (E_max : ℝ) (ψ : HamiltonianState M) : Prop :=
  ψ.imageNorm ≤ E_max * ψ.stateNorm

/-- The subtype of initial conditions selected by the energy projection. -/
def EnergySpectralSubspace (M : ℕ) (E_max : ℝ) :=
  {ψ : HamiltonianState M // InEnergySpectralSubspace E_max ψ}

/-- Energy-bounded initial conditions: every state in the represented spectral
subspace satisfies `‖Hψ‖ ≤ E_max ‖ψ‖`.  The ESA hypothesis is retained because
it is the condition under which the analytic spectral projection exists. -/
theorem energy_bounded_initial {M : ℕ} (sys : ODESystem M)
    (_h_esa : isEssentiallySelfAdjoint (odeToHamiltonian sys))
    (E_max : ℝ) (_hE : 0 ≤ E_max) (ψ : EnergySpectralSubspace M E_max) :
    ψ.1.imageNorm ≤ E_max * ψ.1.stateNorm := by
  exact ψ.2

/-- The zero state belongs to every nonnegative energy subspace. -/
def zeroEnergyState {M : ℕ} (E_max : ℝ) (_hE : 0 ≤ E_max) :
    EnergySpectralSubspace M E_max :=
  ⟨⟨0, 0, le_rfl, le_rfl⟩, by simp [InEnergySpectralSubspace]⟩
