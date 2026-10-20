/-
prove2.me platform library module `Definitions.Def_HighEntropyLimit_gaussian_entropy`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_HighEntropyLimit_gaussian_entropy.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace HighEntropyLimit

/-- Classical entropy (in nats) of a Gaussian phase-space distribution with uncertainty
`Sig = σₓσₚ`, Eq. (2): `S_C(Σ) = ln(2πe Σ / h) = ln(Σ/ħ) + 1`. -/
noncomputable def classicalGaussianEntropy (hbar Sig : ℝ) : ℝ :=
  Real.log (Sig / hbar) + 1

/-- Von Neumann entropy (in nats) of a Gaussian quantum state with uncertainty `Sig`, Eq. (3):
`S_Q(Σ) = (Σ/ħ + 1/2) ln(Σ/ħ + 1/2) - (Σ/ħ - 1/2) ln(Σ/ħ - 1/2)`. -/
noncomputable def quantumGaussianEntropy (hbar Sig : ℝ) : ℝ :=
  (Sig / hbar + 1 / 2) * Real.log (Sig / hbar + 1 / 2)
    - (Sig / hbar - 1 / 2) * Real.log (Sig / hbar - 1 / 2)

/-- The rescaled quantum Gaussian entropy of Section 4.3 / Fig. 3:
`S_Q^λ(Σ) = S_Q(λΣ) - ln λ`. -/
noncomputable def rescaledQuantumGaussianEntropy (hbar lam Sig : ℝ) : ℝ :=
  quantumGaussianEntropy hbar (lam * Sig) - Real.log lam

end HighEntropyLimit
