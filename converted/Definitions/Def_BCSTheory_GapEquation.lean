/-
prove2.me platform library module `Definitions.Def_BCSTheory_GapEquation`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_BCSTheory_GapEquation.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

/-!
# BCS gap equation (weak-coupling BCS model with Debye cutoff)

Parameters used throughout:
* `kB > 0` — the Boltzmann constant,
* `hbarOmegaD > 0` — the Debye cutoff energy `ħ ω_D`,
* `coupling > 0` — the dimensionless coupling `V₀ · Z(E_F)` (attractive potential times
  half the density of states at the Fermi energy).
-/

namespace BCSTheory

/-- The Fermi–Dirac distribution `f(E, T) = 1 / (exp(E / (k_B T)) + 1)`. -/
noncomputable def fermiDirac (kB E T : ℝ) : ℝ :=
  1 / (Real.exp (E / (kB * T)) + 1)

/-- The quasiparticle energy `√(η² + Δ²)`. -/
noncomputable def quasiparticleEnergy (η Δ : ℝ) : ℝ :=
  Real.sqrt (η ^ 2 + Δ ^ 2)

/-- The right-hand side of the zero-temperature gap equation,
`∫₀^{ħω_D} dη / √(η² + Δ²)`. -/
noncomputable def gapIntegralZeroTemp (hbarOmegaD Δ : ℝ) : ℝ :=
  ∫ η in (0 : ℝ)..hbarOmegaD, 1 / quasiparticleEnergy η Δ

/-- The right-hand side of the finite-temperature BCS gap equation,
`∫₀^{ħω_D} dη · tanh(√(η² + Δ²) / (2 k_B T)) / √(η² + Δ²)`.
For `Δ = 0` the integrand is `tanh(η / (2 k_B T)) / η` (the critical-temperature equation). -/
noncomputable def gapIntegral (kB hbarOmegaD Δ T : ℝ) : ℝ :=
  ∫ η in (0 : ℝ)..hbarOmegaD,
    Real.tanh (quasiparticleEnergy η Δ / (2 * kB * T)) / quasiparticleEnergy η Δ

/-- The zero-temperature gap `Δ(0)`: the supremum of all `Δ > 0` solving
`1 / (V₀ Z(E_F)) = ∫₀^{ħω_D} dη / √(η² + Δ²)`. -/
noncomputable def zeroTemperatureGap (hbarOmegaD coupling : ℝ) : ℝ :=
  sSup {Δ : ℝ | 0 < Δ ∧ gapIntegralZeroTemp hbarOmegaD Δ = 1 / coupling}

/-- The critical (transition) temperature `T_c`: the supremum of all `T > 0` solving
`1 / (V₀ Z(E_F)) = ∫₀^{ħω_D} (dη / η) tanh(η / (2 k_B T))`. -/
noncomputable def criticalTemperature (kB hbarOmegaD coupling : ℝ) : ℝ :=
  sSup {T : ℝ | 0 < T ∧ gapIntegral kB hbarOmegaD 0 T = 1 / coupling}

/-- The temperature-dependent gap `Δ(T)`: the supremum of all `Δ > 0` solving the
finite-temperature gap equation `1 / (V₀ Z(E_F)) = gapIntegral kB ħω_D Δ T`
(this is `0` when no positive solution exists, e.g. for `T ≥ T_c`). -/
noncomputable def gap (kB hbarOmegaD coupling T : ℝ) : ℝ :=
  sSup {Δ : ℝ | 0 < Δ ∧ gapIntegral kB hbarOmegaD Δ T = 1 / coupling}

end BCSTheory
