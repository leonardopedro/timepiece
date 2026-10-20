/-
prove2.me platform library module `Definitions.Def_usg_spectral_notions`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_usg_spectral_notions.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_usg_lattice_model

set_option autoImplicit false

open scoped ComplexOrder

namespace UndecidableSpectralGap

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real spectrum of a complex square matrix: the set of real numbers that are
eigenvalues of it. For a Hermitian matrix this is the whole spectrum. -/
def specReal (A : Matrix n n ℂ) : Set ℝ := {μ : ℝ | (μ : ℂ) ∈ spectrum ℂ A}

/-- The ground state energy `λ₀(A)`: the smallest element of the real spectrum. -/
noncomputable def gsEnergy (A : Matrix n n ℂ) : ℝ := sInf (specReal A)

/-- The multiplicity of a real number `μ` as an eigenvalue of `A`, i.e. the dimension of
the corresponding eigenspace. -/
noncomputable def eigMultiplicity (A : Matrix n n ℂ) (μ : ℝ) : ℕ :=
  Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' A) (μ : ℂ))

/-- The ground state of `A` is non-degenerate: the ground state energy has multiplicity one. -/
def GroundStateNondegenerate (A : Matrix n n ℂ) : Prop :=
  eigMultiplicity A (gsEnergy A) = 1

/-- `A` has spectral gap at least `γ`: every eigenvalue other than the ground state energy
is at least `λ₀(A) + γ`. Together with non-degeneracy of the ground state this says
`Δ(A) = λ₁(A) - λ₀(A) ≥ γ`. -/
def HasGapAtLeast (A : Matrix n n ℂ) (γ : ℝ) : Prop :=
  ∀ μ ∈ specReal A, μ ≠ gsEnergy A → gsEnergy A + γ ≤ μ

/-- **Definition 1 (Gapped), with an explicit gap.** The family `{H^{Λ(L)}}` determined by
the interactions `h₁, h_row, h_col` on local dimension `d` is gapped with gap at least
`γ > 0`: there is a system size `L₀` such that for all `L > L₀` the ground state of
`H^{Λ(L)}` is non-degenerate and `Δ(H^{Λ(L)}) ≥ γ`. -/
def GappedWithGap (d : ℕ) (h1 : Matrix (Fin d) (Fin d) ℂ)
    (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (γ : ℝ) : Prop :=
  0 < γ ∧ ∃ L0 : ℕ, ∀ L > L0,
    GroundStateNondegenerate (latticeHam L d h1 hrow hcol) ∧
      HasGapAtLeast (latticeHam L d h1 hrow hcol) γ

/-- **Definition 1 (Gapped).** The family `{H^{Λ(L)}}` is gapped if it is gapped with some
constant gap `γ > 0`. -/
def Gapped (d : ℕ) (h1 : Matrix (Fin d) (Fin d) ℂ)
    (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  ∃ γ : ℝ, GappedWithGap d h1 hrow hcol γ

/-- **Definition 2 (Gapless).** The family `{H^{Λ(L)}}` is gapless if there is a constant
`c > 0` such that for every `ε > 0` there is an `L₀` such that for all `L > L₀` every point
of the interval `[λ₀(H^{Λ(L)}), λ₀(H^{Λ(L)}) + c]` lies within distance `ε` of the spectrum
of `H^{Λ(L)}`. -/
def Gapless (d : ℕ) (h1 : Matrix (Fin d) (Fin d) ℂ)
    (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  ∃ c > 0, ∀ ε > 0, ∃ L0 : ℕ, ∀ L > L0,
    ∀ x ∈ Set.Icc (gsEnergy (latticeHam L d h1 hrow hcol))
        (gsEnergy (latticeHam L d h1 hrow hcol) + c),
      ∃ μ ∈ specReal (latticeHam L d h1 hrow hcol), |x - μ| ≤ ε

/-- The family `{H^{Λ(L)}}` has ground state energy density `E`, i.e.
`E = lim_{L→∞} λ₀(H^{Λ(L)})/L²`. -/
def HasGsEnergyDensity (d : ℕ) (h1 : Matrix (Fin d) (Fin d) ℂ)
    (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (E : ℝ) : Prop :=
  Filter.Tendsto (fun L : ℕ => gsEnergy (latticeHam L d h1 hrow hcol) / (L : ℝ) ^ 2)
    Filter.atTop (nhds E)

/-- The family `{H^{Λ(L)}}` is frustration free: all interaction terms are positive
semidefinite and the ground state energy vanishes for every lattice size. -/
def FrustrationFree (d : ℕ) (h1 : Matrix (Fin d) (Fin d) ℂ)
    (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  h1.PosSemidef ∧ hrow.PosSemidef ∧ hcol.PosSemidef ∧
    ∀ L : ℕ, 0 < L → gsEnergy (latticeHam L d h1 hrow hcol) = 0

end UndecidableSpectralGap
