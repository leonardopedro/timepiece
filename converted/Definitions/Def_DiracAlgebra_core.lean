/-
prove2.me platform library module `Definitions.Def_DiracAlgebra_core`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_DiracAlgebra_core.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace DiracEquation

open Matrix

/-- The Minkowski metric `η^{μν} = diag(1, -1, -1, -1)` in the mainly-negative signature,
with complex entries. -/
def eta (mu nu : Fin 4) : ℂ := if mu = nu then (if mu = 0 then 1 else -1) else 0

/-- `IsGammaFamily g` says that the four `4 × 4` complex matrices `g 0, g 1, g 2, g 3` satisfy
the defining relation of the Dirac algebra, `{γ^μ, γ^ν} = 2 η^{μν} I₄`. -/
def IsGammaFamily (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ mu nu, g mu * g nu + g nu * g mu = (2 * eta mu nu) • (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- The Feynman slash `p̸ = γ^μ p_μ` of a covector `p` with respect to a family `g` of gamma
matrices. -/
noncomputable def slash (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (p : Fin 4 → ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ mu, p mu • g mu

/-- The three Pauli matrices `σ₁, σ₂, σ₃` (indexed by `0, 1, 2`). -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, 1; 1, 0]
  | 1 => !![0, -Complex.I; Complex.I, 0]
  | 2 => !![1, 0; 0, -1]

/-- The gamma matrices in the Dirac representation:
`γ⁰ = [[I₂, 0], [0, -I₂]]` and `γⁱ = [[0, σᵢ], [-σᵢ, 0]]`, written out entrywise. -/
def gammaDirac : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ
  | 0 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]
  | 1 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
  | 2 => !![0, 0, 0, -Complex.I; 0, 0, Complex.I, 0; 0, Complex.I, 0, 0; -Complex.I, 0, 0, 0]
  | 3 => !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]

/-- The Dirac-representation matrix `β = γ⁰` of the Hamiltonian form of the Dirac equation. -/
def betaDirac : Matrix (Fin 4) (Fin 4) ℂ := gammaDirac 0

/-- The Dirac-representation matrices `αⁱ = γ⁰ γⁱ` of the Hamiltonian form of the Dirac
equation (`i = 1, 2, 3`, indexed by `Fin 3` through `Fin.succ`). -/
noncomputable def alphaDirac (i : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  gammaDirac 0 * gammaDirac i.succ

end DiracEquation
