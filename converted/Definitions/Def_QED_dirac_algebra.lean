/-
prove2.me platform library module `Definitions.Def_QED_dirac_algebra`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_QED_dirac_algebra.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_QED_minkowski_spacetime

namespace QED

/-- `IsDiracRepresentation γ` says that the four complex `4 × 4` matrices
`γ 0, γ 1, γ 2, γ 3` are Dirac matrices for the metric `η` with signature
`(+, -, -, -)`:

* the Clifford (anticommutation) relation `γ^μ γ^ν + γ^ν γ^μ = 2 η^{μν} I₄`;
* the hermiticity relation `(γ^μ)† = γ^0 γ^μ γ^0`,
  i.e. `γ^0` is hermitian and `γ^1, γ^2, γ^3` are anti-hermitian. -/
def IsDiracRepresentation (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  (∀ μ ν : Fin 4,
      γ μ * γ ν + γ ν * γ μ = (2 * (minkowski μ ν : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) ∧
  (∀ μ : Fin 4, (γ μ).conjTranspose = γ 0 * γ μ * γ 0)

/-- The gamma matrices in the standard Dirac basis. -/
def diracGamma : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ
  | ⟨0, _⟩ => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]
  | ⟨1, _⟩ => !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
  | ⟨2, _⟩ => !![0, 0, 0, -Complex.I; 0, 0, Complex.I, 0;
                 0, Complex.I, 0, 0; -Complex.I, 0, 0, 0]
  | ⟨3, _⟩ => !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]

/-- The Dirac adjoint pairing `ψ̄ M χ = ψ† γ^0 M χ` of two spinors, for a
`4 × 4` matrix `M` inserted between them. -/
noncomputable def diracPairing (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ)
    (φ χ : Fin 4 → ℂ) : ℂ :=
  ∑ i : Fin 4, ∑ j : Fin 4, (starRingEnd ℂ) (φ i) * ((γ 0 * M) i j) * χ j

end QED
