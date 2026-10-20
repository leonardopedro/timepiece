/-
prove2.me platform library module `Definitions.Def_NewMinimalStandardModel_Defs`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_NewMinimalStandardModel_Defs.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

/-!
# The new Minimal Standard Model — shared definitions

Source: H. Davoudiasl, R. Kitano, T. Li, H. Murayama, *The new Minimal Standard Model*,
Phys. Lett. B 609 (2005) 117–123, doi:10.1016/j.physletb.2005.01.026.

* Neutrino sector: Eq. (4) (p. 119) with two right-handed neutrinos `N_α`, `α = 1, 2`,
  in the basis where the right-handed-neutrino mass matrix is real and diagonal.
* Inflaton sector: Eq. (5) (p. 119), quadratic chaotic inflation, with the standard
  slow-roll observables used on p. 122.
-/

namespace NewMinimalStandardModel

open Matrix

/-! ## Neutrino sector (Eq. (4)) -/

/-- Dirac mass matrix `m_D = h_ν v / √2` (a `2 × 3` complex matrix, rows indexed by the
right-handed neutrinos `α`, columns by the lepton doublets `i`), obtained from the Yukawa
coupling `h_ν^{αi} N_α L_i H̃` of Eq. (4) with Higgs vacuum expectation value `⟨H⟩ = v / √2`. -/
noncomputable def diracMass (v : ℝ) (hν : Matrix (Fin 2) (Fin 3) ℂ) :
    Matrix (Fin 2) (Fin 3) ℂ :=
  ((v : ℂ) / (Real.sqrt 2 : ℂ)) • hν

/-- Majorana mass matrix of the two right-handed neutrinos, `diag(M_1, M_2)`, in the basis
where it is real and diagonal (Eq. (4), p. 119). -/
noncomputable def rhNeutrinoMass (M : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun α => (M α : ℂ)

/-- The full `5 × 5` complex symmetric Majorana mass matrix of the neutral leptons after
electroweak symmetry breaking, in the basis `(ν_1, ν_2, ν_3, N_1, N_2)`:
`[[0, m_Dᵀ], [m_D, diag(M_1, M_2)]]`. -/
noncomputable def neutralLeptonMassMatrix (v : ℝ) (hν : Matrix (Fin 2) (Fin 3) ℂ)
    (M : Fin 2 → ℝ) : Matrix (Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks 0 (diracMass v hν)ᵀ (diracMass v hν) (rhNeutrinoMass M)

/-- The seesaw light-neutrino (left-handed) Majorana mass matrix
`m_ν = - m_Dᵀ diag(M_1, M_2)⁻¹ m_D` (a `3 × 3` complex symmetric matrix). -/
noncomputable def seesawMassMatrix (v : ℝ) (hν : Matrix (Fin 2) (Fin 3) ℂ)
    (M : Fin 2 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  -((diracMass v hν)ᵀ * (rhNeutrinoMass M)⁻¹ * diracMass v hν)

/-- The physical masses of the Majorana mass eigenstates described by a square complex mass
matrix `A`: its singular values, i.e. the square roots of the eigenvalues of the Hermitian
positive semidefinite matrix `Aᴴ A` (listed in the order chosen by Mathlib's spectral
theorem). -/
noncomputable def majoranaMasses {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : n → ℝ :=
  fun i => Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-! ## Inflaton sector (Eq. (5)) and slow-roll observables -/

/-- The quadratic inflaton potential `V(φ) = m² φ² / 2` driving chaotic inflation
(the mass term of Eq. (5); the cubic and quartic terms are neglected, p. 119). -/
noncomputable def quadraticPotential (m : ℝ) : ℝ → ℝ :=
  fun φ => m ^ 2 * φ ^ 2 / 2

/-- First slow-roll parameter `ε(φ) = (M_Pl² / 2) (V'(φ) / V(φ))²`, with `M_Pl` the reduced
Planck mass. -/
noncomputable def slowRollEpsilon (V : ℝ → ℝ) (Mpl φ : ℝ) : ℝ :=
  Mpl ^ 2 / 2 * (deriv V φ / V φ) ^ 2

/-- Second slow-roll parameter `η(φ) = M_Pl² V''(φ) / V(φ)`. -/
noncomputable def slowRollEta (V : ℝ → ℝ) (Mpl φ : ℝ) : ℝ :=
  Mpl ^ 2 * deriv (deriv V) φ / V φ

/-- Number of e-folds of slow-roll inflation between field values `φ_end` and `φ`:
`N = (1 / M_Pl²) ∫_{φ_end}^{φ} V(ψ) / V'(ψ) dψ`. -/
noncomputable def efolds (V : ℝ → ℝ) (Mpl φend φ : ℝ) : ℝ :=
  (1 / Mpl ^ 2) * ∫ ψ in φend..φ, V ψ / deriv V ψ

/-- Slow-roll scalar spectral index `n_s = 1 - 6 ε + 2 η`. -/
noncomputable def spectralIndex (V : ℝ → ℝ) (Mpl φ : ℝ) : ℝ :=
  1 - 6 * slowRollEpsilon V Mpl φ + 2 * slowRollEta V Mpl φ

/-- Slow-roll tensor-to-scalar ratio `r = 16 ε`. -/
noncomputable def tensorToScalarRatio (V : ℝ → ℝ) (Mpl φ : ℝ) : ℝ :=
  16 * slowRollEpsilon V Mpl φ

end NewMinimalStandardModel
