/-
prove2.me platform library module `Definitions.Def_WeinbergLeptons_Model`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_WeinbergLeptons_Model.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

/-!
# Weinberg, "A Model of Leptons" (Phys. Rev. Lett. 19, 1264 (1967)) — tree-level data

A real gauge-field configuration at a point is encoded as a vector `V : Fin 4 → ℝ` with
`V 0 = A¹`, `V 1 = A²`, `V 2 = A³` (the isospin gauge fields) and `V 3 = B` (the hypercharge
gauge field). `g`, `g'` are the isospin and hypercharge gauge couplings and `lam` is the
vacuum expectation value `λ = ⟨φ⁰⟩` of the scalar doublet.
-/

namespace WeinbergLeptons

/-- The spin-one mass terms of the Lagrangian after symmetry breaking, eq. (7):
`-(1/8) λ² g² [(A¹)² + (A²)²] - (1/8) λ² (g A³ + g' B)²`. -/
noncomputable def vectorMassTerm (g g' lam : ℝ) (V : Fin 4 → ℝ) : ℝ :=
  -(1 / 8) * lam ^ 2 * g ^ 2 * (V 0 ^ 2 + V 1 ^ 2) - (1 / 8) * lam ^ 2 * (g * V 2 + g' * V 3) ^ 2

/-- The (mass)² matrix of the spin-one fields `(A¹, A², A³, B)`: the symmetric matrix `𝓜²`
whose quadratic form reproduces eq. (7) as `-(1/2) Vᵀ 𝓜² V`. -/
noncomputable def massSqMatrix (g g' lam : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![lam ^ 2 * g ^ 2 / 4, 0, 0, 0;
     0, lam ^ 2 * g ^ 2 / 4, 0, 0;
     0, 0, lam ^ 2 * g ^ 2 / 4, lam ^ 2 * g * g' / 4;
     0, 0, lam ^ 2 * g * g' / 4, lam ^ 2 * g' ^ 2 / 4]

/-- Coefficient vector of the charged field `W = 2^{-1/2} (A¹ + i A²)`, eq. (8). -/
noncomputable def wVec : Fin 4 → ℂ :=
  ![1 / (Real.sqrt 2 : ℂ), Complex.I / (Real.sqrt 2 : ℂ), 0, 0]

/-- Coefficient vector of `Z = (g² + g'²)^{-1/2} (g A³ + g' B)`, eq. (10). -/
noncomputable def zVec (g g' : ℝ) : Fin 4 → ℝ :=
  (1 / Real.sqrt (g ^ 2 + g' ^ 2)) • ![0, 0, g, g']

/-- Coefficient vector of `A = (g² + g'²)^{-1/2} (-g' A³ + g B)`, eq. (11). -/
noncomputable def photonVec (g g' : ℝ) : Fin 4 → ℝ :=
  (1 / Real.sqrt (g ^ 2 + g' ^ 2)) • ![0, 0, -g', g]

/-- `M_W = (1/2) λ g`, eq. (9). -/
noncomputable def wMass (g lam : ℝ) : ℝ := lam * g / 2

/-- `M_Z = (1/2) λ (g² + g'²)^{1/2}`, eq. (12). -/
noncomputable def zMass (g g' lam : ℝ) : ℝ := lam * Real.sqrt (g ^ 2 + g' ^ 2) / 2

/-- The rationalized electric charge `e = g g' / (g² + g'²)^{1/2}`, eq. (15). -/
noncomputable def electricCharge (g g' : ℝ) : ℝ := g * g' / Real.sqrt (g ^ 2 + g' ^ 2)

/-- The weak coupling constant defined by the first equality of eq. (16),
`G_W / √2 = g² / (8 M_W²)`, i.e. `G_W = √2 g² / (8 M_W²)`. -/
noncomputable def weakCoupling (g lam : ℝ) : ℝ := Real.sqrt 2 * g ^ 2 / (8 * wMass g lam ^ 2)

/-- The electron mass `M_e = λ G_e`, where `G_e` is the electron–scalar Yukawa coupling. -/
noncomputable def electronMass (Ge lam : ℝ) : ℝ := lam * Ge

/-- The scalar self-interaction terms of the Lagrangian (4), `-M₁² φ†φ + h (φ†φ)²`, evaluated on
the vacuum configuration `φ = (x, 0)` with `x` real. -/
noncomputable def scalarPotentialTerm (M1 h x : ℝ) : ℝ := -M1 ^ 2 * x ^ 2 + h * x ^ 4

end WeinbergLeptons
