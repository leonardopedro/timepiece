/-
prove2.me platform library module `Definitions.Def_ChatterjeeQFT_SL2C`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_ChatterjeeQFT_SL2C.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_ChatterjeeQFT_Minkowski

/-!
# `SL(2,C)`, the covering map onto the restricted Lorentz group, and pure boosts

Following S. Chatterjee, *Lectures on Quantum Field Theory*, Lecture 25.
-/

namespace ChatterjeeQFT

open Matrix

/-- The Hermitian matrix attached to a four-vector,
`M(x) = [[x⁰ + x³, x¹ - i x²], [x¹ + i x², x⁰ - x³]]`. -/
def hermOfVec (x : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x 0 : ℂ) + (x 3 : ℂ), (x 1 : ℂ) - Complex.I * (x 2 : ℂ);
     (x 1 : ℂ) + Complex.I * (x 2 : ℂ), (x 0 : ℂ) - (x 3 : ℂ)]

/-- The four-vector attached to a `2 × 2` complex matrix; it inverts `hermOfVec` on Hermitian
matrices. -/
noncomputable def vecOfHerm (H : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℝ :=
  ![((H 0 0 + H 1 1) / 2).re, ((H 0 1 + H 1 0) / 2).re,
    ((H 1 0 - H 0 1) / (2 * Complex.I)).re, ((H 0 0 - H 1 1) / 2).re]

/-- The action `κ(A)` of `A ∈ SL(2,C)` on `R^{1,3}`, determined by `M(κ(A)x) = A M(x) A†`. -/
noncomputable def kappa (A : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  vecOfHerm (A * hermOfVec x * Aᴴ)

/-- The rest four-momentum `p* = (m, 0, 0, 0)`. -/
def restMomentum (m : ℝ) : Fin 4 → ℝ := ![m, 0, 0, 0]

/-- The pure boost `V_p ∈ SL(2,C)` taking `p*` to `p`: the positive-definite square root of
`M(p)/m`, given explicitly by `V_p = (M(p)/m + I) / √(2 + 2p⁰/m)`. -/
noncomputable def pureBoost (m : ℝ) (p : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt (2 + 2 * p 0 / m) : ℝ) : ℂ)⁻¹ • ((m : ℂ)⁻¹ • hermOfVec p + 1)

end ChatterjeeQFT
