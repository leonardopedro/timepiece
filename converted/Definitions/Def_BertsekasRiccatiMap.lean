/-
prove2.me platform library module `Definitions.Def_BertsekasRiccatiMap`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_BertsekasRiccatiMap.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

open Matrix

/-- One step of the discrete-time Riccati equation of Bertsekas, "Dynamic
Programming and Optimal Control", Vol. I, 3rd ed., Section 4.1 (Eq. (4.8),
time-reversed indexing):
`P ↦ Aᵀ (P - P B (Bᵀ P B + R)⁻¹ Bᵀ P) A + Q`. -/
noncomputable def BertsekasRiccatiMap {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Aᵀ * (P - P * B * (Bᵀ * P * B + R)⁻¹ * Bᵀ * P) * A + Q

/-- Definition 4.1.1 of Bertsekas, Vol. I, 3rd ed.: the pair `(A, B)`, with `A`
an `n × n` matrix and `B` an `n × m` matrix, is controllable if the `n × nm`
controllability matrix `[B, AB, A²B, …, A^{n-1}B]` has full rank `n`. -/
noncomputable def BertsekasControllablePair {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  (Matrix.of fun (i : Fin n) (p : Fin n × Fin m) =>
    (A ^ (p.1 : ℕ) * B) i p.2).rank = n

/-- Definition 4.1.1 of Bertsekas, Vol. I, 3rd ed.: the pair `(A, C)`, with `A`
an `n × n` matrix and `C` a `q × n` matrix, is observable if the pair
`(Aᵀ, Cᵀ)` is controllable. -/
noncomputable def BertsekasObservablePair {n q : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin q) (Fin n) ℝ) : Prop :=
  BertsekasControllablePair Aᵀ Cᵀ
