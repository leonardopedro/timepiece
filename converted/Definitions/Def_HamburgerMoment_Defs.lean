/-
prove2.me platform library module `Definitions.Def_HamburgerMoment_Defs`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_HamburgerMoment_Defs.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

/-!
# Hamburger moment problem — definitions

Source: Wikipedia, "Hamburger moment problem" (revision oldid=1356180072),
sections "Hamburger moment problem" (lead), "Characterization" and
"Uniqueness of solutions".
-/

namespace HamburgerMoment

open MeasureTheory

/-- `μ` is a solution of the Hamburger moment problem for `m`: `μ` is a positive Borel
measure on `ℝ` all of whose power moments exist (are finite) and satisfy
`m n = ∫_{-∞}^{∞} x ^ n dμ(x)` for every `n ≥ 0`. -/
def IsMomentMeasure (m : ℕ → ℝ) (μ : Measure ℝ) : Prop :=
  ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ ∧ ∫ x, x ^ n ∂μ = m n

/-- The Hamburger moment problem for `m` is solvable: `m` is the moment sequence of some
positive Borel measure on the real line. -/
def IsMomentSequence (m : ℕ → ℝ) : Prop :=
  ∃ μ : Measure ℝ, IsMomentMeasure m μ

/-- The quadratic form `∑_{j,k ≥ 0} m_{j+k} c_j \overline{c_k}` of the Hankel kernel
`A = (m_{j+k})_{j,k ≥ 0}`, evaluated at a finitary complex sequence `c`
(a finitely supported function `ℕ →₀ ℂ`). -/
noncomputable def hankelForm (m : ℕ → ℝ) (c : ℕ →₀ ℂ) : ℂ :=
  ∑ j ∈ c.support, ∑ k ∈ c.support, (m (j + k) : ℂ) * c j * starRingEnd ℂ (c k)

open scoped ComplexOrder in
/-- The Hankel kernel `A = (m_{j+k})_{j,k ≥ 0}` is positive definite in the sense of the
source: `∑_{j,k ≥ 0} m_{j+k} c_j \overline{c_k} ≥ 0` for every finitary complex sequence
`(c_j)_{j ≥ 0}`. Here `≥ 0` is the order on `ℂ`, i.e. the sum is a nonnegative real. -/
def HankelPosDef (m : ℕ → ℝ) : Prop :=
  ∀ c : ℕ →₀ ℂ, 0 ≤ hankelForm m c

/-- The `(n + 1) × (n + 1)` Hankel matrix `Δ_n = (m_{i+j})_{0 ≤ i, j ≤ n}`. -/
def hankelMatrix (m : ℕ → ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => m (i.val + j.val)

end HamburgerMoment
