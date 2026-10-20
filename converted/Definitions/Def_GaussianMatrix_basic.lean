/-
prove2.me platform library module `Definitions.Def_GaussianMatrix_basic`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_GaussianMatrix_basic.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

/-!
# Standard Gaussian matrices: basic definitions

Shared vocabulary for the "Gaussian Random Matrices" mission series.

* `GaussianMatrix.gaussianMatrix p m` — the law of a `p × m` matrix with independent
  standard normal entries, as the product measure on `Fin p → Fin m → ℝ`. A sample `G` is
  viewed as a matrix via `Matrix.of G`.
* `GaussianMatrix.frobSq`, `frobNorm` — squared Frobenius norm `∑ᵢⱼ Aᵢⱼ²` and its square root.
* `GaussianMatrix.specNorm` — the spectral norm (largest singular value), i.e. Mathlib's
  `ℓ₂ → ℓ₂` operator norm `Matrix.Norms.L2Operator`.
* `GaussianMatrix.sMin` — the smallest singular value of a tall `N × n` matrix,
  `inf { ‖A x‖₂ : ‖x‖₂ = 1 }` (for a wide matrix apply it to the transpose).
* `GaussianMatrix.pinvR` — `Gᵀ (G Gᵀ)⁻¹`, the Moore–Penrose pseudoinverse of a matrix with
  full row rank (Mathlib's `⁻¹` is total, returning `0` on a singular input).
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator

namespace GaussianMatrix

/-- The law of a `p × m` standard Gaussian matrix: independent `N(0,1)` entries, as a product
measure on `Fin p → Fin m → ℝ`. `Matrix.of G` is the matrix view of a sample `G`. -/
noncomputable def gaussianMatrix (p m : ℕ) : Measure (Fin p → Fin m → ℝ) :=
  Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal 0 1

instance gaussianMatrix_isProbabilityMeasure (p m : ℕ) :
    IsProbabilityMeasure (gaussianMatrix p m) := by
  unfold gaussianMatrix; infer_instance

/-- Squared Frobenius norm `‖A‖_F² = ∑ᵢ ∑ⱼ Aᵢⱼ²`. -/
def frobSq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

/-- Frobenius norm `‖A‖_F = √(∑ᵢⱼ Aᵢⱼ²)`. -/
noncomputable def frobNorm {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) : ℝ :=
  Real.sqrt (frobSq A)

/-- Spectral norm `‖A‖ = max_{‖x‖₂ = 1} ‖A x‖₂` (largest singular value): Mathlib's
`ℓ₂ → ℓ₂` operator norm of a real matrix. -/
noncomputable def specNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) : ℝ := ‖A‖

/-- Smallest singular value of a tall matrix `A : Matrix N n`:
`σ_min(A) = inf { ‖A x‖₂ : x ∈ ℝⁿ, ‖x‖₂ = 1 }` (equal to `0` when `n = 0`, by the real
convention `inf ∅ = 0`). For a wide matrix use `sMin Aᵀ`. -/
noncomputable def sMin {N n : Type*} [Fintype N] [Fintype n] (A : Matrix N n ℝ) : ℝ :=
  ⨅ x : {x : n → ℝ // x ⬝ᵥ x = 1}, Real.sqrt ((A *ᵥ x.1) ⬝ᵥ (A *ᵥ x.1))

/-- Right pseudoinverse `G† = Gᵀ (G Gᵀ)⁻¹` of a matrix `G : Matrix m n`; it is the Moore–Penrose
pseudoinverse whenever `G Gᵀ` is invertible (full row rank), and `0` otherwise. -/
noncomputable def pinvR {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (G : Matrix m n ℝ) : Matrix n m ℝ :=
  Gᵀ * (G * Gᵀ)⁻¹

end GaussianMatrix
