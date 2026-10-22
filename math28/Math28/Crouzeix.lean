import Mathlib
import BookProof.Textbook.ChapterH4
import BookProof.Textbook.ChapterH9

/-!
# Crouzeix's inequality with constant `2` (openai/math family 325), as named hypotheses

**Source** (read-only snapshot, Lean v4.34.1, not imported):

* `OAI.CompleteCrouzeix.main` — `math/OAI/Analysis/NumericalRange/Main.lean`, definitions in
  `math/OAI/Analysis/NumericalRange/Model.lean`:
  `UniversalBound 2 ∧ ∀ C : ℝ, UniversalBound C → 2 ≤ C` — the matrix-coefficient
  (completely bounded) Crouzeix inequality with the sharp constant `2`, for every square
  complex matrix.
* `OAI.CrouzeixHilbert.hilbert` — `math/OAI/Analysis/Crouzeix/HilbertInequality.lean`
  (definitions in `math/OAI/Analysis/Crouzeix/Definitions.lean`): for every complex Hilbert
  space `H` and bounded `A`, the polynomial, holomorphic and rational functional calculi of `A`
  (with matrix coefficients) are bounded by `2 · sup` over the closure of the numerical range.

Both import closures were checked textually: they contain no `sorry`, no `axiom` and no
`native_decide`, and import nothing outside `Mathlib` and `OAI`.  They were **not**
re-elaborated here: the snapshot pins Lean v4.34.1 and this repository pins v4.28.0.

**Caveat.**  The scalar bound with constant `2` is Crouzeix's conjecture; the best constant in
the published literature known to this file's author is `1 + √2` (Crouzeix–Palencia).  Treat
both statements strictly as named hypotheses: nothing below assumes them except through an
explicit hypothesis argument.

## What this module states

* `CompleteCrouzeix.Main` — the first source theorem, transcribed with its definitions
  verbatim (every name re-checked on Lean v4.28.0 by elaborating this file).
* `HilbertPolynomialBound` — the scalar-polynomial instance of the second source theorem,
  `‖p(A)‖ ≤ 2 M` whenever `‖p‖ ≤ M` on the numerical range, stated with this project's
  numerical range `BookProof.ChapterH9.numRange` and the polynomial calculus `Polynomial.aeval`.
  The source states the bound with `m × m` matrix coefficients on the completed tensor product
  `H ⊗ ℂᵐ`; the scalar instance is the case `m = 1`.  That specialization (identifying
  `H ⊗ ℂ¹` with `H`) is a reading of the source statement, not a formal derivation.

## Proved bridges into the project (no hypothesis beyond the named one)

* `norm_aeval_le_of_numRange_subset` — the bound over any set `Σ ⊇ W(A)`: this is the form of
  the Crouzeix hypothesis of the SIRK chapters (`BookProof/Textbook/ChapterH4.lean`, eq. 14),
  where `Σ` is a convex set containing the numerical range.  The monotonicity in `Σ` is the
  one-line closure step named in `CONSOLIDATED_PLAN.md` (§ "the conversion lane", item 6).
* `sirk_error_bound_of_hilbertPolynomialBound` — `ChapterH4.sirk_error_bound` with its two
  Crouzeix inputs discharged from `HilbertPolynomialBound`, for polynomial error functions:
  `‖φ_k(A)v − V ψ(B) V∗ v‖ ≤ 4 · D · ‖v‖`.
-/

namespace Math28

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

/-! ## The source statement `OAI.CompleteCrouzeix.main`, verbatim -/

namespace CompleteCrouzeix

/-- Numerical range of a square complex matrix (source: `CompleteCrouzeix.numericalRange`). -/
def numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Set ℂ :=
  {z | ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    inner ℂ x (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x) = z}

/-- A polynomial with `m × m` matrix coefficients, evaluated at `z`. -/
def polynomialValue {m d : ℕ} (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ)
    (z : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ∑ k : Fin (d + 1), (z ^ (k : ℕ)) • B k

/-- The same polynomial evaluated at the matrix `A`: `∑ₖ Aᵏ ⊗ Bₖ`. -/
def polynomialAt {n m d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  ∑ k : Fin (d + 1), Matrix.kronecker (A ^ (k : ℕ)) (B k)

/-- The maximum of `‖p(z)‖` over the numerical range. -/
def rangeMaximum {n m d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  sSup ((fun z => ‖polynomialValue B z‖) '' numericalRange A)

/-- The matrix-coefficient Crouzeix inequality with constant `C`. -/
def UniversalBound (C : ℝ) : Prop :=
  ∀ (n m d : ℕ), 0 < n → 0 < m →
    ∀ (A : Matrix (Fin n) (Fin n) ℂ)
      (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ),
      ‖polynomialAt A B‖ ≤ C * rangeMaximum A B

/-- **Named hypothesis — `OAI.CompleteCrouzeix.main`.**  The complete Crouzeix inequality holds
with constant `2`, and `2` is optimal. -/
def Main : Prop := UniversalBound 2 ∧ ∀ C : ℝ, UniversalBound C → 2 ≤ C

end CompleteCrouzeix

/-! ## The Hilbert-space polynomial form -/

open BookProof.ChapterH9

/-- **Named hypothesis — scalar instance of `OAI.CrouzeixHilbert.hilbert`.**  For every complex
Hilbert space `E`, bounded operator `A` and polynomial `p`, if `‖p‖ ≤ M` on the numerical range
of `A` (and `M ≥ 0`, which matters only for `E = 0`), then `‖p(A)‖ ≤ 2 M`. -/
def HilbertPolynomialBound : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (p : Polynomial ℂ) (M : ℝ), 0 ≤ M →
    (∀ z ∈ numRange A, ‖p.eval z‖ ≤ M) → ‖Polynomial.aeval A p‖ ≤ 2 * M

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Crouzeix over a set containing the numerical range.**  Under `HilbertPolynomialBound`, if
`Σ ⊇ W(A)` and `‖p‖ ≤ D` on `Σ`, then `‖p(A)‖ ≤ 2 D`.  This is the form in which the SIRK
chapters use Crouzeix's inequality (`Σ` convex, containing the numerical range). -/
theorem norm_aeval_le_of_numRange_subset (hC : HilbertPolynomialBound) (A : E →L[ℂ] E)
    (p : Polynomial ℂ) {S : Set ℂ} (hS : numRange A ⊆ S) {D : ℝ} (hD : 0 ≤ D)
    (hp : ∀ z ∈ S, ‖p.eval z‖ ≤ D) : ‖Polynomial.aeval A p‖ ≤ 2 * D :=
  hC E A p D hD fun z hz => hp z (hS hz)

/-- **The SIRK error bound with the Crouzeix inputs discharged by the named hypothesis.**
`ChapterH4.sirk_error_bound` takes the two operator-norm bounds `‖ψ(X) − r(X)‖ ≤ C D` and
`‖ψ(B) − r(B)‖ ≤ C D` as hypotheses.  If both error operators are polynomial calculi
`p(X)`, `q(B)` of polynomials bounded by `D` on a set `Σ` containing both numerical ranges, then
`HilbertPolynomialBound` supplies them with `C = 2`. -/
theorem sirk_error_bound_of_hilbertPolynomialBound (hC : HilbertPolynomialBound)
    (V : F →L[ℂ] E) (phiA psiX rX X : E →L[ℂ] E) (psiB rB B : F →L[ℂ] F)
    (p q : Polynomial ℂ) {S : Set ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hphi : phiA = psiX)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hrt : ∀ v : E, rX v = V (rB (V.adjoint v)))
    (hpX : psiX - rX = Polynomial.aeval X p) (hqB : psiB - rB = Polynomial.aeval B q)
    (hSX : numRange X ⊆ S) (hSB : numRange B ⊆ S)
    (hp : ∀ z ∈ S, ‖p.eval z‖ ≤ D) (hq : ∀ z ∈ S, ‖q.eval z‖ ≤ D) (v : E) :
    ‖phiA v - V (psiB (V.adjoint v))‖ ≤ 4 * D * ‖v‖ := by
  have h1 : ‖psiX - rX‖ ≤ 2 * D := by
    rw [hpX]; exact norm_aeval_le_of_numRange_subset hC X p hSX hD hp
  have h2 : ‖psiB - rB‖ ≤ 2 * D := by
    rw [hqB]; exact norm_aeval_le_of_numRange_subset hC B q hSB hD hq
  have h := BookProof.ChapterH4.sirk_error_bound V phiA psiX rX psiB rB 2 D hphi hViso hVadj
    hrt h1 h2 v
  linarith

end

end Math28
