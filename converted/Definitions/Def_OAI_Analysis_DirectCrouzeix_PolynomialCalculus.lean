/-
prove2.me platform library module `Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/PolynomialCalculus.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

def coefficientEmbedding (n m : ℕ) :
    Matrix (Fin m) (Fin m) ℂ →+*
      Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ where
  toFun B := (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ B
  map_zero' := Matrix.kronecker_zero _
  map_one' := Matrix.one_kronecker_one
  map_add' B C := Matrix.kronecker_add _ B C
  map_mul' B C := by
    simpa using Matrix.mul_kronecker_mul
      (1 : Matrix (Fin n) (Fin n) ℂ) 1 B C

def tensorPolynomial {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Polynomial (Matrix (Fin m) (Fin m) ℂ) →+*
      Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  Polynomial.eval₂RingHom' (coefficientEmbedding n m)
    (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) (by
      intro B
      change (1 ⊗ₖ B) * (A ⊗ₖ 1) = (A ⊗ₖ 1) * (1 ⊗ₖ B)
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
      simp)

def coefficientPolynomial {m d : ℕ}
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    Polynomial (Matrix (Fin m) (Fin m) ℂ) :=
  ∑ k : Fin (d + 1), Polynomial.C (B k) * Polynomial.X ^ (k : ℕ)

@[simp] theorem tensorPolynomial_C {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin m) (Fin m) ℂ) :
    tensorPolynomial A (Polynomial.C B) = (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ B := by
  exact Polynomial.eval₂_C _ _

@[simp] theorem tensorPolynomial_X {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    tensorPolynomial (m := m) A Polynomial.X = A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ) := by
  exact Polynomial.eval₂_X _ _

end DirectCrouzeix

end

end OAI
