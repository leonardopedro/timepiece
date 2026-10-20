/-
prove2.me platform library module `Definitions.Def_DirectCrouzeix`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_DirectCrouzeix.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DirectCrouzeix.lean; bytes 16..1175
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

def numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Set ℂ :=
  {z | ∃ u : EuclideanSpace ℂ (Fin n), ‖u‖ = 1 ∧
    inner ℂ u (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u) = z}

def polynomialValue {m d : ℕ} (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ)
    (z : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ∑ k : Fin (d + 1), z ^ (k : ℕ) • B k

def tensorEvaluation {n m d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  ∑ k : Fin (d + 1), (A ^ (k : ℕ)) ⊗ₖ (B k)

def rangeMaximum {n m d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  sSup ((fun z => ‖polynomialValue B z‖) '' numericalRange A)

def UniversalBound (c : ℝ) : Prop :=
  ∀ (n m d : ℕ), 0 < n → 0 < m →
    ∀ (A : Matrix (Fin n) (Fin n) ℂ)
      (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ),
      ‖tensorEvaluation A B‖ ≤ c * rangeMaximum A B



end DirectCrouzeix
end
end OAI
