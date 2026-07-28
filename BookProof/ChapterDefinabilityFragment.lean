import Mathlib

/-!
# Definability / Conservativity Fragment

This module formalizes the precise, provable fragment of the claim that
the completion of the finitely-supported core does not leak provability
assumptions (PA / Gödelian self-reference).

The full metamathematical claim "the completion is a conservative extension"
is documented here but NOT formalized as a Lean theorem. The formal content
is the `Finsupp.finite_support` lemma: in the finitely-supported fragment,
every denotable vector is finitely supported.
-/

open Finset

/-- In the finitely-supported fragment, every vector is finitely supported.
    This is the core definability result: there are no "infinite" vectors
    definable in the finite-support language. -/
theorem finitely_supported_vectors_are_finite (v : ℕ →₀ ℝ) :
    (v.support : Set ℕ).Finite := by
  simp

/-- No vector in the completion is term-denotable unless it is finitely supported.
    This is the contrapositive: if a vector requires infinite support,
    it cannot be constructed from finitely many basis vectors. -/
theorem non_finitely_supported_not_term_denotable (v : ℕ → ℝ)
    (h_infinite : ¬ (Function.support v).Finite) :
    v ∉ Set.range (fun (w : ℕ →₀ ℝ) => fun n => w n) := by
  intro h
  rcases h with ⟨w, hw⟩
  apply h_infinite
  rw [← hw]
  exact Finsupp.finite_support w

/-- The formal statement: the completion does not make more vectors definable
    than were already definable in the finite-support fragment.

    This is a tautology in the formalism: the completion only adds limit points
    of Cauchy sequences, and a limit point cannot be term-denotable
    (term-denotable vectors have finite support, but limit points in an
    infinite-dimensional space typically do not).

    **This is NOT a theorem in Lean.** It is a metamathematical observation
    documented here for completeness. -/
theorem conservativity_documentation : True := by
  -- The full conservativity claim requires external justification
  -- (e.g., forcing arguments in set theory)
  -- We document it here but do not attempt to prove it in Lean
  trivial
