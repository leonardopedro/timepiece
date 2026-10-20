/-
prove2.me platform library module `Definitions.Def_matrix_completion_bernoulli`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_matrix_completion_bernoulli.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_matrix_completion_svd

/-!
Bernoulli observation model for matrix completion.

The paper proves the probabilistic estimates first for independent Bernoulli
sampling with inclusion probability `p = m / (n1 * n2)`, then transfers the
failure estimate to the fixed-cardinality uniform model.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Probability weight of a particular observation set in the independent
Bernoulli model with inclusion probability `p`. -/
noncomputable def bernoulliObservationWeight {n1 n2 : Nat} (p : Real)
    (Omega : Finset (Fin n1 × Fin n2)) : Real :=
  p ^ Omega.card *
    (1 - p) ^ (Fintype.card (Fin n1 × Fin n2) - Omega.card)

/-- Bernoulli-model probability that nuclear-norm minimization uniquely
recovers `M`. -/
noncomputable def bernoulliEventProb {n1 n2 : Nat} (p : Real)
    (Event : Finset (Fin n1 × Fin n2) → Prop) : Real :=
  ∑ Omega : Finset (Fin n1 × Fin n2),
    if Event Omega then bernoulliObservationWeight p Omega else 0

/-- Expectation of a real-valued statistic of the Bernoulli observation set. -/
noncomputable def bernoulliExpectation {n1 n2 : Nat} (p : Real)
    (F : Finset (Fin n1 × Fin n2) → Real) : Real :=
  ∑ Omega : Finset (Fin n1 × Fin n2),
    bernoulliObservationWeight p Omega * F Omega

/-- Expectation over two independent Bernoulli observation sets with the same
inclusion probability. -/
noncomputable def bernoulliPairExpectation {n1 n2 : Nat} (p : Real)
    (F : Finset (Fin n1 × Fin n2) →
      Finset (Fin n1 × Fin n2) → Real) : Real :=
  ∑ Omega : Finset (Fin n1 × Fin n2),
    ∑ Omega' : Finset (Fin n1 × Fin n2),
      bernoulliObservationWeight p Omega *
        bernoulliObservationWeight p Omega' * F Omega Omega'

/-- Bernoulli-model probability that nuclear-norm minimization uniquely
recovers `M`. -/
noncomputable def bernoulliSuccessProb {n1 n2 : Nat} (p : Real)
    (M : RealMatrix n1 n2) : Real :=
  bernoulliEventProb p (fun Omega => IsUniqueMinimizer Omega M)

end MatrixCompletion
