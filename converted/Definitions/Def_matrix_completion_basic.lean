/-
prove2.me platform library module `Definitions.Def_matrix_completion_basic`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_matrix_completion_basic.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Mathlib.Analysis.InnerProductSpace.PiL2
import Prove2me.Shim.SingularValues  -- was `Mathlib.Analysis.InnerProductSpace.SingularValues`
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Sqrt

/-!
Basic objects for exact matrix completion by nuclear-norm minimization.

This file is intentionally statement-level infrastructure: it contains only the
optimization objective, the fixed-cardinality observation model, and the success
predicate for the convex program.
-/

namespace MatrixCompletion

open scoped Classical BigOperators
open Finset

/-- Real matrices with concrete finite row and column types. -/
abbrev RealMatrix (n1 n2 : Nat) := Matrix (Fin n1) (Fin n2) Real

/-- Nuclear norm `||X||_*`, defined as the sum of the singular values of the
associated Euclidean linear map. -/
noncomputable def nuclearNorm {n1 n2 : Nat} (X : RealMatrix n1 n2) : Real :=
  (Matrix.toEuclideanLin X).singularValues.sum (fun _ x => x)

/-- `X` agrees with `M` on the observed entry set. -/
def AgreesOn {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2))
    (X M : RealMatrix n1 n2) : Prop :=
  ∀ p ∈ Omega, X p.1 p.2 = M p.1 p.2

/-- `M` is the unique feasible minimizer of the nuclear-norm completion program. -/
def IsUniqueMinimizer {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2))
    (M : RealMatrix n1 n2) : Prop :=
  ∀ X : RealMatrix n1 n2,
    AgreesOn Omega X M → X ≠ M → nuclearNorm M < nuclearNorm X

/-- Uniform probability, over all size-`m` observation sets, that the completion
program recovers `M` uniquely. -/
noncomputable def successProb {n1 n2 : Nat} (m : Nat) (M : RealMatrix n1 n2) :
    Real :=
  let sampleSpace := Finset.powersetCard m (Finset.univ : Finset (Fin n1 × Fin n2))
  ((sampleSpace.filter (fun Omega => IsUniqueMinimizer Omega M)).card : Real) /
    sampleSpace.card

end MatrixCompletion
