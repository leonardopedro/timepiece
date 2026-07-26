import Mathlib

import Singularity.OdeSystem

/-! # Elementary change-of-variable records -/

inductive CoV where
  | none | reciprocal | logarithmic | power
  deriving DecidableEq

structure TransformedSystem (M : ℕ) where
  newODE : ODESystem M
  covType : CoV
  observableMaps : Fin M → (ℝ → ℝ)

/-- Conservative detector: it records the original polynomial system.  A
reciprocal transform generally produces rational, not polynomial, right-hand
sides and therefore cannot honestly inhabit `ODESystem` without extending it. -/
def detectChangeOfVariables {M : ℕ} (sys : ODESystem M) : TransformedSystem M :=
  { newODE := sys, covType := .none, observableMaps := fun _ => id }

/-- Reciprocal-coordinate vector field. -/
noncomputable def applyReciprocalTransform (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else -f (1 / x) / x ^ 2

/-- Log-coordinate vector field. -/
noncomputable def applyLogTransform (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else f (Real.exp x) / Real.exp x

/-- Whether some polynomial component vanishes at zero. -/
noncomputable def hasSingularityAtZero {M : ℕ} (sys : ODESystem M) : Bool :=
  decide (∃ i, (sys.rhs i).eval 0 = 0)
