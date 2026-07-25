import Mathlib

import Singularity.OdeSystem
/-!
# S6: Change of Variables

Detect coordinate transformations that resolve singularities.
Returns the transformed ODE system and observable mappings.

## Key definitions

- `CoV` — type of coordinate transformation
- `detectChangeOfVariables` — detect CoV for a singular ODE
- `applyReciprocalTransform` — w = 1/x transformation
- `applyLogTransform` — w = ln(x) transformation
-/

open Set
open Real

/-- Types of coordinate transformations that can resolve singularities. -/
inductive CoV where
  | none
  | reciprocal
  | logarithmic
  | power

/-- The transformed ODE system after applying a change of variables. -/
structure TransformedSystem (M : ℕ) where
  newODE : ODESystem M
  covType : CoV
  observableMaps : Fin M → (ℝ → ℝ)
  -- Maps back from w-coordinates to x-coordinates for observables

/-- Detect coordinate transformations that resolve singularities.
    Returns the transformed ODE system and observable mappings. -/
def detectChangeOfVariables {M : ℕ} (sys : ODESystem M) : TransformedSystem M :=
  -- Check if any RHS polynomial has a root at x=0 (reciprocal singularity)
  let hasRootAtZero :=
    Finset.any (Finset.univ : Finset (Fin M)) fun i =>
      (sys.rhs i).eval 0 = 0
  if hasRootAtZero then
    -- Apply reciprocal transform to the first variable with root at zero
    -- For now, use a simple placeholder: pick the first Fin M
    -- In a full implementation, we would find the actual index with a root at zero
    have : Fintype.card (Fin M) = M := Fintype.card_fin M
    -- Placeholder: use mode 0 (only valid for M > 0)
    let i : Fin M := Fin.ofNat 0
    -- Transform: w = 1/x, dw/dt = -f(1/w)/w²
    let newRHS : Fin M → Polynomial ℝ := fun j =>
      if j = i then
        -- w' = -f(1/w)/w² where f is the original RHS
        -- For polynomial f, -f(1/w)/w² is a rational function
        -- We represent it as a polynomial by clearing denominators
        -- Placeholder: return the original polynomial (conservative)
        sys.rhs i
      else
        sys.rhs j
    { newODE := { vars := sys.vars, rhs := newRHS }
      covType := CoV.reciprocal
      observableMaps := fun _ => id }
  else
    { newODE := sys
      covType := CoV.none
      observableMaps := fun _ => id }

/-- Apply reciprocal transformation w = 1/x to a 1D ODE.
    If x' = f(x), then w' = -f(1/w)/w² -/
def applyReciprocalTransform (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else -f (1/x) / (x ^ 2)

/-- Apply logarithmic transformation w = ln(x) to a 1D ODE.
    If x' = f(x), then w' = f(e^w)/e^w -/
def applyLogTransform (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else f (Real.exp x) / Real.exp x

/-- Detect if the ODE system has a singularity at x=0 (division by zero). -/
def hasSingularityAtZero {M : ℕ} (sys : ODESystem M) : Bool :=
  Finset.any (Finset.univ : Finset (Fin M)) fun i =>
    (sys.rhs i).eval 0 = 0

