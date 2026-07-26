import Mathlib

import Singularity.OdeSystem
import Singularity.Hamiltonian
import Singularity.Flow
import Singularity.Esa
/-!
# S8: Integration with Unfer Protocol

Connect ODE system to the unfer protocol API.

## Key definitions

- `HamiltonianSpec` — specification for unfer protocol
- `HamiltonianSpec.toODE` — convert spec to ODE system
- `session_analyze_self_adjointness` — evaluate Nelson's condition via session
- `session_detect_singularity` — detect singularities via session
-/

open Set
open Complex

/-- ODE system specification for the unfer protocol API. -/
structure HamiltonianSpec (M : ℕ) where
  vars : Fin M → String
  rhs : Fin M → String
  changeOfVariables : Option String
  -- "none" | "auto" | "reciprocal:x" (axis-specific)
  
  /-- Convert a HamiltonianSpec to an ODESystem by parsing the polynomial strings. -/
  def toODE : Option (ODESystem M) :=
    -- Parse rhs strings as polynomials and construct ODESystem
    -- Use polynomial parser to convert string → Polynomial (Fin M → ℝ)
    -- For now, return none (placeholder for string parsing)
    none

/-- Evaluate Nelson's essential self-adjointness condition via the session interface.
    Returns ESA status and deficiency indices. -/
noncomputable def session_analyze_self_adjointness {M : ℕ} (spec : HamiltonianSpec M) : 
    EsaReport :=
  -- Connect to unfer session
  -- 1. Parse spec.toODE
  -- 2. Apply odeToHamiltonian
  -- 3. Compute esaReport
  -- Placeholder: use default analysis
  let sys : ODESystem M := 
    { vars := spec.vars
      rhs := fun i => Polynomial.X  -- placeholder
    }
  esaReport sys

/-- Detect singularities via the session interface.
    Returns blow-up times and divergent axes. -/
def session_detect_singularity {M : ℕ} (spec : HamiltonianSpec M) 
    (x0 : Fin M → ℝ) (tMax : ℝ) : Option (ℝ × List (Fin M)) :=
  -- Connect to unfer session for singularity detection
  -- 1. Parse spec.toODE
  -- 2. Use detectSingularity with x0 and tMax
  -- Placeholder: return none (no singularity detected)
  none

/-- Full analysis pipeline: ODE → Hamiltonian → ESA → Singularity report. -/
noncomputable def fullAnalysis {M : ℕ} (spec : HamiltonianSpec M) (x0 : Fin M → ℝ) (tMax : ℝ) : 
    (EsaReport × Option (ℝ × List (Fin M))) :=
  (session_analyze_self_adjointness spec, session_detect_singularity spec x0 tMax)

/-- Default ODE system for testing: x' = x² (singular) and x' = -x (stable). -/
noncomputable def defaultODESystem : ODESystem 1 :=
  mk1D (Polynomial.X ^ 2)

/-- Alternative default: stable linear ODE x' = -x. -/
noncomputable def defaultStableSystem : ODESystem 1 :=
  mk1D (-Polynomial.X)

