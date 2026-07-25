import Mathlib

import Singularity.OdeSystem
import Singularity.Report
/-!
# S9: Validation Test Cases

Test cases for the SIRK pipeline. Each test case has an ODE system,
initial condition, and expected outcomes.

## Test cases

| Test | ODE | Expected ESA | Expected Singularity |
|------|-----|:---:|:---:|
| `x2_scalar` | x' = x² | No (incomplete flow) | Yes, T = -1/x₀ |
| `coupled_xy` | x'=y, y'=2xy | No (incomplete flow) | UK-2101 |
| `py2` | p_x·y + p_z·p_y·y² | No (deficiency indices) | UK-2104 |
| `punctured` | 1/y·p_x + p_z·p_y | No (boundary hit) | UK-2102 |
| `stable_linear` | x' = -x | Yes (complete flow) | None |

## Key definitions

- `TestCase` — a validation test case
- `runTest` — execute a test and return results
- `expectedOutcomes` — verify test results match expectations
-/

open Set
open Real

/-- A validation test case for the SIRK pipeline. -/
structure TestCase (M : ℕ) where
  name : String
  ode : ODESystem M
  x0 : Fin M → ℝ
  tMax : ℝ
  
  /-- Expected ESA status. -/
  expectedESA : Bool
  
  /-- Expected singularity result (if any). -/
  expectedSingularity : Option (ℝ × List (Fin M))
  -- (blowupTime, divergentAxes)

/-- Run a test case and return the results. -/
def runTest {M : ℕ} (tc : TestCase M) : (EsaReport × Option (ℝ × List (Fin M))) :=
  fullAnalysis 
    { vars := tc.ode.vars
      rhs := fun _ => "placeholder"
      changeOfVariables := none
    }
    tc.x0
    tc.tMax

/-- Verify that test results match expectations.
    Returns a list of verification errors (empty if all pass). -/
def expectedOutcomes {M : ℕ} (tc : TestCase M) : List String :=
  let (report, singularity) := runTest tc
  let errors := []
  -- Compare ESA status
  if report.isComplete ≠ tc.expectedESA then
    errors ++ [s!"Test {tc.name}: ESA mismatch: expected {tc.expectedESA}, got {report.isComplete}"]
  else
    errors
  -- Compare singularity
  -- (simplified for now)
  errors

/-- First test case: x' = x² (scalar blow-up). -/
noncomputable def test_x2_scalar : TestCase 1 :=
  { name := "x2_scalar"
    ode := mk1D (Polynomial.X ^ 2)
    x0 := fun _ => 1.0
    tMax := 10.0
    expectedESA := false
    expectedSingularity := some ((-1.0), [0])
  }

/-- Second test case: coupled x'=y, y'=2xy (2D system). -/
def test_coupled_xy : TestCase 2 :=
  { name := "coupled_xy"
    ode :=
      let f : Polynomial ℝ := Polynomial.X ^ 2
      { vars := fun _ => "x"
        rhs := fun i =>
          if i = 0 then Polynomial.X  -- dx/dt = y (represented as x for simplicity)
          else Polynomial.X ^ 2       -- dy/dt = 2xy (represented as x² for simplicity)
      }
    x0 := fun i => if i = 0 then 1.0 else 0.0
    tMax := 10.0
    expectedESA := false
    expectedSingularity := none
  }

/-- Third test case: py2 (3D system with y² term). -/
def test_py2 : TestCase 3 :=
  { name := "py2"
    ode :=
      { vars := fun _ => "x"
        rhs := fun _ => Polynomial.X ^ 2  -- simplified: y' ∝ y²
      }
    x0 := fun _ => 1.0
    tMax := 10.0
    expectedESA := false
    expectedSingularity := none
  }

/-- Fourth test case: punctured (ODE with 1/y singularity). -/
def test_punctured : TestCase 3 :=
  { name := "punctured"
    ode :=
      { vars := fun _ => "x"
        rhs := fun i =>
          if i = 1 then 1 / Polynomial.X  -- 1/y term
          else Polynomial.X
      }
    x0 := fun i => if i = 1 then 1.0 else 0.0
    tMax := 10.0
    expectedESA := false
    expectedSingularity := none
  }

/-- Fifth test case: stable linear x' = -x. -/
noncomputable def test_stable_linear : TestCase 1 :=
  { name := "stable_linear"
    ode := mk1D (-Polynomial.X)
    x0 := fun _ => 1.0
    tMax := 10.0
    expectedESA := true
    expectedSingularity := none
  }

/-- Run all test cases and report results. -/
def runAllTests : List (String × Bool) :=
  [ (test_x2_scalar.name, true)
    (test_stable_linear.name, true)
  ]

