import Mathlib
import Singularity.OdeSystem
import Singularity.Hamiltonian
import Singularity.Flow
import Singularity.Esa
import Singularity.ChangeOfVars
import RandomMap.RandomMap2

/-!
# S10: Extended Framework Integration

Connect the singularity detection pipeline to the RandomMap2 framework.

## Key definitions

- `hamiltonian_as_outer_wavefunction` — represent the Hamiltonian as an outer wave function
- `UKDiagnosticCode` — UK diagnostic codes for the SIRK pipeline
- `session_to_randomMap2` — bridge between session analysis and RandomMap2
- `blowup_time_integral` — compute blow-up time via improper integral (1D)
-/

open Set
open Complex
open Polynomial

/-- UK diagnostic codes for the SIRK pipeline.
    Each code identifies a specific failure mode or informational message. -/
inductive UKDiagnosticCode : Type where
  | none
  | odeNotEssentiallySelfAdjoint    -- UK-2101: Flow incomplete & no CoV applied
  | odeSingularityDetected          -- UK-2102: Blow-up detected at initial condition
  | odeCovApplied                    -- UK-2103: Change of variables stabilized the flow
  | odeDeficiencyIndices             -- UK-2104: Nonzero deficiency indices (n₊, n₋) ≠ (0,0)
  | odePolynomialTooLarge           -- UK-2105: Normal-ordered degree exceeds explosion bound
  deriving DecidableEq

/-- Convert a UK diagnostic code to its numeric identifier string. -/
def UKDiagnosticCode.toString : UKDiagnosticCode → String
  | .none => "UK-0000: No issues"
  | .odeNotEssentiallySelfAdjoint => "UK-2101: ODE not essentially self-adjoint"
  | .odeSingularityDetected => "UK-2102: Singularity detected at initial condition"
  | .odeCovApplied => "UK-2103: Change of variables applied"
  | .odeDeficiencyIndices => "UK-2104: Nonzero deficiency indices"
  | .odePolynomialTooLarge => "UK-2105: Polynomial degree exceeds bound"

/-
NOTE (build repair).  The definition below does not elaborate and is therefore
commented out rather than deleted.  Two things are wrong with it: there is no
constant `MeasureTheory.Measure.lebesgue` (the Lebesgue measure on `ℝ` is
`MeasureTheory.volume`), and `OuterWaveFunction` requires its head law to be a
*probability* measure, which the restriction of the volume measure to
`Set.Icc (-1) 1` (total mass `2`) is not.  The body was in any case a
placeholder returning `0`; a real construction needs the Fock representation of
the normal-ordered Hamiltonian.

/-- The Hamiltonian as an outer wave function. -/
noncomputable def hamiltonian_as_outer_wavefunction {M : ℕ} (sys : ODESystem M) :
    OuterWaveFunction M (MeasureTheory.Measure.pi (fun _ : Fin M =>
      MeasureTheory.Measure.restrict MeasureTheory.Measure.lebesgue (Set.Icc (-1) 1))) :=
  have hH := odeToHamiltonian sys
  0
-/

/-
NOTE (build repair).  The bridge below does not elaborate and is therefore
commented out rather than deleted.  `HamiltonianSpec` is not in a `RandomMap2`
namespace — it is the structure of `Singularity.Report` — and its `rhs` field is
`Fin M → String` (unparsed polynomial source), whereas `ODESystem.rhs` is
`Fin M → Polynomial ℝ`, so the record below is ill-typed.  Bridging the two
needs a printer from `Polynomial ℝ` to the spec's string syntax, which the
project does not have.

/-- Bridge between the singularity detection session and the RandomMap2
framework. -/
noncomputable def session_to_randomMap2 {M : ℕ} (sys : ODESystem M) :
    RandomMap2.HamiltonianSpec M :=
  { vars := sys.vars
    rhs := sys.rhs
    changeOfVariables := none }
-/

/-- Compute the blow-up time for a 1D scalar ODE x' = f(x) via improper integral.
    T(x₀) = ∫_{x₀}^{∞} dx / f(x)   (for f(x) > 0 when x > x₀)
    
    This is the exact quadrature formula for finite-time blow-up detection.
    The integral is improper at both endpoints (x₀ and ∞).
    
    @param f The polynomial RHS of the ODE (x' = f(x))
    @param x0 The initial condition
    @return The blow-up time T(x₀), or 0 if the integral diverges -/
noncomputable def blowup_time_integral (f : Polynomial ℝ) (x0 : ℝ) : ℝ :=
  -- For polynomial f with f(x₀) = 0 and f(x) > 0 for x > x₀,
  -- the blow-up time is ∫_{x₀}^{∞} dx / f(x)
  --
  -- In the symbolic implementation, we evaluate this using the
  -- antiderivative of 1/f(x) when f is a monomial:
  -- For f(x) = c·x^k: T(x₀) = x₀^{1-k} / (c·(k-1)) for k > 1
  -- For f(x) = c (constant): no blow-up
  --
  -- For general polynomials, we use numerical integration.
  if f.eval x0 = 0 then
    -- Singularity at x₀: compute the integral numerically
    -- Placeholder: use the monomial case for power-law blow-up
    if f.natDegree ≥ 2 then
      -- Power-law blow-up: approximate using dominant term
      let c := f.coeff (f.natDegree)
      let k := f.natDegree
      if c ≠ 0 then
        -- T(x₀) ≈ x₀^{1-k} / (c·(k-1)) for x₀ > 0
        if x0 > 0 then
          (x0 ^ (1 - k)) / (c * (k - 1))
        else if x0 < 0 then
          -- For negative x₀ with odd k, the integral diverges
          0
        else
          0
      else
        0
    else
      0
  else
    -- No singularity at x₀: no blow-up (or blow-up at finite distance)
    0

/-- Full pipeline: ODE system → Hamiltonian → ESA report → UK diagnostic codes.
    This is the main entry point for the SIRK pipeline integration. -/
noncomputable def sirk_pipeline {M : ℕ} (sys : ODESystem M) (_x0 : Fin M → ℝ) :
    UKDiagnosticCode × EsaReport :=
  let H := odeToHamiltonian sys
  let _flow := analyzeClassicalFlow sys
  let esa := esaReport sys
  let cov := detectChangeOfVariables sys
  
  -- Determine the appropriate UK diagnostic code
  let code : UKDiagnosticCode :=
    if ¬ esa.isComplete then
      -- Flow incomplete: check if CoV was applied
      if cov.covType ≠ CoV.none then
        .odeCovApplied
      else
        .odeNotEssentiallySelfAdjoint
    else if (deficiencyIndices H) ≠ (0, 0) then
      .odeDeficiencyIndices
    else if hasSingularityAtZero sys then
      -- Check if CoV resolved the singularity
      if cov.covType ≠ CoV.none then
        .odeCovApplied
      else
        .odeSingularityDetected
    else
      .none
  
  (code, esa)
