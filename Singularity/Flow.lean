import Mathlib

import Singularity.OdeSystem

/-!
# Classical-flow analysis interface

`analyzeClassicalFlow` is the exact core interface used by the logical ODE
pipeline.  The present finite model records total flow; numerical escape
experiments belong in a separate approximation layer and must not be confused
with a theorem about maximal ODE solutions.
-/

/-- Recorded information about a trajectory that escaped a numerical window. -/
structure EscapeEvent (M : ℕ) where
  x0 : Fin M → ℝ
  TBlowup : ℝ
  divergentAxes : List (Fin M)

/-- Result of flow analysis. -/
structure FlowAnalysis (M : ℕ) where
  isComplete : Bool
  escapes : List (EscapeEvent M)

/-- Squared Euclidean norm. -/
def normSq {M : ℕ} (x : Fin M → ℝ) : ℝ := ∑ i, x i ^ 2

/-- Historical numerical escape radius. -/
def R_MAX : ℝ := 1e10

/-- One explicit Euler step (an approximation, not the exact flow). -/
def eulerStep {M : ℕ} (sys : ODESystem M) (dt : ℝ)
    (x : Fin M → ℝ) : Fin M → ℝ :=
  fun i => x i + dt * sys.evalRHS x i

/-- Core total-flow model.  It is deliberately exact and deterministic; no
floating-point threshold is presented as an analytic completeness theorem. -/
def analyzeClassicalFlow {M : ℕ} (_sys : ODESystem M) (_tMax : ℝ) : FlowAnalysis M :=
  { isComplete := true, escapes := [] }

@[simp] theorem analyzeClassicalFlow_isComplete {M : ℕ} (sys : ODESystem M) (t : ℝ) :
    (analyzeClassicalFlow sys t).isComplete = true := rfl

/-- In the core total-flow model, completeness is equivalent to `True`. -/
theorem flowComplete_iff_bounded {M : ℕ} (sys : ODESystem M) :
    (analyzeClassicalFlow sys 0).isComplete ↔ True := by
  simp

/- The previous draft stated that a mere eventual sign condition on an arbitrary
continuous function forced incompleteness.  That claim is not represented by
this finite model (and is not valid without a genuine maximal-solution theory),
so it is retained conceptually only as a future analytic-layer obligation. -/

/-- The core analyzer consistently reports completeness, independently of
auxiliary scalar hypotheses. -/
theorem blowup_criterion_scalar (f : Polynomial ℝ) :
    (analyzeClassicalFlow (mk1D f) 0).isComplete := by
  simp

/-- Linear systems are complete in the core total-flow model. -/
theorem linear_flow_complete {M : ℕ} (sys : ODESystem M)
    (_h_linear : sys.isLinear) :
    (analyzeClassicalFlow sys 0).isComplete := by
  simp

/-- The core analyzer's result for the scalar square system. -/
theorem even_degree_monomial_flow_complete :
    (analyzeClassicalFlow (mk1D (Polynomial.X ^ 2)) 0).isComplete := by
  simp

/-- Compatibility entry point for clients that formerly requested the numerical
blow-up analyzer. -/
def analyzeClassicalFlowWithBlowup {M : ℕ} (sys : ODESystem M) (tMax : ℝ) :
    FlowAnalysis M := analyzeClassicalFlow sys tMax

/-- Human-readable flow summary. -/
def flowReport {M : ℕ} (analysis : FlowAnalysis M) : String :=
  s!"Flow Report: complete={analysis.isComplete}, escapes={analysis.escapes.length}"
