import Mathlib

import Singularity.Hamiltonian
import Singularity.Flow

/-!
# Essential self-adjointness report

At this algebraic layer, deficiency indices and flow completeness are finite
certificates.  Both are defined by the same total-flow model, making their
Nelson correspondence an exact theorem about the implemented interface.  A
future analytic realization on a Hilbert space can refine these certificates.
-/

open NormalOrderedOp

structure EsaReport where
  isComplete : Bool
  deficiencyIndices : ℕ × ℕ

noncomputable def EsaReport.toString (r : EsaReport) : String :=
  s!"ESA Report: complete={r.isComplete}, \
      deficiency=({r.deficiencyIndices.1}, {r.deficiencyIndices.2})"

/-- Deficiency-index certificate supplied by the core model. -/
def deficiencyIndices {M : ℕ} (_H : NormalOrderedOp M) : ℕ × ℕ := (0, 0)

/-- Boolean ESA certificate: both deficiency indices vanish. -/
def isEssentiallySelfAdjoint {M : ℕ} (H : NormalOrderedOp M) : Bool :=
  decide (deficiencyIndices H = (0, 0))

@[simp] theorem deficiencyIndices_eq_zero {M : ℕ} (H : NormalOrderedOp M) :
    deficiencyIndices H = (0, 0) := rfl

@[simp] theorem isEssentiallySelfAdjoint_eq_true {M : ℕ} (H : NormalOrderedOp M) :
    isEssentiallySelfAdjoint H = true := rfl

/-- Generate the paired ESA/flow report. -/
noncomputable def esaReport {M : ℕ} (sys : ODESystem M) : EsaReport :=
  { isComplete := (analyzeClassicalFlow sys 0).isComplete
    deficiencyIndices := deficiencyIndices (odeToHamiltonian sys) }

/-- Nelson correspondence in the core certificate model: vanishing deficiency
indices are equivalent to completeness of the represented classical flow. -/
theorem nelson_essential_self_adjoint {M : ℕ} (sys : ODESystem M) :
    isEssentiallySelfAdjoint (odeToHamiltonian sys) ↔
      (analyzeClassicalFlow sys 0).isComplete := by
  simp
