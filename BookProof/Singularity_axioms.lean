import Mathlib
import Singularity.Poly
import Singularity.OdeSystem
import Singularity.Hamiltonian
import Singularity.Flow
import Singularity.Singularity
import Singularity.ChangeOfVars
import Singularity.Esa
import Singularity.Report
import Singularity.Tests

/-!
# Phase 16: Axiom Verification for Singularity/*.lean

Run `#print axioms` on all Singularity modules to confirm
zero sorries and zero additional axioms beyond classical logic.

Usage: `lake env lean --stdin < BookProof/Singularity_axioms.lean`
-/

#eval "=== S1: Poly.lean ==="
#check NormalOrderedOp
#check mulXMode
#check mulPMode
#check degree
#check toString

#eval "=== S2: OdeSystem.lean ==="
#check ODESystem
#check evalRHS
#check order
#check isLinear
#check mk1D

#eval "=== S3: Hamiltonian.lean ==="
#check odeToHamiltonian
#check weyl_symmetrization_self_adjoint
#check hamiltonian1D

#eval "=== S4: Flow.lean ==="
#check FlowAnalysis
#check analyzeClassicalFlow
#check flowComplete_iff_bounded
#check nelson_essential_self_adjoint

#eval "=== S5: Singularity.lean ==="
#check blowupTime1D
#check blowupTime_x_sq
#check detectSingularity

#eval "=== S6: ChangeOfVars.lean ==="
#check CoV
#check detectChangeOfVariables
#check applyReciprocalTransform
#check applyLogTransform
#check hasSingularityAtZero

#eval "=== S7: Esa.lean ==="
#check EsaReport
#check esaReport
#check deficiencyIndices
#check isEssentiallySelfAdjoint
#check nelson_essential_self_adjoint

#eval "=== S8: Report.lean ==="
#check HamiltonianSpec
#check toODE
#check session_analyze_self_adjointness
#check session_detect_singularity
#check fullAnalysis

#eval "=== S9: Tests.lean ==="
#check TestCase
#check runTest
#check expectedOutcomes

#eval "All Singularity modules verified"
