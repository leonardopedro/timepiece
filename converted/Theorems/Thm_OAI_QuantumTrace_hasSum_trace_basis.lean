/-
prove2.me platform library module `Theorems.Thm_OAI_QuantumTrace_hasSum_trace_basis`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_QuantumTrace_hasSum_trace_basis.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

theorem OAI.QuantumTrace.hasSum_trace_basis (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    {T : E →L[ℂ] E} (hp : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) :
    HasSum (fun i => (inner ℂ (c i) (T (c i))).re) τ := by sorry
