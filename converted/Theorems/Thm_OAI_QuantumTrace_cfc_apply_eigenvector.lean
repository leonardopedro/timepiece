/-
prove2.me platform library module `Theorems.Thm_OAI_QuantumTrace_cfc_apply_eigenvector`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_QuantumTrace_cfc_apply_eigenvector.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open ContinuousLinearMap Module.End
open scoped ContinuousFunctionalCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem OAI.QuantumTrace.cfc_apply_eigenvector {T : E →L[ℂ] E} (hs : T.IsSymmetric)
    {x : E} {μ : ℂ} (he : T x = μ • x) (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ T)) : cfc f T x = f μ • x := by sorry
