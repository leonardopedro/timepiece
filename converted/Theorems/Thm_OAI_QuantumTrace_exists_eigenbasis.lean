/-
prove2.me platform library module `Theorems.Thm_OAI_QuantumTrace_exists_eigenbasis`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_QuantumTrace_exists_eigenbasis.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open ContinuousLinearMap Module.End Submodule
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

theorem OAI.QuantumTrace.exists_eigenbasis {T : E →L[ℂ] E} (hc : IsCompactOperator T)
    (hs : T.IsSymmetric) :
    ∃ (J : Type u) (b : HilbertBasis J ℂ E) (e : J → ℂ),
      ∀ j, T (b j) = e j • b j := by sorry
