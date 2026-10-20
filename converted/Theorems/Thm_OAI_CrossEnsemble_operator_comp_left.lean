/-
prove2.me platform library module `Theorems.Thm_OAI_CrossEnsemble_operator_comp_left`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_CrossEnsemble_operator_comp_left.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators

open OAI OAI.CrossEnsemble
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem OAI.CrossEnsemble.operator_comp_left {u v : I → E} (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (Z : E →L[ℂ] E) :
    Z ∘L operator u v=operator (fun i => Z (u i)) v := by sorry
