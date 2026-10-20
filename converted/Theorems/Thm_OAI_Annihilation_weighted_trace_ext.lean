/-
prove2.me platform library module `Theorems.Thm_OAI_Annihilation_weighted_trace_ext`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_Annihilation_weighted_trace_ext.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms

open OAI OAI.Annihilation
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

theorem OAI.Annihilation.weighted_trace_ext {J : Type*} (b : HilbertBasis J ℂ (Fock n))
    (A Q : Fock n →L[ℂ] Fock n)
    (f g : (Fock n →L[ℂ] Fock n) → ℂ)
    (hf : ∀ Z, HasSum (fun k => inner ℂ (b k) (Z (A (b k)))) (f Z))
    (hg : ∀ Z, HasSum (fun k => inner ℂ (b k) (Z (Q (b k)))) (g Z))
    (h : ∀ Z, f (inverseWeight 2 ∘L Z ∘L inverseWeight 2)=
      g (inverseWeight 2 ∘L Z ∘L inverseWeight 2)) : ∀ Z, f Z=g Z := by sorry
