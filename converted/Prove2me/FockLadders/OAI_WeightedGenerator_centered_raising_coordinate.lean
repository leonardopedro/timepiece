/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : e0b78caa-4efa-44f9-9c1f-934035db0660
* original name       : `OAI.WeightedGenerator.centered_raising_coordinate`
* title               : Spectral coordinates of the centered raising ladder are conjugates of the centered annihilation matrix
* statement author    : Shuze Chen
* solution author     : Shuze Chen (submission 30db8574-30fe-4da3-b724-ea38947f0117,
                        accepted 2026-10-16T04:24:40.13414+00:00)
* source              : https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/ThermalMetric.lean#L545-L564
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/fock-ladders/OAI.WeightedGenerator.centered_raising_coordinate.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/OAI_WeightedGenerator_centered_raising_coordinate.diff`.
-/
-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/ThermalMetric.lean:L548-L567
-- (upload_full_project.md Phase 4): solution for node OAI.WeightedGenerator.centered_raising_coordinate. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.InformationTheory.PhotonNumber.ThermalMetric ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace ThermalMetric

section
open EntropyPhotonNumber DiagonalForms.System

end

section
open DiagonalForms.System

end

section
open EntropyPhotonNumber
variable {J : Type*}

end

section
variable {J : Type*}

end

open scoped ComplexConjugate
variable {J : Type*}

end ThermalMetric

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate BigOperators
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace Annihilation
open EntropyPhotonNumber
variable {n : ℕ} {J : Type*}

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate BigOperators
variable {n : ℕ} {J : Type*}

theorem centered_raising_coordinate (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (j : Fin n) (μ : ℂ) (l r : J) :
    inner ℂ (b r) (centeredLadder j μ true (x l))=
      (Real.sqrt (p l):ℂ)*conj (centeredEntry b p x j μ l r) := by
  classical
  have hw : inverseWeight 1 (inverseWeight 2 (x l))=(Real.sqrt (p l):ℂ) • b l := by
    change (inverseWeight 1 ∘L inverseWeight 2) (x l)=_
    rw [← inverseWeight_add]; exact hi l
  have hb : inner ℂ (b r) (b l)=if r=l then 1 else 0 := orthonormal_iff_ite.mp b.orthonormal r l
  have hd := spectralGain_raising b p hp x hi j l r
  change inner ℂ (b r) (raising j (inverseWeight 2 (x l)))=_ at hd
  simp only [centeredLadder, ↓reduceIte, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, inner_sub_right, inner_smul_right,
    hw, hd, hb, centeredEntry]
  by_cases hh : l=r
  · subst r
    simp only [↓reduceIte, map_sub, mul_one]
    ring
  · simp only [hh, Ne.symm hh, ↓reduceIte, sub_zero, mul_zero]

end WeightedGenerator

namespace EntropyPhotonNumber.GibbsData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end EntropyPhotonNumber.GibbsData

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace ThermalMetric
open scoped ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalMetric

namespace EntropyPhotonNumber.GibbsData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end EntropyPhotonNumber.GibbsData

namespace Annihilation
open EntropyPhotonNumber
variable {n : ℕ}

end Annihilation

namespace EntropyPhotonNumber
open Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

end EntropyPhotonNumber

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber.GibbsData
open Annihilation WeightedGenerator
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end EntropyPhotonNumber.GibbsData

end

end OAI

-- ---- platform node ----
open OAI OAI.WeightedGenerator
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate BigOperators


theorem _root_.Prove2me.Solution.OAI_WeightedGenerator_centered_raising_coordinate : type_of% @_root_.OAI.WeightedGenerator.centered_raising_coordinate := @_root_.OAI.WeightedGenerator.centered_raising_coordinate

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), checked against the solution above.  The solution declares the platform theorem `OAI.WeightedGenerator.centered_raising_coordinate` itself, so the statement is restated as an `example`. -/

section Prove2meStatement

open OAI OAI.WeightedGenerator
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate BigOperators
variable {n : ℕ} {J : Type*}

example (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (j : Fin n) (μ : ℂ) (l r : J) :
    inner ℂ (b r) (centeredLadder j μ true (x l))=
      (Real.sqrt (p l):ℂ)*conj (centeredEntry b p x j μ l r) := by
  first
  | exact _root_.Prove2me.Solution.OAI_WeightedGenerator_centered_raising_coordinate b p hp x hi j μ l r
  | (apply _root_.Prove2me.Solution.OAI_WeightedGenerator_centered_raising_coordinate <;> assumption)


end Prove2meStatement
