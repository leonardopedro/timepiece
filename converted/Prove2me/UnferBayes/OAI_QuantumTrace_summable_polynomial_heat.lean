/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 7a1aff21-fd02-4eb2-adeb-f6061106b529
* original name       : `OAI.QuantumTrace.summable_polynomial_heat`
* title               : Heat-trace summability at half rate implies summability of quadratically weighted terms
* statement author    : Shuze Chen
* solution author     : Shuze Chen (submission 3cf0aec0-b7f0-47a6-9091-c2afff14f78c,
                        accepted 2026-10-16T03:25:13.323986+00:00)
* source              : https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/QuantumTrace/Basic.lean#L1360-L1382
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/unfer-bayes/OAI.QuantumTrace.summable_polynomial_heat.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/OAI_QuantumTrace_summable_polynomial_heat.diff`.
-/
-- Generated from openai/math@1581d4c lean/OAI/Analysis/QuantumTrace/Basic.lean:L1369-L1391
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.summable_polynomial_heat. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

-- ---- from OAI.Analysis.QuantumTrace.Basic ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

namespace QuantumTrace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open Filter

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

end

section
open Filter ContinuousLinearMap InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End Submodule
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End
open scoped ContinuousFunctionalCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

end

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section

open Filter Topology
open scoped Classical
variable {ι : Type*}
end

section
open Filter Topology
open scoped Classical
variable {ι : Type*}

end

section
open Filter Topology
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End Submodule
universe v
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section
open Filter Topology
variable {ι : Type*}

end

section
open Filter Topology

theorem summable_polynomial_heat {J : Type*} (u : J → ℝ) (hu : ∀ j, 0 ≤ u j)
    (hs : Summable (fun j => Real.exp (-(1/2 : ℝ)*u j))) :
    Summable (fun j => Real.exp (-u j)*(1+u j^2)) := by
  have hscalar (x : ℝ) (hx : 0 ≤ x) :
      Real.exp (-x)*(1+x^2) ≤ 17*Real.exp (-(1/2 : ℝ)*x) := by
    have h := Real.add_one_le_exp (x/4)
    have he : x ≤ 4*Real.exp (x/4) := by linarith
    have he2 : x^2 ≤ 16*Real.exp (x/2) := by
      calc
        x^2 ≤ (4*Real.exp (x/4))^2 := pow_le_pow_left₀ hx he 2
        _ = 16*(Real.exp (x/4)*Real.exp (x/4)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 1; ring_nf
    have hm := mul_le_mul_of_nonneg_left he2 (Real.exp_nonneg (-x))
    have heq : Real.exp (-x)*(16*Real.exp (x/2)) = 16*Real.exp (-(1/2 : ℝ)*x) := by
      calc
        _ = 16*(Real.exp (-x)*Real.exp (x/2)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 1; ring_nf
    rw [heq] at hm
    have hle : Real.exp (-x) ≤ Real.exp (-(1/2 : ℝ)*x) := Real.exp_le_exp.mpr (by linarith)
    nlinarith
  apply Summable.of_nonneg_of_le (fun j => by positivity) _ (hs.mul_left 17)
  intro j
  exact hscalar (u j) (hu j)

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*}

end

section
variable {ι J : Type*}

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

end

open scoped BigOperators ComplexConjugate
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end QuantumTrace

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace QuantumTrace
variable {ι J : Type*}

end QuantumTrace

end

end OAI

-- ---- platform node ----
open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open Filter Topology


theorem _root_.Prove2me.Solution.OAI_QuantumTrace_summable_polynomial_heat : type_of% @_root_.OAI.QuantumTrace.summable_polynomial_heat := @_root_.OAI.QuantumTrace.summable_polynomial_heat

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), checked against the solution above.  The solution declares the platform theorem `OAI.QuantumTrace.summable_polynomial_heat` itself, so the statement is restated as an `example`. -/

section Prove2meStatement

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open Filter Topology

example {J : Type*} (u : J → ℝ) (hu : ∀ j, 0 ≤ u j)
    (hs : Summable (fun j => Real.exp (-(1/2 : ℝ)*u j))) :
    Summable (fun j => Real.exp (-u j)*(1+u j^2)) := by
  first
  | exact _root_.Prove2me.Solution.OAI_QuantumTrace_summable_polynomial_heat u hu hs
  | (apply _root_.Prove2me.Solution.OAI_QuantumTrace_summable_polynomial_heat <;> assumption)


end Prove2meStatement
