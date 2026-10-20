/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 63413033-e925-4bec-9cbe-c8ae5265f466
* original name       : `OAI.QuantumTrace.negMulLog_le_crossEntropy`
* title               : Pointwise Gibbs inequality $-p\log p\le q-p-p\log q$
* statement author    : Shuze Chen
* solution author     : Shuze Chen (submission 9d2af639-4d13-4eb4-ac4f-2dfedee1918f,
                        accepted 2026-10-16T03:15:17.656903+00:00)
* source              : https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/QuantumTrace/Basic.lean#L475-L488
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/unfer-bayes/OAI.QuantumTrace.negMulLog_le_crossEntropy.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/OAI_QuantumTrace_negMulLog_le_crossEntropy.diff`.
-/
-- Generated from openai/math@1581d4c lean/OAI/Analysis/QuantumTrace/Basic.lean:L484-L497
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.negMulLog_le_crossEntropy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Prove2me.Shim.Misc  -- conversion shim (platform Mathlib API)

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

theorem negMulLog_le_crossEntropy {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    Real.negMulLog p ≤ q - p + p * (-Real.log q) := by
  by_cases hz : p = 0
  · simp [hz, le_of_lt hq]
  have h := mul_le_mul_of_nonneg_left
    (Real.negMulLog_le_one_sub_self (div_nonneg hp hq.le)) hq.le
  change q * (-(p / q) * Real.log (p / q)) ≤ q * (1 - p / q) at h
  rw [Real.log_div hz hq.ne'] at h
  have hl : q * (-(p / q) * (Real.log p - Real.log q)) =
      -p * Real.log p + p * Real.log q := by field_simp; ring
  have hr : q * (1 - p / q) = q - p := by field_simp
  rw [hl, hr] at h
  dsimp [Real.negMulLog]
  linarith

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


theorem _root_.Prove2me.Solution.OAI_QuantumTrace_negMulLog_le_crossEntropy : type_of% @_root_.OAI.QuantumTrace.negMulLog_le_crossEntropy := @_root_.OAI.QuantumTrace.negMulLog_le_crossEntropy

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), checked against the solution above.  The solution declares the platform theorem `OAI.QuantumTrace.negMulLog_le_crossEntropy` itself, so the statement is restated as an `example`. -/

section Prove2meStatement

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

example {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    Real.negMulLog p ≤ q - p + p * (-Real.log q) := by
  first
  | exact _root_.Prove2me.Solution.OAI_QuantumTrace_negMulLog_le_crossEntropy hp hq
  | (apply _root_.Prove2me.Solution.OAI_QuantumTrace_negMulLog_le_crossEntropy <;> assumption)


end Prove2meStatement
