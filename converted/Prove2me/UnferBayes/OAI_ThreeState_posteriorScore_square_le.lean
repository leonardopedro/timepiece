/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 0e5bab36-d070-4051-a65d-0836add1e03d
* original name       : `OAI.ThreeState.posteriorScore_square_le`
* title               : The squared posterior score is at most twelve times the posterior total variation
* statement author    : Shuze Chen
* solution author     : Shuze Chen (submission 00d54e98-4cb3-4772-bec0-0c3120a314d5,
                        accepted 2026-10-18T09:57:45.782058+00:00)
* source              : https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeState/Supercritical.lean#L238-L253
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/unfer-bayes/OAI.ThreeState.posteriorScore_square_le.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/OAI_ThreeState_posteriorScore_square_le.diff`.
-/
-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/Supercritical.lean:L238-L253
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeState.posteriorScore_square_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic
import Definitions.Def_OAI_Probability_ThreeState_Expectations
import Definitions.Def_OAI_Probability_ThreeState_Messages
import Definitions.Def_OAI_Probability_ThreeState_Observation
import Definitions.Def_OAI_Probability_ThreeState_Update
import Definitions.Def_OAI_Probability_ThreeState_RadialMoments
import Definitions.Def_OAI_Probability_ThreeState_RadialDerivatives
import Definitions.Def_OAI_Probability_ThreeState_PosteriorMoments
import Definitions.Def_OAI_Probability_ThreeState_PoissonCritical
import Definitions.Def_OAI_Probability_ThreeState_Supercritical

-- ---- from OAI.Probability.ThreeState.Basic ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Three-state symmetric broadcast experiments, posterior advantage and total variation. -/

namespace ThreeState

 
 
 

 
 

 
 
 

 
 
 
end ThreeState
namespace ThreeState

lemma mass_bind {α β : Type*} (p : PMF α) (k : α → PMF β) (b : β) :
    mass (p.bind k) b = ∑' a, mass p a * mass (k a) b := by
  simp only [mass, PMF.bind_apply, ENNReal.tsum_toReal_eq
    (fun a => ENNReal.mul_ne_top (p.apply_ne_top a) ((k a).apply_ne_top b)), ENNReal.toReal_mul]

lemma mass_uniform (i : Spin) : mass uniformSpin i = 1/3 := by
  simp [mass, uniformSpin, PMF.ofFintype_apply]

lemma mass_marginal {α : Type*} (law : Spin → PMF α) (y : α) :
    mass (marginal law) y = (∑ i : Spin, mass (law i) y)/3 := by
  simp only [marginal, mass_bind, tsum_fintype, mass_uniform]
  rw [← Finset.mul_sum]
  ring

lemma mass_eq_zero {α : Type*} (p : PMF α) (a : α) : mass p a = 0 ↔ p a = 0 := by
  simp [mass, ENNReal.toReal_eq_zero_iff, p.apply_ne_top a]

lemma posterior_nonneg {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) :
    0 ≤ posterior law y i := by
  unfold posterior
  split_ifs <;> positivity

lemma posterior_sum {α : Type*} (law : Spin → PMF α) (y : α) :
    ∑ i : Spin, posterior law y i = 1 := by
  classical
  have hn := (marginal law).apply_ne_top y
  by_cases h : marginal law y = 0
  · simp [posterior, h]
  · have hm : mass (marginal law) y ≠ 0 := mt (mass_eq_zero _ _).mp h
    simp only [posterior, ite_eq_right h, ← Finset.sum_div]
    change (∑ i : Spin, mass (law i) y)/(3*mass (marginal law) y) = 1
    have he := mass_marginal law y
    field_simp
    linarith

 
 
end ThreeState

end OAI

-- ---- from OAI.Probability.ThreeState.Supercritical ----
namespace OAI

/-! Boundary score moments and reconstruction above the Kesten–Stigum threshold. -/

namespace ThreeState

 

 

 
 

end ThreeState

namespace ThreeState

 
lemma posterior_le_one {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) :
    posterior law y i ≤ 1 := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => posterior_nonneg law y j)
    (Finset.mem_univ i)
  simpa only [posterior_sum] using h

lemma posteriorScore_square_le {α : Type*} (law : Spin → PMF α) (y : α) :
    (posteriorScore law y)^2 ≤ 12*posteriorTV law y := by
  have hn := posterior_nonneg law y 0
  have hu := posterior_le_one law y 0
  have hr : |posteriorScore law y| ≤ 2 := by
    rw [abs_le]
    dsimp [posteriorScore]
    constructor <;> linarith
  have he : |posteriorScore law y| = 3*|posterior law y 0-1/3| := by
    rw [show posteriorScore law y = 3*(posterior law y 0-1/3) by dsimp [posteriorScore]; ring, abs_mul]
    norm_num
  have h0 := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => abs_nonneg (posterior law y i-1/3))
    (Finset.mem_univ (0:Spin))
  dsimp [posteriorTV]
  nlinarith [sq_abs (posteriorScore law y),
    mul_nonneg (abs_nonneg (posteriorScore law y)) (sub_nonneg.mpr hr)]

 

end ThreeState

namespace ThreeState

 

 

 

 

end ThreeState

end OAI

-- ---- platform node ----
open OAI OAI.ThreeState


theorem _root_.Prove2me.Solution.OAI_ThreeState_posteriorScore_square_le : type_of% @_root_.OAI.ThreeState.posteriorScore_square_le := @_root_.OAI.ThreeState.posteriorScore_square_le

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), checked against the solution above.  The solution declares the platform theorem `OAI.ThreeState.posteriorScore_square_le` itself, so the statement is restated as an `example`. -/

section Prove2meStatement

open OAI OAI.ThreeState

example {α : Type*} (law : Spin → PMF α) (y : α) :
    (posteriorScore law y)^2 ≤ 12*posteriorTV law y := by
  first
  | exact _root_.Prove2me.Solution.OAI_ThreeState_posteriorScore_square_le law y
  | (apply _root_.Prove2me.Solution.OAI_ThreeState_posteriorScore_square_le <;> assumption)


end Prove2meStatement
