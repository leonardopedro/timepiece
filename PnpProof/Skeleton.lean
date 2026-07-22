import Mathlib
import PnpProof.Kopperman

/-!
# Part 13: an explicit (computably-enumerable) dense skeleton of the substrate

This module strengthens the abstract `Formalism.skeleton` data — which only
asserts `Countable ∧ Dense` and is populated by `Classical.choose
substrate_decidable_skeleton`, an abstract existence witness — to an **explicit
ℕ-indexed dense enumeration** of the substrate `Substrate = Lp ℝ 2 unitMeasure`.
This is the faithful Lean rendering of the paper's "decidable dense skeleton /
computable approximants".

## The honesty ceiling (read first)

`Substrate = Lp ℝ 2 unitMeasure` is a **quotient** by a.e.-equivalence. Mathlib
has **no `Computable` instance on `Lp`**, and none can even be *stated*: an `Lp`
element is an equivalence class of functions, not a code. Therefore "computable
skeleton" is **not** rendered as `Computable (enum : ℕ → Substrate)` — that is
unstatable. The faithful, available rendering is an enumeration
`enum : Code → Substrate` from an **`Encodable` / `DecidableEq` code type**, with
**dense range**. The *computable* content lives at the level of the **codes**
(an `Encodable` bijection with `ℕ`); `enum` itself is `noncomputable`, as all
`Lp` constructions are. No `Computable` claim is made on `Substrate`/`Lp`.

## What is delivered (S13.3 PROVED — the rational-step witness)

The witness is the **rational step functions** (`RatStepCode`, `ratStepFun`
below): an explicit `Encodable` code type whose decoding into `L²` is the
load-bearing computable datum. Its density theorem `ratStepFun_denseRange`
(`DenseRange ratStepFun`) is now **proved**: rational step functions are dense
in `L²[0,1]`. The proof reduces to the density of bounded continuous functions
(`MeasureTheory.Lp.boundedContinuousFunction_dense`) and then approximates each
bounded continuous function a.e. on `[0,1]` by a uniform rational-endpoint /
rational-value step function (`exists_ratStep_approx`, via uniform continuity on
the compact `[0,1]`), bounding the `L²` error by `MeasureTheory.Lp.norm_le_of_ae_bound`
on the probability measure `unitMeasure`. Accordingly the companion structure
`EnumSkeleton` and its witness `substrate_enumSkeleton` are built with code type
`RatStepCode` and `enum := ratStepFun` — the genuine rational-step witness, no
longer the `denseSeq` fallback. This is an **explicit `Encodable`-indexed
enumeration with dense range** whose codes are concrete rational data.

## Fences

* Companion structure only: `Formalism` and every theorem over it are untouched.
* No new axioms (the standard three only).
* No Clay leverage: this is a fidelity/expressibility upgrade of the NP-side
  "computable approximants" picture; it does not touch T5, the bridge, `σ`, or
  any arithmetic claim.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology BigOperators

noncomputable section

namespace PnpProof
namespace Kopperman

/-- S13.1 — A code for a rational step function on `[0,1]`: a finite list of
    `(left, right, value)` rational triples; the coded vector is
    `Σ (q : value) • 𝟙_(Ioc a b)` in `L²`. The *computable* content of the
    skeleton lives entirely here: `DecidableEq`, `Encodable`, and `Countable`
    are all derived automatically. This is the dense-enumeration code type used
    by `substrate_enumSkeleton` (density: `ratStepFun_denseRange`). -/
abbrev RatStepCode := List (ℚ × ℚ × ℚ)

example : DecidableEq RatStepCode := inferInstance
example : Encodable RatStepCode := inferInstance
example : Countable RatStepCode := inferInstance

/-- S13.2 — the decoding map: each triple `(a, b, q)` is sent to the `L²`
    indicator of `Ioc (a:ℝ) (b:ℝ)` with constant value `q`, and the list is
    summed in `Lp`. (`noncomputable`, as all `Lp` constructions are.) This is
    the witness for the dense skeleton; its density is `ratStepFun_denseRange`. -/
noncomputable def ratStepFun : RatStepCode → Substrate :=
  fun L => (L.map (fun t =>
    indicatorConstLp 2 (measurableSet_Ioc)
      (measure_ne_top unitMeasure (Set.Ioc (t.1 : ℝ) (t.2.1 : ℝ))) (t.2.2 : ℝ))).sum

/-
coeFn of a coded rational step function is a.e. the pointwise indicator sum.
-/
private lemma ratStepFun_coeFn (L : RatStepCode) :
    (ratStepFun L : ℝ → ℝ) =ᵐ[unitMeasure]
      fun x => (L.map (fun t : ℚ × ℚ × ℚ =>
        (Set.Ioc (t.1 : ℝ) (t.2.1 : ℝ)).indicator (fun _ => (t.2.2 : ℝ)) x)).sum := by
  convert MeasureTheory.MemLp.coeFn_toLp _;
  swap;
  induction' L with t L ih;
  all_goals norm_num [ Function.comp, List.map ];
  refine' MemLp.add _ ih;
  convert MeasureTheory.memLp_const ( t.2.2 : ℝ ) |> fun h => h.indicator ( measurableSet_Ioc ) using 1;
  all_goals try infer_instance;
  induction' L with t L ih;
  · unfold ratStepFun; aesop;
  · convert congr_arg₂ ( · + · ) rfl ih using 1

/-
A bounded continuous function is approximated a.e. (w.r.t. `unitMeasure`, i.e.
    on `[0,1]`) by a coded rational step function to within any positive tolerance.
-/
set_option maxHeartbeats 1000000 in
private lemma exists_ratStep_approx (F : BoundedContinuousFunction ℝ ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : RatStepCode, ∀ᵐ x ∂unitMeasure, |(ratStepFun L : ℝ → ℝ) x - F x| ≤ ε := by
  have h_uniform : ∃ δ > 0, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |x - y| < δ → |F x - F y| < ε / 2 := by
    have h_uniform : UniformContinuousOn (fun x : ℝ => F x) (Set.Icc (0 : ℝ) 1) := by
      exact ( isCompact_Icc.uniformContinuousOn_of_continuous F.continuous.continuousOn );
    exact Metric.uniformContinuousOn_iff.mp h_uniform ( ε / 2 ) ( half_pos hε ) |> Exists.imp fun δ hδ => by tauto;
  obtain ⟨δ, hδ_pos, hδ⟩ := h_uniform
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n > 0 ∧ 1 / (n : ℝ) < δ := by
    exact ⟨ ⌊δ⁻¹⌋₊ + 1, Nat.succ_pos _, by simpa using inv_lt_of_inv_lt₀ hδ_pos <| Nat.lt_floor_add_one _ ⟩;
  -- For each `i : Fin n` choose (by `exists_rat_btwn`) a rational `q i` with `|(q i : ℝ) - F (i/n : ℝ)| ≤ ε/2`.
  obtain ⟨q, hq⟩ : ∃ q : Fin n → ℚ, ∀ i : Fin n, |(q i : ℝ) - F (i / n : ℝ)| ≤ ε / 2 := by
    exact ⟨ fun i => Classical.choose ( exists_rat_btwn ( show F ( i / n : ℝ ) - ε / 2 < F ( i / n : ℝ ) by linarith ) ), fun i => abs_le.mpr ⟨ by linarith [ Classical.choose_spec ( exists_rat_btwn ( show F ( i / n : ℝ ) - ε / 2 < F ( i / n : ℝ ) by linarith ) ) ], by linarith [ Classical.choose_spec ( exists_rat_btwn ( show F ( i / n : ℝ ) - ε / 2 < F ( i / n : ℝ ) by linarith ) ) ] ⟩ ⟩;
  refine' ⟨ List.ofFn fun i : Fin n => ( i / n, ( i + 1 ) / n, q i ), _ ⟩;
  have h_sum : ∀ᵐ x ∂unitMeasure, ∃ i : Fin n, x ∈ Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n) ∧ (ratStepFun (List.ofFn fun i : Fin n => ( i / n, ( i + 1 ) / n, q i )) : ℝ → ℝ) x = (q i : ℝ) := by
    have h_sum : ∀ᵐ x ∂unitMeasure, ∃ i : Fin n, x ∈ Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n) := by
      have h_sum : ∀ᵐ x ∂unitMeasure, x ∈ Set.Ioc (0 : ℝ) 1 := by
        rw [ MeasureTheory.ae_iff ] ; norm_num [ unitMeasure ];
        rw [ show { a : ℝ | 0 < a → 1 < a } ∩ Icc 0 1 = { 0 } from Set.eq_singleton_iff_unique_mem.mpr ⟨ by norm_num, fun x hx => le_antisymm ( le_of_not_gt fun hx' => by linarith [ hx.1 hx', hx.2.2 ] ) hx.2.1 ⟩ ] ; norm_num;
      filter_upwards [ h_sum ] with x hx;
      use ⟨ ⌈x * n⌉₊ - 1, by
        rw [ tsub_lt_iff_left ] <;> norm_num;
        · exact_mod_cast ( by nlinarith [ Nat.ceil_lt_add_one ( show 0 ≤ x * n by exact mul_nonneg hx.1.le ( Nat.cast_nonneg _ ) ), hx.2, show ( n : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr hn.1 ] : ( ⌈x * n⌉₊ : ℝ ) < 1 + n );
        · exact mul_pos hx.1 ( Nat.cast_pos.mpr hn.1 ) ⟩
      generalize_proofs at *;
      simp +zetaDelta at *;
      rw [ Nat.cast_sub <| Nat.ceil_pos.mpr <| mul_pos hx.1 <| Nat.cast_pos.mpr hn.1 ] ; norm_num;
      exact ⟨ by rw [ div_lt_iff₀ ( Nat.cast_pos.mpr hn.1 ) ] ; linarith [ Nat.ceil_lt_add_one ( show 0 ≤ x * n by exact mul_nonneg hx.1.le ( Nat.cast_nonneg _ ) ) ], by rw [ le_div_iff₀ ( Nat.cast_pos.mpr hn.1 ) ] ; linarith [ Nat.le_ceil ( x * n ) ] ⟩;
    filter_upwards [ h_sum, ratStepFun_coeFn ( List.ofFn fun i : Fin n => ( i / n, ( i + 1 ) / n, q i ) ) ] with x hx₁ hx₂;
    obtain ⟨ i, hi ⟩ := hx₁; use i; simp_all +decide [ List.sum_ofFn ] ;
    rw [ Finset.sum_eq_single i ] <;> simp_all +decide [ Set.indicator ];
    intro j hj₁ hj₂ hj₃; contrapose! hj₁; simp_all +decide [ Fin.ext_iff, div_lt_iff₀, le_div_iff₀ ] ;
    exact Nat.le_antisymm ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast; linarith ] } ) ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast; linarith ] } );
  filter_upwards [ h_sum, MeasureTheory.ae_restrict_mem measurableSet_Icc, MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton 0 ) ] with x hx₁ hx₂ hx₃;
  obtain ⟨ i, hi₁, hi₂ ⟩ := hx₁; specialize hq i; specialize hδ ( i / n ) ⟨ by positivity, by rw [ div_le_iff₀ ( by norm_cast; linarith ) ] ; nlinarith [ show ( i : ℝ ) + 1 ≤ n by norm_cast; linarith [ Fin.is_lt i ] ] ⟩ x hx₂; simp_all +decide [ abs_sub_comm ] ;
  grind

/-
S13.3 — the density theorem: rational step functions are dense in `L²[0,1]`.
    (The genuine fidelity upgrade; see the module docstring.)
-/
theorem ratStepFun_denseRange : DenseRange ratStepFun := by
  refine' fun x => Metric.mem_closure_range_iff.2 fun ε hε => _;
  -- By the density of bounded continuous functions in $L^2[0,1]$, there exists a bounded continuous function $F$ such that $\|F - x\|_2 < \frac{\epsilon}{2}$.
  obtain ⟨F, hF⟩ : ∃ F : BoundedContinuousFunction ℝ ℝ, ‖(BoundedContinuousFunction.toLp 2 unitMeasure ℝ F : Substrate) - x‖ < ε / 2 := by
    have := Lp.boundedContinuousFunction_dense ( E := ℝ ) ( μ := unitMeasure ) ( p := 2 ) ( by norm_num );
    have := Metric.mem_closure_iff.mp ( this x ) ( ε / 2 ) ( half_pos hε );
    obtain ⟨ b, hb₁, hb₂ ⟩ := this; rw [ dist_comm ] at hb₂; simp_all +decide [ dist_eq_norm ] ;
    rw [ Lp.mem_boundedContinuousFunction_iff ] at hb₁ ; aesop;
  obtain ⟨ L, hL ⟩ := exists_ratStep_approx F ( half_pos hε );
  have h_dist : ‖(ratStepFun L : Substrate) - (BoundedContinuousFunction.toLp 2 unitMeasure ℝ F : Substrate)‖ ≤ ε / 2 := by
    refine' le_trans ( MeasureTheory.Lp.norm_le_of_ae_bound _ _ ) _;
    exact ε / 2;
    · linarith;
    · filter_upwards [ hL, MeasureTheory.Lp.coeFn_sub ( ratStepFun L ) ( BoundedContinuousFunction.toLp 2 unitMeasure ℝ F ), BoundedContinuousFunction.coeFn_toLp 2 unitMeasure ℝ F ] with x hx₁ hx₂ hx₃ using by aesop;
    · norm_num [ measureUnivNNReal ];
  use L;
  rw [ dist_comm, dist_eq_norm ];
  exact lt_of_le_of_lt ( by simpa using norm_add_le ( ratStepFun L - ( BoundedContinuousFunction.toLp 2 unitMeasure ℝ ) F ) ( ( BoundedContinuousFunction.toLp 2 unitMeasure ℝ ) F - x ) ) ( by linarith )

/-- S13.4 — An explicit computably-enumerable dense skeleton: a dense
    enumeration of `H` by an `Encodable` code type. The faithful rendering of
    "decidable/computable skeleton" — the computability is in `Code`, not in the
    noncomputable `enum` into the `Lp`-quotient (see the honesty ceiling). -/
structure EnumSkeleton (H : Type*) [TopologicalSpace H] where
  /-- The code type — where the decidable/computable content lives. -/
  Code : Type
  [codeEnc : Encodable Code]
  /-- The (noncomputable) decoding into the carrier. -/
  enum : Code → H
  /-- The decoded range is dense. -/
  enum_dense : DenseRange enum

/-- The substrate admits an explicit rational-step dense enumeration (S13.3):
    code type `RatStepCode` with `enum := ratStepFun`, dense by
    `ratStepFun_denseRange`. -/
noncomputable def substrate_enumSkeleton : EnumSkeleton Substrate :=
  { Code := RatStepCode
    enum := ratStepFun
    enum_dense := ratStepFun_denseRange }

/-- The explicit skeleton *refines* the abstract `Formalism.skeleton` data: its
    range is a countable dense set, so it is a legitimate `skeleton`. (Recorded
    as a bridge; `formalismOfPrior` is **not** changed.) -/
theorem enumSkeleton_refines (S : EnumSkeleton Substrate) :
    (Set.range S.enum).Countable ∧ Dense (Set.range S.enum) := by
  haveI := S.codeEnc
  haveI : Countable S.Code := Encodable.countable
  exact ⟨Set.countable_range _, S.enum_dense⟩

end Kopperman
end PnpProof
