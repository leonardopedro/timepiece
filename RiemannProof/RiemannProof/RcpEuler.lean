import Mathlib
import RiemannProof.RectangleStrategy
import RiemannProof.GaussianEuler

/-!
# RH via a bounded-coefficient prior + regular conditional probability

This file implements **Phases 0–2** of `IMPLEMENTATION_PLAN_RCP.md`: the
bounded-coefficient exponential Euler product `eulerB`, the unit-ball prior
`priorBall`, the regular-conditional-probability kernel `rcpKernel`, and the
`rcpZeroAt` non-detectability layer.

It is a *different* route from `GaussianEuler.lean` (the Gaussian model): here the
coefficients live in the closed unit ball of `ℂ`, which gives, for **every** `ω`,
absolute and locally uniform convergence of the prime tails on `{Re ≥ a > 1}`
(note N2 of the plan) — no a.s. qualifier.

## Status (per the plan's `[LB]`/`[mech]` flags)

* `[mech]` facts (`eulerB_ne_zero`, `eulerB_differentiableOn`) are proved.
* The bounded-coefficient tail estimate `bSum_tail_small` (the corrected,
  genuinely-true form of N2, an `M`-test) is **proved**.
* The prior layer is now fully constructed and `sorry`-free: `diskLaw` (uniform
  law on the closed unit disk), `priorBall := Measure.infinitePi (fun _ => diskLaw)`
  (the independent product), `priorBall_isProb`, `priorBall_ball` (support in the
  closed unit ball) and `priorBall_atomless` (the prior is atomless, so its
  continuous part is nontrivial, cf. N1).
* rcp non-detectability (Phase 2.2) comes in **two forms** (2026-06-19 maintainer
  refinement). `not_rcpZeroAtAll` — the `∀ k` *placeholder* form `rcpZeroAtAll` —
  is **proved** but trivial: with coefficients in the closed unit ball, the
  interior value `eulerB (P 0) s₀ ·` is bounded away from `0` by a positive
  constant on the support of `priorBall`, so selecting the fixed cutoff `k = 0`
  makes the joint event null for small `r`. It needs only boundedness and does not
  see whether `η(s₀) = 0`. The substantive object is the **limit / eventual-`k`**
  form `rcpZeroAt`, whose non-detectability `not_rcpZeroAt` is genuinely
  load-bearing (`¬ rcpZeroAt` is `η(s₀) ≠ 0` uniformly in `s₀`, i.e. RH itself; its
  content is the rcp limit `L ≠ 1`, Bagchi/Voronin universality on a local
  neighborhood). `not_rcpZeroAt` is therefore left as an honest `sorry` with the
  recipe — it is not weaker than RH and is not improvised, exactly as the plan
  directs.
* `rcp_recipEulerB_tendsto_recipEta` (Phase 1.4) is now **proved**, together with
  its supporting continuity helpers (`etaRect_continuousOn`,
  `etaEulerApprox_ne_zero_closure`, `eulerB_continuousOn`,
  `recipEulerB_continuousOn`, `recipEtaRect_continuousOn_boundary`) and the
  reusable per-edge dominated-convergence step `edge_integral_tendsto`. The added
  hypothesis `Re < 1` on the closure (the critical strip) is what makes
  `etaRect`/`eulerB` continuous there.
* `priorBall_edgeNbhd_pos` (Phase 1.3) has been **restated and proved**. The
  original statement compared `eulerB P · ω` to the *true* `η` (`etaRect`) at a
  fixed `P`, which is dubious/false (small-coefficient concentration only yields
  closeness to the approximant `etaEulerApprox P`, off by the fixed approximation
  gap). The honest, *true* content — every neighborhood of the `η`-trace measured
  **against the approximant** `etaEulerApprox P` has positive prior mass (the
  Tjur "defined only on the support" precondition) — is now proved from the
  positive-mass coefficient box `priorBall_box_pos` (built on
  `diskLaw_closedBall_pos` and `Measure.infinitePi_pi`) together with
  `Complex.norm_exp_sub_one_le`. `rcpKernel`
  remains a definition (the `condDistrib` disintegration). The bridge
  `counterexample_iff_rcpZero` (in `SchoenfeldPRA.lean`) is the second
  load-bearing obligation (Schoenfeld 1976 at the mean realization); it is left as
  an honest `sorry`. Together with `not_rcpZeroAt` (the limit form) these carry the
  entire un-formalized analytic content of the route and are not improvised,
  exactly as the plan directs ("do not improvise a proof").

The reused infrastructure (`Rect`, `Rect.boundaryIntegral`, `rect_cauchy`,
`boundary_integral_limit_eq_zero`, `reciprocal_tendstoUniformlyOn_of_nonvanishing`,
`etaRect`, `etaEulerApprox`, `GaussianEuler.cCorr`) is **not** re-proved here.
-/

open Complex Finset Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace RcpEuler

/-! ## Phase 0.1 — Coefficient and product -/

/-- Sample space: a coefficient per prime index, valued in `ℂ`. -/
abbrev Ωb : Type := ℕ → ℂ

/-- Bounded coefficient: the `ω`-th coordinate, used only where `‖·‖ ≤ 1` a.e. -/
def Xb (p : ℕ) (ω : Ωb) : ℂ := ω p

/-- Exponential Euler product with bounded coefficients. The deterministic
    centering `GaussianEuler.cCorr P s = log (etaEulerApprox P s)` is shared with
    the Gaussian route. -/
def eulerB (P : ℕ) (s : ℂ) (ω : Ωb) : ℂ :=
  Complex.exp ((∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, Xb p ω * (p : ℂ) ^ (-s))
               + GaussianEuler.cCorr P s)

/-! ## Phase 0.2 — Structural facts -/

/-- **[mech]** `eulerB` is `exp` of something, hence never zero (no hypotheses on
    `s`, `P`, `ω`). This is the structural payoff of the exponential form. -/
lemma eulerB_ne_zero (P : ℕ) (s : ℂ) (ω : Ωb) : eulerB P s ω ≠ 0 :=
  Complex.exp_ne_zero _

/-- The finite random Dirichlet sum, as a function of `s`. -/
def bSum (P : ℕ) (ω : Ωb) (s : ℂ) : ℂ :=
  ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, Xb p ω * (p : ℂ) ^ (-s)

@[simp] lemma eulerB_eq (P : ℕ) (s : ℂ) (ω : Ωb) :
    eulerB P s ω = Complex.exp (bSum P ω s + GaussianEuler.cCorr P s) := rfl

/-- **[mech]** On a rectangle whose closure lies in `{Re > 0}` and avoids the
    zeros of `etaEulerApprox P` (so the centering `cCorr` is analytic and
    `exp ∘ cCorr = etaEulerApprox` there), `eulerB` is differentiable.
    Mirrors `GaussianEuler.eulerG_differentiableOn`. -/
lemma eulerB_differentiableOn (P : ℕ) (ω : Ωb) (R : Rect)
    (hRpos : ∀ z ∈ R.closure, 0 < z.re)
    (hAna : ∀ z ∈ R.closure, etaEulerApprox P z ≠ 0) :
    DifferentiableOn ℂ (fun s => eulerB P s ω) R.closure := by
  have hbSum : Differentiable ℂ (bSum P ω) := by
    unfold bSum
    intro s
    refine DifferentiableAt.fun_sum (fun p hp => ?_)
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hpp.pos.ne'
    exact (differentiableAt_const _).mul
      ((Differentiable.const_cpow differentiable_neg (Or.inl hp0)) s)
  have hprod : DifferentiableOn ℂ
      (fun s => Complex.exp (bSum P ω s) * etaEulerApprox P s) R.closure := by
    apply DifferentiableOn.mul
    · exact (hbSum.cexp).differentiableOn
    · exact ((etaEulerApprox_analyticOnNhd P).differentiableOn).mono
        (fun z hz => show z.re > 0 from hRpos z hz)
  refine hprod.congr (fun z hz => ?_)
  rw [eulerB_eq, Complex.exp_add]
  congr 1
  exact Complex.exp_log (hAna z hz)

/-
**[mech, honest restatement of N2]** Bounded-coefficient tail Cauchy
    criterion. For coefficients in the closed unit ball, the tail of the prime
    Dirichlet sum is uniformly small on `{Re ≥ a}` with `a > 1`, dominated by
    `∑_{p>P} p^{-a}` (Weierstrass `M`-test), uniformly in `ω`.

    The plan's Phase-0.2 statement asks for `eulerB P · ω → etaRect`; that is
    **false** for a generic `ω` in the ball, because the random factor
    `exp (∑_p X_p p^{-s})` does not tend to `1`. The genuine, true content of N2
    is this uniform tail smallness, which is all the conditional route (1.4) uses.
    Left `[LB] sorry` with the `M`-test recipe.
-/
lemma bSum_tail_small (a : ℝ) (ha : 1 < a) (ω : Ωb) (hω : ∀ p, ‖Xb p ω‖ ≤ 1) :
    ∀ ε > 0, ∃ P₀ : ℕ, ∀ P ≥ P₀, ∀ Q ≥ P, ∀ s : ℂ, a ≤ s.re →
      ‖(∑ p ∈ ((Finset.range (Q + 1)).filter Nat.Prime) \
            ((Finset.range (P + 1)).filter Nat.Prime), Xb p ω * (p : ℂ) ^ (-s))‖ ≤ ε := by
  intro ε hε_pos
  have h_summable : Summable (fun n : ℕ => (n : ℝ) ^ (-a)) := by
    exact Real.summable_nat_rpow.2 ( by linarith );
  obtain ⟨ P₀, hP₀ ⟩ := Metric.tendsto_atTop.mp h_summable.hasSum.tendsto_sum_nat ( ε / 2 ) ( half_pos hε_pos ) ; use P₀; intros P hP Q hQ s hs; refine' le_trans ( norm_sum_le _ _ ) _ ; simp_all +decide [ Finset.sum_ite ] ;
  -- Apply the bound on the norm of the terms in the sum.
  have h_term_bound : ∀ p ∈ ((Finset.range (Q + 1)).filter Nat.Prime) \ ((Finset.range (P + 1)).filter Nat.Prime), ‖Xb p ω * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-a) := by
    intro p hp; specialize hω p; simp_all +decide [ Complex.norm_cpow_of_ne_zero, Nat.Prime.ne_zero ] ;
    exact le_trans ( mul_le_of_le_one_left ( by positivity ) hω ) ( Real.rpow_le_rpow_of_exponent_le ( mod_cast hp.1.2.one_lt.le ) ( by linarith ) );
  refine' le_trans ( Finset.sum_le_sum fun p hp => by simpa only [ ← norm_mul ] using h_term_bound p hp ) _;
  refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( show _ ⊆ Finset.Ico ( P + 1 ) ( Q + 1 ) from _ ) fun _ _ _ => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) _;
  · grind;
  · have := hP₀ ( Q + 1 ) ( by linarith ) ; have := hP₀ ( P + 1 ) ( by linarith ) ; simp_all +decide [ dist_eq_norm, Finset.sum_Ico_eq_sub _ ( by linarith : P + 1 ≤ Q + 1 ) ] ;
    linarith [ abs_lt.mp ‹|∑ i ∈ range ( Q + 1 ), ( i : ℝ ) ^ ( -a ) - ∑' i : ℕ, ( i : ℝ ) ^ ( -a )| < ε / 2›, abs_lt.mp ‹|∑ i ∈ range ( P + 1 ), ( i : ℝ ) ^ ( -a ) - ∑' i : ℕ, ( i : ℝ ) ^ ( -a )| < ε / 2› ]

/-! ## Phase 0.3 — The bounded-coefficient prior

`priorBall` is a probability measure on `Ωb` concentrated on the closed unit ball
`{ω | ∀ p, ‖ω p‖ ≤ 1}`, taken (per N1) to be a possibly **mixed**
continuous+discrete product law whose continuous part is nontrivial. The
Kopperman-formalism bridge (`rcpFormalism` via `formalismOfPrior`) lives in
`SchoenfeldPRA.lean`, where the substrate measurable-space instances are in
scope. -/

/-- The uniform probability law on the closed unit disk of `ℂ`: the (normalized)
    restriction of Lebesgue measure to `Metric.closedBall 0 1`. This is the
    continuous, atomless single-coordinate law of the prior. -/
def diskLaw : Measure ℂ := ProbabilityTheory.cond volume (Metric.closedBall (0 : ℂ) 1)

instance diskLaw_isProb : IsProbabilityMeasure diskLaw := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Complex.volume_closedBall]; simp [NNReal.pi_pos.ne']
  · rw [Complex.volume_closedBall]; simp

/-- `diskLaw` gives full mass to the closed unit disk. -/
lemma diskLaw_ball : diskLaw (Metric.closedBall (0 : ℂ) 1) = 1 := by
  rw [diskLaw, ProbabilityTheory.cond_apply measurableSet_closedBall, Set.inter_self,
    ENNReal.inv_mul_cancel] <;> rw [Complex.volume_closedBall] <;> simp [NNReal.pi_pos.ne']

/-- The unit-ball prior on coefficient space: the countable product of the
    uniform unit-disk law `diskLaw` over the prime indices. Each coordinate is an
    independent uniform draw from the closed unit disk, so the prior is supported
    on the closed unit ball `{ω | ∀ p, ‖ω p‖ ≤ 1}` and its continuous part is
    nontrivial (atomless), as required by N1. -/
def priorBall : Measure Ωb := Measure.infinitePi (fun _ : ℕ => diskLaw)

/-- `priorBall` is a probability measure. -/
instance priorBall_isProb : IsProbabilityMeasure priorBall := by
  unfold priorBall; infer_instance

/-- `priorBall` is concentrated on the closed unit ball. -/
lemma priorBall_ball : ∀ᵐ ω ∂priorBall, ∀ p, ‖Xb p ω‖ ≤ 1 := by
  have hms : ∀ p : ℕ, MeasurableSet {ω : Ωb | ‖Xb p ω‖ ≤ 1} := by
    intro p
    have : {ω : Ωb | ‖Xb p ω‖ ≤ 1} = (fun ω : Ωb => ω p) ⁻¹' (Metric.closedBall (0 : ℂ) 1) := by
      ext ω; simp [Xb, Metric.mem_closedBall]
    rw [this]; exact measurableSet_closedBall.preimage (measurable_pi_apply p)
  have hcoord : ∀ p : ℕ, priorBall {ω : Ωb | ‖Xb p ω‖ ≤ 1} = 1 := by
    intro p
    have hpre : {ω : Ωb | ‖Xb p ω‖ ≤ 1}
        = (fun ω : Ωb => ω p) ⁻¹' (Metric.closedBall (0 : ℂ) 1) := by
      ext ω; simp [Xb, Metric.mem_closedBall]
    rw [hpre, priorBall, ← Measure.map_apply (measurable_pi_apply p) measurableSet_closedBall,
      Measure.infinitePi_map_eval]
    exact diskLaw_ball
  rw [ae_iff]
  have heq : {ω : Ωb | ¬ ∀ p, ‖Xb p ω‖ ≤ 1} = ⋃ p, {ω : Ωb | ‖Xb p ω‖ ≤ 1}ᶜ := by
    ext ω; simp
  rw [heq]
  refine measure_iUnion_null (fun p => ?_)
  rw [prob_compl_eq_zero_iff (hms p)]
  exact hcoord p

/-- `diskLaw` is atomless: every singleton is null (it is absolutely continuous
    w.r.t. Lebesgue measure). -/
lemma diskLaw_atomless (z : ℂ) : diskLaw {z} = 0 := by
  rw [diskLaw, cond_apply measurableSet_closedBall, mul_eq_zero]
  right
  exact measure_mono_null Set.inter_subset_right (by simp)

/-- `priorBall` is atomless: every singleton coefficient sequence is null. The
    continuous part of the prior is thus nontrivial (cf. N1). -/
lemma priorBall_atomless (ω : Ωb) : priorBall {ω} = 0 := by
  have hsub : ({ω} : Set Ωb) ⊆ (fun x : Ωb => x 0) ⁻¹' ({ω 0} : Set ℂ) := by
    intro x hx; simp only [Set.mem_singleton_iff] at hx; simp [hx]
  refine measure_mono_null hsub ?_
  rw [priorBall, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton _),
    Measure.infinitePi_map_eval]
  exact diskLaw_atomless _

/-! ## Phase 1.1 — Edge-evaluation map -/

/-- The boundary trace of `eulerB` on the edges `R.closure \ R.openInt` of a
    strip-internal loop. -/
def edgeTrace (P : ℕ) (R : Rect) (ω : Ωb) : (↥(R.closure \ R.openInt)) → ℂ :=
  fun z => eulerB P (z : ℂ) ω

/-- The interior value of `eulerB` at `s₀`. -/
def interiorVal (P : ℕ) (s₀ : ℂ) (ω : Ωb) : ℂ := eulerB P s₀ ω

/-! ## Phase 1.2 — The rcp kernel

The regular conditional distribution of the interior value given the edge trace,
using the genuine disintegration API `ProbabilityTheory.condDistrib` (N1: this is
**not** `ProbabilityTheory.cond` on a single event). -/

/-- **[LB]** The rcp kernel: the conditional law of the interior value
    `eulerB P s₀ ·` given the edge trace `edgeTrace P R`, under `priorBall`.
    Built with `condDistrib`; measurability of both maps (continuity of `eulerB`
    in `ω`) and `IsFiniteMeasure priorBall` are the inputs. -/
def rcpKernel (P : ℕ) (s₀ : ℂ) (R : Rect) :
    ProbabilityTheory.Kernel ((↥(R.closure \ R.openInt)) → ℂ) ℂ :=
  ProbabilityTheory.condDistrib (fun ω => interiorVal P s₀ ω) (edgeTrace P R) priorBall

/-! ## Phase 1.3 — Positivity of the edge-neighborhood event

**Restated (plan §"The simplification", step 1 / Phase-1.3 restatement).** The
original statement compared `eulerB P · ω` to the *true* `η` (`etaRect`) at a
fixed `P`; that is dubious/false, because small-coefficient concentration only
yields closeness to the **approximant** `etaEulerApprox P`. The honest, *true*
content is the support statement: every neighborhood of the `η`-trace — measured
**against the approximant** `etaEulerApprox P`, the deterministic skeleton that
`eulerB` actually centers on — has positive prior mass. This is exactly the
"`e_η` is in the support of the trace law" / Tjur "defined only on the support"
precondition. It is now **proved**. -/

/-- The event that the edge trace of `eulerB P · ω` is within `ε` of the
    deterministic approximant `etaEulerApprox P` on the edges of `R`. -/
def edgeNbhd (P : ℕ) (R : Rect) (ε : ℝ) : Set Ωb :=
  {ω | ∀ z ∈ R.closure \ R.openInt, ‖eulerB P (z : ℂ) ω - etaEulerApprox P z‖ < ε}

/-
The closed `δ`-disk has positive `diskLaw` mass, for any `δ > 0`.
-/
lemma diskLaw_closedBall_pos (δ : ℝ) (hδ : 0 < δ) :
    0 < diskLaw (Metric.closedBall (0 : ℂ) δ) := by
  rw [ diskLaw, ProbabilityTheory.cond_apply measurableSet_closedBall ];
  refine' ENNReal.mul_pos _ _ <;> norm_num;
  refine' ne_of_gt ( lt_of_lt_of_le _ ( MeasureTheory.measure_mono _ ) );
  rotate_left;
  exact Metric.closedBall 0 ( Min.min 1 δ );
  · exact fun x hx => ⟨ Metric.closedBall_subset_closedBall ( min_le_left _ _ ) hx, Metric.closedBall_subset_closedBall ( min_le_right _ _ ) hx ⟩;
  · simp +decide [ Complex.volume_closedBall, hδ ];
    exact ⟨ by exact ENNReal.pow_pos ( lt_min zero_lt_one ( ENNReal.ofReal_pos.mpr hδ ) ) _, by exact NNReal.coe_pos.mpr Real.pi_pos ⟩

/-- The finite-cylinder box `{ω | ∀ p ∈ s, ‖ω p‖ ≤ δ}` has positive `priorBall`
    mass, for any finite index set `s` and any radius `δ > 0`. -/
lemma priorBall_box_pos (s : Finset ℕ) (δ : ℝ) (hδ : 0 < δ) :
    0 < priorBall (Set.pi (↑s) (fun _ => Metric.closedBall (0 : ℂ) δ)) := by
  haveI : ∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ => diskLaw) i) := fun _ => diskLaw_isProb
  have h := Measure.infinitePi_pi (μ := fun _ : ℕ => diskLaw)
    (s := s) (t := fun _ => Metric.closedBall (0 : ℂ) δ)
    (fun i _ => measurableSet_closedBall)
  rw [priorBall, h, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  exact fun i _ => (diskLaw_closedBall_pos δ hδ).ne'

/-
**[LB, restated — PROVED]** The edge-neighborhood event (against the
    approximant) carries positive `priorBall` mass.

    Recipe (plan 1.3, restated): small-coefficient concentration. On the compact
    edge `R.closure \ R.openInt` (where `Re z > 1/2`) and using `hAna`,
    `eulerB P z ω = exp (bSum P ω z) · etaEulerApprox P z`, so
    `eulerB P z ω - etaEulerApprox P z = etaEulerApprox P z · (exp (bSum) - 1)`,
    bounded via `Complex.norm_exp_sub_one_le` on a small coefficient box of
    positive mass (`priorBall_box_pos`).
-/
lemma priorBall_edgeNbhd_pos (P : ℕ) (R : Rect)
    (hRlo : ∀ z ∈ R.closure, 1 / 2 < z.re)
    (hAna : ∀ z ∈ R.closure, etaEulerApprox P z ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    0 < priorBall (edgeNbhd P R ε) := by
  -- Set `δ := min(1/(C+1), ε/(2*(M+1)*(C+1)))` where `C := ∑ p ∈ S, (p:ℝ)^(-(1:ℝ)/2)`.
  obtain ⟨M, hM⟩ : ∃ M ≥ 0, ∀ z ∈ R.closure \ R.openInt, ‖etaEulerApprox P z‖ ≤ M := by
    obtain ⟨ M, hM ⟩ := IsCompact.exists_bound_of_continuousOn ( show IsCompact ( R.closure \ R.openInt ) from by
                                                                  apply_rules [ IsCompact.diff, Rect.isCompact_closure ];
                                                                  exact isOpen_Ioi.preimage Complex.continuous_re |> IsOpen.inter <| isOpen_Iio.preimage Complex.continuous_re |> IsOpen.inter <| isOpen_Ioi.preimage Complex.continuous_im |> IsOpen.inter <| isOpen_Iio.preimage Complex.continuous_im ) ( show ContinuousOn ( fun z => etaEulerApprox P z ) ( R.closure \ R.openInt ) from by
                                                                                                                              exact ( etaEulerApprox_analyticOnNhd P |> AnalyticOnNhd.continuousOn |> ContinuousOn.mono <| fun z hz => show z.re > 0 from by linarith [ hRlo z <| by exact hz.1 ] ) ) ; use Max.max M 1 ; aesop;
  -- Set `δ := min(1/(C+1), ε/(2*(M+1)*(C+1)))` where `C := ∑ p ∈ S, (p:ℝ)^(-(1:ℝ)/2)`. Then `δ > 0`.
  obtain ⟨δ, hδ_pos, hδ_bound⟩ : ∃ δ > 0, δ * (∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, (p : ℝ) ^ (-(1 / 2 : ℝ))) ≤ 1 ∧ 2 * M * (δ * (∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, (p : ℝ) ^ (-(1 / 2 : ℝ)))) < ε := by
    refine' ⟨ Min.min ( 1 / ( ∑ p ∈ Finset.filter Nat.Prime ( Finset.range ( P + 1 ) ), ( p : ℝ ) ^ ( - ( 1 / 2 : ℝ ) ) + 1 ) ) ( ε / ( 2 * ( M + 1 ) * ( ∑ p ∈ Finset.filter Nat.Prime ( Finset.range ( P + 1 ) ), ( p : ℝ ) ^ ( - ( 1 / 2 : ℝ ) ) + 1 ) ) ), _, _, _ ⟩ <;> norm_num;
    · exact ⟨ add_pos_of_nonneg_of_pos ( Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) zero_lt_one, div_pos hε ( mul_pos ( mul_pos two_pos ( add_pos_of_nonneg_of_pos hM.1 zero_lt_one ) ) ( add_pos_of_nonneg_of_pos ( Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) zero_lt_one ) ) ⟩;
    · exact le_trans ( mul_le_mul_of_nonneg_right ( min_le_left _ _ ) ( Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ( by rw [ inv_mul_le_iff₀ ] <;> linarith [ show 0 ≤ ∑ x ∈ Finset.filter Nat.Prime ( Finset.range ( P + 1 ) ), ( x : ℝ ) ^ ( - ( 1 / 2 : ℝ ) ) from Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ] );
    · refine' lt_of_le_of_lt ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_right ( min_le_right _ _ ) <| Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) <| by linarith ) _;
      rw [ div_mul_eq_mul_div, mul_div, div_lt_iff₀ ] <;> nlinarith [ show 0 ≤ ∑ x ∈ Finset.filter Nat.Prime ( Finset.range ( P + 1 ) ), ( x : ℝ ) ^ ( - ( 1 / 2 : ℝ ) ) by exact Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _, mul_div_cancel₀ ε ( show ( 2 * ( M + 1 ) ) ≠ 0 by linarith ) ];
  -- Show that the box $B$ is contained in the edge-neighborhood.
  have h_box_subset : ∀ ω ∈ Set.pi (↑((Finset.range (P + 1)).filter Nat.Prime)) (fun _ => Metric.closedBall (0 : ℂ) δ), ∀ z ∈ R.closure \ R.openInt, ‖eulerB P z ω - etaEulerApprox P z‖ < ε := by
    intro ω hω z hz
    have h_bSum_bound : ‖bSum P ω z‖ ≤ δ * (∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, (p : ℝ) ^ (-(1 / 2 : ℝ))) := by
      have h_bSum_bound : ∀ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ‖Xb p ω * (p : ℂ) ^ (-z)‖ ≤ δ * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
        intro p hp; specialize hω p hp; simp_all +decide [ Xb, Complex.norm_cpow_of_ne_zero, Nat.Prime.ne_zero ] ;
        exact mul_le_mul hω ( Real.rpow_le_rpow_of_exponent_le ( mod_cast hp.2.one_lt.le ) ( by linarith [ hRlo z hz.1 ] ) ) ( by positivity ) ( by positivity );
      exact le_trans ( norm_sum_le _ _ ) ( by simpa only [ Finset.mul_sum _ _ _ ] using Finset.sum_le_sum h_bSum_bound );
    have h_exp_bound : ‖Complex.exp (bSum P ω z) - 1‖ ≤ 2 * ‖bSum P ω z‖ := by
      have := Complex.norm_exp_sub_one_le ( show ‖bSum P ω z‖ ≤ 1 by linarith ) ; linarith;
    have h_eulerB_bound : ‖eulerB P z ω - etaEulerApprox P z‖ ≤ ‖etaEulerApprox P z‖ * ‖Complex.exp (bSum P ω z) - 1‖ := by
      rw [ ← norm_mul ] ; rw [ eulerB_eq ] ; rw [ Complex.exp_add ] ; ring_nf;
      rw [ show cexp ( GaussianEuler.cCorr P z ) = etaEulerApprox P z from Complex.exp_log ( hAna z hz.1 ) ];
    exact h_eulerB_bound.trans_lt ( by nlinarith [ hM.2 z hz, norm_nonneg ( bSum P ω z ), norm_nonneg ( Complex.exp ( bSum P ω z ) - 1 ) ] );
  refine' lt_of_lt_of_le _ ( MeasureTheory.measure_mono <| show edgeNbhd P R ε ⊇ Set.pi (↑((Finset.range (P + 1)).filter Nat.Prime)) (fun _ => Metric.closedBall (0 : ℂ) δ) from fun ω hω => h_box_subset ω hω );
  convert priorBall_box_pos ( Finset.filter Nat.Prime ( Finset.range ( P + 1 ) ) ) δ hδ_pos using 1

/-! ## Phase 1.4 — Conditional contour convergence -/

/-- `etaRect` is analytic, hence continuous, on the closure of a rectangle
    contained in the critical strip `{1/2 < Re < 1}`. -/
lemma etaRect_continuousOn (R : Rect)
    (hRlo : ∀ z ∈ R.closure, 1 / 2 < z.re) (hRhi : ∀ z ∈ R.closure, z.re < 1) :
    ContinuousOn etaRect R.closure := by
  have h_ana : AnalyticOnNhd ℂ etaRect {s : ℂ | s.re > 1 / 2 ∧ s.re < 1} := by
    apply_rules [ DifferentiableOn.analyticOnNhd ]
    · refine' DifferentiableOn.mul _ _
      · refine' DifferentiableOn.sub _ _ <;> norm_num [ Complex.cpow_def ]
        exact DifferentiableOn.cexp
          ( DifferentiableOn.mul ( differentiableOn_const _ ) ( differentiableOn_id.const_sub _ ) )
      · intro s hs; exact differentiableAt_riemannZeta ( by aesop ) |>.differentiableWithinAt
    · exact isOpen_Ioo.preimage Complex.continuous_re
  exact (h_ana.differentiableOn.continuousOn).mono
    (fun z hz => ⟨hRlo z hz, hRhi z hz⟩)

/-- On the closure of a strip-internal rectangle, `etaEulerApprox P` never
    vanishes (it lies in `{1/2 < Re < 1}`). -/
lemma etaEulerApprox_ne_zero_closure (P : ℕ) (R : Rect)
    (hRlo : ∀ z ∈ R.closure, 1 / 2 < z.re) (hRhi : ∀ z ∈ R.closure, z.re < 1) :
    ∀ z ∈ R.closure, etaEulerApprox P z ≠ 0 :=
  fun z hz => etaEulerApprox_ne_zero P z (hRlo z hz) (hRhi z hz)

/-- `eulerB P · ω` is continuous on the closure of a strip-internal rectangle. -/
lemma eulerB_continuousOn (P : ℕ) (ω : Ωb) (R : Rect)
    (hRlo : ∀ z ∈ R.closure, 1 / 2 < z.re) (hRhi : ∀ z ∈ R.closure, z.re < 1) :
    ContinuousOn (fun s => eulerB P s ω) R.closure :=
  (eulerB_differentiableOn P ω R (fun z hz => by have := hRlo z hz; linarith)
    (etaEulerApprox_ne_zero_closure P R hRlo hRhi)).continuousOn

/-- `1 / eulerB P · ω` is continuous on the closure (since `eulerB` is nonzero). -/
lemma recipEulerB_continuousOn (P : ℕ) (ω : Ωb) (R : Rect)
    (hRlo : ∀ z ∈ R.closure, 1 / 2 < z.re) (hRhi : ∀ z ∈ R.closure, z.re < 1) :
    ContinuousOn (fun s => 1 / eulerB P s ω) R.closure :=
  (continuousOn_const).div (eulerB_continuousOn P ω R hRlo hRhi)
    (fun z _ => eulerB_ne_zero P z ω)

/-- `1 / etaRect` is continuous on the rectangle boundary, where `etaRect ≠ 0`
    (the only zero `s₀` is interior). -/
lemma recipEtaRect_continuousOn_boundary (R : Rect) (s₀ : ℂ)
    (hRlo : ∀ z ∈ R.closure, 1 / 2 < z.re) (hRhi : ∀ z ∈ R.closure, z.re < 1)
    (hs₀ : s₀ ∈ R.openInt) (hη : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0) :
    ContinuousOn (fun s => 1 / etaRect s) (R.closure \ R.openInt) :=
  (continuousOn_const).div
    ((etaRect_continuousOn R hRlo hRhi).mono (Set.diff_subset))
    (fun z hz => hη z hz.1 (fun h => hz.2 (h ▸ hs₀)))

/-- Reusable dominated-convergence step on a single edge. If the reciprocals
    `1 / eulerB (P k) · (w k)` converge uniformly to `1 / etaRect` on the boundary
    `K := R.closure \ R.openInt`, then for any continuous edge parametrization
    `g : ℝ → ℂ` whose image over `[a,b]` lies in `K`, the edge integrals converge.
    Proof: `intervalIntegral.tendsto_integral_filter_of_dominated_convergence`
    with dominator `t ↦ ‖1 / etaRect (g t)‖ + 1`; measurability and dominator
    integrability come from `recipEulerB_continuousOn` /
    `recipEtaRect_continuousOn_boundary` composed with `g`, the bound from the
    uniform convergence (`ε = 1`), and pointwise convergence from
    `TendstoUniformlyOn.tendsto_at`. -/
lemma edge_integral_tendsto (R : Rect) (s₀ : ℂ) (P : ℕ → ℕ) (w : ℕ → Ωb)
    (hRlo : ∀ z ∈ R.closure, 1 / 2 < z.re) (hRhi : ∀ z ∈ R.closure, z.re < 1)
    (hs₀ : s₀ ∈ R.openInt) (hη : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0)
    (h_recip : TendstoUniformlyOn (fun k z => 1 / eulerB (P k) z (w k))
      (fun z => 1 / etaRect z) atTop (R.closure \ R.openInt))
    (g : ℝ → ℂ) (hg : Continuous g) (a b : ℝ) (hab : a ≤ b)
    (hmaps : ∀ t ∈ Set.Icc a b, g t ∈ R.closure \ R.openInt) :
    Tendsto (fun k => ∫ t in a..b, 1 / eulerB (P k) (g t) (w k)) atTop
      (𝓝 (∫ t in a..b, 1 / etaRect (g t))) := by
  have huIoc : Set.uIoc a b = Set.Ioc a b := Set.uIoc_of_le hab
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t => ‖1 / etaRect (g t)‖ + 1) ?_ ?_ ?_ ?_
  · -- a.e.-strong-measurability of each integrand on `uIoc a b`
    refine Filter.Eventually.of_forall (fun k => ?_)
    rw [huIoc]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine (recipEulerB_continuousOn (P k) (w k) R hRlo hRhi).comp
      hg.continuousOn ?_
    intro t ht
    exact (hmaps t (Set.Ioc_subset_Icc_self ht)).1
  · -- dominating bound, from uniform convergence with `ε = 1`
    rw [Metric.tendstoUniformlyOn_iff] at h_recip
    filter_upwards [h_recip 1 zero_lt_one] with k hk
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [huIoc] at ht
    have hmem : g t ∈ R.closure \ R.openInt := hmaps t (Set.Ioc_subset_Icc_self ht)
    have hd := hk (g t) hmem
    rw [dist_eq_norm, norm_sub_rev] at hd
    have htri : ‖1 / eulerB (P k) (g t) (w k)‖ ≤
        ‖1 / eulerB (P k) (g t) (w k) - 1 / etaRect (g t)‖ + ‖1 / etaRect (g t)‖ := by
      have h := norm_add_le (1 / eulerB (P k) (g t) (w k) - 1 / etaRect (g t))
        (1 / etaRect (g t))
      simpa using h
    linarith
  · -- integrability of the dominator
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    refine ((recipEtaRect_continuousOn_boundary R s₀ hRlo hRhi hs₀ hη).comp
      hg.continuousOn (fun t ht => hmaps t ht)).norm.add continuousOn_const
  · -- pointwise convergence
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [huIoc] at ht
    exact h_recip.tendsto_at (hmaps t (Set.Ioc_subset_Icc_self ht))

/-- **[LB]** Along `P k → ∞` with coefficients `w k` drawn from shrinking
    edge-neighborhood events (`ε k ↓ 0`), the reciprocal boundary integrals of
    `1 / eulerB` converge to that of `1 / η`.

    Recipe (plan 1.4): `reciprocal_tendstoUniformlyOn_of_nonvanishing`
    (`EtaConvergenceExtended`) on the edges + dominated convergence on each edge
    (`edge_integral_tendsto`).
    This is the maintainer's "neighborhood converges to η, integrals converge."

    The convergence hypothesis `hconv` records that `w k` lies in the
    `ε k`-edge-neighborhood with `ε k ↓ 0` (the genuine content drawn from 1.3),
    making the statement honest rather than vacuous. The hypothesis `hRhi`
    (`Re < 1` on the closure) ensures `etaRect`/`eulerB` are continuous on the
    closure (the critical strip), which is what makes the boundary integrals and
    the reciprocal uniform limit well-defined. -/
lemma rcp_recipEulerB_tendsto_recipEta (R : Rect) (s₀ : ℂ)
    (P : ℕ → ℕ) (w : ℕ → Ωb)
    (hRlo : ∀ z ∈ R.closure, 1 / 2 < z.re) (hRhi : ∀ z ∈ R.closure, z.re < 1)
    (hs₀ : s₀ ∈ R.openInt)
    (hη : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0)
    (hconv : ∀ ε > 0, ∀ᶠ k in atTop,
      ∀ z ∈ R.closure \ R.openInt, ‖eulerB (P k) (z : ℂ) (w k) - etaRect z‖ < ε) :
    Tendsto (fun k => R.boundaryIntegral (fun z => 1 / eulerB (P k) z (w k)))
      atTop (𝓝 (R.boundaryIntegral (fun z => 1 / etaRect z))) := by
  -- reciprocal uniform convergence on the boundary
  have h_recip : TendstoUniformlyOn (fun k z => 1 / eulerB (P k) z (w k))
      (fun z => 1 / etaRect z) atTop (R.closure \ R.openInt) := by
    have h_unif : TendstoUniformlyOn (fun k z => eulerB (P k) z (w k)) etaRect atTop
        (R.closure \ R.openInt) := by
      rw [Metric.tendstoUniformlyOn_iff]
      simpa only [dist_eq_norm', norm_sub_rev] using hconv
    have hK : IsCompact (R.closure \ R.openInt) := by
      refine R.isCompact_closure.diff ?_
      exact (isOpen_lt continuous_const Complex.continuous_re).inter <|
        (isOpen_lt Complex.continuous_re continuous_const).inter <|
        (isOpen_lt continuous_const Complex.continuous_im).inter <|
        (isOpen_lt Complex.continuous_im continuous_const)
    exact reciprocal_tendstoUniformlyOn_of_nonvanishing _ hK _ _ h_unif
      ((etaRect_continuousOn R hRlo hRhi).mono Set.diff_subset)
      (fun z hz => hη z hz.1 (fun h => hz.2 (h ▸ hs₀)))
  -- a uniform helper to build each edge membership
  have hsimp : ∀ (x y : ℝ), ((x : ℂ) + (y : ℂ) * I).re = x ∧ ((x : ℂ) + (y : ℂ) * I).im = y := by
    intro x y; constructor <;> simp
  have hbot : ∀ t ∈ Set.Icc R.x_lo R.x_hi, ((t : ℂ) + R.y_lo * I) ∈ R.closure \ R.openInt := by
    intro t ht
    obtain ⟨h1, h2⟩ := ht
    obtain ⟨hre, him⟩ := hsimp t R.y_lo
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hre]; exact h1
    · rw [hre]; exact h2
    · rw [him]
    · rw [him]; exact R.hy.le
    · rw [Rect.openInt]; rintro ⟨_, _, h, _⟩; rw [him] at h; exact lt_irrefl _ h
  have htop : ∀ t ∈ Set.Icc R.x_lo R.x_hi, ((t : ℂ) + R.y_hi * I) ∈ R.closure \ R.openInt := by
    intro t ht
    obtain ⟨h1, h2⟩ := ht
    obtain ⟨hre, him⟩ := hsimp t R.y_hi
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hre]; exact h1
    · rw [hre]; exact h2
    · rw [him]; exact R.hy.le
    · rw [him]
    · rw [Rect.openInt]; rintro ⟨_, _, _, h⟩; rw [him] at h; exact lt_irrefl _ h
  have hright : ∀ t ∈ Set.Icc R.y_lo R.y_hi, ((R.x_hi : ℂ) + t * I) ∈ R.closure \ R.openInt := by
    intro t ht
    obtain ⟨h1, h2⟩ := ht
    obtain ⟨hre, him⟩ := hsimp R.x_hi t
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hre]; exact R.hx.le
    · rw [hre]
    · rw [him]; exact h1
    · rw [him]; exact h2
    · rw [Rect.openInt]; rintro ⟨_, h, _, _⟩; rw [hre] at h; exact lt_irrefl _ h
  have hleft : ∀ t ∈ Set.Icc R.y_lo R.y_hi, ((R.x_lo : ℂ) + t * I) ∈ R.closure \ R.openInt := by
    intro t ht
    obtain ⟨h1, h2⟩ := ht
    obtain ⟨hre, him⟩ := hsimp R.x_lo t
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hre]
    · rw [hre]; exact R.hx.le
    · rw [him]; exact h1
    · rw [him]; exact h2
    · rw [Rect.openInt]; rintro ⟨h, _, _, _⟩; rw [hre] at h; exact lt_irrefl _ h
  unfold Rect.boundaryIntegral
  refine Filter.Tendsto.sub (Filter.Tendsto.add (Filter.Tendsto.sub ?_ ?_)
    (Filter.Tendsto.const_smul ?_ I)) (Filter.Tendsto.const_smul ?_ I)
  · exact edge_integral_tendsto R s₀ P w hRlo hRhi hs₀ hη h_recip
      (fun t => (t : ℂ) + R.y_lo * I) (by fun_prop) R.x_lo R.x_hi R.hx.le hbot
  · exact edge_integral_tendsto R s₀ P w hRlo hRhi hs₀ hη h_recip
      (fun t => (t : ℂ) + R.y_hi * I) (by fun_prop) R.x_lo R.x_hi R.hx.le htop
  · exact edge_integral_tendsto R s₀ P w hRlo hRhi hs₀ hη h_recip
      (fun t => (R.x_hi : ℂ) + t * I) (by fun_prop) R.y_lo R.y_hi R.hy.le hright
  · exact edge_integral_tendsto R s₀ P w hRlo hRhi hs₀ hη h_recip
      (fun t => (R.x_lo : ℂ) + t * I) (by fun_prop) R.y_lo R.y_hi R.hy.le hleft

/-! ## Phase 2.1 — The rcp-zero predicate

"`η` has a zero at `s₀` in the regular-conditional-probability sense": conditioned
on edge-closeness to `η`, the conditional law of the interior value charges every
neighborhood of `0` even in the `ε → 0` limit. We phrase this concretely in terms
of `priorBall` masses of the joint events (positive conditional mass near `0`
persisting as `ε ↓ 0`), which is a stable `Prop` and avoids the kernel typeclass
overhead while capturing exactly the kernel-level meaning of `rcpKernel`.

**Two forms (2026-06-19 maintainer refinement).** The honest, substantive object
is the **limit / eventual-`k`** form `rcpZeroAt` below: for every radius `r > 0`
the joint event keeps positive `priorBall` mass *for all sufficiently large `k`*
(as the cutoff `P k → ∞`, neighborhood size `ε k ↓ 0`). The earlier `∀ k` form
(kept as `rcpZeroAtAll`) is a **placeholder**: because it also quantifies over the
fixed first cutoff `k = 0`, where `eulerB (P 0) s₀ ·` is a finite product bounded
away from `0` on the prior support, that event is null and `rcpZeroAtAll` is
*unconditionally false* (`not_rcpZeroAtAll`), regardless of whether `η(s₀) = 0`.
The `∀ k` form therefore loads *all* content onto the bridge; the eventual-`k`
form is the one that genuinely detects a strip zero. -/

/-- **[LB, placeholder]** The `∀ k` (joint-mass at *every* cutoff) form. This is
    the trivial placeholder: it is unconditionally false (`not_rcpZeroAtAll`) via
    the `k = 0` finite product, so it carries no analytic content. -/
def rcpZeroAtAll (P : ℕ → ℕ) (R : Rect) (s₀ : ℂ) : Prop :=
  ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k) ∧ Tendsto ε atTop (𝓝 0) ∧
    ∀ r > 0, ∀ k,
      0 < priorBall {ω | (∀ z ∈ R.closure \ R.openInt,
            ‖eulerB (P k) (z : ℂ) ω - etaRect z‖ < ε k) ∧ ‖eulerB (P k) s₀ ω‖ < r}

/-- **[LB, definition — the substantive limit form]** The rcp-zero predicate at
    `s₀` over a cutoff schedule `P`. There is a schedule `ε k ↓ 0` of edge
    tolerances along which, for every radius `r > 0`, the joint event "edges within
    `ε k` of `η`" **and** "interior value within `r` of `0`" keeps positive
    `priorBall` mass **for all sufficiently large `k`** — i.e. the conditional mass
    near `0` does not vanish in the neighborhood (`P k → ∞`, `ε k ↓ 0`) limit. -/
def rcpZeroAt (P : ℕ → ℕ) (R : Rect) (s₀ : ℂ) : Prop :=
  ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k) ∧ Tendsto ε atTop (𝓝 0) ∧
    ∀ r > 0, ∀ᶠ k in atTop,
      0 < priorBall {ω | (∀ z ∈ R.closure \ R.openInt,
            ‖eulerB (P k) (z : ℂ) ω - etaRect z‖ < ε k) ∧ ‖eulerB (P k) s₀ ω‖ < r}

/-! ## Phase 2.2 — rcp non-detectability of a strip zero -/

/-- **[placeholder, proved]** The `∀ k` placeholder form `rcpZeroAtAll` has no
    rcp-zero, **unconditionally** — by selecting the fixed cutoff `k = 0`, where the
    finite product `eulerB (P 0) s₀ ·` is bounded away from `0` on the prior support
    (`priorBall_ball`), so the joint event with `‖eulerB (P 0) s₀ ω‖ < r` is
    `priorBall`-null for small `r`. This needs **only boundedness**, which is exactly
    why it is trivial: it does not see whether `η(s₀) = 0`. -/
lemma not_rcpZeroAtAll (P : ℕ → ℕ) (R : Rect) (s₀ : ℂ) (hs₀ : s₀ ∈ R.openInt)
    (hRlo : ∀ z ∈ R.closure, 1 / 2 < z.re)
    (hAna : ∀ k, ∀ z ∈ R.closure, etaEulerApprox (P k) z ≠ 0) :
    ¬ rcpZeroAtAll P R s₀ := by
  contrapose! hAna; simp_all +decide [ rcpZeroAtAll ] ;
  obtain ⟨ ε, hε_pos, hε_tendsto, hε ⟩ := hAna; have := hε ( 1 / 2 ) ( by norm_num ) 0; simp_all +decide [ Complex.norm_exp ] ;
  -- Choose $r$ small enough such that the set where the real part of the exponential is less than $r$ has measure zero.
  obtain ⟨ r, hr_pos, hr_small ⟩ : ∃ r > 0, ∀ ω : Ωb, (∀ p, ‖Xb p ω‖ ≤ 1) → Real.exp ((bSum (P 0) ω s₀).re + (GaussianEuler.cCorr (P 0) s₀).re) ≥ r := by
    -- By definition of $bSum$, we know that $|bSum (P 0) ω s₀| ≤ B$ for some constant $B$.
    obtain ⟨ B, hB ⟩ : ∃ B : ℝ, ∀ ω : Ωb, (∀ p, ‖Xb p ω‖ ≤ 1) → ‖bSum (P 0) ω s₀‖ ≤ B := by
      use ∑ p ∈ (Finset.range (P 0 + 1)).filter Nat.Prime, ‖(p : ℂ) ^ (-s₀)‖; intro ω hω; exact (by
      exact le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun p hp => by simpa [ Xb ] using mul_le_mul_of_nonneg_right ( hω p ) ( by positivity ) ) |> le_trans <| by simp +decide [ bSum ] ;);
    use Real.exp ( -B + ( GaussianEuler.cCorr ( P 0 ) s₀ |> Complex.re ) ), Real.exp_pos _, fun ω hω => Real.exp_le_exp.mpr <| by linarith [ abs_le.mp ( Complex.abs_re_le_norm ( bSum ( P 0 ) ω s₀ ) ), hB ω hω ] ;
  have h_measure_zero : priorBall {ω : Ωb | ¬∀ p, ‖Xb p ω‖ ≤ 1} = 0 := by
    convert priorBall_ball using 1;
  have h_measure_zero : priorBall {ω : Ωb | Real.exp ((bSum (P 0) ω s₀).re + (GaussianEuler.cCorr (P 0) s₀).re) < r} = 0 := by
    exact MeasureTheory.measure_mono_null ( fun x hx => by contrapose! hx; aesop ) h_measure_zero;
  contrapose! hε;
  exact ⟨ r, hr_pos, 0, le_trans ( MeasureTheory.measure_mono <| fun x hx => hx.2 ) h_measure_zero.le ⟩

/-- **[LB — load-bearing, 2026-06-19]** Under the bounded prior, there is **no**
    rcp-zero (in the substantive *limit* form `rcpZeroAt`) in the strip interior.

    Unlike `not_rcpZeroAtAll`, the limit form cannot be discharged by selecting a
    fixed cutoff: `¬ rcpZeroAt` asserts that no positive joint mass accumulates at
    `s₀` for *large* `k` (`P k → ∞`), i.e. `η(s₀) ≠ 0` — uniformly in `s₀`, which is
    the Riemann Hypothesis itself. Its genuine content is the rcp limit `L ≠ 1`:
    the existence of a zero-free random Dirichlet series consistent with the
    (local) edge conditioning, which is **Bagchi/Voronin universality** (1981) on a
    local, non-`s₀`-enclosing neighborhood (so the maximum-modulus principle never
    pins `s₀`). This is one of the route's two deep, un-formalized analytic inputs
    (the other being Schoenfeld 1976 in the bridge). Left `sorry` with the recipe;
    **do not improvise** — it is not weaker than RH.
-/
lemma not_rcpZeroAt (P : ℕ → ℕ) (R : Rect) (s₀ : ℂ) (hs₀ : s₀ ∈ R.openInt)
    (hRlo : ∀ z ∈ R.closure, 1 / 2 < z.re)
    (hAna : ∀ k, ∀ z ∈ R.closure, etaEulerApprox (P k) z ≠ 0) :
    ¬ rcpZeroAt P R s₀ := by
  sorry

end RcpEuler
