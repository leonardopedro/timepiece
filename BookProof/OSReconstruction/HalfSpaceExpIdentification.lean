import Mathlib
import BookProof.OSReconstruction.HalfSpaceGenerator
import BookProof.OSReconstruction.HalfSpaceExponential

/-!
# Identifying the half-space semigroup with the exponential `e^{−τH}`

Plan: `cftproof.md`, **E3**.  `HalfSpaceGenerator` proves `hsGenerator_eq_neg` — the generator of
the half-space transfer semigroup is `−H` — **conditionally** on

`hflow : ∀ z, HasDerivWithinAt (fun τ => hsEvolCompletionFun Λ hT hinv τ z) (-(H z)) (Ioi 0) 0`,

the local form of `P(τ) = e^{−τH}`.  `HalfSpaceExponential` realises that shape for a bounded `H`
(`hsExpOp_hasDerivWithinAt_zero`), but for the *exponential* family, not for `hsEvolCompletionFun`;
the hypothesis therefore stayed an assumption about the abstract semigroup.

This module closes exactly that gap: **under `hflow`, the abstract semigroup *is* the exponential**,
`hsEvolCompletionFun Λ hT hinv τ z = hsExpOp Λ H τ z` for `τ ≥ 0`.  So `hflow` says nothing the
exponential does not already provide: it is *equivalent* to the identification
(`hsExpOp_iff_flow`), and the generator statement `hsGenerator_eq_neg` is then a statement about
`e^{−τH}` itself.

## The argument

The classical uniqueness proof, run so that only one-sided derivatives are ever needed:

* **`hsEvolCompletionFun_comp_neg`** — under `hflow` the semigroup commutes with `H`:
  `P(τ)(−H y) = −H(P(τ)y)`.  This is `A P(τ) = P(τ) A` for `A = −H`, with `A = −H` on *all* of
  `Hhalf` (the domain is `⊤` under `hflow`), written out with difference quotients.
* **`hasDerivWithinAt_hsEvol_flow`** — hence the orbit has right derivative `−H(P(τ)z)` at every
  `τ ≥ 0`, not merely `P(τ)(−Hz)` as the generator identity alone gives.
* The exponential's orbit has right derivative `−H(e^{−τH}z)` at every `τ` (proved in
  `HalfSpaceExponential`), so the difference `v(τ) = P(τ)z − e^{−τH}z` satisfies the linear ODE
  `v' = −H v` with `v(0) = 0`.  **Grönwall** (`norm_le_gronwallBound_of_norm_deriv_right_le`), with
  `δ = ε = 0`, gives `‖v‖ ≤ 0`.

## Contents

* `hsEvolCompletionFun_comp_neg`, `hasDerivWithinAt_hsEvol_flow` — the two ingredients above;
* `hsEvolCompletionFun_eq_hsExpOp` — **`P(τ)z = e^{−τH}z`** for `τ ≥ 0`;
* `hsGenerator_eq_neg_exp` — `hsGenerator_eq_neg` plus the identification in one statement: for
  every `z`, `z` is in the generator's domain, `A z = −H z`, **and** the semigroup at `z` is the
  exponential;
* `hsExpOp_iff_flow` — the equivalence: `hflow` holds iff the semigroup is the exponential.

## Boundary

`H` is bounded and `hflow` remains an assumption; what is proved is that it is the *right*
assumption — it determines the semigroup completely, as `e^{−τH}`, so it is not independent
information about the flow and cannot be satisfied by anything else.  `hflow` itself (the concrete
lattice translation evolving by `H`) is the physical input `hsGenerator_eq_neg` always carried;
nothing here derives it from the lattice data.
-/

noncomputable section

open BookProof.ReflectionPositivity
open Filter Set
open scoped Topology

namespace BookProof.OSReconstruction

variable {Λ : HalfSpaceState} {T : TimeTranslation}

section Flow

variable (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT)
variable (H : Hhalf Λ →L[ℝ] Hhalf Λ)
variable (hflow : ∀ z : Hhalf Λ,
  HasDerivWithinAt (fun τ : ℝ => hsEvolCompletionFun Λ hT hinv τ z) (-(H z)) (Ioi 0) 0)
include hT hinv H hflow

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search through `Hhalf`'s completion uniformity exceeds the default budget.
/-- **The semigroup commutes with `H`.**  With `A = −H` the generator, this is `A P(τ) = P(τ) A`,
proved with difference quotients: `P(τ)` is continuous, so it carries the quotient of `y` to the
quotient of `P(τ)y`, and both limits are generator values. -/
theorem hsEvolCompletionFun_comp_neg {τ : ℝ} (hτ : 0 ≤ τ) (y : Hhalf Λ) :
    hsEvolCompletionFun Λ hT hinv τ (-(H y))
      = -(H (hsEvolCompletionFun Λ hT hinv τ y)) := by
  have hqy : Tendsto (fun h : ℝ => hsDiffQuot Λ hT hinv h y) (𝓝[>] 0) (𝓝 (-(H y))) :=
    tendsto_hsDiffQuot_of_hasDerivWithinAt Λ hT hinv (hflow y)
  have hqPy : Tendsto (fun h : ℝ => hsDiffQuot Λ hT hinv h
      (hsEvolCompletionFun Λ hT hinv τ y)) (𝓝[>] 0)
      (𝓝 (-(H (hsEvolCompletionFun Λ hT hinv τ y)))) :=
    tendsto_hsDiffQuot_of_hasDerivWithinAt Λ hT hinv
      (hflow (hsEvolCompletionFun Λ hT hinv τ y))
  have hmain : Tendsto
      (fun h : ℝ => hsEvolCompletionFun Λ hT hinv τ (hsDiffQuot Λ hT hinv h y))
      (𝓝[>] 0) (𝓝 (hsEvolCompletionFun Λ hT hinv τ (-(H y)))) :=
    ((hsEvolCompletionFun Λ hT hinv τ).continuous.tendsto _).comp hqy
  have key : (fun h : ℝ => hsEvolCompletionFun Λ hT hinv τ (hsDiffQuot Λ hT hinv h y))
      =ᶠ[𝓝[>] (0 : ℝ)]
        fun h => hsDiffQuot Λ hT hinv h (hsEvolCompletionFun Λ hT hinv τ y) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : 0 ≤ h := le_of_lt hh
    rw [hsDiffQuot, hsDiffQuot, map_smul, map_sub,
      hsEvolCompletionFun_comp Λ hT hinv hτ hh0,
      hsEvolCompletionFun_comp Λ hT hinv hh0 hτ, show τ + h = h + τ from add_comm τ h]
  exact (tendsto_nhds_unique hqPy (hmain.congr' key)).symm

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search through `Hhalf`'s completion uniformity exceeds the default budget.
/-- **The orbit has right derivative `−H(P(τ)z)` at every `τ ≥ 0`.**  The exchange of `H` past the
semigroup is `hsEvolCompletionFun_comp_neg`. -/
theorem hasDerivWithinAt_hsEvol_flow {τ : ℝ} (hτ : 0 ≤ τ) (z : Hhalf Λ) :
    HasDerivWithinAt (fun s : ℝ => hsEvolCompletionFun Λ hT hinv s z)
      (-(H (hsEvolCompletionFun Λ hT hinv τ z))) (Ioi τ) τ := by
  have hq : Tendsto (fun h : ℝ => hsDiffQuot Λ hT hinv h z) (𝓝[>] 0) (𝓝 (-(H z))) :=
    tendsto_hsDiffQuot_of_hasDerivWithinAt Λ hT hinv (hflow z)
  have hmain : Tendsto
      (fun h : ℝ => hsEvolCompletionFun Λ hT hinv τ (hsDiffQuot Λ hT hinv h z))
      (𝓝[>] 0) (𝓝 (-(H (hsEvolCompletionFun Λ hT hinv τ z)))) := by
    have h := ((hsEvolCompletionFun Λ hT hinv τ).continuous.tendsto (-(H z))).comp hq
    rwa [hsEvolCompletionFun_comp_neg hT hinv H hflow hτ z] at h
  have hsub : Tendsto (fun y : ℝ => y - τ) (𝓝[Ioi τ] τ) (𝓝[>] (0 : ℝ)) := by
    have h1 : Tendsto (fun y : ℝ => y - τ) (𝓝[Ioi τ] τ) (𝓝 (0 : ℝ)) := by
      have hcont : Continuous fun y : ℝ => y - τ := continuous_id.sub continuous_const
      have h : Tendsto (fun y : ℝ => y - τ) (𝓝[Ioi τ] τ) (𝓝 (τ - τ)) :=
        hcont.continuousWithinAt
      rwa [sub_self] at h
    change Tendsto (fun y : ℝ => y - τ) (𝓝[Ioi τ] τ) (𝓝 (0 : ℝ) ⊓ 𝓟 (Ioi 0))
    rw [tendsto_inf, tendsto_principal]
    exact ⟨h1, by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact sub_pos.2 (mem_Ioi.mp hy)⟩
  rw [hasDerivWithinAt_iff_tendsto_slope,
    show Ioi τ \ {τ} = Ioi τ from diff_singleton_eq_self (by simp)]
  refine (hmain.comp hsub).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hpos : 0 < y - τ := sub_pos.2 (mem_Ioi.mp hy)
  have hcomp : hsEvolCompletionFun Λ hT hinv y z
      = hsEvolCompletionFun Λ hT hinv τ
          (hsEvolCompletionFun Λ hT hinv (y - τ) z) := by
    conv_lhs => rw [show y = τ + (y - τ) from by ring]
    rw [← hsEvolCompletionFun_comp Λ hT hinv hτ hpos.le]
  have hslope : slope (fun s : ℝ => hsEvolCompletionFun Λ hT hinv s z) τ y
      = (y - τ)⁻¹ • (hsEvolCompletionFun Λ hT hinv y z
        - hsEvolCompletionFun Λ hT hinv τ z) := by
    rw [slope_def_module]
  rw [hslope, hcomp, ← map_sub, ← map_smul]
  rfl

set_option maxHeartbeats 800000 in
-- Grönwall plus the completed-space instances exceeds the default budgets.
set_option synthInstance.maxHeartbeats 400000 in
/-- **The abstract semigroup is the exponential.**  Both orbits solve `v' = −H v` from `0`, so
Grönwall forces them to agree. -/
theorem hsEvolCompletionFun_eq_hsExpOp
    (hcont : ∀ F : Observable, F ∈ PositiveTimeAlgebra →
      Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    {τ : ℝ} (hτ : 0 ≤ τ) (z : Hhalf Λ) :
    hsEvolCompletionFun Λ hT hinv τ z = hsExpOp Λ H τ z := by
  set v : ℝ → Hhalf Λ :=
    fun s => hsEvolCompletionFun Λ hT hinv s z - hsExpOp Λ H s z with hv
  have hzero : v 0 = 0 := by
    simp only [hv, hsEvolCompletionFun_zero Λ hT hinv, hsExpOp_zero,
      ContinuousLinearMap.one_apply, sub_self]
  have hcontv : ContinuousOn v (Icc 0 τ) := by
    refine ContinuousOn.sub ?_ ?_
    · exact (continuousOn_hsEvolCompletionFun Λ hT hinv hcont z).mono fun x hx => hx.1
    · have hexp : Continuous fun s : ℝ => hsExpOp Λ H s z :=
        (continuous_hsExpOp H).clm_apply continuous_const
      exact hexp.continuousOn
  have hderiv : ∀ x ∈ Ico (0 : ℝ) τ, HasDerivWithinAt v (-(H (v x))) (Ici x) x := by
    intro x hx
    have hP := hasDerivWithinAt_hsEvol_flow hT hinv H hflow hx.1 z
    have hE := (hasDerivAt_hsExpOp_apply H x z).hasDerivWithinAt (s := Ioi x)
    have hval : -(H (hsEvolCompletionFun Λ hT hinv x z)) - -(H (hsExpOp Λ H x z))
        = -(H (v x)) := by
      rw [hv]
      simp only [map_sub]
      abel
    have hsub := hP.sub hE
    rw [hval] at hsub
    -- `Ici x` and `Ioi x` cut out the same punctured neighbourhood of `x`.
    rw [hasDerivWithinAt_iff_tendsto_slope] at hsub ⊢
    rw [show Ici x \ {x} = Ioi x from by
      ext y
      simp only [mem_diff, mem_Ici, mem_singleton_iff, mem_Ioi]
      exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, h.ne'⟩⟩]
    simpa [hv] using hsub
  have hbound : ∀ x ∈ Ico (0 : ℝ) τ, ‖-(H (v x))‖ ≤ ‖H‖ * ‖v x‖ + 0 := by
    intro x _
    have h := ContinuousLinearMap.le_opNorm H (v x)
    rw [norm_neg]
    simpa using h
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le (f := v)
    (f' := fun x => -(H (v x))) (δ := 0) (K := ‖H‖) (ε := 0) (a := 0) (b := τ)
    hcontv hderiv (by simp [hzero]) hbound
  have hgb : gronwallBound 0 ‖H‖ 0 (τ - 0) = 0 := by
    unfold gronwallBound
    split <;> simp
  have hfin : ‖v τ‖ ≤ 0 := by
    have h := hgron τ ⟨hτ, le_rfl⟩
    rw [hgb] at h
    simpa using h
  have hz : v τ = 0 := norm_eq_zero.mp (le_antisymm hfin (norm_nonneg _))
  exact sub_eq_zero.mp hz

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search through `Hhalf`'s completion uniformity exceeds the default budget.
/-- **`hsGenerator_eq_neg` together with the identification.**  For every `z`: `z` is in the
generator's domain, the generator is `−H z`, and the semigroup is `e^{−τH}` at `z`. -/
theorem hsGenerator_eq_neg_exp
    (hcont : ∀ F : Observable, F ∈ PositiveTimeAlgebra →
      Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F) (z : Hhalf Λ) :
    ∃ h : HsHasGen Λ hT hinv z,
      hsGenerator Λ hT hinv ⟨z, h⟩ = -H z ∧
        ∀ τ : ℝ, 0 ≤ τ → hsEvolCompletionFun Λ hT hinv τ z = hsExpOp Λ H τ z :=
  ⟨hsHasGen_of_hasDerivWithinAt Λ hT hinv (hflow z),
    hsGenerator_apply_eq_of_tendsto Λ hT hinv _
      (tendsto_hsDiffQuot_of_hasDerivWithinAt Λ hT hinv (hflow z)),
    fun _ hτ => hsEvolCompletionFun_eq_hsExpOp hT hinv H hflow hcont hτ z⟩

end Flow

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search through `Hhalf`'s completion uniformity exceeds the default budget.
/-- **`hflow` is exactly the identification.**  The generator hypothesis of `hsGenerator_eq_neg`
holds iff the abstract semigroup is the exponential at all nonnegative times; it therefore
determines the flow completely and is not independent information about it. -/
theorem hsExpOp_iff_flow (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) (H : Hhalf Λ →L[ℝ] Hhalf Λ)
    (hcont : ∀ F : Observable, F ∈ PositiveTimeAlgebra →
      Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F) :
    (∀ z : Hhalf Λ, HasDerivWithinAt
        (fun τ : ℝ => hsEvolCompletionFun Λ hT hinv τ z) (-(H z)) (Ioi 0) 0) ↔
      ∀ (τ : ℝ), 0 ≤ τ → ∀ z : Hhalf Λ,
        hsEvolCompletionFun Λ hT hinv τ z = hsExpOp Λ H τ z := by
  constructor
  · intro hfl τ hτ z
    exact hsEvolCompletionFun_eq_hsExpOp hT hinv H hfl hcont hτ z
  · intro hid z
    have h := (hasDerivAt_hsExpOp_apply H 0 z).hasDerivWithinAt (s := Ioi 0)
    have h' : HasDerivWithinAt (fun τ : ℝ => hsExpOp Λ H τ z) (-(H z)) (Ioi 0) 0 := by
      simpa [hsExpOp_zero, ContinuousLinearMap.one_apply] using h
    refine h'.congr ?_ ?_
    · intro τ hτ
      exact hid τ (le_of_lt hτ) z
    · exact hid 0 le_rfl z

end BookProof.OSReconstruction
