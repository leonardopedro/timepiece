import Mathlib
import BookProof.OSReconstruction.HalfSpaceHilbert

/-!
# The exponential `e^{−τH}` on the half-space carrier

Plan: `cftproof.md`, **E3** — the execution table lists "the exponential `e^{−τH}`" as the missing
concrete input of the reconstruction, and `HalfSpaceGenerator` can only *identify* a generator
conditionally on it: `hsGenerator_eq_neg` assumes

`∀ z, HasDerivWithinAt (fun τ => hsEvolCompletionFun Λ hT hinv τ z) (-(H z)) (Ioi 0) 0`,

the local form of `P(τ) = e^{−τH}`.  This module constructs that exponential for a **bounded**
Hamiltonian `H : Hhalf Λ →L[ℝ] Hhalf Λ` and proves, for the family itself, every property the plan
asks of `P`: `P(0) = I`, `P(s+t) = P(s)P(t)`, `P(τ)* = P(τ)`, contractivity for a nonnegative `H`,
strong continuity at `0⁺`, and the generator statement at `0⁺` in exactly the shape
`hsGenerator_eq_neg` consumes.  So that hypothesis is no longer vacuous: it holds for a genuine
symmetric contraction semigroup.

## Contents

* `hsExpOp` — the family `exp(τ • −H)`, `NormedSpace.exp` applied to the bounded operator `−τH`;
* `hsExpOp_apply`, `hsExpOp_zero` — its value and `P(0) = I`;
* `hsExpOp_add` — **`P(s+t) = P(s)P(t)`**, from `exp_add_of_commute_of_mem_ball` and the fact that
  two scalar multiples of `−H` commute;
* `hsExpOp_isSelfAdjoint` — **`P(τ)* = P(τ)`** whenever `H` is self-adjoint (`NormedSpace.star_exp`
  and `star (τ • −H) = τ • −H`);
* `hasDerivAt_hsExpOp` — the operator-level derivative `P'(τ) = P(τ) · (−H)`;
* `hasDerivAt_hsExpOp_apply`, `hsExpOp_hasDerivWithinAt_zero` — the orbit `τ ↦ P(τ) z` has
  derivative `−H (P(τ) z)` at every `τ`, hence `−H z` at `0⁺`: the `hflow` hypothesis of
  `hsGenerator_eq_neg`, discharged for this family;
* `norm_hsExpOp_antitone`, `norm_hsExpOp_le` — **contractivity for `τ ≥ 0`** when the quadratic form
  of `H` is nonnegative: `‖P(τ) z‖ ≤ ‖z‖`.  The proof is the derivative test,
  `d/dτ ‖P(τ) z‖² = −2 ⟪H (P(τ) z), P(τ) z⟫ ≤ 0`, so `‖P(·) z‖` is antitone;
* `tendsto_hsExpOp_zero` — **strong continuity at `0⁺`**.

Every declaration below is wrapped in `set_option synthInstance.maxHeartbeats 400000 in`: the
algebraic structure of `Hhalf Λ →L[ℝ] Hhalf Λ` is inherited from `Hhalf Λ = Completion (HsSpace Λ)`,
and synthesising it (a `Ring`, an `HSMul ℝ`, a `T2Space`, …) exceeds the default instance-search
budget, as it does in `HalfSpaceComplex`.

## Boundary

* `H` is a **bounded** operator.  The exponential of an unbounded (densely defined, self-adjoint)
  Hamiltonian is not constructed here; that is the spectral-theorem job the multiplier model
  (`MultiplierSelfAdjoint`) does for its own `MulModel`, and E3's remaining infinite-volume work.
* The family is *not* identified with the abstract half-space semigroup `hsEvolCompletion` of
  `HalfSpaceHilbert`.  Doing so needs uniqueness of solutions of the linear ODE `ẋ = −H x` on the
  completion (a Grönwall argument) **plus** the identification of the abstract `TimeTranslation`
  with the concrete lattice translation; neither is in the corpus.  What is proved is that the
  exponential exists, is a symmetric strongly continuous contraction semigroup, and has generator
  `−H` — the input `hsGenerator_eq_neg` names.
* Contractivity assumes `⟪H z, z⟫ ≥ 0` rather than `H` self-adjoint and nonnegative; that quadratic
  form condition is what the derivative test uses, and for a self-adjoint `H` it *is* the statement
  `H ≥ 0`.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace BookProof.OSReconstruction

variable {Λ : HalfSpaceState}

/-! ## The family -/

set_option synthInstance.maxHeartbeats 400000 in
-- The CLM algebra over the completion `Hhalf Λ` is expensive to synthesise (see the module docs).
/-- **The exponential `e^{−τH}`** of a bounded operator on the half-space carrier, as a bounded
operator: `exp(−τ • H)`.  Multiplicativity of the family (`hsExpOp_add`) holds because all its
elements are functions of one operator. -/
def hsExpOp (Λ : HalfSpaceState) (H : Hhalf Λ →L[ℝ] Hhalf Λ) (τ : ℝ) :
    Hhalf Λ →L[ℝ] Hhalf Λ :=
  NormedSpace.exp (τ • (-H))

set_option synthInstance.maxHeartbeats 400000 in
-- Same reason: the statement mentions the CLM algebra and the operator norm on it.
/-- The exponential acts by applying `exp(−τ • H)` pointwise. -/
theorem hsExpOp_apply (H : Hhalf Λ →L[ℝ] Hhalf Λ) (τ : ℝ) (z : Hhalf Λ) :
    hsExpOp Λ H τ z = NormedSpace.exp (τ • (-H)) z :=
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- Same reason: `1` and `0` are the CLM algebra's unit and zero.
/-- **`P(0) = I`.** -/
theorem hsExpOp_zero (H : Hhalf Λ →L[ℝ] Hhalf Λ) :
    hsExpOp Λ H 0 = 1 := by
  simp [hsExpOp]

/-! ## The semigroup law -/

set_option synthInstance.maxHeartbeats 400000 in
-- Same reason: `Commute`, `*` and `•` are read in the CLM algebra.
/-- Two scalar multiples of the same operator commute, so `exp` is multiplicative on them. -/
theorem commute_smul_neg (H : Hhalf Λ →L[ℝ] Hhalf Λ) (s t : ℝ) :
    Commute (s • (-H)) (t • (-H)) := by
  rw [Commute, SemiconjBy]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm]

set_option synthInstance.maxHeartbeats 400000 in
-- Same reason, and the `expSeries` radius is stated in terms of the same algebra.
/-- **`P(s + t) = P(s) P(t)`.** -/
theorem hsExpOp_add (H : Hhalf Λ →L[ℝ] Hhalf Λ) (s t : ℝ) :
    hsExpOp Λ H (s + t) = hsExpOp Λ H s * hsExpOp Λ H t := by
  have hx : s • (-H) ∈
      Metric.eball (0 : Hhalf Λ →L[ℝ] Hhalf Λ)
        (NormedSpace.expSeries ℝ (Hhalf Λ →L[ℝ] Hhalf Λ)).radius :=
    (NormedSpace.expSeries_radius_eq_top ℝ (Hhalf Λ →L[ℝ] Hhalf Λ)).symm ▸ edist_lt_top _ _
  have hy : t • (-H) ∈
      Metric.eball (0 : Hhalf Λ →L[ℝ] Hhalf Λ)
        (NormedSpace.expSeries ℝ (Hhalf Λ →L[ℝ] Hhalf Λ)).radius :=
    (NormedSpace.expSeries_radius_eq_top ℝ (Hhalf Λ →L[ℝ] Hhalf Λ)).symm ▸ edist_lt_top _ _
  rw [hsExpOp, hsExpOp, hsExpOp, add_smul]
  exact NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) (commute_smul_neg H s t) hx hy

/-! ## Symmetry -/

set_option synthInstance.maxHeartbeats 400000 in
-- Same reason: `star` and `IsSelfAdjoint` are those of the CLM algebra, plus `T2Space` for `exp`.
/-- **`P(τ)* = P(τ)`** for a self-adjoint `H`: `exp` commutes with `star`, and `τ • −H` is fixed by
the star operation. -/
theorem hsExpOp_isSelfAdjoint (H : Hhalf Λ →L[ℝ] Hhalf Λ) (hH : IsSelfAdjoint H) (τ : ℝ) :
    IsSelfAdjoint (hsExpOp Λ H τ) := by
  rw [IsSelfAdjoint, hsExpOp, NormedSpace.star_exp, star_smul, star_neg, hH.star_eq,
    star_trivial]

/-! ## The flow equation -/

set_option synthInstance.maxHeartbeats 400000 in
-- Same reason: the derivative is taken in the normed algebra of bounded operators.
/-- **The operator-level derivative `P'(τ) = P(τ) · (−H)`.** -/
theorem hasDerivAt_hsExpOp (H : Hhalf Λ →L[ℝ] Hhalf Λ) (τ : ℝ) :
    HasDerivAt (hsExpOp Λ H) (hsExpOp Λ H τ * (-H)) τ := by
  simpa only [hsExpOp] using hasDerivAt_exp_smul_const (-H) τ

set_option synthInstance.maxHeartbeats 400000 in
-- Same reason: `clm_apply` and `−H` are read in the CLM algebra.
/-- **The orbit `τ ↦ P(τ) z` solves `ẋ = −H x`**: its derivative at `τ` is `−H (P(τ) z)`. -/
theorem hasDerivAt_hsExpOp_apply (H : Hhalf Λ →L[ℝ] Hhalf Λ) (τ : ℝ) (z : Hhalf Λ) :
    HasDerivAt (fun u : ℝ => hsExpOp Λ H u z) (-(H (hsExpOp Λ H τ z))) τ := by
  simpa [hsExpOp] using
    (hasDerivAt_exp_smul_const' (-H) τ).clm_apply (hasDerivAt_const (x := τ) z)

set_option synthInstance.maxHeartbeats 400000 in
-- Same reason: the statement contains the previous derivative and the CLM unit.
/-- **The generator statement at `0⁺`**: `d/dτ P(τ) z = −H z` at `0` from the right, with no
hypothesis on `z`.  This is literally the `hflow` hypothesis of `hsGenerator_eq_neg`. -/
theorem hsExpOp_hasDerivWithinAt_zero (H : Hhalf Λ →L[ℝ] Hhalf Λ) (z : Hhalf Λ) :
    HasDerivWithinAt (fun τ : ℝ => hsExpOp Λ H τ z) (-(H z)) (Ioi 0) 0 := by
  have h := hasDerivAt_hsExpOp_apply H 0 z
  simpa [hsExpOp_zero, ContinuousLinearMap.one_apply] using h.hasDerivWithinAt

/-! ## Contractivity -/

set_option synthInstance.maxHeartbeats 400000 in
-- Same reason: inner products on `Hhalf Λ` and the CLM applications of `H` are searched here.
/-- `τ ↦ ‖P(τ) z‖` is **antitone** when the quadratic form of `H` is nonnegative.  The derivative of
`‖P(τ) z‖² = ⟪P(τ) z, P(τ) z⟫` is `2 ⟪P(τ) z, −H (P(τ) z)⟫ = −2 ⟪H (P(τ) z), P(τ) z⟫ ≤ 0`, so the
derivative test gives monotonicity, and `‖·‖ ≥ 0` turns `‖·‖²` monotonicity into `‖·‖`
monotonicity. -/
theorem norm_hsExpOp_antitone (H : Hhalf Λ →L[ℝ] Hhalf Λ)
    (hpos : ∀ z : Hhalf Λ, 0 ≤ inner ℝ (H z) z) (z : Hhalf Λ) :
    Antitone fun τ : ℝ => ‖hsExpOp Λ H τ z‖ := by
  have hF : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => inner ℝ (hsExpOp Λ H s z) (hsExpOp Λ H s z))
        (2 * (-inner ℝ (H (hsExpOp Λ H t z)) (hsExpOp Λ H t z))) t := by
    intro t
    have h1 := hasDerivAt_hsExpOp_apply H t z
    have h2 := HasDerivAt.inner (𝕜 := ℝ) h1 h1
    have h3 : inner ℝ (hsExpOp Λ H t z) (-(H (hsExpOp Λ H t z)))
        + inner ℝ (-(H (hsExpOp Λ H t z))) (hsExpOp Λ H t z)
        = 2 * (-inner ℝ (H (hsExpOp Λ H t z)) (hsExpOp Λ H t z)) := by
      rw [real_inner_comm (-(H (hsExpOp Λ H t z))) (hsExpOp Λ H t z)]
      simp only [inner_neg_left]
      ring
    rw [h3] at h2
    exact h2
  have hderiv : ∀ t : ℝ,
      deriv (fun s : ℝ => inner ℝ (hsExpOp Λ H s z) (hsExpOp Λ H s z)) t ≤ 0 := by
    intro t
    rw [(hF t).deriv]
    have hp := hpos (hsExpOp Λ H t z)
    linarith
  have hdiff : Differentiable ℝ fun s : ℝ => inner ℝ (hsExpOp Λ H s z) (hsExpOp Λ H s z) :=
    fun t => (hF t).differentiableAt
  have hinner : Antitone fun s : ℝ => inner ℝ (hsExpOp Λ H s z) (hsExpOp Λ H s z) :=
    antitone_of_deriv_nonpos hdiff hderiv
  intro a b hab
  have h := hinner hab
  simp only [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (hsExpOp Λ H a z)]

set_option synthInstance.maxHeartbeats 400000 in
-- Same reason: the statement evaluates the family at `τ = 0` and `τ = a`.
/-- **Contractivity for nonnegative time**: `‖P(τ) z‖ ≤ ‖z‖` for `τ ≥ 0`, i.e. `e^{−τH}` is a
contraction when `H ≥ 0` in quadratic form. -/
theorem norm_hsExpOp_le (H : Hhalf Λ →L[ℝ] Hhalf Λ)
    (hpos : ∀ z : Hhalf Λ, 0 ≤ inner ℝ (H z) z) {τ : ℝ} (hτ : 0 ≤ τ) (z : Hhalf Λ) :
    ‖hsExpOp Λ H τ z‖ ≤ ‖z‖ := by
  have h := norm_hsExpOp_antitone H hpos z (a := (0 : ℝ)) (b := τ) hτ
  simpa [hsExpOp_zero, ContinuousLinearMap.one_apply] using h

/-! ## Strong continuity -/

set_option synthInstance.maxHeartbeats 400000 in
-- Same reason: continuity of a CLM-valued function is read in the operator norm.
/-- The family is continuous in `τ`: every orbit has a derivative at every time. -/
theorem continuous_hsExpOp (H : Hhalf Λ →L[ℝ] Hhalf Λ) : Continuous (hsExpOp Λ H) :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_hsExpOp H u).differentiableAt.continuousAt

set_option synthInstance.maxHeartbeats 400000 in
-- Same reason: the evaluation map `CLM → z` and the CLM unit occur in the statement.
/-- **Strong continuity at `0⁺`**: `P(τ) z → z` as `τ ↓ 0`. -/
theorem tendsto_hsExpOp_zero (H : Hhalf Λ →L[ℝ] Hhalf Λ) (z : Hhalf Λ) :
    Tendsto (fun τ : ℝ => hsExpOp Λ H τ z) (𝓝[>] 0) (𝓝 z) := by
  have h1 : Tendsto (fun u : ℝ => hsExpOp Λ H u) (𝓝[>] 0) (𝓝 (hsExpOp Λ H 0)) :=
    continuous_hsExpOp H |>.continuousAt |>.mono_left nhdsWithin_le_nhds
  have h2 := (ContinuousLinearMap.apply ℝ (Hhalf Λ) z).continuous.continuousAt.tendsto.comp h1
  simpa [hsExpOp_zero, ContinuousLinearMap.one_apply] using h2

end BookProof.OSReconstruction
