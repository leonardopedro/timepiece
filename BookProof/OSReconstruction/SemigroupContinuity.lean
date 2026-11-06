import Mathlib
import BookProof.OSReconstruction.GeneratorClosed

/-!
# Strong continuity of the transfer semigroup from matrix elements alone

`OSReconstruction.HilbertSpace` derives strong continuity of `P(τ)` from continuity of the
two-point function, but its proof routes through `osBilin_evol_self`: contractivity at `τ` *and* at
`−τ` makes `P(τ)` an isometry, and then `‖P(τ)x − x‖² = 2(⟨x,x⟩ − ⟨P(τ)x,x⟩)` is an equality.

That is the wrong hypothesis for a Euclidean transfer matrix.  The physical object is defined for
`τ ≥ 0`, where it is a contraction; `P(−τ)` is `e^{τH}`, unbounded.  This module removes the
dependence: contractivity at the single time being approached already gives the *inequality*

`‖P(τ)x − x‖² ≤ 2(⟨x,x⟩ − ⟨P(τ)x,x⟩)`  (`norm_physEvol_sub_sq_le`),

because `⟨P(τ)x, P(τ)x⟩ ≤ ⟨x,x⟩` suffices where the earlier proof used `=`.  The right-hand side
tends to `0` by matrix element continuity — the OS axiom — so

* `tendsto_norm_physEvol_sub_right` — `‖P(τ)x − x‖ → 0` as `τ → 0⁺`, on the dense subspace;
* `tendsto_physEvolCompletion_right` — `P(τ)z → z` as `τ → 0⁺`, for every `z ∈ ℋ`,

both along the *one-sided* filter `𝓝[>] 0`, using `hinv` only at nonnegative times.  The abstract
Hilbert-space fact behind the inequality is `norm_sub_sq_le_two_mul_sub_inner`, and
`tendsto_of_contractive_weak` is its general form: a contraction family with continuous matrix
elements is strongly continuous, with no isometry and no group structure.

Consequently the strong-continuity input of the generator survives the change of hypothesis from
"contractive for all `τ`" to "contractive for `τ ≥ 0`".  Together with `P(0) = 1`,
`P(s + t) = P(s) P(t)` and `‖P(τ)‖ ≤ 1` (`physEvolCompletion_zero`, `physEvolCompletion_add`,
`physEvolCompletion_contractive`, all valid at nonnegative times), this is the transfer *semigroup*
phase 4.2 needs.

## Boundary

This is the continuity half of the semi-group rebuild, not the whole of it.  Making the hypothesis
forward-only throughout also requires:

* `physEvolCompletion` to consume a proof `0 ≤ τ`, because `LinearMap.extendOfNorm` needs the norm
  bound `‖physEvol τ‖ ≤ 1`, which is exactly what fails for `τ < 0`;
* the generator's difference quotient to be one-sided (`𝓝[>] 0`) rather than punctured at `0`;
* the closedness argument of `GeneratorClosed` to be re-derived.  Its integral representation
  differentiates the orbit at interior times, and a one-sided semigroup has no left derivative
  there (`P(t + h) = P(t)P(h)` needs `h ≥ 0`), so `hasDerivAt_physEvol` does not survive verbatim;
  the standard replacement is the resolvent/Laplace representation rather than the fundamental
  theorem of calculus.

Until that is done, `generator_isClosed` and `generator_isSymmetric` remain stated under the group
hypothesis, and the degeneracy of `TransferSelfAdjoint` remains a property of *that* hypothesis.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity
open Filter
open scoped Topology
open RealInnerProductSpace

noncomputable section

/-! ## The abstract contraction bound -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Contractivity gives the distance bound.**  For `‖T‖ ≤ 1`,
`‖T x − x‖² ≤ 2(⟨x,x⟩ − ⟨T x,x⟩)`; no isometry is involved, only `‖T x‖ ≤ ‖x‖`. -/
theorem norm_sub_sq_le_two_mul_sub_inner (T : E →L[ℝ] E) (hT : ‖T‖ ≤ 1) (x : E) :
    ‖T x - x‖ ^ 2 ≤ 2 * (⟪x, x⟫ - ⟪T x, x⟫) := by
  have hsq : ‖T x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have hle : ‖T x‖ ≤ ‖x‖ := by
      calc ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
        _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg x)
        _ = ‖x‖ := one_mul ‖x‖
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hxx : ⟪x, x⟫ = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  rw [norm_sub_sq_real]
  nlinarith [hsq, hxx]

/-- **A contractive family with continuous matrix elements is strongly continuous at the origin.**
This is the abstract content of the OS input: no isometry, no group law, and the filter is
arbitrary. -/
theorem tendsto_of_contractive_weak {l : Filter ℝ} (T : ℝ → E →L[ℝ] E)
    (hT : ∀ t, ‖T t‖ ≤ 1) (hweak : ∀ x : E, Tendsto (fun t => ⟪T t x, x⟫) l (𝓝 ⟪x, x⟫))
    (x : E) : Tendsto (fun t => T t x) l (𝓝 x) := by
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hlim : Tendsto (fun t => 2 * (⟪x, x⟫ - ⟪T t x, x⟫)) l (𝓝 0) := by
    have hsub : Tendsto (fun t => ⟪x, x⟫ - ⟪T t x, x⟫) l (𝓝 (⟪x, x⟫ - ⟪x, x⟫)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => ⟪x, x⟫) l (𝓝 ⟪x, x⟫)).sub (hweak x)
    simpa using hsub.const_mul 2
  have hev : ∀ᶠ t in l, 2 * (⟪x, x⟫ - ⟪T t x, x⟫) < ε ^ 2 :=
    hlim.eventually (isOpen_Iio.mem_nhds (by simpa using (show (0 : ℝ) < ε ^ 2 by nlinarith)))
  filter_upwards [hev] with t ht
  have hb := norm_sub_sq_le_two_mul_sub_inner (T t) (hT t) x
  have hnn : (0 : ℝ) ≤ ‖T t x - x‖ := norm_nonneg _
  have hlt : ‖T t x - x‖ < ε := by nlinarith
  simpa [Real.dist_eq, abs_of_nonneg hnn] using hlt

end Abstract

/-! ## The OS two-point function gives the contraction bound on `𝔄/𝔑` -/

/-- Contractivity of the evolution, read on the OS form: `⟨P(τ)x, P(τ)x⟩ ≤ ⟨x,x⟩`. -/
theorem physForm_evol_self_le (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (τ : ℝ) (x : PhysSpace Λ) :
    physForm Λ.ω (physEvol Λ T hinv τ x) (physEvol Λ T hinv τ x) ≤ physForm Λ.ω x x := by
  have h : ‖physEvol Λ T hinv τ x‖ ≤ ‖x‖ := physEvol_contractive Λ T hinv τ x
  have h1 : ‖physEvol Λ T hinv τ x‖ ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rwa [physNorm_eq, physNorm_eq, Real.sq_sqrt (physForm_self_nonneg Λ _),
    Real.sq_sqrt (physForm_self_nonneg Λ _)] at h1

/-- **The contraction bound** on the dense subspace: `‖P(τ)x − x‖²` is at most twice the drop in
the matrix element.  This is the inequality that replaces the isometry equality. -/
theorem norm_physEvol_sub_sq_le (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (τ : ℝ) (x : PhysSpace Λ) :
    ‖physEvol Λ T hinv τ x - x‖ ^ 2
      ≤ 2 * (physForm Λ.ω x x - physForm Λ.ω (physEvol Λ T hinv τ x) x) := by
  have hexp : ‖physEvol Λ T hinv τ x - x‖ ^ 2
      = physForm Λ.ω (physEvol Λ T hinv τ x - x) (physEvol Λ T hinv τ x - x) := by
    rw [physNorm_eq, Real.sq_sqrt (physForm_self_nonneg Λ _)]
  rw [hexp, physForm_sub_sub, physForm_symm Λ.ω x (physEvol Λ T hinv τ x)]
  have h := physForm_evol_self_le Λ T hinv τ x
  nlinarith

/-- **The distance to the evolved state vanishes at `0⁺`**, from matrix element continuity alone. -/
theorem tendsto_norm_physEvol_sub_right (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (hcont : ∀ F : Observable, Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    (x : PhysSpace Λ) :
    Tendsto (fun τ : ℝ => ‖physEvol Λ T hinv τ x - x‖) (𝓝[>] 0) (𝓝 0) := by
  have hme : Tendsto (fun τ : ℝ => physForm Λ.ω (physEvol Λ T hinv τ x) x) (𝓝[>] 0)
      (𝓝 (physForm Λ.ω x x)) := by
    have hc := continuous_physForm_physEvol Λ T hinv hcont x
    have h0 : physForm Λ.ω (physEvol Λ T hinv 0 x) x = physForm Λ.ω x x := by
      rw [physEvol_zero]
    have ht : Tendsto (fun τ : ℝ => physForm Λ.ω (physEvol Λ T hinv τ x) x) (𝓝 0)
        (𝓝 (physForm Λ.ω x x)) := by
      have := hc.tendsto 0
      rwa [h0] at this
    exact ht.mono_left nhdsWithin_le_nhds
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hlim : Tendsto (fun τ : ℝ =>
      2 * (physForm Λ.ω x x - physForm Λ.ω (physEvol Λ T hinv τ x) x)) (𝓝[>] 0) (𝓝 0) := by
    have hsub : Tendsto (fun τ : ℝ =>
        physForm Λ.ω x x - physForm Λ.ω (physEvol Λ T hinv τ x) x) (𝓝[>] 0)
        (𝓝 (physForm Λ.ω x x - physForm Λ.ω x x)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => physForm Λ.ω x x) (𝓝[>] (0 : ℝ))
        (𝓝 (physForm Λ.ω x x))).sub hme
    simpa using hsub.const_mul 2
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      2 * (physForm Λ.ω x x - physForm Λ.ω (physEvol Λ T hinv τ x) x) < ε ^ 2 :=
    hlim.eventually (isOpen_Iio.mem_nhds (by simpa using (show (0 : ℝ) < ε ^ 2 by nlinarith)))
  filter_upwards [hev] with τ hτ
  have hb := norm_physEvol_sub_sq_le Λ T hinv τ x
  have hnn : (0 : ℝ) ≤ ‖physEvol Λ T hinv τ x - x‖ := norm_nonneg _
  have hlt : ‖physEvol Λ T hinv τ x - x‖ < ε := by nlinarith
  simpa [Real.dist_eq, abs_of_nonneg hnn] using hlt

/-! ## Strong continuity on `ℋ` -/

/-- **Strong continuity of the transfer semigroup at `0⁺`**, from matrix element continuity.

Approximate `z` by a vector of the dense subspace, use contractivity for the two outer terms and
`tendsto_norm_physEvol_sub_right` for the middle one.  Only `hinv` at nonnegative times is used, so
this survives restricting the hypothesis to `τ ≥ 0`. -/
theorem tendsto_physEvolCompletion_right (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (hcont : ∀ F : Observable, Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    (z : Hphys Λ) :
    Tendsto (fun τ : ℝ => physEvolCompletion Λ T hinv τ z) (𝓝[>] 0) (𝓝 z) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨x, hzx⟩ := (denseRange_physCoe Λ).exists_dist_lt z (show (0 : ℝ) < ε / 4 by linarith)
  have hnorm := tendsto_norm_physEvol_sub_right Λ T hinv hcont x
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ‖physEvol Λ T hinv τ x - x‖ < ε / 2 := by
    have h := Metric.tendsto_nhds.mp hnorm (ε / 2) (by linarith)
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using h
  filter_upwards [hev] with τ hτ
  have hmid : dist (physEvolCompletion Λ T hinv τ ((x : PhysSpace Λ) : Hphys Λ))
      ((x : PhysSpace Λ) : Hphys Λ) = ‖physEvol Λ T hinv τ x - x‖ := by
    rw [physEvolCompletion_coe, dist_eq_norm, ← UniformSpace.Completion.coe_sub,
      UniformSpace.Completion.norm_coe]
  have hout : dist (physEvolCompletion Λ T hinv τ z)
      (physEvolCompletion Λ T hinv τ ((x : PhysSpace Λ) : Hphys Λ))
      ≤ dist z ((x : PhysSpace Λ) : Hphys Λ) := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact physEvolCompletion_contractive Λ T hinv τ _
  have hfin : dist (physEvolCompletion Λ T hinv τ z) z
      ≤ dist z ((x : PhysSpace Λ) : Hphys Λ)
        + (‖physEvol Λ T hinv τ x - x‖ + dist ((x : PhysSpace Λ) : Hphys Λ) z) := by
    calc dist (physEvolCompletion Λ T hinv τ z) z
        ≤ dist (physEvolCompletion Λ T hinv τ z)
            (physEvolCompletion Λ T hinv τ ((x : PhysSpace Λ) : Hphys Λ))
          + dist (physEvolCompletion Λ T hinv τ ((x : PhysSpace Λ) : Hphys Λ)) z :=
          dist_triangle _ _ _
      _ ≤ dist z ((x : PhysSpace Λ) : Hphys Λ)
          + (dist (physEvolCompletion Λ T hinv τ ((x : PhysSpace Λ) : Hphys Λ))
              ((x : PhysSpace Λ) : Hphys Λ) + dist ((x : PhysSpace Λ) : Hphys Λ) z) := by
          have h2 := dist_triangle (physEvolCompletion Λ T hinv τ ((x : PhysSpace Λ) : Hphys Λ))
            ((x : PhysSpace Λ) : Hphys Λ) z
          linarith
      _ = _ := by rw [hmid]
  have hle : dist ((x : PhysSpace Λ) : Hphys Λ) z < ε / 4 := by
    rw [dist_comm]
    exact hzx
  linarith [hfin, hle, hτ]

end

end BookProof.OSReconstruction
