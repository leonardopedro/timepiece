import Mathlib
import BookProof.OSReconstruction.SemigroupContinuity

/-!
# The transfer semigroup at nonnegative Euclidean time

`OSReconstruction.HilbertSpace` builds `physEvol` / `physEvolCompletion` from a hypothesis
`hinv : ∀ τ, osBilin ω (T τ F) (T τ F) ≤ osBilin ω F F` quantified over **all** real `τ`.  That
is more than the Euclidean theory supplies: the transfer matrix is defined for `τ ≥ 0`, where it
is a contraction, and `P(−τ)` is `e^{τH}`, which is unbounded.  `SemigroupContinuity` already
derives strong continuity at `0⁺` from the one-sided hypothesis, and `SemigroupGenerator` builds
the forward-time generator and proves it closed.  What was still missing is the semigroup itself
on `τ ≥ 0`: the descended evolution, its extension to `ℋ`, and the algebraic laws.

This module supplies exactly that, with no negative time anywhere:

* `HinvRight` — contractivity stated only for `τ ≥ 0`;
* `radical_invariant_right` — the evolution preserves the radical of the OS form at nonnegative
  times (the same Cauchy–Schwarz argument as `radical_invariant`, using `hinv τ hτ`);
* `physEvolRight` — the evolution descended to `𝔄/𝔑`, taking `0 ≤ τ` as an argument.  Because a
  proof argument is awkward to carry through limits, the `τ`-dependent statements use
  `physEvolRightFun`, which is `physEvolRight` for `τ ≥ 0` and `0` otherwise
  (`physEvolRightFun_of_nonneg`); only the positive side is ever used.
* `physEvolCompletionRight` — the continuous extension to `ℋ` by `LinearMap.extendOfNorm`, which
  needs only `‖physEvolRight τ‖ ≤ 1`, hence only `τ ≥ 0`;
* `physEvolCompletionRight_zero`, `physEvolCompletionRight_add` — `P(0) = 1` and
  `P(s + t) = P(s) P(t)` for `s, t ≥ 0`, on `ℋ`;
* `physEvolCompletionRight_contractive` — `‖P(τ)‖ ≤ 1`;
* `tendsto_physEvolCompletionRightFun` — strong continuity at `0⁺`, from matrix element
  continuity, by the contraction inequality (no isometry).

## Boundary

`HinvRight` is strictly weaker than `hinv`, so the two-sided lemmas of `HilbertSpace` do not
follow from it -- and must not: `osBilin_evol_self`, `physForm_evol_self` and
`norm_physEvolCompletion_eq` all use the negative half, and the degeneracy of
`TransferSelfAdjoint` is a theorem about *that* hypothesis.  The results here are the ones that
survive, and they are the ones the Euclidean theory needs.  `physEvolCompletionRight_eq` records
that when the two-sided hypothesis happens to hold, the forward semigroup is the restriction of
the old one, so nothing is lost by working with the weaker hypothesis.

The generator side is not duplicated: `SemigroupGenerator` already defines `genDomainRight`,
`generatorRight` and proves `generatorRight_isClosed`, `generatorRight_inner_le_zero` and the a
priori resolvent bound.  Its definitions still take the two-sided `hinv` as a *type*, however:
`diffQuot` is phrased in terms of `physEvolCompletion`.  Re-phrasing `diffQuot` on
`physEvolCompletionRightFun` would be a change of the generator's definition, and the two agree
where both are defined (`physEvolCompletionRight_eq`), so the generator statements transfer
verbatim; this module does not restate them.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity
open Filter
open scoped Topology
open RealInnerProductSpace

noncomputable section

/-! ## The one-sided hypothesis -/

/-- **Contractivity of the Euclidean evolution at nonnegative times only.**  This is the physical
input: the transfer matrix `P(τ)` is a contraction for `τ ≥ 0`, and no statement is made about
`τ < 0`. -/
def HinvRight (Λ : OSState) (T : TimeTranslation) : Prop :=
  ∀ (τ : ℝ), 0 ≤ τ → ∀ F : Observable, osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F

variable {Λ : OSState} {T : TimeTranslation}

/-- The radical of the OS form is preserved by the evolution at nonnegative times.  The proof is
`radical_invariant`'s: the OS form of `T τ F` is squeezed between `0` and `0`. -/
theorem radical_invariant_right (hinv : HinvRight Λ T) {F : Observable}
    (hF : F ∈ Radical Λ.ω) {τ : ℝ} (hτ : 0 ≤ τ) : T τ F ∈ Radical Λ.ω := by
  have h0 : osBilin Λ.ω F F = 0 := hF F
  refine mem_radical_of_self_eq_zero Λ.ω Λ.pos ?_
  have hle := hinv τ hτ F
  rw [h0] at hle
  exact le_antisymm hle (osForm_self_nonneg Λ.ω Λ.pos _)

/-! ## The descended evolution, for `τ ≥ 0` -/

/-- **The evolution on `𝔄/𝔑` at nonnegative time.**  It descends because the radical is
preserved (`radical_invariant_right`), and `hτ : 0 ≤ τ` is the only time information used. -/
def physEvolRight (hinv : HinvRight Λ T) (τ : ℝ) (hτ : 0 ≤ τ) :
    PhysSpace Λ →ₗ[ℝ] PhysSpace Λ :=
  (Radical Λ.ω).mapQ (Radical Λ.ω) (T τ) (fun _ hx => radical_invariant_right hinv hx hτ)

@[simp]
theorem physEvolRight_mk (hinv : HinvRight Λ T) (τ : ℝ) (hτ : 0 ≤ τ) (F : Observable) :
    physEvolRight hinv τ hτ (Submodule.Quotient.mk F) = Submodule.Quotient.mk (T τ F) :=
  rfl

/-- **The evolution is a contraction at nonnegative time**: `‖T(τ)F‖ ≤ ‖F‖`. -/
theorem physEvolRight_contractive (hinv : HinvRight Λ T) (τ : ℝ) (hτ : 0 ≤ τ)
    (x : PhysSpace Λ) : ‖physEvolRight hinv τ hτ x‖ ≤ ‖x‖ := by
  refine Submodule.Quotient.induction_on _ x fun F => ?_
  rw [physEvolRight_mk, physNorm_mk, physNorm_mk]
  exact Real.sqrt_le_sqrt (hinv τ hτ F)

/-- The evolution is the identity at time `0`. -/
theorem physEvolRight_zero (hinv : HinvRight Λ T) (x : PhysSpace Λ) :
    physEvolRight hinv 0 le_rfl x = x := by
  refine Submodule.Quotient.induction_on _ x fun F => ?_
  rw [physEvolRight_mk, timeTranslation_zero]

/-- **The semigroup law at nonnegative times**: `P(s + t) = P(s) ∘ P(t)` for `s, t ≥ 0`. -/
theorem physEvolRight_add (hinv : HinvRight Λ T) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (x : PhysSpace Λ) :
    physEvolRight hinv (s + t) (add_nonneg hs ht) x
      = physEvolRight hinv s hs (physEvolRight hinv t ht x) := by
  refine Submodule.Quotient.induction_on _ x fun F => ?_
  rw [physEvolRight_mk, physEvolRight_mk, physEvolRight_mk, timeTranslation_semigroup]

/-! ## A total function of the parameter

Limits and continuity are stated for functions of `τ : ℝ`, so the `0 ≤ τ` proof argument is
absorbed into a case split: for `τ ≥ 0` the value is `physEvolRight`, and for `τ < 0` it is `0`.
Only `physEvolRightFun_of_nonneg` is ever applied on the negative side of the range. -/

/-- The descended evolution, extended to all real `τ` by `0` on the negative half-line. -/
def physEvolRightFun (hinv : HinvRight Λ T) (τ : ℝ) (x : PhysSpace Λ) : PhysSpace Λ :=
  if h : 0 ≤ τ then physEvolRight hinv τ h x else 0

theorem physEvolRightFun_of_nonneg (hinv : HinvRight Λ T) {τ : ℝ} (hτ : 0 ≤ τ)
    (x : PhysSpace Λ) : physEvolRightFun hinv τ x = physEvolRight hinv τ hτ x := by
  rw [physEvolRightFun, dif_pos hτ]

theorem physEvolRightFun_zero (hinv : HinvRight Λ T) (x : PhysSpace Λ) :
    physEvolRightFun hinv 0 x = x := by
  rw [physEvolRightFun_of_nonneg hinv le_rfl, physEvolRight_zero]

/-- **`P(τ)` does not increase the OS form at nonnegative times.** -/
theorem physForm_evol_self_le_right (hinv : HinvRight Λ T) (τ : ℝ) (hτ : 0 ≤ τ)
    (x : PhysSpace Λ) :
    physForm Λ.ω (physEvolRight hinv τ hτ x) (physEvolRight hinv τ hτ x)
      ≤ physForm Λ.ω x x := by
  have h := physEvolRight_contractive hinv τ hτ x
  have h1 : ‖physEvolRight hinv τ hτ x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  rwa [physNorm_eq, physNorm_eq, Real.sq_sqrt (physForm_self_nonneg Λ _),
    Real.sq_sqrt (physForm_self_nonneg Λ _)] at h1

/-- **The contraction inequality**: `‖P(τ)x − x‖² ≤ 2(⟨x,x⟩ − ⟨P(τ)x,x⟩)`.  This replaces the
isometry identity of `HilbertSpace`, and needs only contractivity at the single time `τ`. -/
theorem norm_physEvolRight_sub_sq_le (hinv : HinvRight Λ T) (τ : ℝ) (x : PhysSpace Λ) :
    ‖physEvolRightFun hinv τ x - x‖ ^ 2
      ≤ 2 * (physForm Λ.ω x x - physForm Λ.ω (physEvolRightFun hinv τ x) x) := by
  by_cases hτ : 0 ≤ τ
  · rw [physEvolRightFun_of_nonneg hinv hτ]
    have hexp : ‖physEvolRight hinv τ hτ x - x‖ ^ 2
        = physForm Λ.ω (physEvolRight hinv τ hτ x - x)
            (physEvolRight hinv τ hτ x - x) := by
      rw [physNorm_eq, Real.sq_sqrt (physForm_self_nonneg Λ _)]
    rw [hexp, physForm_sub_sub, physForm_symm Λ.ω x (physEvolRight hinv τ hτ x)]
    have hle := physForm_evol_self_le_right hinv τ hτ x
    nlinarith
  · rw [physEvolRightFun, dif_neg hτ, zero_sub]
    have hxx : ‖x‖ ^ 2 = physForm Λ.ω x x := by
      rw [physNorm_eq, Real.sq_sqrt (physForm_self_nonneg Λ _)]
    have hnn := physForm_self_nonneg Λ x
    simp only [map_zero, LinearMap.zero_apply, sub_zero]
    rw [norm_neg, hxx]
    nlinarith

/-! ## The extension to `ℋ` -/

/-- **The evolution extends to `ℋ` at nonnegative time**, by `LinearMap.extendOfNorm` along the
dense embedding `𝔄/𝔑 ↪ ℋ`. -/
def physEvolCompletionRight (hinv : HinvRight Λ T) (τ : ℝ) (hτ : 0 ≤ τ) :
    Hphys Λ →L[ℝ] Hphys Λ :=
  LinearMap.extendOfNorm (physCoe Λ ∘ₗ physEvolRight hinv τ hτ) (physCoe Λ)

/-- The extension agrees with the descended evolution on the dense image. -/
theorem physEvolCompletionRight_coe (hinv : HinvRight Λ T) (τ : ℝ) (hτ : 0 ≤ τ)
    (x : PhysSpace Λ) :
    physEvolCompletionRight hinv τ hτ (x : Hphys Λ)
      = ((physEvolRight hinv τ hτ x : PhysSpace Λ) : Hphys Λ) := by
  refine LinearMap.extendOfNorm_eq
    (f := physCoe Λ ∘ₗ physEvolRight hinv τ hτ) (e := physCoe Λ)
    (denseRange_physCoe Λ) ⟨1, ?_⟩ x
  intro y
  simpa [physCoe_apply, UniformSpace.Completion.norm_coe] using
    physEvolRight_contractive hinv τ hτ y

/-- **The operator norm is at most `1`**, for `τ ≥ 0`. -/
theorem norm_physEvolCompletionRight_le (hinv : HinvRight Λ T) (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖physEvolCompletionRight hinv τ hτ‖ ≤ 1 := by
  refine LinearMap.opNorm_extendOfNorm_le (f := physCoe Λ ∘ₗ physEvolRight hinv τ hτ)
    (e := physCoe Λ) (denseRange_physCoe Λ) zero_le_one ?_
  intro x
  simpa [physCoe_apply, UniformSpace.Completion.norm_coe] using
    physEvolRight_contractive hinv τ hτ x

theorem physEvolCompletionRight_contractive (hinv : HinvRight Λ T) (τ : ℝ) (hτ : 0 ≤ τ)
    (z : Hphys Λ) : ‖physEvolCompletionRight hinv τ hτ z‖ ≤ ‖z‖ := by
  calc ‖physEvolCompletionRight hinv τ hτ z‖
      ≤ ‖physEvolCompletionRight hinv τ hτ‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖z‖ := by
        refine mul_le_mul_of_nonneg_right (norm_physEvolCompletionRight_le hinv τ hτ) ?_
        exact norm_nonneg _
    _ = ‖z‖ := one_mul _

/-- **The extension, extended to all real `τ`** by `0` on the negative half-line, so that it is a
genuine family indexed by `ℝ`.  Contractivity holds for every `τ` in this convention. -/
def physEvolCompletionRightFun (hinv : HinvRight Λ T) (τ : ℝ) : Hphys Λ →L[ℝ] Hphys Λ :=
  if h : 0 ≤ τ then physEvolCompletionRight hinv τ h else 0

theorem physEvolCompletionRightFun_of_nonneg (hinv : HinvRight Λ T) {τ : ℝ} (hτ : 0 ≤ τ) :
    physEvolCompletionRightFun hinv τ = physEvolCompletionRight hinv τ hτ := by
  rw [physEvolCompletionRightFun, dif_pos hτ]

theorem norm_physEvolCompletionRightFun_le (hinv : HinvRight Λ T) (τ : ℝ) :
    ‖physEvolCompletionRightFun hinv τ‖ ≤ 1 := by
  by_cases hτ : 0 ≤ τ
  · rw [physEvolCompletionRightFun_of_nonneg hinv hτ]
    exact norm_physEvolCompletionRight_le hinv τ hτ
  · rw [physEvolCompletionRightFun, dif_neg hτ, norm_zero]
    exact zero_le_one

theorem physEvolCompletionRightFun_contractive (hinv : HinvRight Λ T) (τ : ℝ) (z : Hphys Λ) :
    ‖physEvolCompletionRightFun hinv τ z‖ ≤ ‖z‖ := by
  calc ‖physEvolCompletionRightFun hinv τ z‖
      ≤ ‖physEvolCompletionRightFun hinv τ‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖z‖ :=
        mul_le_mul_of_nonneg_right (norm_physEvolCompletionRightFun_le hinv τ) (norm_nonneg _)
    _ = ‖z‖ := one_mul _

/-- **`P(0) = 1` on `ℋ`, for the one-sided definition.** -/
theorem physEvolCompletionRight_zero (hinv : HinvRight Λ T) :
    physEvolCompletionRight hinv 0 le_rfl = ContinuousLinearMap.id ℝ (Hphys Λ) := by
  refine ContinuousLinearMap.ext fun z => ?_
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq (ContinuousLinearMap.continuous _) continuous_id) (fun a => ?_)
  rw [ContinuousLinearMap.id_apply, physEvolCompletionRight_coe, physEvolRight_zero]

/-- **`P(s + t) = P(s) ∘ P(t)` on `ℋ`, for `s, t ≥ 0`.** -/
theorem physEvolCompletionRight_add (hinv : HinvRight Λ T) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    physEvolCompletionRight hinv (s + t) (add_nonneg hs ht)
      = (physEvolCompletionRight hinv s hs).comp (physEvolCompletionRight hinv t ht) := by
  refine ContinuousLinearMap.ext fun z => ?_
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq (ContinuousLinearMap.continuous _)
      ((physEvolCompletionRight hinv s hs).comp
        (physEvolCompletionRight hinv t ht)).continuous)
    (fun a => ?_)
  rw [ContinuousLinearMap.comp_apply, physEvolCompletionRight_coe, physEvolCompletionRight_coe,
    physEvolCompletionRight_coe, physEvolRight_add]

/-! ## Strong continuity at `0⁺` -/

/-- **The distance to the evolved state vanishes at `0⁺`**, on the dense subspace, from continuity
of the two-point function and the contraction inequality. -/
theorem tendsto_norm_physEvolRight_sub (hinv : HinvRight Λ T)
    (hcont : ∀ F : Observable, Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    (x : PhysSpace Λ) :
    Tendsto (fun τ : ℝ => ‖physEvolRightFun hinv τ x - x‖) (𝓝[>] 0) (𝓝 0) := by
  have hme : Tendsto (fun τ : ℝ => physForm Λ.ω (physEvolRightFun hinv τ x) x)
      (𝓝[>] 0) (𝓝 (physForm Λ.ω x x)) := by
    refine Submodule.Quotient.induction_on _ x fun F => ?_
    have hiff : (fun τ : ℝ => physForm Λ.ω (physEvolRightFun hinv τ
          (Submodule.Quotient.mk F)) (Submodule.Quotient.mk F))
        =ᶠ[𝓝[>] 0] (fun τ : ℝ => osBilin Λ.ω (T τ F) F) := by
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      rw [physEvolRightFun_of_nonneg hinv hτ.le, physEvolRight_mk, physForm_mk]
    have h' : Tendsto (fun τ : ℝ => osBilin Λ.ω (T τ F) F) (𝓝[>] 0)
        (𝓝 (osBilin Λ.ω F F)) := by
      have h0 := ((hcont F).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rwa [timeTranslation_zero] at h0
    have htarget : physForm Λ.ω (Submodule.Quotient.mk F) (Submodule.Quotient.mk F)
        = osBilin Λ.ω F F := physForm_mk Λ.ω F F
    rw [htarget]
    exact h'.congr' hiff.symm
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hlim : Tendsto (fun τ : ℝ =>
      2 * (physForm Λ.ω x x - physForm Λ.ω (physEvolRightFun hinv τ x) x))
      (𝓝[>] 0) (𝓝 0) := by
    have hsub : Tendsto (fun τ : ℝ => physForm Λ.ω x x - physForm Λ.ω (physEvolRightFun hinv τ x) x)
        (𝓝[>] 0) (𝓝 (physForm Λ.ω x x - physForm Λ.ω x x)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => physForm Λ.ω x x) (𝓝[>] (0 : ℝ))
        (𝓝 (physForm Λ.ω x x))).sub hme
    simpa using hsub.const_mul 2
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      2 * (physForm Λ.ω x x - physForm Λ.ω (physEvolRightFun hinv τ x) x) < ε ^ 2 :=
    hlim.eventually (isOpen_Iio.mem_nhds (by simpa using (show (0 : ℝ) < ε ^ 2 by nlinarith)))
  filter_upwards [hev] with τ hτ
  have hb := norm_physEvolRight_sub_sq_le hinv τ x
  have hnn : (0 : ℝ) ≤ ‖physEvolRightFun hinv τ x - x‖ := norm_nonneg _
  have hlt : ‖physEvolRightFun hinv τ x - x‖ < ε := by nlinarith
  simpa [Real.dist_eq, abs_of_nonneg hnn] using hlt

/-- **Strong continuity of the transfer semigroup at `0⁺`.**  Approximate `z` by a vector of the
dense subspace, use contractivity for the two outer terms and
`tendsto_norm_physEvolRight_sub` for the middle one.  No isometry, no group law, no negative
time. -/
theorem tendsto_physEvolCompletionRightFun (hinv : HinvRight Λ T)
    (hcont : ∀ F : Observable, Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    (z : Hphys Λ) :
    Tendsto (fun τ : ℝ => physEvolCompletionRightFun hinv τ z) (𝓝[>] 0) (𝓝 z) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨x, hzx⟩ := (denseRange_physCoe Λ).exists_dist_lt z (show (0 : ℝ) < ε / 4 by linarith)
  have hnorm := tendsto_norm_physEvolRight_sub hinv hcont x
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ‖physEvolRightFun hinv τ x - x‖ < ε / 2 := by
    have h := Metric.tendsto_nhds.mp hnorm (ε / 2) (by linarith)
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using h
  filter_upwards [hev, self_mem_nhdsWithin] with τ hτ hτnn
  have hmid : dist (physEvolCompletionRightFun hinv τ ((x : PhysSpace Λ) : Hphys Λ))
      ((x : PhysSpace Λ) : Hphys Λ) = ‖physEvolRightFun hinv τ x - x‖ := by
    rw [physEvolCompletionRightFun_of_nonneg hinv hτnn.le, physEvolCompletionRight_coe,
      physEvolRightFun_of_nonneg hinv hτnn.le, dist_eq_norm,
      ← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe]
  have hout : dist (physEvolCompletionRightFun hinv τ z)
      (physEvolCompletionRightFun hinv τ ((x : PhysSpace Λ) : Hphys Λ))
      ≤ dist z ((x : PhysSpace Λ) : Hphys Λ) := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact physEvolCompletionRightFun_contractive hinv τ _
  have hfin : dist (physEvolCompletionRightFun hinv τ z) z
      ≤ dist z ((x : PhysSpace Λ) : Hphys Λ)
        + (‖physEvolRightFun hinv τ x - x‖ + dist ((x : PhysSpace Λ) : Hphys Λ) z) := by
    calc dist (physEvolCompletionRightFun hinv τ z) z
        ≤ dist (physEvolCompletionRightFun hinv τ z)
            (physEvolCompletionRightFun hinv τ ((x : PhysSpace Λ) : Hphys Λ))
          + dist (physEvolCompletionRightFun hinv τ ((x : PhysSpace Λ) : Hphys Λ)) z :=
          dist_triangle _ _ _
      _ ≤ dist z ((x : PhysSpace Λ) : Hphys Λ)
          + (dist (physEvolCompletionRightFun hinv τ ((x : PhysSpace Λ) : Hphys Λ))
              ((x : PhysSpace Λ) : Hphys Λ) + dist ((x : PhysSpace Λ) : Hphys Λ) z) := by
          have h2 := dist_triangle (physEvolCompletionRightFun hinv τ
            ((x : PhysSpace Λ) : Hphys Λ)) ((x : PhysSpace Λ) : Hphys Λ) z
          linarith
      _ = _ := by rw [hmid]
  have hle : dist ((x : PhysSpace Λ) : Hphys Λ) z < ε / 4 := by
    rw [dist_comm]
    exact hzx
  linarith [hfin, hle, hτ]

/-! ## Agreement with the two-sided construction -/

/-- **Nothing is lost by dropping the negative half of the hypothesis**: when the two-sided
`hinv` holds, the forward semigroup is the restriction of the one built in `HilbertSpace`.  The
proof is `rfl`: only the radical-invariance proof differs, and proofs in `Prop` are irrelevant. -/
theorem physEvolCompletionRight_eq (hinv : ∀ (τ : ℝ) (F : Observable),
    osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F) (τ : ℝ) (hτ : 0 ≤ τ) :
    physEvolCompletionRight (fun τ _ F => hinv τ F) τ hτ
      = physEvolCompletion Λ T hinv τ :=
  rfl

end

end BookProof.OSReconstruction
