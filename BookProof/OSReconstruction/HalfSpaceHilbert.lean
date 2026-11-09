import Mathlib
import BookProof.OSReconstruction.HalfSpaceState
import BookProof.OSReconstruction.Hamiltonian

/-!
# The forward transfer semigroup on the half-space Hilbert space

Plan: `cftproof.md`, **E3** — on `ℋ = 𝔄₊/𝔑₊` (here `HalfSpaceState.Hhalf`), "prove forward
translation preserves support and the null space", with `P(0) = I`, `P(s+t) = P(s)P(t)`,
`P(t)* = P(t)` and strong continuity.

`OSReconstruction.TransferSemigroupRight` does this for the quotient of the *whole* observable
algebra, under the two-sided state hypothesis `HinvRight`.  This module is the half-space version:
the evolution is only allowed to move `𝔄₊` inside itself, so the descended map is a linear map of
`𝔄₊/𝔑₊`, and contractivity is asked for on `𝔄₊` only.

## Contents

* `PreservesPositiveTime` — **forward translation preserves positive-time support**: the named
  hypothesis that `T τ` maps `𝔄₊` into itself.  This is the "support preservation" the plan asks
  for; it is *not* deduced, because the corpus's `TimeTranslation` is an abstract one-parameter
  family of linear maps on all observables and no lattice translation is instantiated;
* `hsEvol` — the evolution as a linear endomorphism of the subalgebra `𝔄₊`, and `hsEvol_coe`,
  `hsEvol_zero`, `hsEvol_add` — its identity and semigroup law, read off `T`'s;
* `HsHinv` — **contractivity of the OS form on `𝔄₊` at nonnegative times**;
* `hsRadical_invariant` — **forward translation preserves the null space** `𝔑₊`: the Cauchy–Schwarz
  squeeze `0 ≤ ⟨T τ F, T τ F⟩ ≤ ⟨F,F⟩ = 0`;
* `hsQuotMap` — the descended endomorphism of `𝔄₊/𝔑₊` (`Submodule.mapQ`), with
  `hsQuotMap_mk`, contractivity, `hsQuotMap_zero` and `hsQuotMap_add`;
* `hsEvolFun` — the same object with the parameter total in `τ` (`0` for `τ < 0`), so that limits in
  `τ` can be taken; `norm_hsEvolFun_sub_sq_le` is the contraction inequality
  `‖P(τ)x − x‖² ≤ 2(⟨x,x⟩ − ⟨P(τ)x,x⟩)`;
* `hsEvolCompletion` — the extension to `Hhalf` by `LinearMap.extendOfNorm`, with `‖P(τ)‖ ≤ 1`,
  `P(0) = 1`, `P(s+t) = P(s)P(t)`, and `tendsto_hsEvolCompletionFun` — **strong continuity at
  `0⁺`** from matrix-element continuity;
* `HsSymmetric` — the symmetry of the two-point function under the forward evolution, and
  `hsEvolCompletion_isSelfAdjoint` — **`P(τ)* = P(τ)`** for `τ ≥ 0`, by density from the dense
  subspace.

## Boundary

* `PreservesPositiveTime` and `HsHinv` are hypotheses, exactly as `HinvRight` is in the corpus:
  the transfer matrix exists for `τ ≥ 0` and moves `𝔄₊` forward; neither is proved here.
* `HsSymmetric` is a hypothesis.  The corpus likewise consumes `∀ τ, IsSelfAdjoint (P τ)` as input
  (`OSReconstruction.Generator.generator_isSymmetric`) rather than deriving it, and it cannot be
  derived from contractivity alone.  What is proved here is the implication
  *two-point symmetry on the dense subspace ⟹ self-adjointness on the completion*; the induction
  proving that implication is the new content.
* The **generator** on `𝔄₊/𝔑₊` (domain, closedness, dissipativity, resolvent bound) is *not* built
  here.  `OSReconstruction.SemigroupGenerator` proves those statements for `Hphys` under
  `HinvRight`; the half-space copy needs `hsQuotMap` in place of `physEvolRight` and duplicate
  `diffQuot`/`HasGenRight`/resolvent machinery, and is left open (E3's "generator domain /
  resolvent identified").
* The space is real.  `Hhalf` is a real Hilbert space (`HalfSpaceState`); the complex structure the
  CFT needs is the complexification mentioned in that module's boundary note, not built here.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity
open Filter
open scoped Topology
open RealInnerProductSpace

noncomputable section

/-! ## Support preservation and the evolution on `𝔄₊` -/

/-- **Forward translation preserves positive-time support**: `T τ` maps the positive-time algebra
into itself.  The positive half-space is `{x₀ > 0}`, and translating it forward by `τ ≥ 0` keeps it
there; the operator statement is the hypothesis, since `TimeTranslation` is abstract in this
corpus. -/
def PreservesPositiveTime (T : TimeTranslation) : Prop :=
  ∀ (τ : ℝ) (F : PositiveTimeAlgebra), T τ (F : Observable) ∈ PositiveTimeAlgebra

/-- **The evolution on `𝔄₊`**: `T τ` restricted to the positive-time algebra, as a linear
endomorphism of it.  `PreservesPositiveTime` is exactly what makes the codomain correct. -/
def hsEvol {T : TimeTranslation} (hT : PreservesPositiveTime T) (τ : ℝ) :
    PositiveTimeAlgebra →ₗ[ℝ] PositiveTimeAlgebra where
  toFun F := ⟨T τ (F : Observable), hT τ F⟩
  map_add' F G := by
    refine Subtype.ext ?_
    simp
  map_smul' c F := by
    refine Subtype.ext ?_
    simp

@[simp]
theorem hsEvol_coe {T : TimeTranslation} (hT : PreservesPositiveTime T) (τ : ℝ)
    (F : PositiveTimeAlgebra) : (hsEvol hT τ F : Observable) = T τ (F : Observable) := rfl

/-- The restricted evolution is the identity at time `0`. -/
theorem hsEvol_zero {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (F : PositiveTimeAlgebra) : hsEvol hT 0 F = F :=
  Subtype.ext (timeTranslation_zero T (F : Observable))

/-- **The restricted evolution is a semigroup**: `T(s + t) = T(s) T(t)` on `𝔄₊`. -/
theorem hsEvol_add {T : TimeTranslation} (hT : PreservesPositiveTime T) (s t : ℝ)
    (F : PositiveTimeAlgebra) : hsEvol hT (s + t) F = hsEvol hT s (hsEvol hT t F) :=
  Subtype.ext (timeTranslation_semigroup T s t (F : Observable))

/-- **Contractivity on the half-space at nonnegative times**: the one-sided OS hypothesis, stated
on `𝔄₊`.  Compare `TransferSemigroupRight.HinvRight`, which states it on all observables. -/
def HsHinv (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T) : Prop :=
  ∀ (τ : ℝ), 0 ≤ τ → ∀ F : PositiveTimeAlgebra,
    hsBilin Λ (hsEvol hT τ F) (hsEvol hT τ F) ≤ hsBilin Λ F F

/-- **Forward translation preserves the null space `𝔑₊`.**  `0 ≤ ⟨T τ F, T τ F⟩ ≤ ⟨F,F⟩ = 0`
for `F` null, so `T τ F` is null by Cauchy–Schwarz (`mem_hsRadical_of_self_eq_zero`). -/
theorem hsRadical_invariant (Λ : HalfSpaceState) {T : TimeTranslation}
    {hT : PreservesPositiveTime T}
    (hinv : HsHinv Λ hT) {F : PositiveTimeAlgebra} (hF : F ∈ HsRadical Λ) {τ : ℝ} (hτ : 0 ≤ τ) :
    hsEvol hT τ F ∈ HsRadical Λ := by
  have h0 : hsBilin Λ F F = 0 := hF F
  refine mem_hsRadical_of_self_eq_zero Λ ?_
  have hle := hinv τ hτ F
  rw [h0] at hle
  exact le_antisymm hle (hsBilin_self_nonneg Λ _)

/-! ## The descended evolution on `𝔄₊/𝔑₊` -/

/-- **The evolution descended to `𝔄₊/𝔑₊`** at nonnegative time: it descends because the null
space is preserved (`hsRadical_invariant`). -/
def hsQuotMap (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) (τ : ℝ) (hτ : 0 ≤ τ) : HsSpace Λ →ₗ[ℝ] HsSpace Λ :=
  (HsRadical Λ).mapQ (HsRadical Λ) (hsEvol hT τ) (fun _ hx => hsRadical_invariant Λ hinv hx hτ)

@[simp]
theorem hsQuotMap_mk (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) (τ : ℝ) (hτ : 0 ≤ τ) (F : PositiveTimeAlgebra) :
    hsQuotMap Λ hT hinv τ hτ (Submodule.Quotient.mk F) = Submodule.Quotient.mk (hsEvol hT τ F) :=
  rfl

/-- **The descended evolution is a contraction**: `‖P(τ)x‖ ≤ ‖x‖` on `𝔄₊/𝔑₊`. -/
theorem hsQuotMap_contractive (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) (τ : ℝ) (hτ : 0 ≤ τ) (x : HsSpace Λ) :
    ‖hsQuotMap Λ hT hinv τ hτ x‖ ≤ ‖x‖ := by
  refine Submodule.Quotient.induction_on _ x fun F => ?_
  rw [hsQuotMap_mk, hsNorm_mk, hsNorm_mk]
  exact Real.sqrt_le_sqrt (hinv τ hτ F)

/-- `P(0) = 1` on `𝔄₊/𝔑₊`. -/
theorem hsQuotMap_zero (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) (x : HsSpace Λ) : hsQuotMap Λ hT hinv 0 le_rfl x = x := by
  refine Submodule.Quotient.induction_on _ x fun F => ?_
  rw [hsQuotMap_mk]
  exact congrArg Submodule.Quotient.mk (hsEvol_zero hT F)

/-- `P(s + t) = P(s) P(t)` on `𝔄₊/𝔑₊` for `s, t ≥ 0`. -/
theorem hsQuotMap_add (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (x : HsSpace Λ) :
    hsQuotMap Λ hT hinv (s + t) (add_nonneg hs ht) x
      = hsQuotMap Λ hT hinv s hs (hsQuotMap Λ hT hinv t ht x) := by
  refine Submodule.Quotient.induction_on _ x fun F => ?_
  rw [hsQuotMap_mk, hsQuotMap_mk, hsQuotMap_mk]
  exact congrArg Submodule.Quotient.mk (hsEvol_add hT s t F)

/-! ## A total function of the parameter -/

/-- The descended evolution, extended to all real `τ` by `0` on the negative half-line, so that
functions of `τ` have a limit to discuss. -/
def hsEvolFun (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) (τ : ℝ) (x : HsSpace Λ) : HsSpace Λ :=
  if h : 0 ≤ τ then hsQuotMap Λ hT hinv τ h x else 0

theorem hsEvolFun_of_nonneg (Λ : HalfSpaceState) {T : TimeTranslation}
    {hT : PreservesPositiveTime T}
    {hinv : HsHinv Λ hT} {τ : ℝ} (hτ : 0 ≤ τ) (x : HsSpace Λ) :
    hsEvolFun Λ hT hinv τ x = hsQuotMap Λ hT hinv τ hτ x := by
  rw [hsEvolFun, dif_pos hτ]

/-- `P(τ)` does not increase the OS form on `𝔄₊/𝔑₊` at nonnegative times. -/
theorem hsForm_evol_self_le (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) (τ : ℝ) (hτ : 0 ≤ τ) (x : HsSpace Λ) :
    hsForm Λ (hsQuotMap Λ hT hinv τ hτ x) (hsQuotMap Λ hT hinv τ hτ x) ≤ hsForm Λ x x := by
  have h := hsQuotMap_contractive Λ hT hinv τ hτ x
  have h1 : ‖hsQuotMap Λ hT hinv τ hτ x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  rwa [hsNorm_eq, hsNorm_eq, Real.sq_sqrt (hsForm_self_nonneg Λ _),
    Real.sq_sqrt (hsForm_self_nonneg Λ _)] at h1

/-- **The contraction inequality**: `‖P(τ)x − x‖² ≤ 2(⟨x,x⟩ − ⟨P(τ)x,x⟩)`, from contractivity at
the single time `τ` (the analogue of `norm_physEvolRight_sub_sq_le`). -/
theorem norm_hsEvolFun_sub_sq_le (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) (τ : ℝ) (x : HsSpace Λ) :
    ‖hsEvolFun Λ hT hinv τ x - x‖ ^ 2
      ≤ 2 * (hsForm Λ x x - hsForm Λ (hsEvolFun Λ hT hinv τ x) x) := by
  by_cases hτ : 0 ≤ τ
  · rw [hsEvolFun_of_nonneg Λ hτ]
    have hexp : ‖hsQuotMap Λ hT hinv τ hτ x - x‖ ^ 2
        = hsForm Λ (hsQuotMap Λ hT hinv τ hτ x - x)
            (hsQuotMap Λ hT hinv τ hτ x - x) := by
      rw [hsNorm_eq, Real.sq_sqrt (hsForm_self_nonneg Λ _)]
    rw [hexp, hsForm_sub_sub, hsForm_symm Λ x (hsQuotMap Λ hT hinv τ hτ x)]
    have hle := hsForm_evol_self_le Λ hT hinv τ hτ x
    nlinarith
  · rw [hsEvolFun, dif_neg hτ, zero_sub]
    have hxx : ‖x‖ ^ 2 = hsForm Λ x x := by
      rw [hsNorm_eq, Real.sq_sqrt (hsForm_self_nonneg Λ _)]
    have hnn := hsForm_self_nonneg Λ x
    simp only [map_zero, LinearMap.zero_apply, sub_zero]
    rw [norm_neg, hxx]
    nlinarith

/-! ## The extension to `Hhalf` -/

/-- **The evolution extends to `Hhalf`** by `LinearMap.extendOfNorm` along the dense embedding. -/
def hsEvolCompletion (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) (τ : ℝ) (hτ : 0 ≤ τ) : Hhalf Λ →L[ℝ] Hhalf Λ :=
  LinearMap.extendOfNorm (hsCoe Λ ∘ₗ hsQuotMap Λ hT hinv τ hτ) (hsCoe Λ)

/-- The extension agrees with the descended evolution on the dense image. -/
theorem hsEvolCompletion_coe (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) (τ : ℝ) (hτ : 0 ≤ τ) (x : HsSpace Λ) :
    hsEvolCompletion Λ hT hinv τ hτ (x : Hhalf Λ)
      = ((hsQuotMap Λ hT hinv τ hτ x : HsSpace Λ) : Hhalf Λ) := by
  refine LinearMap.extendOfNorm_eq
    (f := hsCoe Λ ∘ₗ hsQuotMap Λ hT hinv τ hτ) (e := hsCoe Λ)
    (denseRange_hsCoe Λ) ⟨1, ?_⟩ x
  intro y
  simpa [hsCoe_apply, UniformSpace.Completion.norm_coe] using
    hsQuotMap_contractive Λ hT hinv τ hτ y

/-- **The operator norm is at most `1`** for `τ ≥ 0`. -/
theorem norm_hsEvolCompletion_le (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖hsEvolCompletion Λ hT hinv τ hτ‖ ≤ 1 := by
  refine LinearMap.opNorm_extendOfNorm_le (f := hsCoe Λ ∘ₗ hsQuotMap Λ hT hinv τ hτ)
    (e := hsCoe Λ) (denseRange_hsCoe Λ) zero_le_one ?_
  intro x
  simpa [hsCoe_apply, UniformSpace.Completion.norm_coe] using
    hsQuotMap_contractive Λ hT hinv τ hτ x

theorem hsEvolCompletion_contractive (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) (τ : ℝ) (hτ : 0 ≤ τ) (z : Hhalf Λ) :
    ‖hsEvolCompletion Λ hT hinv τ hτ z‖ ≤ ‖z‖ := by
  calc ‖hsEvolCompletion Λ hT hinv τ hτ z‖
      ≤ ‖hsEvolCompletion Λ hT hinv τ hτ‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖z‖ :=
        mul_le_mul_of_nonneg_right (norm_hsEvolCompletion_le Λ hT hinv τ hτ) (norm_nonneg _)
    _ = ‖z‖ := one_mul _

/-- The extension, extended to all real `τ` by `0` on the negative half-line. -/
def hsEvolCompletionFun (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) (τ : ℝ) : Hhalf Λ →L[ℝ] Hhalf Λ :=
  if h : 0 ≤ τ then hsEvolCompletion Λ hT hinv τ h else 0

theorem hsEvolCompletionFun_of_nonneg (Λ : HalfSpaceState) {T : TimeTranslation}
    {hT : PreservesPositiveTime T} {hinv : HsHinv Λ hT} {τ : ℝ} (hτ : 0 ≤ τ) :
    hsEvolCompletionFun Λ hT hinv τ = hsEvolCompletion Λ hT hinv τ hτ := by
  rw [hsEvolCompletionFun, dif_pos hτ]

theorem norm_hsEvolCompletionFun_le (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) (τ : ℝ) :
    ‖hsEvolCompletionFun Λ hT hinv τ‖ ≤ 1 := by
  by_cases hτ : 0 ≤ τ
  · rw [hsEvolCompletionFun_of_nonneg Λ hτ]
    exact norm_hsEvolCompletion_le Λ hT hinv τ hτ
  · rw [hsEvolCompletionFun, dif_neg hτ, norm_zero]
    exact zero_le_one

theorem hsEvolCompletionFun_contractive (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) (τ : ℝ) (z : Hhalf Λ) :
    ‖hsEvolCompletionFun Λ hT hinv τ z‖ ≤ ‖z‖ := by
  calc ‖hsEvolCompletionFun Λ hT hinv τ z‖
      ≤ ‖hsEvolCompletionFun Λ hT hinv τ‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖z‖ :=
        mul_le_mul_of_nonneg_right (norm_hsEvolCompletionFun_le Λ hT hinv τ) (norm_nonneg _)
    _ = ‖z‖ := one_mul _

/-- **`P(0) = 1` on `Hhalf`.** -/
theorem hsEvolCompletion_zero (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) :
    hsEvolCompletion Λ hT hinv 0 le_rfl = ContinuousLinearMap.id ℝ (Hhalf Λ) := by
  refine ContinuousLinearMap.ext fun z => ?_
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq (ContinuousLinearMap.continuous _) continuous_id) (fun a => ?_)
  rw [ContinuousLinearMap.id_apply, hsEvolCompletion_coe, hsQuotMap_zero]

/-- **`P(s + t) = P(s) P(t)` on `Hhalf`** for `s, t ≥ 0`. -/
theorem hsEvolCompletion_add (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    hsEvolCompletion Λ hT hinv (s + t) (add_nonneg hs ht)
      = (hsEvolCompletion Λ hT hinv s hs).comp (hsEvolCompletion Λ hT hinv t ht) := by
  refine ContinuousLinearMap.ext fun z => ?_
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq (ContinuousLinearMap.continuous _)
      ((hsEvolCompletion Λ hT hinv s hs).comp
        (hsEvolCompletion Λ hT hinv t ht)).continuous) (fun a => ?_)
  rw [ContinuousLinearMap.comp_apply, hsEvolCompletion_coe, hsEvolCompletion_coe,
    hsEvolCompletion_coe, hsQuotMap_add]

/-- The semigroup law in application form, for nonnegative times. -/
theorem hsEvolCompletionFun_comp (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (z : Hhalf Λ) :
    hsEvolCompletionFun Λ hT hinv s (hsEvolCompletionFun Λ hT hinv t z)
      = hsEvolCompletionFun Λ hT hinv (s + t) z := by
  rw [hsEvolCompletionFun_of_nonneg Λ hs, hsEvolCompletionFun_of_nonneg Λ ht,
    hsEvolCompletionFun_of_nonneg Λ (add_nonneg hs ht),
    ← ContinuousLinearMap.comp_apply, ← hsEvolCompletion_add]

/-! ## Strong continuity at `0⁺` -/

/-- **The distance to the evolved state vanishes at `0⁺`**, on the dense subspace, from continuity
of the two-point function and the contraction inequality. -/
theorem tendsto_norm_hsEvolFun_sub (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT)
    (hcont : ∀ F : Observable, F ∈ PositiveTimeAlgebra →
      Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    (x : HsSpace Λ) :
    Tendsto (fun τ : ℝ => ‖hsEvolFun Λ hT hinv τ x - x‖) (𝓝[>] 0) (𝓝 0) := by
  have hme : Tendsto (fun τ : ℝ => hsForm Λ (hsEvolFun Λ hT hinv τ x) x)
      (𝓝[>] 0) (𝓝 (hsForm Λ x x)) := by
    refine Submodule.Quotient.induction_on _ x fun F => ?_
    have hiff : (fun τ : ℝ => hsForm Λ (hsEvolFun Λ hT hinv τ
          (Submodule.Quotient.mk F)) (Submodule.Quotient.mk F))
        =ᶠ[𝓝[>] 0] (fun τ : ℝ => osBilin Λ.ω (T τ (F : Observable)) (F : Observable)) := by
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      rw [hsEvolFun_of_nonneg Λ hτ.le, hsQuotMap_mk, hsForm_mk]
      simp [hsBilin]
    have h' : Tendsto (fun τ : ℝ => osBilin Λ.ω (T τ (F : Observable)) (F : Observable))
        (𝓝[>] 0) (𝓝 (osBilin Λ.ω (F : Observable) (F : Observable))) := by
      have h0 := ((hcont (F : Observable) F.2).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rwa [timeTranslation_zero] at h0
    have htarget : hsForm Λ (Submodule.Quotient.mk F) (Submodule.Quotient.mk F)
        = osBilin Λ.ω (F : Observable) (F : Observable) := hsForm_mk Λ F F
    rw [htarget]
    exact h'.congr' hiff.symm
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hlim : Tendsto (fun τ : ℝ =>
      2 * (hsForm Λ x x - hsForm Λ (hsEvolFun Λ hT hinv τ x) x)) (𝓝[>] 0) (𝓝 0) := by
    have hsub : Tendsto (fun τ : ℝ => hsForm Λ x x - hsForm Λ (hsEvolFun Λ hT hinv τ x) x)
        (𝓝[>] 0) (𝓝 (hsForm Λ x x - hsForm Λ x x)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => hsForm Λ x x) (𝓝[>] (0 : ℝ))
        (𝓝 (hsForm Λ x x))).sub hme
    simpa using hsub.const_mul 2
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      2 * (hsForm Λ x x - hsForm Λ (hsEvolFun Λ hT hinv τ x) x) < ε ^ 2 :=
    hlim.eventually (isOpen_Iio.mem_nhds (by simpa using (show (0 : ℝ) < ε ^ 2 by nlinarith)))
  filter_upwards [hev] with τ hτ
  have hb := norm_hsEvolFun_sub_sq_le Λ hT hinv τ x
  have hnn : (0 : ℝ) ≤ ‖hsEvolFun Λ hT hinv τ x - x‖ := norm_nonneg _
  have hlt : ‖hsEvolFun Λ hT hinv τ x - x‖ < ε := by nlinarith
  simpa [Real.dist_eq, abs_of_nonneg hnn] using hlt

/-- **Strong continuity of the forward transfer semigroup at `0⁺`**, by density and
contractivity.  The hypotheses are the same as `TransferSemigroupRight`'s: matrix-element
continuity of the evolution at `0`, carried as the OS axiom of time-translation continuity, and
now restricted to `𝔄₊`. -/
theorem tendsto_hsEvolCompletionFun (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT)
    (hcont : ∀ F : Observable, F ∈ PositiveTimeAlgebra →
      Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    (z : Hhalf Λ) :
    Tendsto (fun τ : ℝ => hsEvolCompletionFun Λ hT hinv τ z) (𝓝[>] 0) (𝓝 z) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨x, hzx⟩ :=
    (denseRange_hsCoe Λ).exists_dist_lt z (show (0 : ℝ) < ε / 4 by linarith)
  have hnorm := tendsto_norm_hsEvolFun_sub Λ hT hinv hcont x
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ‖hsEvolFun Λ hT hinv τ x - x‖ < ε / 2 := by
    have h := Metric.tendsto_nhds.mp hnorm (ε / 2) (by linarith)
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using h
  filter_upwards [hev, self_mem_nhdsWithin] with τ hτ hτnn
  have hmid : dist (hsEvolCompletionFun Λ hT hinv τ ((x : HsSpace Λ) : Hhalf Λ))
      ((x : HsSpace Λ) : Hhalf Λ) = ‖hsEvolFun Λ hT hinv τ x - x‖ := by
    rw [hsEvolCompletionFun_of_nonneg Λ hτnn.le, hsEvolCompletion_coe,
      hsEvolFun_of_nonneg Λ hτnn.le, dist_eq_norm,
      ← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe]
  have hout : dist (hsEvolCompletionFun Λ hT hinv τ z)
      (hsEvolCompletionFun Λ hT hinv τ ((x : HsSpace Λ) : Hhalf Λ))
      ≤ dist z ((x : HsSpace Λ) : Hhalf Λ) := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact hsEvolCompletionFun_contractive Λ hT hinv τ _
  have hfin : dist (hsEvolCompletionFun Λ hT hinv τ z) z
      ≤ dist z ((x : HsSpace Λ) : Hhalf Λ)
        + (‖hsEvolFun Λ hT hinv τ x - x‖ + dist ((x : HsSpace Λ) : Hhalf Λ) z) := by
    calc dist (hsEvolCompletionFun Λ hT hinv τ z) z
        ≤ dist (hsEvolCompletionFun Λ hT hinv τ z)
            (hsEvolCompletionFun Λ hT hinv τ ((x : HsSpace Λ) : Hhalf Λ))
          + dist (hsEvolCompletionFun Λ hT hinv τ ((x : HsSpace Λ) : Hhalf Λ)) z :=
          dist_triangle _ _ _
      _ ≤ dist z ((x : HsSpace Λ) : Hhalf Λ)
          + (dist (hsEvolCompletionFun Λ hT hinv τ ((x : HsSpace Λ) : Hhalf Λ))
              ((x : HsSpace Λ) : Hhalf Λ) + dist ((x : HsSpace Λ) : Hhalf Λ) z) := by
          have h2 := dist_triangle (hsEvolCompletionFun Λ hT hinv τ
            ((x : HsSpace Λ) : Hhalf Λ)) ((x : HsSpace Λ) : Hhalf Λ) z
          linarith
      _ = _ := by rw [hmid]
  have hle : dist ((x : HsSpace Λ) : Hhalf Λ) z < ε / 4 := by
    rw [dist_comm]
    exact hzx
  linarith [hfin, hle, hτ]

/-! ## Self-adjointness of the forward evolution -/

/-- **Symmetry of the two-point function under the forward evolution**: the OS form of `P(τ)x`
against `y` is the OS form of `x` against `P(τ)y`.  This is the half-space input from which
`P(τ)* = P(τ)` follows; it is a hypothesis, as `∀ τ, IsSelfAdjoint (P τ)` is in
`OSReconstruction.Generator`. -/
def HsSymmetric (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) : Prop :=
  ∀ (τ : ℝ) (hτ : 0 ≤ τ) (x y : HsSpace Λ),
    hsForm Λ (hsQuotMap Λ hT hinv τ hτ x) y = hsForm Λ x (hsQuotMap Λ hT hinv τ hτ y)

/-- On `HsSpace` the inner product is the descended OS form. -/
theorem hsInner_eq (Λ : HalfSpaceState) (x y : HsSpace Λ) :
    ⟪x, y⟫ = hsForm Λ x y := rfl

/-- **The descended evolution is a symmetric operator** under `HsSymmetric`. -/
theorem hsQuotMap_isSymmetric (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) {hinv : HsHinv Λ hT} (hsym : HsSymmetric Λ hT hinv)
    {τ : ℝ} (hτ : 0 ≤ τ) : LinearMap.IsSymmetric (hsQuotMap Λ hT hinv τ hτ) :=
  fun x y => by
    rw [hsInner_eq, hsInner_eq]
    exact hsym τ hτ x y

/-- **Self-adjointness on the completion, from symmetry on the dense subspace.**  Both sides of
`⟪P(τ)x, y⟫ = ⟪x, P(τ)y⟫` are continuous in each variable, so the identity extends from
`𝔄₊/𝔑₊ × 𝔄₊/𝔑₊` to `Hhalf × Hhalf` by two `UniformSpace.Completion.induction_on`s. -/
theorem hsEvolCompletion_isSymmetric (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) {hinv : HsHinv Λ hT} (hsym : HsSymmetric Λ hT hinv)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    LinearMap.IsSymmetric
      ((hsEvolCompletion Λ hT hinv τ hτ : Hhalf Λ →L[ℝ] Hhalf Λ) : Hhalf Λ →ₗ[ℝ] Hhalf Λ) := by
  intro x y
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq
      (continuous_inner.comp ((hsEvolCompletion Λ hT hinv τ hτ).continuous.prodMk
        continuous_const))
      (continuous_inner.comp (continuous_id.prodMk continuous_const))
  intro a
  refine UniformSpace.Completion.induction_on y ?_ ?_
  · exact isClosed_eq
      (continuous_inner.comp (continuous_const.prodMk continuous_id))
      (continuous_inner.comp (continuous_const.prodMk
        (hsEvolCompletion Λ hT hinv τ hτ).continuous))
  intro b
  simp only [ContinuousLinearMap.coe_coe]
  rw [hsEvolCompletion_coe, hsEvolCompletion_coe, UniformSpace.Completion.inner_coe,
    UniformSpace.Completion.inner_coe]
  exact hsQuotMap_isSymmetric Λ hT hsym hτ a b

/-- **`P(τ)* = P(τ)`**: the forward transfer operator at nonnegative time is self-adjoint. -/
theorem hsEvolCompletion_isSelfAdjoint (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) {hinv : HsHinv Λ hT} (hsym : HsSymmetric Λ hT hinv)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    IsSelfAdjoint (hsEvolCompletion Λ hT hinv τ hτ) :=
  LinearMap.IsSymmetric.isSelfAdjoint (hsEvolCompletion_isSymmetric Λ hT hsym hτ)

end

end BookProof.OSReconstruction
