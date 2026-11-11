import Mathlib
import BookProof.OSReconstruction.HalfSpaceHilbert

/-!
# The generator of the half-space transfer semigroup

Plan: `cftproof.md`, **E3** — on `ℋ = 𝔄₊/𝔑₊` (here `HalfSpaceState.Hhalf`), the forward
translation has a generator whose "domain / resolvent" is identified.  `HalfSpaceHilbert` builds
the semigroup `P(τ)`, `τ ≥ 0`, and its strong continuity at `0⁺`; this module attaches the
generator to it.

The construction is the one-sided one of `OSReconstruction.SemigroupGenerator`, carried out with the
half-space semigroup and the half-space contractivity hypothesis `HsHinv` in place of `HinvRight`:

* `hsDiffQuot` — the difference quotient `τ⁻¹ • (P(τ)z − z)` of `hsEvolCompletionFun`, defined for
  all `τ` (it is `0` for `τ < 0`), so that limits along `𝓝[>] 0` can be taken;
* `HsHasGen`, `hsGenDomain`, `hsGenerator` — the forward domain (convergence of the quotient at
  `0⁺`) as a submodule, and the generator as a partially defined linear map, with its value a
  chosen limit; linearity is recovered from uniqueness of limits;
* `hasDerivWithinAt_hsEvol` — the orbit of a domain vector has the *right* derivative
  `P(t)(A z)` within `Ioi t`, for `t ≥ 0`, from the semigroup law only;
* `hsEvol_sub_eq_integral` — the integral representation `P(τ)z − z = ∫₀^τ P(s)(A z) ds` for
  `τ ≥ 0`, from the right-derivative form of the fundamental theorem of calculus;
* `hsGenerator_isClosed` — the graph of `hsGenerator` is closed;
* `hsGenerator_inner_le_zero` — `⟪A z, z⟫ ≤ 0`: the generator is dissipative, forced by
  contractivity alone (this is the Wick-rotated shadow of positivity of the Hamiltonian);
* `hsGenerator_resolvent_bound` — the a priori estimate `λ‖z‖ ≤ ‖λ z − A z‖` for `λ > 0`, and
  `hsGenerator_resolvent_injective` — `λ − A` is injective on the domain.

## The identification `H = −A`

`hsGenerator_eq_neg` states the sign: if `H` is the self-adjoint operator whose flow the semigroup
is — the local form of `P(τ) = e^{−τH}` is that the orbit has right derivative `−H z` at `0⁺` —
then `Hhalf` is *entirely* in the domain and `A z = −H z` on it.  The derivative hypothesis is the
statement that the semigroup is the flow of `H`; deriving it from `P(τ) = e^{−τH}` (i.e. building
the exponential) is the spectral-theory step this development does not take, exactly as in
`OSReconstruction.SemigroupGenerator`'s boundary note.  The matrix-element form
`hsGenerator_inner_eq_neg` is the version the Källén–Lehmann representation consumes: it says
`⟪A z, z⟫ = −⟪H z, z⟫`, so a nonnegative `H` is dissipativity of `A` and vice versa.

## Boundary

* The hypotheses are the half-space ones of `HalfSpaceHilbert`: `PreservesPositiveTime` (forward
  translation keeps `𝔄₊` inside itself), `HsHinv` (contractivity of the OS form on `𝔄₊` at
  `τ ≥ 0`), and — for closedness and the integral representation — matrix-element continuity of the
  evolution at `0`, restricted to `𝔄₊`.  None of them is derived here.
* The range condition `ran(λ − A) = Hhalf` (the surjectivity half of Lumer–Phillips) is *not*
  proved; only the a priori estimate and injectivity are.  Surjectivity is the statement that the
  resolvent exists, and it needs the realization, not the OS axioms: in the multiplier model it is
  `OSReconstruction.MultiplierGenerator.range_sub_generatorRight_mulModel`.
* Nothing here re-derives self-adjointness of the Hamiltonian: `A` is dissipative, not symmetric,
  and the passage from "closed dissipative with dense domain" to a self-adjoint `H = −A` is
  Lumer–Phillips plus the spectral theorem, neither of which Mathlib has.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity
open Filter MeasureTheory Set
open scoped Topology RealInnerProductSpace Interval

noncomputable section

/-! ## The forward-time difference quotient -/

/-- **The difference quotient of the half-space transfer semigroup.**  It is built on the one-sided
semigroup `hsEvolCompletionFun` (zero at negative times), and all limits below are taken along
`𝓝[>] 0`, so no negative time is ever used. -/
def hsDiffQuot (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) (τ : ℝ) (z : Hhalf Λ) : Hhalf Λ :=
  τ⁻¹ • (hsEvolCompletionFun Λ hT hinv τ z - z)

/-- The difference quotient vanishes at the origin. -/
theorem hsDiffQuot_zero (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) (τ : ℝ) : hsDiffQuot Λ hT hinv τ (0 : Hhalf Λ) = 0 := by
  simp [hsDiffQuot]

/-- The difference quotient is additive in the vector. -/
theorem hsDiffQuot_add (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) (τ : ℝ) (z w : Hhalf Λ) :
    hsDiffQuot Λ hT hinv τ (z + w) = hsDiffQuot Λ hT hinv τ z + hsDiffQuot Λ hT hinv τ w := by
  simp only [hsDiffQuot, map_add]
  rw [show hsEvolCompletionFun Λ hT hinv τ z + hsEvolCompletionFun Λ hT hinv τ w - (z + w)
      = (hsEvolCompletionFun Λ hT hinv τ z - z)
        + (hsEvolCompletionFun Λ hT hinv τ w - w) from by abel,
    smul_add]

/-- The difference quotient is homogeneous in the vector. -/
theorem hsDiffQuot_smul (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) (τ : ℝ) (c : ℝ) (z : Hhalf Λ) :
    hsDiffQuot Λ hT hinv τ (c • z) = c • hsDiffQuot Λ hT hinv τ z := by
  rw [hsDiffQuot, hsDiffQuot, map_smul, ← smul_sub, smul_comm τ⁻¹ c]

/-- The semigroup is the identity at time `0`, as a vector identity. -/
theorem hsEvolCompletionFun_zero (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) (z : Hhalf Λ) :
    hsEvolCompletionFun Λ hT hinv 0 z = z := by
  rw [hsEvolCompletionFun_of_nonneg Λ le_rfl, hsEvolCompletion_zero]
  simp

/-! ## Continuity of the orbit on `[0, ∞)` -/

/-- **Two orbit points**: their distance is at most the distance of `P(|y − s₀|)z` from `z`. -/
theorem dist_hsEvolCompletionFun_le (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) (z : Hhalf Λ) {y s₀ : ℝ}
    (hy : 0 ≤ y) (hs : 0 ≤ s₀) :
    dist (hsEvolCompletionFun Λ hT hinv y z) (hsEvolCompletionFun Λ hT hinv s₀ z)
      ≤ ‖hsEvolCompletionFun Λ hT hinv |y - s₀| z - z‖ := by
  rcases le_total s₀ y with hle | hle
  · have habs : |y - s₀| = y - s₀ := abs_of_nonneg (by linarith)
    have hcomp : hsEvolCompletionFun Λ hT hinv y z
        = hsEvolCompletionFun Λ hT hinv s₀
            (hsEvolCompletionFun Λ hT hinv (y - s₀) z) := by
      have hc := hsEvolCompletionFun_comp Λ hT hinv hs
        (show (0 : ℝ) ≤ y - s₀ by linarith) z
      rw [show s₀ + (y - s₀) = y from by ring] at hc
      exact hc.symm
    rw [hcomp, habs, dist_eq_norm, ← map_sub]
    exact hsEvolCompletionFun_contractive Λ hT hinv s₀ _
  · have habs : |y - s₀| = s₀ - y := by
      rw [abs_of_nonpos (by linarith)]
      ring
    have hcomp : hsEvolCompletionFun Λ hT hinv s₀ z
        = hsEvolCompletionFun Λ hT hinv y
            (hsEvolCompletionFun Λ hT hinv (s₀ - y) z) := by
      have hc := hsEvolCompletionFun_comp Λ hT hinv hy
        (show (0 : ℝ) ≤ s₀ - y by linarith) z
      rw [show y + (s₀ - y) = s₀ from by ring] at hc
      exact hc.symm
    rw [hcomp, habs, dist_eq_norm, ← map_sub]
    calc ‖hsEvolCompletionFun Λ hT hinv y
          (z - hsEvolCompletionFun Λ hT hinv (s₀ - y) z)‖
        ≤ ‖z - hsEvolCompletionFun Λ hT hinv (s₀ - y) z‖ :=
          hsEvolCompletionFun_contractive Λ hT hinv y _
      _ = ‖hsEvolCompletionFun Λ hT hinv (s₀ - y) z - z‖ := norm_sub_rev _ _

/-- **The orbit is continuous on `[0, ∞)`**, from the distance bound and strong continuity at
`0⁺`. -/
theorem continuousOn_hsEvolCompletionFun (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT)
    (hcont : ∀ F : Observable, F ∈ PositiveTimeAlgebra →
      Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F) (z : Hhalf Λ) :
    ContinuousOn (fun s : ℝ => hsEvolCompletionFun Λ hT hinv s z) (Ici 0) := by
  intro s₀ hs₀
  have hs₀0 : 0 ≤ s₀ := hs₀
  refine Metric.continuousWithinAt_iff.2 fun ε hε => ?_
  have hlim : Tendsto (fun δ : ℝ => ‖hsEvolCompletionFun Λ hT hinv δ z - z‖)
      (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_hsEvolCompletionFun Λ hT hinv hcont z
    have hsub : Tendsto (fun δ : ℝ => hsEvolCompletionFun Λ hT hinv δ z - z) (𝓝[>] 0)
        (𝓝 (z - z)) :=
      h.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ => z) (𝓝[>] (0 : ℝ)) (𝓝 z))
    simpa using hsub.norm
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ‖hsEvolCompletionFun Λ hT hinv δ z - z‖ < ε := by
    have h := Metric.tendsto_nhds.mp hlim ε hε
    filter_upwards [h] with δ hδ
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hδ
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.mem_nhdsWithin_iff.1 hev
  refine ⟨ρ, hρpos, ?_⟩
  intro y hy hyρ
  have hy0 : 0 ≤ y := hy
  rcases eq_or_ne y s₀ with heq | hne
  · subst heq
    simpa using hε
  · have hle := dist_hsEvolCompletionFun_le Λ hT hinv z hy0 hs₀0
    have hsmall : ‖hsEvolCompletionFun Λ hT hinv |y - s₀| z - z‖ < ε := by
      refine hρ ⟨?_, abs_pos.2 (sub_ne_zero.2 hne)⟩
      simpa [Metric.mem_ball, Real.dist_eq, abs_abs] using hyρ
    exact lt_of_le_of_lt hle hsmall

/-- **The orbit is interval-integrable on `[0, b]`** for `b ≥ 0`. -/
theorem intervalIntegrable_hsEvolCompletionFun (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT)
    (hcont : ∀ F : Observable, F ∈ PositiveTimeAlgebra →
      Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    (w : Hhalf Λ) {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable (fun s : ℝ => hsEvolCompletionFun Λ hT hinv s w) volume 0 b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hb]
  exact (continuousOn_hsEvolCompletionFun Λ hT hinv hcont w).mono fun x hx => hx.1

/-! ## The forward-time domain -/

/-- `z` is in the forward-time domain when the difference quotient converges as `τ → 0⁺`. -/
def HsHasGen (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) (z : Hhalf Λ) : Prop :=
  ∃ y : Hhalf Λ, Tendsto (fun τ : ℝ => hsDiffQuot Λ hT hinv τ z) (𝓝[>] 0) (𝓝 y)

/-- The origin is in the forward-time domain, with generator value `0`. -/
theorem hsHasGen_zero (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) : HsHasGen Λ hT hinv (0 : Hhalf Λ) := by
  refine ⟨0, ?_⟩
  simpa only [hsDiffQuot_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : Hhalf Λ)) (𝓝[>] 0) (𝓝 0))

/-- The forward-time domain is closed under addition. -/
theorem hsHasGen_add (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) {z w : Hhalf Λ}
    (hz : HsHasGen Λ hT hinv z) (hw : HsHasGen Λ hT hinv w) :
    HsHasGen Λ hT hinv (z + w) := by
  obtain ⟨y, hy⟩ := hz
  obtain ⟨y', hy'⟩ := hw
  refine ⟨y + y', ?_⟩
  refine (hy.add hy').congr' ?_
  exact Eventually.of_forall fun τ => (hsDiffQuot_add Λ hT hinv τ z w).symm

/-- The forward-time domain is closed under scalar multiplication. -/
theorem hsHasGen_smul (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) (c : ℝ) {z : Hhalf Λ} (hz : HsHasGen Λ hT hinv z) :
    HsHasGen Λ hT hinv (c • z) := by
  obtain ⟨y, hy⟩ := hz
  refine ⟨c • y, ?_⟩
  refine (hy.const_smul c).congr' ?_
  exact Eventually.of_forall fun τ => (hsDiffQuot_smul Λ hT hinv τ c z).symm

/-- **The forward-time domain of the generator**, as a real submodule of `Hhalf`. -/
def hsGenDomain (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) : Submodule ℝ (Hhalf Λ) where
  carrier := {z | HsHasGen Λ hT hinv z}
  add_mem' := fun hz hw => hsHasGen_add Λ hT hinv hz hw
  zero_mem' := hsHasGen_zero Λ hT hinv
  smul_mem' := fun c _ hz => hsHasGen_smul Λ hT hinv c hz

/-- Membership in the forward-time domain is convergence of the quotient at `0⁺`. -/
@[simp]
theorem mem_hsGenDomain (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) (z : Hhalf Λ) :
    z ∈ hsGenDomain Λ hT hinv ↔ HsHasGen Λ hT hinv z :=
  Iff.rfl

/-- The generator's value at a domain point, as a chosen limit. -/
def hsGenValue (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) (z : hsGenDomain Λ hT hinv) : Hhalf Λ :=
  Classical.choose z.2

/-- The defining limit property of `hsGenValue`. -/
theorem hsGenValue_tendsto (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) (z : hsGenDomain Λ hT hinv) :
    Tendsto (fun τ : ℝ => hsDiffQuot Λ hT hinv τ (z : Hhalf Λ)) (𝓝[>] 0)
      (𝓝 (hsGenValue Λ hT hinv z)) :=
  Classical.choose_spec z.2

/-- `hsGenValue` is additive, by uniqueness of limits. -/
theorem hsGenValue_add (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) (z w : hsGenDomain Λ hT hinv) :
    hsGenValue Λ hT hinv (z + w) = hsGenValue Λ hT hinv z + hsGenValue Λ hT hinv w := by
  refine tendsto_nhds_unique (hsGenValue_tendsto Λ hT hinv (z + w)) ?_
  have h : Tendsto (fun τ : ℝ => hsDiffQuot Λ hT hinv τ (z : Hhalf Λ)
      + hsDiffQuot Λ hT hinv τ (w : Hhalf Λ)) (𝓝[>] 0)
      (𝓝 (hsGenValue Λ hT hinv z + hsGenValue Λ hT hinv w)) :=
    (hsGenValue_tendsto Λ hT hinv z).add (hsGenValue_tendsto Λ hT hinv w)
  refine h.congr' ?_
  exact Eventually.of_forall fun τ =>
    (hsDiffQuot_add Λ hT hinv τ (z : Hhalf Λ) (w : Hhalf Λ)).symm

/-- `hsGenValue` is homogeneous, by uniqueness of limits. -/
theorem hsGenValue_smul (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) (c : ℝ)
    (z : hsGenDomain Λ hT hinv) :
    hsGenValue Λ hT hinv (c • z) = c • hsGenValue Λ hT hinv z := by
  refine tendsto_nhds_unique (hsGenValue_tendsto Λ hT hinv (c • z)) ?_
  have h : Tendsto (fun τ : ℝ => c • hsDiffQuot Λ hT hinv τ (z : Hhalf Λ)) (𝓝[>] 0)
      (𝓝 (c • hsGenValue Λ hT hinv z)) := (hsGenValue_tendsto Λ hT hinv z).const_smul c
  refine h.congr' ?_
  exact Eventually.of_forall fun τ => (hsDiffQuot_smul Λ hT hinv τ c (z : Hhalf Λ)).symm

/-- The generator's action as a linear map on its domain. -/
def hsGenFun (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) : hsGenDomain Λ hT hinv →ₗ[ℝ] Hhalf Λ where
  toFun := hsGenValue Λ hT hinv
  map_add' := hsGenValue_add Λ hT hinv
  map_smul' := hsGenValue_smul Λ hT hinv

/-- **The generator of the half-space transfer semigroup.** -/
def hsGenerator (Λ : HalfSpaceState) {T : TimeTranslation} (hT : PreservesPositiveTime T)
    (hinv : HsHinv Λ hT) : Hhalf Λ →ₗ.[ℝ] Hhalf Λ where
  domain := hsGenDomain Λ hT hinv
  toFun := hsGenFun Λ hT hinv

/-- The defining property of the generator. -/
theorem hsGenerator_apply_tendsto (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT)
    (z : (hsGenerator Λ hT hinv).domain) :
    Tendsto (fun τ : ℝ => hsDiffQuot Λ hT hinv τ (z : Hhalf Λ)) (𝓝[>] 0)
      (𝓝 (hsGenerator Λ hT hinv z)) :=
  hsGenValue_tendsto Λ hT hinv z

/-- Uniqueness: any other limit of the difference quotient is the generator's value. -/
theorem hsGenerator_apply_eq_of_tendsto (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT)
    (z : (hsGenerator Λ hT hinv).domain) {y : Hhalf Λ}
    (hy : Tendsto (fun τ : ℝ => hsDiffQuot Λ hT hinv τ (z : Hhalf Λ)) (𝓝[>] 0) (𝓝 y)) :
    hsGenerator Λ hT hinv z = y :=
  tendsto_nhds_unique (hsGenerator_apply_tendsto Λ hT hinv z) hy

/-! ## The right derivative of the orbit -/

/-- **The orbit of a forward-time domain vector has a right derivative at every `t ≥ 0`**, namely
`P(t)(A z)`.  For `h > 0` the semigroup law gives `P(t + h)z − P(t)z = P(t)(P(h)z − z)`, so the
difference quotient of the orbit is the image under the continuous map `P(t)` of the quotient at
`0`. -/
theorem hasDerivWithinAt_hsEvol (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT)
    (z : (hsGenerator Λ hT hinv).domain) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => hsEvolCompletionFun Λ hT hinv s (z : Hhalf Λ))
      (hsEvolCompletionFun Λ hT hinv t (hsGenerator Λ hT hinv z)) (Ioi t) t := by
  have hq : Tendsto
      (fun h : ℝ =>
        h⁻¹ • (hsEvolCompletionFun Λ hT hinv h (z : Hhalf Λ) - (z : Hhalf Λ)))
      (𝓝[>] 0) (𝓝 (hsGenerator Λ hT hinv z)) :=
    hsGenerator_apply_tendsto Λ hT hinv z
  have hpc : Tendsto (hsEvolCompletionFun Λ hT hinv t) (𝓝 (hsGenerator Λ hT hinv z))
      (𝓝 (hsEvolCompletionFun Λ hT hinv t (hsGenerator Λ hT hinv z))) :=
    (hsEvolCompletionFun Λ hT hinv t).continuous.tendsto _
  have hmain : Tendsto
      (fun h : ℝ => hsEvolCompletionFun Λ hT hinv t
        (h⁻¹ • (hsEvolCompletionFun Λ hT hinv h (z : Hhalf Λ) - (z : Hhalf Λ))))
      (𝓝[>] 0) (𝓝 (hsEvolCompletionFun Λ hT hinv t (hsGenerator Λ hT hinv z))) :=
    hpc.comp hq
  have hsub : Tendsto (fun y : ℝ => y - t) (𝓝[Ioi t] t) (𝓝[>] (0 : ℝ)) := by
    have h1 : Tendsto (fun y : ℝ => y - t) (𝓝[Ioi t] t) (𝓝 (0 : ℝ)) := by
      have hcont : Continuous fun y : ℝ => y - t := continuous_id.sub continuous_const
      have h : Tendsto (fun y : ℝ => y - t) (𝓝[Ioi t] t) (𝓝 (t - t)) :=
        hcont.continuousWithinAt
      rwa [sub_self] at h
    change Tendsto (fun y : ℝ => y - t) (𝓝[Ioi t] t) (𝓝 (0 : ℝ) ⊓ 𝓟 (Ioi 0))
    rw [tendsto_inf, tendsto_principal]
    exact ⟨h1, by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact sub_pos.2 (mem_Ioi.mp hy)⟩
  rw [hasDerivWithinAt_iff_tendsto_slope,
    show Ioi t \ {t} = Ioi t from diff_singleton_eq_self (by simp)]
  refine (hmain.comp hsub).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hpos : 0 < y - t := sub_pos.2 (mem_Ioi.mp hy)
  have hcomp : hsEvolCompletionFun Λ hT hinv y (z : Hhalf Λ)
      = hsEvolCompletionFun Λ hT hinv t
          (hsEvolCompletionFun Λ hT hinv (y - t) (z : Hhalf Λ)) := by
    conv_lhs => rw [show y = t + (y - t) from by ring]
    rw [← hsEvolCompletionFun_comp Λ hT hinv ht hpos.le]
  have hslope : slope (fun s : ℝ => hsEvolCompletionFun Λ hT hinv s (z : Hhalf Λ)) t y
      = (y - t)⁻¹ • (hsEvolCompletionFun Λ hT hinv y (z : Hhalf Λ)
        - hsEvolCompletionFun Λ hT hinv t (z : Hhalf Λ)) := by
    rw [slope_def_module]
  rw [hslope, hcomp, ← map_sub, ← map_smul]
  rfl

/-! ## The integral representation, for nonnegative times -/

/-- **The integral representation for the half-space semigroup**: for `τ ≥ 0` and a domain vector,
`∫₀^τ P(s)(A z) ds = P(τ)z − z`.  This is the fundamental theorem of calculus in its
right-derivative form, fed by `hasDerivWithinAt_hsEvol`. -/
theorem hsEvol_sub_eq_integral (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT)
    (hcont : ∀ F : Observable, F ∈ PositiveTimeAlgebra →
      Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    (z : (hsGenerator Λ hT hinv).domain) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∫ s in (0 : ℝ)..τ, hsEvolCompletionFun Λ hT hinv s (hsGenerator Λ hT hinv z)
      = hsEvolCompletionFun Λ hT hinv τ (z : Hhalf Λ) - (z : Hhalf Λ) := by
  have hcurve : ContinuousOn
      (fun s : ℝ => hsEvolCompletionFun Λ hT hinv s (z : Hhalf Λ)) (Icc 0 τ) :=
    (continuousOn_hsEvolCompletionFun Λ hT hinv hcont (z : Hhalf Λ)).mono fun x hx => hx.1
  have hint := intervalIntegrable_hsEvolCompletionFun Λ hT hinv hcont
    (hsGenerator Λ hT hinv z) hτ
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hτ hcurve
    (fun x hx => hasDerivWithinAt_hsEvol Λ hT hinv z x (le_of_lt hx.1)) hint
  simpa [hsEvolCompletionFun_zero Λ hT hinv, ContinuousLinearMap.id_apply] using h

/-! ## Averaging a curve that is right-continuous at `0` -/

/-- **The average converges to the value at `0` from the right.** -/
theorem tendsto_average_hsEvol (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT)
    (hcont : ∀ F : Observable, F ∈ PositiveTimeAlgebra →
      Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    (y : Hhalf Λ) :
    Tendsto (fun τ : ℝ => τ⁻¹ • ∫ s in (0 : ℝ)..τ, hsEvolCompletionFun Λ hT hinv s y)
      (𝓝[>] 0) (𝓝 y) := by
  have hint : ∀ b : ℝ, 0 ≤ b → IntervalIntegrable
      (fun s : ℝ => hsEvolCompletionFun Λ hT hinv s y) volume 0 b :=
    fun b hb => intervalIntegrable_hsEvolCompletionFun Λ hT hinv hcont y hb
  have hsplit : ∀ τ : ℝ, 0 ≤ τ →
      (∫ s in (0 : ℝ)..τ, hsEvolCompletionFun Λ hT hinv s y)
        = (∫ s in (0 : ℝ)..τ, (hsEvolCompletionFun Λ hT hinv s y - y)) + τ • y := by
    intro τ hτ
    have h2 : (∫ s in (0 : ℝ)..τ, hsEvolCompletionFun Λ hT hinv s y)
        = ∫ s in (0 : ℝ)..τ, ((hsEvolCompletionFun Λ hT hinv s y - y) + y) :=
      intervalIntegral.integral_congr fun s _ => by abel
    rw [h2, intervalIntegral.integral_add ((hint τ hτ).sub intervalIntegrable_const)
      intervalIntegrable_const, intervalIntegral.integral_const]
    simp
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖hsEvolCompletionFun Λ hT hinv s y - y‖ < ε / 2 := by
    have h := Metric.tendsto_nhds.mp (tendsto_hsEvolCompletionFun Λ hT hinv hcont y)
      (ε / 2) (by linarith)
    filter_upwards [h] with s hs
    simpa [dist_eq_norm] using hs
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hsmall
  have hevδ : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ < δ := by
    have hball : ∀ᶠ τ in 𝓝 (0 : ℝ), τ < δ := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδpos] with τ hτ
      exact (abs_lt.1 (by simpa [Real.dist_eq] using hτ)).2
    exact hball.filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hevδ] with τ hτ hτδ
  have hτpos : 0 < τ := hτ
  have hdiff : τ⁻¹ • (∫ s in (0 : ℝ)..τ, hsEvolCompletionFun Λ hT hinv s y) - y
      = τ⁻¹ • ∫ s in (0 : ℝ)..τ, (hsEvolCompletionFun Λ hT hinv s y - y) := by
    rw [hsplit τ hτpos.le, smul_add, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hτpos), one_smul, add_sub_cancel_right]
  have hbound : ‖∫ s in (0 : ℝ)..τ, (hsEvolCompletionFun Λ hT hinv s y - y)‖
      ≤ (ε / 2) * |τ| := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / 2) ?_).trans_eq ?_
    · intro s hs
      have hsIoo : s ∈ Ioo (0 : ℝ) δ := by
        rcases Set.mem_uIoc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, lt_of_le_of_lt h2 hτδ⟩
        · exact absurd (lt_trans hτpos h1) (not_lt.2 h2)
      refine le_of_lt (hδsub ⟨?_, hsIoo.1⟩)
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hsIoo.1]
      exact hsIoo.2
    · rw [sub_zero]
  have hdist : dist (τ⁻¹ • (∫ s in (0 : ℝ)..τ, hsEvolCompletionFun Λ hT hinv s y)) y
      = ‖τ⁻¹ • ∫ s in (0 : ℝ)..τ, (hsEvolCompletionFun Λ hT hinv s y - y)‖ := by
    rw [dist_eq_norm, hdiff]
  rw [hdist, norm_smul, Real.norm_eq_abs, abs_inv]
  refine lt_of_le_of_lt ?_ (by linarith : ε / 2 < ε)
  calc |τ|⁻¹ * ‖∫ s in (0 : ℝ)..τ, (hsEvolCompletionFun Λ hT hinv s y - y)‖
      ≤ |τ|⁻¹ * ((ε / 2) * |τ|) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = ε / 2 := by
        rw [mul_comm (ε / 2) |τ|, ← mul_assoc,
          inv_mul_cancel₀ (abs_ne_zero.2 (ne_of_gt hτpos)), one_mul]

/-! ## Closedness, from the one-sided representation -/

/-- **The half-space generator has closed graph**, proved with right derivatives only. -/
theorem hsGenerator_isClosed (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT)
    (hcont : ∀ F : Observable, F ∈ PositiveTimeAlgebra →
      Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F) :
    ∀ (u : ℕ → (hsGenerator Λ hT hinv).domain) {z₀ y : Hhalf Λ},
      Tendsto (fun n => (u n : Hhalf Λ)) atTop (𝓝 z₀) →
      Tendsto (fun n => hsGenerator Λ hT hinv (u n)) atTop (𝓝 y) →
      ∃ h : HsHasGen Λ hT hinv z₀, hsGenerator Λ hT hinv ⟨z₀, h⟩ = y := by
  intro u z₀ y hu hy
  have hmain : ∀ τ : ℝ, 0 ≤ τ →
      hsEvolCompletionFun Λ hT hinv τ z₀ - z₀
        = ∫ s in (0 : ℝ)..τ, hsEvolCompletionFun Λ hT hinv s y := by
    intro τ hτ
    have hleft : Tendsto
        (fun n => hsEvolCompletionFun Λ hT hinv τ (u n) - (u n : Hhalf Λ))
        atTop (𝓝 (hsEvolCompletionFun Λ hT hinv τ z₀ - z₀)) :=
      (((hsEvolCompletionFun Λ hT hinv τ).continuous.tendsto z₀).comp hu).sub hu
    have hlim : Tendsto (fun n => |τ| * ‖hsGenerator Λ hT hinv (u n) - y‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => ‖hsGenerator Λ hT hinv (u n) - y‖) atTop (𝓝 0) := by
        have hsub : Tendsto (fun n => hsGenerator Λ hT hinv (u n) - y) atTop (𝓝 (y - y)) :=
          hy.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y))
        simpa using hsub.norm
      simpa using h1.const_mul |τ|
    have hright : Tendsto
        (fun n => ∫ s in (0 : ℝ)..τ,
          hsEvolCompletionFun Λ hT hinv s (hsGenerator Λ hT hinv (u n)))
        atTop (𝓝 (∫ s in (0 : ℝ)..τ, hsEvolCompletionFun Λ hT hinv s y)) := by
      refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
      have hb : ∀ n,
          ‖(∫ s in (0 : ℝ)..τ,
              hsEvolCompletionFun Λ hT hinv s (hsGenerator Λ hT hinv (u n)))
            - (∫ s in (0 : ℝ)..τ, hsEvolCompletionFun Λ hT hinv s y)‖
            ≤ |τ| * ‖hsGenerator Λ hT hinv (u n) - y‖ := by
        intro n
        rw [← intervalIntegral.integral_sub
          (intervalIntegrable_hsEvolCompletionFun Λ hT hinv hcont _ hτ)
          (intervalIntegrable_hsEvolCompletionFun Λ hT hinv hcont _ hτ)]
        refine (intervalIntegral.norm_integral_le_of_norm_le_const
          (C := ‖hsGenerator Λ hT hinv (u n) - y‖) ?_).trans_eq ?_
        · intro s _
          rw [← map_sub]
          exact hsEvolCompletionFun_contractive Λ hT hinv s _
        · rw [sub_zero, mul_comm]
      rw [Metric.tendsto_atTop] at hlim ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := hlim ε hε
      refine ⟨N, fun n hn => ?_⟩
      have hlt := hN n hn
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))] at hlt
      simpa [Real.dist_eq] using lt_of_le_of_lt (hb n) hlt
    exact tendsto_nhds_unique hleft
      (hright.congr' (Eventually.of_forall fun n =>
        hsEvol_sub_eq_integral Λ hT hinv hcont (u n) τ hτ))
  have hquot : (fun τ : ℝ => hsDiffQuot Λ hT hinv τ z₀)
      =ᶠ[𝓝[>] 0]
        (fun τ : ℝ => τ⁻¹ • ∫ s in (0 : ℝ)..τ, hsEvolCompletionFun Λ hT hinv s y) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    change τ⁻¹ • (hsEvolCompletionFun Λ hT hinv τ z₀ - z₀)
      = τ⁻¹ • ∫ s in (0 : ℝ)..τ, hsEvolCompletionFun Λ hT hinv s y
    rw [hmain τ hτ.le]
  have hlim : Tendsto (fun τ : ℝ => hsDiffQuot Λ hT hinv τ z₀) (𝓝[>] 0) (𝓝 y) :=
    (tendsto_average_hsEvol Λ hT hinv hcont y).congr' hquot.symm
  have hgen : HsHasGen Λ hT hinv z₀ := ⟨y, hlim⟩
  exact ⟨hgen, tendsto_nhds_unique (hsGenValue_tendsto Λ hT hinv ⟨z₀, hgen⟩) hlim⟩

/-! ## Dissipativity: the one-sided substitute for symmetry -/

/-- **The half-space generator is dissipative**: `⟪A z, z⟫ ≤ 0` throughout its domain.  `P(τ)` is a
contraction for every `τ ≥ 0`, so `⟪P(τ)z, z⟫ ≤ ⟪z, z⟫` by Cauchy–Schwarz, and the difference
quotient of this inequality converges to `⟪A z, z⟫` along `𝓝[>] 0`. -/
theorem hsGenerator_inner_le_zero (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT)
    (z : (hsGenerator Λ hT hinv).domain) :
    ⟪hsGenerator Λ hT hinv z, (z : Hhalf Λ)⟫ ≤ 0 := by
  have hq : Tendsto (fun τ : ℝ => hsDiffQuot Λ hT hinv τ (z : Hhalf Λ)) (𝓝[>] 0)
      (𝓝 (hsGenerator Λ hT hinv z)) :=
    hsGenerator_apply_tendsto Λ hT hinv z
  have hinner : Tendsto (fun τ : ℝ => ⟪hsDiffQuot Λ hT hinv τ (z : Hhalf Λ), (z : Hhalf Λ)⟫)
      (𝓝[>] 0) (𝓝 ⟪hsGenerator Λ hT hinv z, (z : Hhalf Λ)⟫) :=
    hq.inner tendsto_const_nhds
  refine le_of_tendsto_of_tendsto hinner tendsto_const_nhds ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hquot : ⟪hsDiffQuot Λ hT hinv τ (z : Hhalf Λ), (z : Hhalf Λ)⟫
      = τ⁻¹ * (⟪hsEvolCompletionFun Λ hT hinv τ (z : Hhalf Λ), (z : Hhalf Λ)⟫
        - ⟪(z : Hhalf Λ), (z : Hhalf Λ)⟫) := by
    rw [hsDiffQuot, real_inner_smul_left, inner_sub_left]
  rw [hquot]
  refine mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (le_of_lt hτ)) (sub_nonpos.2 ?_)
  calc ⟪hsEvolCompletionFun Λ hT hinv τ (z : Hhalf Λ), (z : Hhalf Λ)⟫
      ≤ ‖hsEvolCompletionFun Λ hT hinv τ (z : Hhalf Λ)‖ * ‖(z : Hhalf Λ)‖ :=
        real_inner_le_norm _ _
    _ ≤ ‖(z : Hhalf Λ)‖ * ‖(z : Hhalf Λ)‖ :=
        mul_le_mul_of_nonneg_right (hsEvolCompletionFun_contractive Λ hT hinv τ _)
          (norm_nonneg _)
    _ = ⟪(z : Hhalf Λ), (z : Hhalf Λ)⟫ := (real_inner_self_eq_norm_mul_norm _).symm

/-! ## The a priori estimate for the resolvent -/

/-- **The a priori resolvent bound**: for `λ > 0` and a domain vector, `λ‖z‖ ≤ ‖λ z − A z‖`.
Expanding `‖λ z − A z‖²` and using only dissipativity, the last two terms are nonnegative. -/
theorem hsGenerator_resolvent_bound (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT)
    (z : (hsGenerator Λ hT hinv).domain) {lam : ℝ} (hlam : 0 < lam) :
    lam * ‖(z : Hhalf Λ)‖ ≤ ‖lam • (z : Hhalf Λ) - hsGenerator Λ hT hinv z‖ := by
  have hdis : ⟪hsGenerator Λ hT hinv z, (z : Hhalf Λ)⟫ ≤ 0 :=
    hsGenerator_inner_le_zero Λ hT hinv z
  have hprod : lam * ⟪hsGenerator Λ hT hinv z, (z : Hhalf Λ)⟫ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlam.le hdis
  have hcross : ⟪lam • (z : Hhalf Λ), hsGenerator Λ hT hinv z⟫
      = lam * ⟪hsGenerator Λ hT hinv z, (z : Hhalf Λ)⟫ := by
    rw [real_inner_smul_left, real_inner_comm (z : Hhalf Λ) (hsGenerator Λ hT hinv z)]
  have hnorm : ‖lam • (z : Hhalf Λ)‖ = lam * ‖(z : Hhalf Λ)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
  have hexp : ‖lam • (z : Hhalf Λ) - hsGenerator Λ hT hinv z‖ ^ 2
      = (lam * ‖(z : Hhalf Λ)‖) ^ 2
        - 2 * (lam * ⟪hsGenerator Λ hT hinv z, (z : Hhalf Λ)⟫)
        + ‖hsGenerator Λ hT hinv z‖ ^ 2 := by
    rw [norm_sub_sq_real, hcross, hnorm, mul_pow]
  have hsq : (lam * ‖(z : Hhalf Λ)‖) ^ 2
      ≤ ‖lam • (z : Hhalf Λ) - hsGenerator Λ hT hinv z‖ ^ 2 := by
    rw [hexp]
    nlinarith [sq_nonneg ‖hsGenerator Λ hT hinv z‖]
  have hnonneg : 0 ≤ lam * ‖(z : Hhalf Λ)‖ := mul_nonneg hlam.le (norm_nonneg _)
  have h' : |lam * ‖(z : Hhalf Λ)‖|
      ≤ |‖lam • (z : Hhalf Λ) - hsGenerator Λ hT hinv z‖| :=
    sq_le_sq.mp hsq
  rwa [abs_of_nonneg hnonneg, abs_of_nonneg (norm_nonneg _)] at h'

/-- **`λ − A` is injective on the domain** for `λ > 0`, from the a priori bound. -/
theorem hsGenerator_resolvent_injective (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) {lam : ℝ} (hlam : 0 < lam) :
    Function.Injective fun z : (hsGenerator Λ hT hinv).domain =>
      lam • (z : Hhalf Λ) - hsGenerator Λ hT hinv z := by
  intro z w hzw
  have hzw' : lam • (z : Hhalf Λ) - hsGenerator Λ hT hinv z
      = lam • (w : Hhalf Λ) - hsGenerator Λ hT hinv w := hzw
  have hzero : lam • ((z : Hhalf Λ) - (w : Hhalf Λ))
      - hsGenerator Λ hT hinv (z - w) = 0 := by
    have hval : hsGenerator Λ hT hinv (z - w)
        = hsGenerator Λ hT hinv z - hsGenerator Λ hT hinv w :=
      map_sub (hsGenFun Λ hT hinv) z w
    calc lam • ((z : Hhalf Λ) - (w : Hhalf Λ))
          - hsGenerator Λ hT hinv (z - w)
        = (lam • (z : Hhalf Λ) - hsGenerator Λ hT hinv z)
            - (lam • (w : Hhalf Λ) - hsGenerator Λ hT hinv w) := by
          rw [hval, smul_sub]
          abel
      _ = 0 := by rw [hzw', sub_self]
  have hbound := hsGenerator_resolvent_bound Λ hT hinv
    (z - w : (hsGenerator Λ hT hinv).domain) hlam
  have hnorm : ((z - w : (hsGenerator Λ hT hinv).domain) : Hhalf Λ) = 0 := by
    have h1 : lam * ‖((z - w : (hsGenerator Λ hT hinv).domain) : Hhalf Λ)‖ = 0 :=
      le_antisymm (by simpa [hzero] using hbound)
        (mul_nonneg hlam.le (norm_nonneg _))
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hlam.ne'
    · exact norm_eq_zero.1 h
  exact sub_eq_zero.1 (Subtype.coe_injective hnorm)

/-! ## The identification `H = −A` -/

/-- **The difference quotient is the slope of the orbit at `0`.**  Hence a right derivative of the
orbit at `0⁺` is exactly a limit of the difference quotient. -/
theorem tendsto_hsDiffQuot_of_hasDerivWithinAt (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) {z y : Hhalf Λ}
    (hy : HasDerivWithinAt (fun τ : ℝ => hsEvolCompletionFun Λ hT hinv τ z) y (Ioi 0) 0) :
    Tendsto (fun τ : ℝ => hsDiffQuot Λ hT hinv τ z) (𝓝[>] 0) (𝓝 y) := by
  have h := (hasDerivWithinAt_iff_tendsto_slope.1 hy)
  rw [show Ioi (0 : ℝ) \ {0} = Ioi 0 from diff_singleton_eq_self (by simp)] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  rw [slope_def_module, hsEvolCompletionFun_zero Λ hT hinv, sub_zero]
  rfl

/-- **A right derivative of the orbit at `0⁺` is a generator value.**  If the orbit of `z` has
right derivative `y` at `0`, then `z` is in the domain and `A z = y`. -/
theorem hsHasGen_of_hasDerivWithinAt (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) {z y : Hhalf Λ}
    (hy : HasDerivWithinAt (fun τ : ℝ => hsEvolCompletionFun Λ hT hinv τ z) y (Ioi 0) 0) :
    HsHasGen Λ hT hinv z :=
  ⟨y, tendsto_hsDiffQuot_of_hasDerivWithinAt Λ hT hinv hy⟩

/-- **`z` is in the domain of the generator whenever the orbit has a right derivative at `0⁺`.**
In particular, a semigroup that is the flow of a bounded operator has all of `Hhalf` in the
domain. -/
theorem hsGenDomain_eq_top_of_hasDerivWithinAt (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) (y : Hhalf Λ → Hhalf Λ)
    (hderiv : ∀ z : Hhalf Λ,
      HasDerivWithinAt (fun τ : ℝ => hsEvolCompletionFun Λ hT hinv τ z) (y z) (Ioi 0) 0) :
    hsGenDomain Λ hT hinv = ⊤ := by
  refine top_unique fun z _ => ?_
  exact hsHasGen_of_hasDerivWithinAt Λ hT hinv (hderiv z)

/-- **The self-adjoint Hamiltonian is `H = −A`.**

If the half-space semigroup is the flow of `H` — the local form of `P(τ) = e^{−τH}`, namely that
the orbit of every vector has right derivative `−H z` at `0⁺` — then the generator of the semigroup
is `−H`: the domain is all of `Hhalf` and `A z = −H z`.  The hypothesis `hH` records that `H` is
the self-adjoint Hamiltonian the reconstruction is supposed to produce; the *equation* `A = −H`
does not need it, and is proved without it. -/
theorem hsGenerator_eq_neg (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) (H : Hhalf Λ →L[ℝ] Hhalf Λ)
    (_hH : IsSelfAdjoint H)
    (hflow : ∀ z : Hhalf Λ,
      HasDerivWithinAt (fun τ : ℝ => hsEvolCompletionFun Λ hT hinv τ z) (-(H z)) (Ioi 0) 0) :
    ∀ z : Hhalf Λ, ∃ h : HsHasGen Λ hT hinv z,
      hsGenerator Λ hT hinv ⟨z, h⟩ = -H z := by
  intro z
  have hz := hsHasGen_of_hasDerivWithinAt Λ hT hinv (hflow z)
  exact ⟨hz, hsGenerator_apply_eq_of_tendsto Λ hT hinv ⟨z, hz⟩
    (tendsto_hsDiffQuot_of_hasDerivWithinAt Λ hT hinv (hflow z))⟩

/-- **Matrix elements of the identification**: with `P(τ)` the flow of `H`, `⟪A z, z⟫ = −⟪H z, z⟫`.
Since a self-adjoint nonnegative `H` has `⟪H z, z⟫ ≥ 0`, this is the exact sense in which
dissipativity of `A` is the Wick-rotated shadow of positivity of `H`. -/
theorem hsGenerator_inner_eq_neg (Λ : HalfSpaceState) {T : TimeTranslation}
    (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT) (H : Hhalf Λ →L[ℝ] Hhalf Λ)
    (hflow : ∀ z : Hhalf Λ,
      HasDerivWithinAt (fun τ : ℝ => hsEvolCompletionFun Λ hT hinv τ z) (-(H z)) (Ioi 0) 0)
    (z : Hhalf Λ) :
    ⟪hsGenerator Λ hT hinv
        ⟨z, hsHasGen_of_hasDerivWithinAt Λ hT hinv (hflow z)⟩, z⟫ = -⟪H z, z⟫ := by
  have hgen : hsGenerator Λ hT hinv ⟨z, hsHasGen_of_hasDerivWithinAt Λ hT hinv (hflow z)⟩
      = -H z :=
    hsGenerator_apply_eq_of_tendsto Λ hT hinv _
      (tendsto_hsDiffQuot_of_hasDerivWithinAt Λ hT hinv (hflow z))
  rw [hgen, inner_neg_left]

end

end BookProof.OSReconstruction
