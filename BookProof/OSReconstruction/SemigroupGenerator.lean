import Mathlib
import BookProof.OSReconstruction.TransferSemigroupRight

/-!
# The generator of the transfer *semigroup*, on the forward-time semigroup

`OSReconstruction.Generator` defines the generator through difference quotients converging along the
*punctured* filter `𝓝[≠] 0`, and `OSReconstruction.GeneratorClosed` proves it closed through the
fundamental theorem of calculus applied to the orbit `s ↦ P(s)z`, whose derivative `P(s)(A z)` is a
two-sided derivative at every real `s`.

Both choices are wrong for a Euclidean transfer matrix, which exists only for `τ ≥ 0`.  On that side
the orbit has a right derivative at interior points but no left derivative (`P(t + h) = P(t)P(h)`
needs `h ≥ 0`), and a limit along `𝓝[>] 0` does **not** upgrade to `𝓝[≠] 0`: there is no left-hand
information to supply.  So the forward-time generator needs its own domain, and this module builds
it on the one-sided semigroup of `OSReconstruction.TransferSemigroupRight`, together with the
closedness argument that goes with it:

* `diffQuot` — the difference quotient `τ⁻¹ • (P(τ)z − z)`, built on
  `physEvolCompletionRightFun` and typed with the forward hypothesis `HinvRight` (`0 ≤ τ` only).
  This is the module's `diffQuot`; the *group-level* quotient of `Generator` is
  `Generator.diffQuotGroup`, and it is the only one that needs negative times;
* `HasGenRight`, `genDomainRight`, `generatorRight` — the same construction as `HasGen`,
  `genDomain` and `generator` of `Generator`, with `𝓝[>] 0` in place of `𝓝[≠] 0` and `HinvRight` in
  place of the two-sided hypothesis.  Linearity of the difference quotient is filter-independent,
  and the limits are unique, so the proofs are the same;
* `hasDerivWithinAt_physEvolRight` — for `t ≥ 0` the orbit has the *right* derivative `P(t)(A z)`
  within `Ioi t`: for `h > 0` the quotient of the translated vector is the translate of the
  quotient, `h⁻¹ • (P(t+h)z − P(t)z) = P(t)(h⁻¹ • (P(h)z − z))`;
* `physEvol_sub_eq_integral_right` — `P(τ)z − z = ∫₀^τ P(s)(A z) ds` for `τ ≥ 0`, from the
  right-derivative form of the fundamental theorem of calculus
  (`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`), with the continuity of the orbit on
  `[0, τ]` supplied by `continuousOn_physEvolCompletionRightFun` — one-sided, not by shifting by a
  negative time;
* `tendsto_average_physEvol_right` — `τ⁻¹ • ∫₀^τ P(s)y ds → y` as `τ → 0⁺`, from strong continuity
  at `0⁺` and contractivity;
* `generatorRight_isClosed` — the graph of `generatorRight` is closed;
* `generatorRight_inner_le_zero` — the generator is *dissipative*: `⟪A z, z⟫ ≤ 0` on its domain,
  the one-sided substitute for symmetry, forced by contractivity alone;
* `generatorRight_resolvent_bound` — the a priori estimate `lam‖z‖ ≤ ‖lam z − A z‖` for `lam > 0`,
  obtained by expanding `‖lam z − A z‖²` and dropping the nonnegative term `−2lam⟪A z, z⟫`;
* `generatorRight_resolvent_injective` — consequently `lam − A` is injective on the domain.  This is
  the *estimate* half of Lumer–Phillips; surjectivity onto `ℋ` (a range condition on `lam − A`) is
  a separate matter and is not proved here.

## Boundary

Every definition in this module takes `hinv : HinvRight Λ T`, i.e. contractivity at nonnegative
times only, and every proof uses the one-sided semigroup: the orbit derivative is a right
derivative at `t ≥ 0`, the integrals run over `[0, τ]`, and continuity of the orbit is
`ContinuousOn … (Ici 0)` rather than global continuity.

Two layers of `OSReconstruction` still carry the two-sided hypothesis, and neither can be made
one-sided without changing its subject:

* `HilbertSpace`'s `physEvol` / `physEvolCompletion` and `Generator`'s `diffQuotGroup` /
  `HasGen` / `genDomain` / `generator` describe the *group-level* transfer family `P : ℝ → B(ℋ)`.
  Under the forward hypothesis that object does not exist for `τ < 0` (there `P(τ)` would have to be
  `e^{τH}`, unbounded), so a definition of it cannot be typed with `HinvRight`;
* `TransferSelfAdjoint` is about that hypothesis on purpose: its theorem is that a family
  contractive at every real time and self-adjoint is trivial.  It needs the negative half, and
  dropping it would change the theorem.

What the forward theory needs — the domain, the generator, closedness, dissipativity, the a priori
estimate — is all in this module, and none of it takes the two-sided hypothesis.

## Self-adjointness is not what fails here

The degeneracy in `TransferSelfAdjoint` concerns *Euclidean* time: a family `P(τ)`, `τ ∈ ℝ`,
that is contractive **and** self-adjoint at every real `τ` and obeys the group law must be
trivial.  It says nothing against the Hamiltonian.  In real time the 4d Hamiltonian is
self-adjoint -- positivity plus essential self-adjointness (Faris–Lavine, or the Friedrichs
extension), with the unitary flow by Stone's theorem; in this corpus that is
`qgOuterFock_esa`, `smFockHam_esa` and `exists_stone_flow_of_esa`, acting on the nested Fock
space whose sector operators are inner Hamiltonians sandwiched between outer creation and
annihilation (`sandwich`, `secHam_matrix_element`).  Euclidean time is the Wick rotation:
`P(τ) = e^{−τH}` with `H ≥ 0` self-adjoint, so `A = −H` and `⟪A z, z⟫ = −⟪H z, z⟫ ≤ 0`.
Dissipativity (`generatorRight_inner_le_zero`) is the Wick-rotated shadow of positivity, not a
substitute for symmetry of `H`.  The range condition behind Lumer–Phillips,
`ran(λ − A) = ℋ`, is `ran(λ + H) = ℋ`, which holds for `λ > 0` once `H ≥ 0` is self-adjoint
(the a priori estimate below is `‖(λ + H)⁻¹‖ ≤ 1/λ`).  What this chapter does not yet do is
identify the abstract `ℋ` with the nested Fock space and derive `P(τ) = e^{−τH}` from the OS
axioms; neither of those is a statement about self-adjointness of `H`.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity
open Filter MeasureTheory Set
open scoped Topology RealInnerProductSpace Interval

noncomputable section

/-! ## The forward-time difference quotient -/

/-- **The difference quotient of the transfer semigroup at nonnegative time.**  It is built on the
one-sided semigroup, so the hypothesis is `HinvRight` and no negative time appears. -/
def diffQuot (hinv : HinvRight Λ T) (τ : ℝ) (z : Hphys Λ) : Hphys Λ :=
  τ⁻¹ • (physEvolCompletionRightFun hinv τ z - z)

/-- The difference quotient vanishes at the origin. -/
theorem diffQuot_zero (hinv : HinvRight Λ T) (τ : ℝ) : diffQuot hinv τ (0 : Hphys Λ) = 0 := by
  simp [diffQuot]

/-- The difference quotient is additive in the vector. -/
theorem diffQuot_add (hinv : HinvRight Λ T) (τ : ℝ) (z w : Hphys Λ) :
    diffQuot hinv τ (z + w) = diffQuot hinv τ z + diffQuot hinv τ w := by
  simp only [diffQuot, map_add]
  rw [show physEvolCompletionRightFun hinv τ z + physEvolCompletionRightFun hinv τ w - (z + w)
      = (physEvolCompletionRightFun hinv τ z - z)
        + (physEvolCompletionRightFun hinv τ w - w) from by abel,
    smul_add]

/-- The difference quotient is homogeneous in the vector. -/
theorem diffQuot_smul (hinv : HinvRight Λ T) (τ : ℝ) (c : ℝ) (z : Hphys Λ) :
    diffQuot hinv τ (c • z) = c • diffQuot hinv τ z := by
  rw [diffQuot, diffQuot, map_smul, ← smul_sub, smul_comm τ⁻¹ c]

/-- **The orbit is integrable on `[0, b]`** for `b ≥ 0`: continuity of the orbit on `[0, ∞)` gives
`ContinuousOn … (uIcc 0 b)`, hence interval integrability. -/
theorem intervalIntegrable_physEvolCompletionRightFun (hinv : HinvRight Λ T)
    (hcont : ∀ F : Observable, Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    (w : Hphys Λ) {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable (fun s : ℝ => physEvolCompletionRightFun hinv s w) volume 0 b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hb]
  exact (continuousOn_physEvolCompletionRightFun hinv hcont w).mono fun x hx => hx.1

/-! ## The forward-time domain -/

/-- `z` is in the forward-time domain when the difference quotient converges as `τ → 0⁺`. -/
def HasGenRight (hinv : HinvRight Λ T) (z : Hphys Λ) : Prop :=
  ∃ y : Hphys Λ, Tendsto (fun τ : ℝ => diffQuot hinv τ z) (𝓝[>] 0) (𝓝 y)

/-- The origin is in the forward-time domain, with generator value `0`. -/
theorem hasGenRight_zero (hinv : HinvRight Λ T) : HasGenRight hinv (0 : Hphys Λ) := by
  refine ⟨0, ?_⟩
  simpa only [diffQuot_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : Hphys Λ)) (𝓝[>] 0) (𝓝 0))

/-- The forward-time domain is closed under addition. -/
theorem hasGenRight_add (hinv : HinvRight Λ T) {z w : Hphys Λ}
    (hz : HasGenRight hinv z) (hw : HasGenRight hinv w) : HasGenRight hinv (z + w) := by
  obtain ⟨y, hy⟩ := hz
  obtain ⟨y', hy'⟩ := hw
  refine ⟨y + y', ?_⟩
  refine (hy.add hy').congr' ?_
  exact Eventually.of_forall fun τ => (diffQuot_add hinv τ z w).symm

/-- The forward-time domain is closed under scalar multiplication. -/
theorem hasGenRight_smul (hinv : HinvRight Λ T) (c : ℝ) {z : Hphys Λ}
    (hz : HasGenRight hinv z) : HasGenRight hinv (c • z) := by
  obtain ⟨y, hy⟩ := hz
  refine ⟨c • y, ?_⟩
  refine (hy.const_smul c).congr' ?_
  exact Eventually.of_forall fun τ => (diffQuot_smul hinv τ c z).symm

/-- **The forward-time domain of the generator** as a real submodule of `ℋ`. -/
def genDomainRight (hinv : HinvRight Λ T) : Submodule ℝ (Hphys Λ) where
  carrier := {z | HasGenRight hinv z}
  add_mem' := fun hz hw => hasGenRight_add hinv hz hw
  zero_mem' := hasGenRight_zero hinv
  smul_mem' := fun c _ hz => hasGenRight_smul hinv c hz

/-- Membership in the forward-time domain is convergence of the quotient at `0⁺`. -/
@[simp]
theorem mem_genDomainRight (hinv : HinvRight Λ T) (z : Hphys Λ) :
    z ∈ genDomainRight hinv ↔ HasGenRight hinv z :=
  Iff.rfl

/-- The forward-time generator's value at a domain point, as a chosen limit. -/
def genValueRight (hinv : HinvRight Λ T) (z : genDomainRight hinv) : Hphys Λ :=
  Classical.choose z.2

/-- The defining limit property of `genValueRight`. -/
theorem genValueRight_tendsto (hinv : HinvRight Λ T) (z : genDomainRight hinv) :
    Tendsto (fun τ : ℝ => diffQuot hinv τ (z : Hphys Λ)) (𝓝[>] 0)
      (𝓝 (genValueRight hinv z)) :=
  Classical.choose_spec z.2

/-- `genValueRight` is additive, by uniqueness of limits. -/
theorem genValueRight_add (hinv : HinvRight Λ T) (z w : genDomainRight hinv) :
    genValueRight hinv (z + w) = genValueRight hinv z + genValueRight hinv w := by
  refine tendsto_nhds_unique (genValueRight_tendsto hinv (z + w)) ?_
  have h : Tendsto (fun τ : ℝ => diffQuot hinv τ (z : Hphys Λ)
      + diffQuot hinv τ (w : Hphys Λ)) (𝓝[>] 0)
      (𝓝 (genValueRight hinv z + genValueRight hinv w)) :=
    (genValueRight_tendsto hinv z).add (genValueRight_tendsto hinv w)
  refine h.congr' ?_
  exact Eventually.of_forall fun τ =>
    (diffQuot_add hinv τ (z : Hphys Λ) (w : Hphys Λ)).symm

/-- `genValueRight` is homogeneous, by uniqueness of limits. -/
theorem genValueRight_smul (hinv : HinvRight Λ T) (c : ℝ) (z : genDomainRight hinv) :
    genValueRight hinv (c • z) = c • genValueRight hinv z := by
  refine tendsto_nhds_unique (genValueRight_tendsto hinv (c • z)) ?_
  have h : Tendsto (fun τ : ℝ => c • diffQuot hinv τ (z : Hphys Λ)) (𝓝[>] 0)
      (𝓝 (c • genValueRight hinv z)) := (genValueRight_tendsto hinv z).const_smul c
  refine h.congr' ?_
  exact Eventually.of_forall fun τ => (diffQuot_smul hinv τ c (z : Hphys Λ)).symm

/-- The forward-time generator's action as a linear map on its domain. -/
def genFunRight (hinv : HinvRight Λ T) : genDomainRight hinv →ₗ[ℝ] Hphys Λ where
  toFun := genValueRight hinv
  map_add' := genValueRight_add hinv
  map_smul' := genValueRight_smul hinv

/-- **The generator of the forward-time transfer semigroup.** -/
def generatorRight (hinv : HinvRight Λ T) : Hphys Λ →ₗ.[ℝ] Hphys Λ where
  domain := genDomainRight hinv
  toFun := genFunRight hinv

/-- The defining property of the forward-time generator. -/
theorem generatorRight_apply_tendsto (hinv : HinvRight Λ T)
    (z : (generatorRight hinv).domain) :
    Tendsto (fun τ : ℝ => diffQuot hinv τ (z : Hphys Λ)) (𝓝[>] 0)
      (𝓝 (generatorRight hinv z)) :=
  genValueRight_tendsto hinv z

/-- Uniqueness: any other limit of the difference quotient is the generator's value. -/
theorem generatorRight_apply_eq_of_tendsto (hinv : HinvRight Λ T) (z : (generatorRight hinv).domain)
    {y : Hphys Λ} (hy : Tendsto (fun τ : ℝ => diffQuot hinv τ (z : Hphys Λ)) (𝓝[>] 0) (𝓝 y)) :
    generatorRight hinv z = y :=
  tendsto_nhds_unique (generatorRight_apply_tendsto hinv z) hy

/-! ## The right derivative of the orbit -/

/-- **The orbit of a forward-time domain vector has a right derivative at every `t ≥ 0`**, namely
`P(t)(A z)`.

For `h > 0` the semigroup law gives `P(t + h)z − P(t)z = P(t)(P(h)z − z)`, so the difference
quotient of the orbit is the image under the continuous map `P(t)` of the difference quotient at
`0`, which converges to `A z` along `𝓝[>] 0`.  No left derivative is involved, and no negative time
appears: the hypothesis `0 ≤ t` is what makes the semigroup law applicable. -/
theorem hasDerivWithinAt_physEvolRight (hinv : HinvRight Λ T)
    (z : (generatorRight hinv).domain) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => physEvolCompletionRightFun hinv s (z : Hphys Λ))
      (physEvolCompletionRightFun hinv t (generatorRight hinv z)) (Ioi t) t := by
  have hq : Tendsto
      (fun h : ℝ => h⁻¹ • (physEvolCompletionRightFun hinv h (z : Hphys Λ) - (z : Hphys Λ)))
      (𝓝[>] 0) (𝓝 (generatorRight hinv z)) :=
    generatorRight_apply_tendsto hinv z
  have hpc : Tendsto (physEvolCompletionRightFun hinv t) (𝓝 (generatorRight hinv z))
      (𝓝 (physEvolCompletionRightFun hinv t (generatorRight hinv z))) :=
    (physEvolCompletionRightFun hinv t).continuous.tendsto _
  have hmain : Tendsto
      (fun h : ℝ => physEvolCompletionRightFun hinv t
        (h⁻¹ • (physEvolCompletionRightFun hinv h (z : Hphys Λ) - (z : Hphys Λ))))
      (𝓝[>] 0) (𝓝 (physEvolCompletionRightFun hinv t (generatorRight hinv z))) :=
    hpc.comp hq
  -- reindex along `h ↦ h - t`, which sends `𝓝[Ioi t] t` to `𝓝[>] 0`
  have hsub : Tendsto (fun y : ℝ => y - t) (𝓝[Ioi t] t) (𝓝[>] (0 : ℝ)) := by
    have h1 : Tendsto (fun y : ℝ => y - t) (𝓝[Ioi t] t) (𝓝 (0 : ℝ)) := by
      have hcont : Continuous fun y : ℝ => y - t := continuous_id.sub continuous_const
      have h : Tendsto (fun y : ℝ => y - t) (𝓝[Ioi t] t) (𝓝 (t - t)) := hcont.continuousWithinAt
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
  have hcomp : physEvolCompletionRightFun hinv y (z : Hphys Λ)
      = physEvolCompletionRightFun hinv t
          (physEvolCompletionRightFun hinv (y - t) (z : Hphys Λ)) := by
    conv_lhs => rw [show y = t + (y - t) from by ring]
    rw [← physEvolCompletionRightFun_comp hinv ht hpos.le]
  have hslope : slope (fun s : ℝ => physEvolCompletionRightFun hinv s (z : Hphys Λ)) t y
      = (y - t)⁻¹ • (physEvolCompletionRightFun hinv y (z : Hphys Λ)
        - physEvolCompletionRightFun hinv t (z : Hphys Λ)) := by
    rw [slope_def_module]
  rw [hslope, hcomp, ← map_sub, ← map_smul]
  rfl

/-! ## The integral representation, for nonnegative times -/

/-- **The integral representation for a one-sided semigroup**: for `τ ≥ 0` and a domain vector,
`∫₀^τ P(s)(A z) ds = P(τ)z − z`.

This is the fundamental theorem of calculus in its right-derivative form, fed by
`hasDerivWithinAt_physEvolRight`.  Only interior right derivatives and continuity on `[0, τ]` are
required, the latter supplied by `continuousOn_physEvolCompletionRightFun`, so no left derivative
of the orbit is ever taken. -/
theorem physEvol_sub_eq_integral_right (hinv : HinvRight Λ T)
    (hcont : ∀ F : Observable, Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    (z : (generatorRight hinv).domain) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∫ s in (0 : ℝ)..τ, physEvolCompletionRightFun hinv s (generatorRight hinv z)
      = physEvolCompletionRightFun hinv τ (z : Hphys Λ) - (z : Hphys Λ) := by
  have hcurve : ContinuousOn
      (fun s : ℝ => physEvolCompletionRightFun hinv s (z : Hphys Λ)) (Icc 0 τ) :=
    (continuousOn_physEvolCompletionRightFun hinv hcont (z : Hphys Λ)).mono fun x hx => hx.1
  have hint := intervalIntegrable_physEvolCompletionRightFun hinv hcont
    (generatorRight hinv z) hτ
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hτ hcurve
    (fun x hx => hasDerivWithinAt_physEvolRight hinv z x (le_of_lt hx.1)) hint
  simpa [physEvolCompletionRightFun_zero, ContinuousLinearMap.id_apply] using h

/-! ## Averaging a curve that is right-continuous at `0` -/

/-- **The average converges to the value at `0` from the right.**  Strong continuity at `0⁺` gives
`‖P(s)y − y‖ < ε/2` on `(0, δ)`, and the average of `P(·)y − y` over `(0, τ]` is then bounded by
`ε/2` for `τ < δ`, by the norm bound for the vector-valued integral. -/
theorem tendsto_average_physEvol_right (hinv : HinvRight Λ T)
    (hcont : ∀ F : Observable, Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    (y : Hphys Λ) :
    Tendsto (fun τ : ℝ => τ⁻¹ • ∫ s in (0 : ℝ)..τ, physEvolCompletionRightFun hinv s y)
      (𝓝[>] 0) (𝓝 y) := by
  have hint : ∀ b : ℝ, 0 ≤ b → IntervalIntegrable
      (fun s : ℝ => physEvolCompletionRightFun hinv s y) volume 0 b :=
    fun b hb => intervalIntegrable_physEvolCompletionRightFun hinv hcont y hb
  have hsplit : ∀ τ : ℝ, 0 ≤ τ →
      (∫ s in (0 : ℝ)..τ, physEvolCompletionRightFun hinv s y)
        = (∫ s in (0 : ℝ)..τ, (physEvolCompletionRightFun hinv s y - y)) + τ • y := by
    intro τ hτ
    have h2 : (∫ s in (0 : ℝ)..τ, physEvolCompletionRightFun hinv s y)
        = ∫ s in (0 : ℝ)..τ, ((physEvolCompletionRightFun hinv s y - y) + y) :=
      intervalIntegral.integral_congr fun s _ => by abel
    rw [h2, intervalIntegral.integral_add ((hint τ hτ).sub intervalIntegrable_const)
      intervalIntegrable_const, intervalIntegral.integral_const]
    simp
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- strong continuity at `0⁺` gives `‖P(s)y − y‖ < ε/2` on a right neighbourhood of `0`
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖physEvolCompletionRightFun hinv s y - y‖ < ε / 2 := by
    have h := Metric.tendsto_nhds.mp (tendsto_physEvolCompletionRightFun hinv hcont y)
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
  have hdiff : τ⁻¹ • (∫ s in (0 : ℝ)..τ, physEvolCompletionRightFun hinv s y) - y
      = τ⁻¹ • ∫ s in (0 : ℝ)..τ, (physEvolCompletionRightFun hinv s y - y) := by
    rw [hsplit τ hτpos.le, smul_add, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hτpos), one_smul, add_sub_cancel_right]
  have hbound : ‖∫ s in (0 : ℝ)..τ, (physEvolCompletionRightFun hinv s y - y)‖
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
  have hdist : dist (τ⁻¹ • (∫ s in (0 : ℝ)..τ, physEvolCompletionRightFun hinv s y)) y
      = ‖τ⁻¹ • ∫ s in (0 : ℝ)..τ, (physEvolCompletionRightFun hinv s y - y)‖ := by
    rw [dist_eq_norm, hdiff]
  rw [hdist, norm_smul, Real.norm_eq_abs, abs_inv]
  refine lt_of_le_of_lt ?_ (by linarith : ε / 2 < ε)
  calc |τ|⁻¹ * ‖∫ s in (0 : ℝ)..τ, (physEvolCompletionRightFun hinv s y - y)‖
      ≤ |τ|⁻¹ * ((ε / 2) * |τ|) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = ε / 2 := by
        rw [mul_comm (ε / 2) |τ|, ← mul_assoc,
          inv_mul_cancel₀ (abs_ne_zero.2 (ne_of_gt hτpos)), one_mul]

/-! ## Closedness, from the one-sided representation -/

/-- **The forward-time generator has closed graph**, proved with right derivatives only.

If `uₙ → z₀` in the graph norm, the integral representation passes to the limit at every `τ ≥ 0`
by contractivity; dividing by `τ` exhibits the difference quotient of `z₀` as the average of the
strongly right-continuous curve `P(·)y`, which converges to `y` as `τ → 0⁺`. -/
theorem generatorRight_isClosed (hinv : HinvRight Λ T)
    (hcont : ∀ F : Observable, Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F) :
    ∀ (u : ℕ → (generatorRight hinv).domain) {z₀ y : Hphys Λ},
      Tendsto (fun n => (u n : Hphys Λ)) atTop (𝓝 z₀) →
      Tendsto (fun n => generatorRight hinv (u n)) atTop (𝓝 y) →
      ∃ h : HasGenRight hinv z₀, generatorRight hinv ⟨z₀, h⟩ = y := by
  intro u z₀ y hu hy
  have hmain : ∀ τ : ℝ, 0 ≤ τ →
      physEvolCompletionRightFun hinv τ z₀ - z₀
        = ∫ s in (0 : ℝ)..τ, physEvolCompletionRightFun hinv s y := by
    intro τ hτ
    have hleft : Tendsto (fun n => physEvolCompletionRightFun hinv τ (u n) - (u n : Hphys Λ))
        atTop (𝓝 (physEvolCompletionRightFun hinv τ z₀ - z₀)) :=
      (((physEvolCompletionRightFun hinv τ).continuous.tendsto z₀).comp hu).sub hu
    have hlim : Tendsto (fun n => |τ| * ‖generatorRight hinv (u n) - y‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => ‖generatorRight hinv (u n) - y‖) atTop (𝓝 0) := by
        have hsub : Tendsto (fun n => generatorRight hinv (u n) - y) atTop (𝓝 (y - y)) :=
          hy.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y))
        simpa using hsub.norm
      simpa using h1.const_mul |τ|
    have hright : Tendsto
        (fun n => ∫ s in (0 : ℝ)..τ,
          physEvolCompletionRightFun hinv s (generatorRight hinv (u n)))
        atTop (𝓝 (∫ s in (0 : ℝ)..τ, physEvolCompletionRightFun hinv s y)) := by
      refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
      have hb : ∀ n,
          ‖(∫ s in (0 : ℝ)..τ, physEvolCompletionRightFun hinv s (generatorRight hinv (u n)))
            - (∫ s in (0 : ℝ)..τ, physEvolCompletionRightFun hinv s y)‖
            ≤ |τ| * ‖generatorRight hinv (u n) - y‖ := by
        intro n
        rw [← intervalIntegral.integral_sub
          (intervalIntegrable_physEvolCompletionRightFun hinv hcont _ hτ)
          (intervalIntegrable_physEvolCompletionRightFun hinv hcont _ hτ)]
        refine (intervalIntegral.norm_integral_le_of_norm_le_const
          (C := ‖generatorRight hinv (u n) - y‖) ?_).trans_eq ?_
        · intro s _
          rw [← map_sub]
          exact physEvolCompletionRightFun_contractive hinv s _
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
        physEvol_sub_eq_integral_right hinv hcont (u n) τ hτ))
  have hquot : (fun τ : ℝ => diffQuot hinv τ z₀)
      =ᶠ[𝓝[>] 0]
        (fun τ : ℝ => τ⁻¹ • ∫ s in (0 : ℝ)..τ, physEvolCompletionRightFun hinv s y) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    change τ⁻¹ • (physEvolCompletionRightFun hinv τ z₀ - z₀)
      = τ⁻¹ • ∫ s in (0 : ℝ)..τ, physEvolCompletionRightFun hinv s y
    rw [hmain τ hτ.le]
  have hlim : Tendsto (fun τ : ℝ => diffQuot hinv τ z₀) (𝓝[>] 0) (𝓝 y) :=
    (tendsto_average_physEvol_right hinv hcont y).congr' hquot.symm
  have hgen : HasGenRight hinv z₀ := ⟨y, hlim⟩
  exact ⟨hgen, tendsto_nhds_unique (genValueRight_tendsto hinv ⟨z₀, hgen⟩) hlim⟩

/-! ## Dissipativity: the one-sided substitute for symmetry -/

/-- **The forward-time generator is dissipative**: `⟪A z, z⟫ ≤ 0` throughout its domain.

`P(τ)` is a contraction for every `τ`, so `⟪P(τ)z, z⟫ ≤ ‖P(τ)z‖ ‖z‖ ≤ ⟪z, z⟫` by
Cauchy–Schwarz, and the difference quotient of this inequality converges to `⟪A z, z⟫` along
`𝓝[>] 0`.  Only `τ ≥ 0` is used, which is why this replaces `generator_isSymmetric` in the
forward-time theory: a self-adjoint `P(τ)` would force `P ≡ 1` (`physEvolCompletion_eq_one`). -/
theorem generatorRight_inner_le_zero (hinv : HinvRight Λ T) (z : (generatorRight hinv).domain) :
    ⟪generatorRight hinv z, (z : Hphys Λ)⟫ ≤ 0 := by
  have hq : Tendsto (fun τ : ℝ => diffQuot hinv τ (z : Hphys Λ)) (𝓝[>] 0)
      (𝓝 (generatorRight hinv z)) :=
    generatorRight_apply_tendsto hinv z
  have hinner : Tendsto (fun τ : ℝ => ⟪diffQuot hinv τ (z : Hphys Λ), (z : Hphys Λ)⟫)
      (𝓝[>] 0) (𝓝 ⟪generatorRight hinv z, (z : Hphys Λ)⟫) :=
    hq.inner tendsto_const_nhds
  refine le_of_tendsto_of_tendsto hinner tendsto_const_nhds ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hquot : ⟪diffQuot hinv τ (z : Hphys Λ), (z : Hphys Λ)⟫
      = τ⁻¹ * (⟪physEvolCompletionRightFun hinv τ (z : Hphys Λ), (z : Hphys Λ)⟫
        - ⟪(z : Hphys Λ), (z : Hphys Λ)⟫) := by
    rw [diffQuot, real_inner_smul_left, inner_sub_left]
  rw [hquot]
  refine mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (le_of_lt hτ)) (sub_nonpos.2 ?_)
  calc ⟪physEvolCompletionRightFun hinv τ (z : Hphys Λ), (z : Hphys Λ)⟫
      ≤ ‖physEvolCompletionRightFun hinv τ (z : Hphys Λ)‖ * ‖(z : Hphys Λ)‖ :=
        real_inner_le_norm _ _
    _ ≤ ‖(z : Hphys Λ)‖ * ‖(z : Hphys Λ)‖ :=
        mul_le_mul_of_nonneg_right (physEvolCompletionRightFun_contractive hinv τ _) (norm_nonneg _)
    _ = ⟪(z : Hphys Λ), (z : Hphys Λ)⟫ := (real_inner_self_eq_norm_mul_norm _).symm

/-! ## The a priori estimate for the resolvent -/

/-- **The a priori resolvent bound**: for `lam > 0` and a domain vector,
`lam ‖z‖ ≤ ‖lam z − A z‖`.

Expanding `‖lam z − A z‖² = lam²‖z‖² − 2lam⟪A z, z⟫ + ‖A z‖²` and using only dissipativity
(`⟪A z, z⟫ ≤ 0`), the last two terms are nonnegative, so the right-hand side dominates
`(lam‖z‖)²`; take square roots.  This is the quantitative estimate behind
`generatorRight_resolvent_injective`, and the estimate Lumer–Phillips assumes in addition to
dissipativity. -/
theorem generatorRight_resolvent_bound (hinv : HinvRight Λ T)
    (z : (generatorRight hinv).domain) {lam : ℝ} (hlam : 0 < lam) :
    lam * ‖(z : Hphys Λ)‖ ≤ ‖lam • (z : Hphys Λ) - generatorRight hinv z‖ := by
  have hdis : ⟪generatorRight hinv z, (z : Hphys Λ)⟫ ≤ 0 :=
    generatorRight_inner_le_zero hinv z
  have hprod : lam * ⟪generatorRight hinv z, (z : Hphys Λ)⟫ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlam.le hdis
  have hcross : ⟪lam • (z : Hphys Λ), generatorRight hinv z⟫
      = lam * ⟪generatorRight hinv z, (z : Hphys Λ)⟫ := by
    rw [real_inner_smul_left, real_inner_comm (z : Hphys Λ) (generatorRight hinv z)]
  have hnorm : ‖lam • (z : Hphys Λ)‖ = lam * ‖(z : Hphys Λ)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
  have hexp : ‖lam • (z : Hphys Λ) - generatorRight hinv z‖ ^ 2
      = (lam * ‖(z : Hphys Λ)‖) ^ 2
        - 2 * (lam * ⟪generatorRight hinv z, (z : Hphys Λ)⟫)
        + ‖generatorRight hinv z‖ ^ 2 := by
    rw [norm_sub_sq_real, hcross, hnorm, mul_pow]
  have hsq : (lam * ‖(z : Hphys Λ)‖) ^ 2
      ≤ ‖lam • (z : Hphys Λ) - generatorRight hinv z‖ ^ 2 := by
    rw [hexp]
    nlinarith [sq_nonneg ‖generatorRight hinv z‖]
  have hnonneg : 0 ≤ lam * ‖(z : Hphys Λ)‖ := mul_nonneg hlam.le (norm_nonneg _)
  have h' : |lam * ‖(z : Hphys Λ)‖|
      ≤ |‖lam • (z : Hphys Λ) - generatorRight hinv z‖| :=
    sq_le_sq.mp hsq
  rwa [abs_of_nonneg hnonneg, abs_of_nonneg (norm_nonneg _)] at h'

/-- **`lam − A` is injective on the domain** for `lam > 0`, immediately from the a priori bound:
`lam z − A z = 0` forces `lam‖z‖ ≤ 0`, hence `z = 0`. -/
theorem generatorRight_resolvent_injective (hinv : HinvRight Λ T) {lam : ℝ} (hlam : 0 < lam) :
    Function.Injective fun z : (generatorRight hinv).domain =>
      lam • (z : Hphys Λ) - generatorRight hinv z := by
  intro z w hzw
  have hzw' : lam • (z : Hphys Λ) - generatorRight hinv z
      = lam • (w : Hphys Λ) - generatorRight hinv w := hzw
  have hzero : lam • ((z : Hphys Λ) - (w : Hphys Λ))
      - generatorRight hinv (z - w) = 0 := by
    have hval : generatorRight hinv (z - w)
        = generatorRight hinv z - generatorRight hinv w :=
      map_sub (genFunRight hinv) z w
    calc lam • ((z : Hphys Λ) - (w : Hphys Λ))
          - generatorRight hinv (z - w)
        = (lam • (z : Hphys Λ) - generatorRight hinv z)
            - (lam • (w : Hphys Λ) - generatorRight hinv w) := by
          rw [hval, smul_sub]
          abel
      _ = 0 := by rw [hzw', sub_self]
  have hbound := generatorRight_resolvent_bound hinv
    (z - w : (generatorRight hinv).domain) hlam
  have hnorm : ((z - w : (generatorRight hinv).domain) : Hphys Λ) = 0 := by
    have h1 : lam * ‖((z - w : (generatorRight hinv).domain) : Hphys Λ)‖ = 0 :=
      le_antisymm (by simpa [hzero] using hbound)
        (mul_nonneg hlam.le (norm_nonneg _))
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hlam.ne'
    · exact norm_eq_zero.1 h
  exact sub_eq_zero.1 (Subtype.coe_injective hnorm)

end

end BookProof.OSReconstruction
