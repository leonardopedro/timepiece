import Mathlib
import BookProof.OSReconstruction.HilbertSpace

/-!
# The generator of the transfer semigroup

`OSReconstruction.HilbertSpace` assembles the physical Hilbert space `ℋ` and the contractive
extension `P(τ)` of the time evolution to it, and derives strong continuity at `0` from continuity
of the two-point function.  This module attaches the *generator* to that semigroup.

The definition is the standard one, with no integration theory: `z` is in the domain when the
difference quotient

`diffQuotGroup τ z = τ⁻¹ • (P(τ) z − z)`

converges as `τ → 0`, and the generator is the limit.  The limit is taken over the *punctured*
filter `𝓝[≠] 0`: the quotient is junk at `τ = 0` (`0⁻¹ = 0` in `ℝ`), so a limit over `𝓝 0` would
force the value `0` there and shrink the domain to the fixed points of `P`.  Puncturing is also
what makes the two signs equivalent: the evolution is a group (`physEvolCompletion_add`, with
`P(τ)⁻¹ = P(−τ)`), so the one-sided and two-sided domains coincide, and the punctured filter makes
the linearity proofs below trivial.

What is proved:

* `diffQuotGroup_zero`, `diffQuotGroup_add`, `diffQuotGroup_smul` — the difference quotient is linear in the
  vector for every fixed `τ`;
* `HasGen` — convergence of the quotient, and `hasGen_zero`/`hasGen_add`/`hasGen_smul` — it is
  closed under the vector operations, because a limit of a sum is the sum of the limits and limits
  in a normed space are unique (`tendsto_nhds_unique`);
* `genDomain` / `generator` — the domain as a `Submodule` and the generator as a `LinearPMap`,
  whose value is `Classical.choose` of the limit, with linearity recovered from uniqueness;
* `generator_apply_tendsto` — the defining property, and `generator_apply_eq_of_tendsto` —
  uniqueness of the value;
* `hasGen_evol` / `generator_evol` — `P(t)` preserves the domain and commutes with the generator,
  which is what makes the limit "the generator of `P`" and not merely a symmetric operator;
* `generator_isSymmetric` — `⟪A z, w⟫ = ⟪z, A w⟫` on the domain.

## Boundary

Symmetry is *conditional* on each `P(τ)` being self-adjoint, and that hypothesis is not derived
from the OS axioms here.  What reflection positivity supplies is contractivity in both time
directions, hence — through the group law — that `P(τ)` is an isometry of `ℋ`
(`physForm_evol_self`), i.e. unitary.  A unitary operator is not symmetric in general (a symmetric
unitary has spectrum in `{±1}`).  Self-adjointness of the transfer operator is a property of the
*realization*: in the nested Fock space of `BookProof/`, the transfer operator is `e^{-τH}` for the
self-adjoint operator `H` obtained from the closed form by Faris–Lavine / Friedrichs extension, and
`e^{-τH}` is self-adjoint for every real `τ`.  That realization-level identification is not repeated
here; the theorem below takes `∀ τ, IsSelfAdjoint (P τ)` as its hypothesis, exactly as
`HilbertSpace.lean` takes matrix element continuity as its hypothesis for strong continuity.

Closedness *is* proved, in `OSReconstruction.GeneratorClosed`, and it needs no Bochner
integration of `ℋ`-valued functions: the orbit derivative `hasDerivAt_physEvol` and the fundamental
theorem of calculus give `P(τ) z − z = ∫₀^τ P(s) (A z) ds` on the domain, the identity is compared
with the difference quotient of a fixed vector, and contractivity passes it to the limit
(`generator_isClosed`).  The same argument, run with a one-sided difference quotient and the
right-derivative form of the fundamental theorem of calculus, gives the forward-time generator and
its closedness in `OSReconstruction.SemigroupGenerator`; the punctured filter is usable here only
because the evolution is a group.  What remains is the step from *closed symmetric* to
*self-adjoint*:
deficiency indices of the closed symmetric operator, or a resolvent representation identifying it
with the realization's `H`.  Symmetry is what the Källén–Lehmann representation of matrix
elements consumes, and it is available without that step.

The self-adjointness hypothesis is moreover *empty* for nontrivial dynamics in this framework:
with contractivity in both time directions `P(τ)` is an isometry, and
`OSReconstruction.TransferSelfAdjoint` proves that a self-adjoint isometry is an involution, hence
`P(τ) = P(τ/2) P(τ/2) = 1` for every `τ` (`physEvolCompletion_eq_one`).  The symmetric operator
above is then `0` with domain all of `ℋ` (`generator_apply_eq_zero_of_selfAdjoint`).  Nontrivial
dynamics needs the transfer semi-group on `τ ≥ 0`, where `P(τ)` is a contraction, not a unitary.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity
open Filter
open scoped Topology
open RealInnerProductSpace

noncomputable section

/-! ## Difference quotients -/

/-- The difference quotient `τ⁻¹ • (P(τ) z − z)` of the transfer semigroup. -/
def diffQuotGroup (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (τ : ℝ) (z : Hphys Λ) : Hphys Λ :=
  τ⁻¹ • (physEvolCompletion Λ T hinv τ z - z)

/-- The difference quotient vanishes at the origin. -/
theorem diffQuotGroup_zero (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (τ : ℝ) : diffQuotGroup Λ T hinv τ (0 : Hphys Λ) = 0 := by
  simp [diffQuotGroup]

/-- The difference quotient is additive in the vector. -/
theorem diffQuotGroup_add (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (τ : ℝ) (z w : Hphys Λ) :
    diffQuotGroup Λ T hinv τ (z + w) = diffQuotGroup Λ T hinv τ z + diffQuotGroup Λ T hinv τ w := by
  simp only [diffQuotGroup, map_add]
  rw [show physEvolCompletion Λ T hinv τ z + physEvolCompletion Λ T hinv τ w - (z + w)
      = (physEvolCompletion Λ T hinv τ z - z)
        + (physEvolCompletion Λ T hinv τ w - w) from by abel,
    smul_add]

/-- The difference quotient is homogeneous in the vector. -/
theorem diffQuotGroup_smul (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (τ : ℝ) (c : ℝ) (z : Hphys Λ) :
    diffQuotGroup Λ T hinv τ (c • z) = c • diffQuotGroup Λ T hinv τ z := by
  rw [diffQuotGroup, diffQuotGroup, map_smul, ← smul_sub, smul_comm τ⁻¹ c]

/-! ## The domain -/

/-- `z` is in the domain of the generator when the difference quotient converges at `τ = 0`. -/
def HasGen (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (z : Hphys Λ) : Prop :=
  ∃ y : Hphys Λ, Tendsto (fun τ : ℝ => diffQuotGroup Λ T hinv τ z) (𝓝[≠] 0) (𝓝 y)

/-- The origin is in the domain, with generator value `0`. -/
theorem hasGen_zero (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F) :
    HasGen Λ T hinv (0 : Hphys Λ) := by
  refine ⟨0, ?_⟩
  simpa only [diffQuotGroup_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : Hphys Λ)) (𝓝[≠] 0) (𝓝 0))

/-- The domain is closed under addition: the quotient of a sum is the sum of the quotients. -/
theorem hasGen_add (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    {z w : Hphys Λ} (hz : HasGen Λ T hinv z) (hw : HasGen Λ T hinv w) :
    HasGen Λ T hinv (z + w) := by
  obtain ⟨y, hy⟩ := hz
  obtain ⟨y', hy'⟩ := hw
  refine ⟨y + y', ?_⟩
  refine (hy.add hy').congr' ?_
  exact Eventually.of_forall fun τ => (diffQuotGroup_add Λ T hinv τ z w).symm

/-- The domain is closed under scalar multiplication. -/
theorem hasGen_smul (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (c : ℝ) {z : Hphys Λ} (hz : HasGen Λ T hinv z) : HasGen Λ T hinv (c • z) := by
  obtain ⟨y, hy⟩ := hz
  refine ⟨c • y, ?_⟩
  refine (hy.const_smul c).congr' ?_
  exact Eventually.of_forall fun τ => (diffQuotGroup_smul Λ T hinv τ c z).symm

/-- **The domain of the generator** as a real submodule of `ℋ`. -/
def genDomain (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F) :
    Submodule ℝ (Hphys Λ) where
  carrier := {z | HasGen Λ T hinv z}
  add_mem' := fun hz hw => hasGen_add Λ T hinv hz hw
  zero_mem' := hasGen_zero Λ T hinv
  smul_mem' := fun c _ hz => hasGen_smul Λ T hinv c hz

/-- Membership in the domain is exactly convergence of the difference quotient. -/
@[simp]
theorem mem_genDomain (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (z : Hphys Λ) : z ∈ genDomain Λ T hinv ↔ HasGen Λ T hinv z :=
  Iff.rfl

/-! ## The generator as a partially defined linear map

The value at `z` is a chosen limit.  Linearity does not hold by construction, so it is recovered
from uniqueness of limits in a normed space: both sides are limits of the same net. -/

/-- The generator's value at a domain point, as a chosen limit of the difference quotient. -/
def genValue (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (z : genDomain Λ T hinv) : Hphys Λ :=
  Classical.choose z.2

/-- The defining limit property of `genValue`. -/
theorem genValue_tendsto (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (z : genDomain Λ T hinv) :
    Tendsto (fun τ : ℝ => diffQuotGroup Λ T hinv τ (z : Hphys Λ)) (𝓝[≠] 0)
      (𝓝 (genValue Λ T hinv z)) :=
  Classical.choose_spec z.2

/-- `genValue` is additive, by uniqueness of limits. -/
theorem genValue_add (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (z w : genDomain Λ T hinv) :
    genValue Λ T hinv (z + w) = genValue Λ T hinv z + genValue Λ T hinv w := by
  refine tendsto_nhds_unique (genValue_tendsto Λ T hinv (z + w)) ?_
  have h : Tendsto (fun τ : ℝ => diffQuotGroup Λ T hinv τ (z : Hphys Λ)
      + diffQuotGroup Λ T hinv τ (w : Hphys Λ)) (𝓝[≠] 0)
      (𝓝 (genValue Λ T hinv z + genValue Λ T hinv w)) :=
    (genValue_tendsto Λ T hinv z).add (genValue_tendsto Λ T hinv w)
  refine h.congr' ?_
  exact Eventually.of_forall fun τ =>
    (diffQuotGroup_add Λ T hinv τ (z : Hphys Λ) (w : Hphys Λ)).symm

/-- `genValue` is homogeneous, by uniqueness of limits. -/
theorem genValue_smul (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (c : ℝ) (z : genDomain Λ T hinv) :
    genValue Λ T hinv (c • z) = c • genValue Λ T hinv z := by
  refine tendsto_nhds_unique (genValue_tendsto Λ T hinv (c • z)) ?_
  have h : Tendsto (fun τ : ℝ => c • diffQuotGroup Λ T hinv τ (z : Hphys Λ)) (𝓝[≠] 0)
      (𝓝 (c • genValue Λ T hinv z)) := (genValue_tendsto Λ T hinv z).const_smul c
  refine h.congr' ?_
  exact Eventually.of_forall fun τ => (diffQuotGroup_smul Λ T hinv τ c (z : Hphys Λ)).symm

/-- The generator's action as a linear map on its domain. -/
def genFun (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F) :
    genDomain Λ T hinv →ₗ[ℝ] Hphys Λ where
  toFun := genValue Λ T hinv
  map_add' := genValue_add Λ T hinv
  map_smul' := genValue_smul Λ T hinv

/-- **The generator of the transfer semigroup**, as a partially defined linear map. -/
def generator (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F) :
    Hphys Λ →ₗ.[ℝ] Hphys Λ where
  domain := genDomain Λ T hinv
  toFun := genFun Λ T hinv

/-- The defining property of the generator: the difference quotient converges to its value. -/
theorem generator_apply_tendsto (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (z : (generator Λ T hinv).domain) :
    Tendsto (fun τ : ℝ => diffQuotGroup Λ T hinv τ (z : Hphys Λ)) (𝓝[≠] 0)
      (𝓝 (generator Λ T hinv z)) :=
  genValue_tendsto Λ T hinv z

/-- Uniqueness: any other limit of the difference quotient is the generator's value. -/
theorem generator_apply_eq_of_tendsto (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (z : (generator Λ T hinv).domain) {y : Hphys Λ}
    (h : Tendsto (fun τ : ℝ => diffQuotGroup Λ T hinv τ (z : Hphys Λ)) (𝓝[≠] 0) (𝓝 y)) :
    generator Λ T hinv z = y :=
  tendsto_nhds_unique (generator_apply_tendsto Λ T hinv z) h

/-! ## The evolution commutes with the generator

`P(t)` preserves the domain and intertwines the generator with itself: the quotient of the evolved
vector is the evolved quotient, because `P(t)` commutes with `P(τ)` and is linear.  This is the
statement that the limit really is the generator *of this semigroup*. -/

/-- The evolved difference quotient is the difference quotient of the evolved vector. -/
theorem diffQuotGroup_evol (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (t τ : ℝ) (z : Hphys Λ) :
    diffQuotGroup Λ T hinv τ (physEvolCompletion Λ T hinv t z)
      = physEvolCompletion Λ T hinv t (diffQuotGroup Λ T hinv τ z) := by
  have hcomm : physEvolCompletion Λ T hinv τ (physEvolCompletion Λ T hinv t z)
      = physEvolCompletion Λ T hinv t (physEvolCompletion Λ T hinv τ z) := by
    have h1 : physEvolCompletion Λ T hinv (τ + t) z
        = physEvolCompletion Λ T hinv τ (physEvolCompletion Λ T hinv t z) := by
      rw [physEvolCompletion_add]
      rfl
    have h2 : physEvolCompletion Λ T hinv (τ + t) z
        = physEvolCompletion Λ T hinv t (physEvolCompletion Λ T hinv τ z) := by
      rw [add_comm τ t, physEvolCompletion_add]
      rfl
    exact h1.symm.trans h2
  rw [diffQuotGroup, diffQuotGroup, hcomm, ← map_sub, map_smul]

/-- **`P(t)` preserves the domain of the generator.** -/
theorem hasGen_evol (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (t : ℝ) {z : Hphys Λ} (hz : HasGen Λ T hinv z) :
    HasGen Λ T hinv (physEvolCompletion Λ T hinv t z) := by
  obtain ⟨y, hy⟩ := hz
  refine ⟨physEvolCompletion Λ T hinv t y, ?_⟩
  have hcont : Tendsto (physEvolCompletion Λ T hinv t) (𝓝 y)
      (𝓝 (physEvolCompletion Λ T hinv t y)) :=
    (physEvolCompletion Λ T hinv t).continuous.tendsto y
  refine (hcont.comp hy).congr' ?_
  exact Eventually.of_forall fun τ => (diffQuotGroup_evol Λ T hinv t τ z).symm

/-- **`P(t)` commutes with the generator**: on the domain, `A P(t) z = P(t) A z`. -/
theorem generator_evol (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (t : ℝ) (z : (generator Λ T hinv).domain) :
    generator Λ T hinv
        ⟨physEvolCompletion Λ T hinv t (z : Hphys Λ),
          hasGen_evol Λ T hinv t z.2⟩
      = physEvolCompletion Λ T hinv t (generator Λ T hinv z) := by
  have hcomp : Tendsto
      (fun τ : ℝ => physEvolCompletion Λ T hinv t (diffQuotGroup Λ T hinv τ (z : Hphys Λ)))
      (𝓝[≠] 0) (𝓝 (physEvolCompletion Λ T hinv t (generator Λ T hinv z))) :=
    ((physEvolCompletion Λ T hinv t).continuous.tendsto (generator Λ T hinv z)).comp
      (generator_apply_tendsto Λ T hinv z)
  refine generator_apply_eq_of_tendsto Λ T hinv _ ?_
  refine hcomp.congr' ?_
  exact Eventually.of_forall fun τ => (diffQuotGroup_evol Λ T hinv t τ (z : Hphys Λ)).symm

/-! ## Symmetry of the generator

If every `P(τ)` is self-adjoint, the difference quotients satisfy
`⟪τ⁻¹ • (P(τ)z − z), w⟫ = ⟪z, τ⁻¹ • (P(τ)w − w)⟫` for all `τ`, and taking limits gives symmetry.
No integral representation is needed. -/

/-- Pointwise symmetry of the difference quotients, from self-adjointness of `P(τ)`. -/
theorem inner_diffQuot_comm (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (hsa : ∀ τ : ℝ, IsSelfAdjoint (physEvolCompletion Λ T hinv τ))
    (τ : ℝ) (z w : Hphys Λ) :
    ⟪diffQuotGroup Λ T hinv τ z, w⟫ = ⟪z, diffQuotGroup Λ T hinv τ w⟫ := by
  have hsym : ⟪(physEvolCompletion Λ T hinv τ) z, w⟫
      = ⟪z, (physEvolCompletion Λ T hinv τ) w⟫ := (hsa τ).isSymmetric z w
  rw [diffQuotGroup, diffQuotGroup, real_inner_smul_left, real_inner_smul_right, inner_sub_left,
    inner_sub_right, hsym]

/-- **The generator is symmetric**: `⟪A z, w⟫ = ⟪z, A w⟫` on its domain. -/
theorem generator_isSymmetric (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (hsa : ∀ τ : ℝ, IsSelfAdjoint (physEvolCompletion Λ T hinv τ)) :
    ∀ z w : (generator Λ T hinv).domain,
      ⟪generator Λ T hinv z, (w : Hphys Λ)⟫
        = ⟪(z : Hphys Λ), generator Λ T hinv w⟫ := by
  intro z w
  have hz : Tendsto (fun τ : ℝ => ⟪diffQuotGroup Λ T hinv τ (z : Hphys Λ), (w : Hphys Λ)⟫)
      (𝓝[≠] 0) (𝓝 ⟪generator Λ T hinv z, (w : Hphys Λ)⟫) :=
    (generator_apply_tendsto Λ T hinv z).inner tendsto_const_nhds
  refine tendsto_nhds_unique hz ?_
  have hw : Tendsto (fun τ : ℝ => ⟪(z : Hphys Λ), diffQuotGroup Λ T hinv τ (w : Hphys Λ)⟫)
      (𝓝[≠] 0) (𝓝 ⟪(z : Hphys Λ), generator Λ T hinv w⟫) :=
    tendsto_const_nhds.inner (generator_apply_tendsto Λ T hinv w)
  refine hw.congr' ?_
  exact Eventually.of_forall fun τ => (inner_diffQuot_comm Λ T hinv hsa τ _ _).symm

end

end BookProof.OSReconstruction
