import Mathlib
import BookProof.OSReconstruction.Hamiltonian

/-!
# The physical Hilbert space, assembled

Plan: `cftproof.md`, Phase 4.1 — "The OS form `⟨F, G⟩_phys = ω(θF ∘ G)`, with `ω` a state
satisfying RP, defines an inner product on `𝔄 / 𝔑` … its completion is the physical Hilbert
space `ℋ`" — and Phase 4.2's contractive semigroup.

`OSReconstruction.PhysicalSpace` proves the ingredients (bilinearity, symmetry, positivity,
Cauchy–Schwarz, the radical, descent to the quotient) and left the assembly to this module.
The assembly is performed here:

* `OSState` — a `θ`-invariant linear functional together with its reflection positivity: the
  data that fixes the Hilbert space;
* `osBilinMap` — the OS form as a bilinear map `Observable →ₗ[ℝ] Observable →ₗ[ℝ] ℝ`;
* `physForm` — `LinearMap.liftQ₂` descends it to the quotient `Observable ⧸ Radical Λ.ω`;
* `physPreCore` / `physCore` — `PreInnerProductSpace.Core` and `InnerProductSpace.Core` on the
  quotient.  The core is *definite*: `⟨F,F⟩ = 0` forces `F` into the radical
  (`mem_radical_of_self_eq_zero`), so the class of `F` is `0`;
* `physSeminormed` / `physInnerProductSpace` — `InnerProductSpace.ofCore`, registered as
  instances, so that `‖x‖ = √⟨x,x⟩` on `𝔄 / 𝔑`;
* `Hphys Λ` — the completion `UniformSpace.Completion (Observable ⧸ Radical Λ.ω)`, with
  Mathlib's completion instances (`InnerProductSpace`, `CompleteSpace`): a `HilbertSpace`;
* `physNorm_mk` — `‖mk F‖ = √⟨F,F⟩` on the dense subspace, and `physNorm_eq_zero_iff` — the
  seminorm is a norm;
* `physEvol` — the time evolution descended to the quotient (`Submodule.mapQ`);
  `physEvol_contractive` — `‖physEvol τ x‖ ≤ ‖x‖`;
* `physEvolCompletion` — `LinearMap.extendOfNorm` extends the evolution to `ℋ`, with
  `norm_physEvolCompletion_le : ‖physEvolCompletion τ‖ ≤ 1` and `physEvolCompletion_coe` — it
  agrees with the evolution on the dense image.

## Boundary

What is assembled is the Hilbert space as a type with its structure, and the contractive
extension of a given one-parameter family of evolutions.  The *generator* `H = −log P`, its
self-adjointness and its boundedness below need the spectral theorem for unbounded operators and
Stone's theorem; neither is in Mathlib, as the header of `OSReconstruction.Hamiltonian` records.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity

noncomputable section

/-! ## The OS form as a bilinear map -/

/-- The OS form `⟨F, G⟩ = ω(θF · G)` bundled as a bilinear map. -/
def osBilinMap (ω : LinearFunctional) : Observable →ₗ[ℝ] Observable →ₗ[ℝ] ℝ where
  toFun F :=
    { toFun := fun G => osBilin ω F G
      map_add' := fun G H => osForm_add_right' ω F G H
      map_smul' := fun c G => osForm_smul_right' ω c F G }
  map_add' F H := LinearMap.ext fun G => osForm_add_left ω F H G
  map_smul' c F := LinearMap.ext fun G => osForm_smul_left ω c F G

@[simp]
theorem osBilinMap_apply (ω : LinearFunctional) (F G : Observable) :
    osBilinMap ω F G = osBilin ω F G := rfl

/-! ## The quotient `𝔄 / 𝔑` -/

/-- A reflection positive state: a `θ`-invariant linear functional on the observables together
with its reflection positivity.  This is the data of OS reconstruction. -/
structure OSState where
  /-- The expectation functional. -/
  ω : LinearFunctional
  /-- Reflection positivity of the expectation. -/
  pos : IsReflectionPositive (fun F => ω.toFun F)

/-- The quotient `𝔄 / 𝔑` of the observables by the radical of the OS form. -/
abbrev PhysSpace (Λ : OSState) : Type := Observable ⧸ Radical Λ.ω

/-- The OS form on the quotient.  It descends because the form vanishes on the radical in
either argument (`Radical` is defined by vanishing in the *first* argument, and symmetry gives
the second). -/
def physForm (ω : LinearFunctional) :
    (Observable ⧸ Radical ω) →ₗ[ℝ] (Observable ⧸ Radical ω) →ₗ[ℝ] ℝ :=
  (osBilinMap ω).liftQ₂ (Radical ω) (Radical ω)
    (fun x hx => by
      rw [LinearMap.mem_ker]
      exact LinearMap.ext fun G => hx G)
    (fun y hy => by
      rw [LinearMap.mem_ker]
      exact LinearMap.ext fun F => (osForm_symm' ω F y).trans (hy F))

@[simp]
theorem physForm_mk (ω : LinearFunctional) (F G : Observable) :
    physForm ω (Submodule.Quotient.mk F) (Submodule.Quotient.mk G) = osBilin ω F G :=
  LinearMap.liftQ₂_mk _ _ _ _

theorem physForm_add_left (ω : LinearFunctional) (x y z : Observable ⧸ Radical ω) :
    physForm ω (x + y) z = physForm ω x z + physForm ω y z := by
  rw [map_add]
  rfl

theorem physForm_smul_left (ω : LinearFunctional) (c : ℝ) (x y : Observable ⧸ Radical ω) :
    physForm ω (c • x) y = c * physForm ω x y := by
  rw [map_smul]
  rfl

theorem physForm_symm (ω : LinearFunctional) (x y : Observable ⧸ Radical ω) :
    physForm ω x y = physForm ω y x := by
  refine Submodule.Quotient.induction_on _ x fun F => ?_
  refine Submodule.Quotient.induction_on _ y fun G => ?_
  simp [osForm_symm' ω F G]

theorem physForm_self_nonneg (Λ : OSState) (x : PhysSpace Λ) : 0 ≤ physForm Λ.ω x x := by
  refine Submodule.Quotient.induction_on _ x fun F => ?_
  simpa using osForm_self_nonneg Λ.ω Λ.pos F

/-- **Definiteness on the quotient**: the radical is exactly the null set of the OS form, so the
descended form is an inner product and not merely a seminorm. -/
theorem physForm_self_eq_zero_iff (Λ : OSState) (x : PhysSpace Λ) :
    physForm Λ.ω x x = 0 ↔ x = 0 := by
  constructor
  · refine Submodule.Quotient.induction_on _ x fun F => ?_
    intro hx
    have hF : F ∈ Radical Λ.ω := mem_radical_of_self_eq_zero Λ.ω Λ.pos (by simpa using hx)
    exact (Submodule.Quotient.mk_eq_zero (Radical Λ.ω) (x := F)).mpr hF
  · rintro rfl
    simp [physForm]

/-! ## The inner product core and the inner product space  `𝔄 / 𝔑` -/

/-- The *pre*-inner-product core on `𝔄 / 𝔑`: bilinearity, symmetry and positivity of the OS
form.  This is the `PreInnerProductSpace.Core` that `InnerProductSpace.ofCore` consumes. -/
def physPreCore (Λ : OSState) : PreInnerProductSpace.Core ℝ (PhysSpace Λ) where
  inner x y := physForm Λ.ω x y
  conj_inner_symm x y := by
    rw [physForm_symm Λ.ω y x, RCLike.conj_to_real]
  re_inner_nonneg x := physForm_self_nonneg Λ x
  add_left x y z := physForm_add_left Λ.ω x y z
  smul_left x y r := physForm_smul_left Λ.ω r x y

/-- The inner product core on `𝔄 / 𝔑`, with definiteness. -/
def physCore (Λ : OSState) : InnerProductSpace.Core ℝ (PhysSpace Λ) where
  inner := (physPreCore Λ).inner
  conj_inner_symm := (physPreCore Λ).conj_inner_symm
  re_inner_nonneg := (physPreCore Λ).re_inner_nonneg
  add_left := (physPreCore Λ).add_left
  smul_left := (physPreCore Λ).smul_left
  definite x hx := (physForm_self_eq_zero_iff Λ x).1 hx

/-- The norm on `𝔄 / 𝔑` induced by the OS inner product, `‖x‖ = √⟨x,x⟩`. -/
abbrev physSeminormed (Λ : OSState) : SeminormedAddCommGroup (PhysSpace Λ) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℝ (PhysSpace Λ) _ _ _ (physPreCore Λ)

/-- **The OS inner product space `𝔄 / 𝔑`**, via `InnerProductSpace.ofCore`. -/
def physInnerProductSpace (Λ : OSState) :
    @InnerProductSpace ℝ (PhysSpace Λ) _ (physSeminormed Λ) :=
  InnerProductSpace.ofCore (physPreCore Λ)

instance instSeminormedPhysSpace (Λ : OSState) : SeminormedAddCommGroup (PhysSpace Λ) :=
  physSeminormed Λ

instance instInnerProductSpacePhysSpace (Λ : OSState) : InnerProductSpace ℝ (PhysSpace Λ) :=
  physInnerProductSpace Λ

/-- The norm is the square root of the OS form on the diagonal. -/
theorem physNorm_eq (Λ : OSState) (x : PhysSpace Λ) :
    ‖x‖ = Real.sqrt (physForm Λ.ω x x) := rfl

/-- On the dense subspace, the norm is the OS norm: `‖mk F‖ = √⟨F,F⟩`. -/
theorem physNorm_mk (Λ : OSState) (F : Observable) :
    ‖(Submodule.Quotient.mk F : PhysSpace Λ)‖ = Real.sqrt (osBilin Λ.ω F F) := by
  rw [physNorm_eq, physForm_mk]

/-- The seminorm is a norm: `‖x‖ = 0` forces `x = 0`, by definiteness of the OS form. -/
theorem physNorm_eq_zero_iff (Λ : OSState) (x : PhysSpace Λ) : ‖x‖ = 0 ↔ x = 0 := by
  rw [physNorm_eq, Real.sqrt_eq_zero']
  constructor
  · intro h
    exact (physForm_self_eq_zero_iff Λ x).1 (le_antisymm h (physForm_self_nonneg Λ x))
  · rintro rfl
    simp [physForm]

/-! ## The physical Hilbert space -/

/-- **The physical Hilbert space** `ℋ`: the completion of `𝔄 / 𝔑` in the OS norm, with Mathlib's
completion instances (`InnerProductSpace`, `CompleteSpace`). -/
abbrev Hphys (Λ : OSState) : Type := UniformSpace.Completion (PhysSpace Λ)

instance instCompleteSpaceHphys (Λ : OSState) : CompleteSpace (Hphys Λ) := inferInstance

/-- The completion of `𝔄 / 𝔑` is a Hilbert space. -/
instance instHilbertSpaceHphys (Λ : OSState) : HilbertSpace ℝ (Hphys Λ) := ⟨⟩

/-- `𝔄 / 𝔑` is dense in `ℋ`, so theorems about `ℋ` reduce to the quotient. -/
theorem denseRange_physCoe (Λ : OSState) : DenseRange ((↑) : PhysSpace Λ → Hphys Λ) :=
  UniformSpace.Completion.denseRange_coe

/-- The embedding of `𝔄 / 𝔑` into its completion, as a linear map. -/
def physCoe (Λ : OSState) : PhysSpace Λ →ₗ[ℝ] Hphys Λ where
  toFun x := (x : Hphys Λ)
  map_add' := UniformSpace.Completion.coe_add
  map_smul' := UniformSpace.Completion.coe_smul

@[simp]
theorem physCoe_apply (Λ : OSState) (x : PhysSpace Λ) : physCoe Λ x = (x : Hphys Λ) := rfl

/-! ## The time evolution descends and is a contraction -/

/-- **The time evolution on `𝔄 / 𝔑`**: since the evolution preserves the radical, it descends to
the quotient. -/
def physEvol (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (τ : ℝ) : PhysSpace Λ →ₗ[ℝ] PhysSpace Λ :=
  (Radical Λ.ω).mapQ (Radical Λ.ω) (T τ)
    (fun _ hx => radical_invariant Λ.ω Λ.pos T hinv hx τ)

@[simp]
theorem physEvol_mk (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (τ : ℝ) (F : Observable) :
    physEvol Λ T hinv τ (Submodule.Quotient.mk F) = Submodule.Quotient.mk (T τ F) :=
  rfl

/-- **The evolution is a contraction on `𝔄 / 𝔑`**: the hypothesis that the evolution does not
increase the OS form becomes `‖T(τ)F‖ ≤ ‖F‖`. -/
theorem physEvol_contractive (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (τ : ℝ) (x : PhysSpace Λ) : ‖physEvol Λ T hinv τ x‖ ≤ ‖x‖ := by
  refine Submodule.Quotient.induction_on _ x fun F => ?_
  rw [physEvol_mk, physNorm_mk, physNorm_mk]
  exact Real.sqrt_le_sqrt (hinv τ F)

/-- **The evolution is the identity at time `0`**, read off the quotient from
`timeTranslation_zero`. -/
theorem physEvol_zero (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (x : PhysSpace Λ) : physEvol Λ T hinv 0 x = x := by
  refine Submodule.Quotient.induction_on _ x fun F => ?_
  rw [physEvol_mk, timeTranslation_zero]

/-- **The evolution is a semigroup on the physical space**: `P(s + t) = P(s) ∘ P(t)`.  This is
`timeTranslation_semigroup` under the quotient — the algebraic half of Phase 4.2's semigroup,
before any topology is used. -/
theorem physEvol_add (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (s t : ℝ) (x : PhysSpace Λ) :
    physEvol Λ T hinv (s + t) x = physEvol Λ T hinv s (physEvol Λ T hinv t x) := by
  refine Submodule.Quotient.induction_on _ x fun F => ?_
  rw [physEvol_mk, physEvol_mk, physEvol_mk, timeTranslation_semigroup]

/-- **The evolution extends to the completion** as a continuous linear map, by
`LinearMap.extendOfNorm` along the dense embedding `𝔄/𝔑 ↪ ℋ`. -/
def physEvolCompletion (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (τ : ℝ) : Hphys Λ →L[ℝ] Hphys Λ :=
  LinearMap.extendOfNorm (physCoe Λ ∘ₗ physEvol Λ T hinv τ) (physCoe Λ)

/-- The extension agrees with the evolution on the dense image: nothing is changed on `𝔄 / 𝔑`. -/
theorem physEvolCompletion_coe (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (τ : ℝ) (x : PhysSpace Λ) :
    physEvolCompletion Λ T hinv τ (x : Hphys Λ) =
      ((physEvol Λ T hinv τ x : PhysSpace Λ) : Hphys Λ) := by
  refine LinearMap.extendOfNorm_eq (f := physCoe Λ ∘ₗ physEvol Λ T hinv τ) (e := physCoe Λ)
    (denseRange_physCoe Λ) ⟨1, ?_⟩ x
  intro y
  simpa [physCoe_apply, UniformSpace.Completion.norm_coe] using
    physEvol_contractive Λ T hinv τ y

/-- **The evolution is a contraction on the completion**: `‖T(τ)‖ ≤ 1` as an operator norm. -/
theorem norm_physEvolCompletion_le (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (τ : ℝ) : ‖physEvolCompletion Λ T hinv τ‖ ≤ 1 := by
  refine LinearMap.opNorm_extendOfNorm_le (f := physCoe Λ ∘ₗ physEvol Λ T hinv τ)
    (e := physCoe Λ) (denseRange_physCoe Λ) zero_le_one ?_
  intro x
  simpa [physCoe_apply, UniformSpace.Completion.norm_coe] using
    physEvol_contractive Λ T hinv τ x

/-- Pointwise form of contractivity on the completion. -/
theorem physEvolCompletion_contractive (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (τ : ℝ) (z : Hphys Λ) : ‖physEvolCompletion Λ T hinv τ z‖ ≤ ‖z‖ := by
  calc ‖physEvolCompletion Λ T hinv τ z‖
      ≤ ‖physEvolCompletion Λ T hinv τ‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖z‖ := by
        refine mul_le_mul_of_nonneg_right (norm_physEvolCompletion_le Λ T hinv τ) ?_
        exact norm_nonneg _
    _ = ‖z‖ := one_mul _

/-! ## The semigroup law on the completion

Contractivity is not a semigroup: `P(0) = 1` and `P(s + t) = P(s) P(t)` are separate statements,
and on `ℋ` they hold because both sides are continuous and agree on the dense image of `𝔄 / 𝔑`,
where they are `physEvol_zero` and `physEvol_add`.  This is the algebraic content Phase 4.2's
Hille–Yosida step consumes; what it still does *not* supply is strong continuity at `0`, which is
the hypothesis on the `TimeTranslation` and remains an input. -/

/-- **`P(0) = 1` on `ℋ`.** -/
theorem physEvolCompletion_zero (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F) :
    physEvolCompletion Λ T hinv 0 = ContinuousLinearMap.id ℝ (Hphys Λ) := by
  refine ContinuousLinearMap.ext fun z => ?_
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq (ContinuousLinearMap.continuous _) continuous_id) (fun a => ?_)
  rw [ContinuousLinearMap.id_apply, physEvolCompletion_coe, physEvol_zero]

/-- **`P(s + t) = P(s) ∘ P(t)` on `ℋ`.**  Together with `physEvolCompletion_zero` this makes the
time evolution a one-parameter contraction semigroup on the reconstructed Hilbert space, i.e. the
object Hille–Yosida/Stone theory takes a generator of. -/
theorem physEvolCompletion_add (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (s t : ℝ) :
    physEvolCompletion Λ T hinv (s + t)
      = (physEvolCompletion Λ T hinv s).comp (physEvolCompletion Λ T hinv t) := by
  refine ContinuousLinearMap.ext fun z => ?_
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq (ContinuousLinearMap.continuous (physEvolCompletion Λ T hinv (s + t)))
      ((physEvolCompletion Λ T hinv s).comp
        (physEvolCompletion Λ T hinv t)).continuous)
    (fun a => ?_)
  rw [ContinuousLinearMap.comp_apply, physEvolCompletion_coe, physEvolCompletion_coe,
    physEvolCompletion_coe, physEvol_add]

end

end BookProof.OSReconstruction
