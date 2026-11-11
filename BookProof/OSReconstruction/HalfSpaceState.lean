import Mathlib
import BookProof.OSReconstruction.ReflectionKernel

/-!
# The half-space state and the OS quotient on `𝔄₊`

Plan: `cftproof.md`, **E3** — "Construct the complex sesquilinear form
`⟨F,G⟩_OS = ω((ΘF)G)` on `𝒜₊`, its null **subspace** `𝒩`, and the completion of
`𝒜₊/𝒩`.  …  Include the unit to define `Ω_OS = [1]` and prove `‖Ω_OS‖ = 1`."

`OSReconstruction.HilbertSpace` assembles the quotient `𝔄 / 𝔑` from a state that is reflection
positive on the *whole* observable algebra.  `ReflectionKernel` shows why that is the wrong
hypothesis: for a genuine state, full-algebra reflection positivity forces `θ` to be the identity
on `𝔄 / 𝔑` (`mk_thetaObs_eq_mk`), so the reconstruction loses its time direction.  The physical
hypothesis is reflection positivity **on `𝔄₊` only**, and this module builds the quotient from
that weaker input instead of feeding it to `OSState`.

## Contents

* `HalfSpaceState` — a `θ`-invariant linear functional, reflection positive on `𝔄₊`, normalized
  (`ω 1 = 1`).  All three are separate fields: positivity is *not* extended to all observables,
  and the normalization is what makes the vacuum a unit vector;
* `hsBilin` and its bilinearity / symmetry — the OS form restricted to `𝔄₊ × 𝔄₊`.  Symmetry is
  inherited from `θ`-invariance of the state and commutativity of the observable algebra, exactly
  as in `osForm_symm'`; it does *not* need positivity;
* `hsBilin_expand`, **`hsBilin_cauchy_schwarz`** — the quadratic expansion and Cauchy–Schwarz,
  proved from `hsBilin_self_nonneg` alone, i.e. from the half-space hypothesis;
* `HsRadical` — the null **submodule** `𝔑₊ = {F ∈ 𝔄₊ | ∀ G ∈ 𝔄₊, ⟨F,G⟩ = 0}`,
  `mem_hsRadical_of_self_eq_zero` — it is exactly the null set (Cauchy–Schwarz), and
  `hsBilin_well_defined` — the form descends to it;
* `HsSpace` — the quotient `𝔄₊ / 𝔑₊`, with `hsForm` the descended form, its inner-product cores
  `hsPreCore` / `hsCore`, the registered `InnerProductSpace` instance, and `Hhalf` its
  completion: the reconstructed Hilbert space of the half-space carrier;
* `hsVacuum` — `Ω_OS = [1]`, with **`hsVacuum_norm`**: `‖Ω_OS‖ = 1`.

## Boundary

* **`𝔑₊` is not claimed to be an algebra ideal.**  `PositiveTimeAlgebra` is closed under
  multiplication, but ideal stability of the null set would need the state to be multiplicative or
  the form to be an algebra form, and neither is available.  `HsSpace` is therefore a quotient of
  vector spaces, which is all the completion consumes; the multiplication is not descended.
* **The form is real.**  The corpus's observables are real-valued, so `hsForm` is an
  `ℝ`-bilinear form.  The plan's complex sesquilinear form is the complexification of this one
  (`ℂ ⊗_ℝ HsSpace` with the conjugate-linear first slot); that complexification is *not* built
  here, and no complex Hilbert space is claimed.  `hsForm` is the real structure the plan calls a
  "reusable prototype".
* The observable algebra is `Config → ℝ` with `Config = Fin latticeDim → ℝ`
  (`ReflectionPositivity.HalfSpaceAlgebra`), and `𝔄₊` is read as *dependence* on the positive-time
  components, not pointwise support.  Both are the corpus's model choices, recorded there.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity

noncomputable section

/-! ## The half-space state -/

/-- **A half-space state**: a `θ`-invariant linear functional on the observables that is reflection
positive on the positive-time algebra `𝔄₊` and normalized on the unit.

This is deliberately *not* an `OSState`: the latter's `pos` field quantifies over every observable,
and `ReflectionKernel.mk_thetaObs_eq_mk` shows that hypothesis trivialises the reflection. -/
structure HalfSpaceState where
  /-- The expectation functional. -/
  ω : LinearFunctional
  /-- Reflection positivity **on the half-space algebra only**. -/
  pos : IsReflectionPositiveOn (PositiveTimeAlgebra : Set Observable) (fun F => ω.toFun F)
  /-- Normalization on the unit, so that the reconstructed vacuum has norm one. -/
  norm_one : ω.toFun (1 : Observable) = 1

/-! ## The OS form on `𝔄₊` -/

/-- **The OS form on the positive-time algebra**: `⟨F, G⟩ = ω(θF · G)` for `F, G ∈ 𝔄₊`.
`θF` lies in the past algebra (`thetaObs_dependsOn_negTime`), so the product is an observable and
the state evaluates it; only the *positivity* of the form is restricted to `𝔄₊`. -/
def hsBilin (Λ : HalfSpaceState) (F G : PositiveTimeAlgebra) : ℝ :=
  osBilin Λ.ω (F : Observable) (G : Observable)

theorem hsBilin_apply (Λ : HalfSpaceState) (F G : PositiveTimeAlgebra) :
    hsBilin Λ F G = Λ.ω.toFun (thetaObs (F : Observable) * (G : Observable)) := rfl

theorem hsBilin_add_left (Λ : HalfSpaceState) (F G H : PositiveTimeAlgebra) :
    hsBilin Λ (F + G) H = hsBilin Λ F H + hsBilin Λ G H := by
  simpa [hsBilin] using osForm_add_left Λ.ω (F : Observable) (G : Observable) (H : Observable)

theorem hsBilin_smul_left (Λ : HalfSpaceState) (c : ℝ) (F G : PositiveTimeAlgebra) :
    hsBilin Λ (c • F) G = c * hsBilin Λ F G := by
  simpa [hsBilin] using osForm_smul_left Λ.ω c (F : Observable) (G : Observable)

theorem hsBilin_add_right (Λ : HalfSpaceState) (F G H : PositiveTimeAlgebra) :
    hsBilin Λ F (G + H) = hsBilin Λ F G + hsBilin Λ F H := by
  simpa [hsBilin] using osForm_add_right' Λ.ω (F : Observable) (G : Observable) (H : Observable)

theorem hsBilin_smul_right (Λ : HalfSpaceState) (c : ℝ) (F G : PositiveTimeAlgebra) :
    hsBilin Λ F (c • G) = c * hsBilin Λ F G := by
  simpa [hsBilin] using osForm_smul_right' Λ.ω c (F : Observable) (G : Observable)

/-- `hsBilin Λ 0 G = 0`, from linearity of the state. -/
theorem hsBilin_zero_left (Λ : HalfSpaceState) (G : PositiveTimeAlgebra) :
    hsBilin Λ 0 G = 0 := by
  have h : hsBilin Λ (0 : PositiveTimeAlgebra) G
      = hsBilin Λ (0 : PositiveTimeAlgebra) G + hsBilin Λ (0 : PositiveTimeAlgebra) G := by
    simpa using hsBilin_add_left Λ 0 0 G
  linarith

/-- **Symmetry of the OS form on `𝔄₊`**, from `θ`-invariance of the state: `θ(θF · G) = F · θG`,
so `ω(θF · G) = ω(F · θG) = ω(θG · F)`.  No positivity is used. -/
theorem hsBilin_symm (Λ : HalfSpaceState) (F G : PositiveTimeAlgebra) :
    hsBilin Λ F G = hsBilin Λ G F :=
  osForm_symm' Λ.ω (F : Observable) (G : Observable)

/-- **Positivity of the form on `𝔄₊`** is the state's half-space reflection positivity,
verbatim. -/
theorem hsBilin_self_nonneg (Λ : HalfSpaceState) (F : PositiveTimeAlgebra) :
    0 ≤ hsBilin Λ F F :=
  Λ.pos F F.2

/-- The quadratic expansion on `𝔄₊`. -/
theorem hsBilin_expand (Λ : HalfSpaceState) (F G : PositiveTimeAlgebra) (t : ℝ) :
    hsBilin Λ (F + t • G) (F + t • G)
      = hsBilin Λ F F + 2 * t * hsBilin Λ F G + t ^ 2 * hsBilin Λ G G := by
  have hFG : hsBilin Λ G F = hsBilin Λ F G := hsBilin_symm Λ G F
  rw [hsBilin_add_left, hsBilin_smul_left, hsBilin_add_right, hsBilin_smul_right,
    hsBilin_add_right, hsBilin_smul_right, hFG]
  ring

/-- **Cauchy–Schwarz on `𝔄₊`**, from the half-space positivity alone.  The proof is
`PhysicalSpace.osForm_cauchy_schwarz`'s, with the hypothesis restricted to the carrier. -/
theorem hsBilin_cauchy_schwarz (Λ : HalfSpaceState) (F G : PositiveTimeAlgebra) :
    hsBilin Λ F G ^ 2 ≤ hsBilin Λ F F * hsBilin Λ G G := by
  set a := hsBilin Λ F F with ha
  set b := hsBilin Λ F G with hb
  set c := hsBilin Λ G G with hc
  have ha0 : 0 ≤ a := hsBilin_self_nonneg Λ F
  have hc0 : 0 ≤ c := hsBilin_self_nonneg Λ G
  have key : ∀ t : ℝ, 0 ≤ a + 2 * t * b + t ^ 2 * c := by
    intro t
    have h := hsBilin_self_nonneg Λ (F + t • G)
    rw [hsBilin_expand Λ F G t, ← ha, ← hb, ← hc] at h
    exact h
  rcases lt_or_eq_of_le hc0 with hcpos | hc0'
  · have h := key (-b / c)
    have hquad : a + 2 * (-b / c) * b + (-b / c) ^ 2 * c = a - b ^ 2 / c := by
      field_simp
      ring
    rw [hquad] at h
    have h' : b ^ 2 / c ≤ a := by linarith
    rw [div_le_iff₀ hcpos] at h'
    linarith
  · have hb0 : b = 0 := by
      by_contra hbne
      have h := key (-(a + 1) / (2 * b))
      rw [← hc0'] at h
      have hquad : a + 2 * (-(a + 1) / (2 * b)) * b + (-(a + 1) / (2 * b)) ^ 2 * 0 =
          a - (a + 1) := by
        field_simp
        ring
      rw [hquad] at h
      linarith
    rw [hb0, ← hc0']
    simp

/-! ## The null subspace `𝔑₊` -/

/-- **The null subspace of the half-space OS form**:
`𝔑₊ = {F ∈ 𝔄₊ | ⟨F, G⟩ = 0 for every G ∈ 𝔄₊}`.

It is a submodule by construction.  It is *not* claimed to be an algebra ideal: `𝔄₊` is a
subalgebra, but ideal stability of the null set is not available from reflection positivity, and
the quotient below is used as a vector space only. -/
def HsRadical (Λ : HalfSpaceState) : Submodule ℝ PositiveTimeAlgebra where
  carrier := {F | ∀ G : PositiveTimeAlgebra, hsBilin Λ F G = 0}
  zero_mem' := fun G => hsBilin_zero_left Λ G
  add_mem' := by
    intro F H hF hH G
    rw [hsBilin_add_left, hF G, hH G, add_zero]
  smul_mem' := by
    intro c F hF G
    rw [hsBilin_smul_left, hF G, mul_zero]

theorem mem_hsRadical_iff {Λ : HalfSpaceState} {F : PositiveTimeAlgebra} :
    F ∈ HsRadical Λ ↔ ∀ G : PositiveTimeAlgebra, hsBilin Λ F G = 0 := Iff.rfl

/-- **Membership in `𝔑₊` from vanishing on the diagonal** (Cauchy–Schwarz). -/
theorem mem_hsRadical_of_self_eq_zero (Λ : HalfSpaceState) {F : PositiveTimeAlgebra}
    (hF : hsBilin Λ F F = 0) : F ∈ HsRadical Λ := by
  intro G
  have h := hsBilin_cauchy_schwarz Λ F G
  rw [hF, zero_mul] at h
  have hsq : hsBilin Λ F G ^ 2 = 0 := by linarith [sq_nonneg (hsBilin Λ F G)]
  exact pow_eq_zero_iff two_ne_zero |>.1 hsq

/-- **The form descends to `𝔑₊`**: `⟨F, G⟩` depends only on the class of `F`. -/
theorem hsBilin_well_defined (Λ : HalfSpaceState) {F F' : PositiveTimeAlgebra}
    (h : F - F' ∈ HsRadical Λ) (G : PositiveTimeAlgebra) :
    hsBilin Λ F G = hsBilin Λ F' G := by
  have h1 : hsBilin Λ (F - F') G = 0 := h G
  have hexp : hsBilin Λ (F - F') G = hsBilin Λ F G - hsBilin Λ F' G := by
    rw [sub_eq_add_neg, hsBilin_add_left]
    congr 1
    rw [show (-F' : PositiveTimeAlgebra) = (-1 : ℝ) • F' from by simp]
    rw [hsBilin_smul_left]
    ring
  linarith

/-! ## The quotient `𝔄₊ / 𝔑₊` -/

/-- The OS form as a bilinear map on `𝔄₊`. -/
def hsBilinMap (Λ : HalfSpaceState) :
    PositiveTimeAlgebra →ₗ[ℝ] PositiveTimeAlgebra →ₗ[ℝ] ℝ where
  toFun F :=
    { toFun := fun G => hsBilin Λ F G
      map_add' := fun G H => hsBilin_add_right Λ F G H
      map_smul' := fun c G => hsBilin_smul_right Λ c F G }
  map_add' F H := LinearMap.ext fun G => hsBilin_add_left Λ F H G
  map_smul' c F := LinearMap.ext fun G => hsBilin_smul_left Λ c F G

@[simp]
theorem hsBilinMap_apply (Λ : HalfSpaceState) (F G : PositiveTimeAlgebra) :
    hsBilinMap Λ F G = hsBilin Λ F G := rfl

/-- **The OS form on the quotient `𝔄₊ / 𝔑₊`**, descended by `LinearMap.liftQ₂`. -/
def hsForm (Λ : HalfSpaceState) :
    (PositiveTimeAlgebra ⧸ HsRadical Λ) →ₗ[ℝ]
      (PositiveTimeAlgebra ⧸ HsRadical Λ) →ₗ[ℝ] ℝ :=
  (hsBilinMap Λ).liftQ₂ (HsRadical Λ) (HsRadical Λ)
    (fun x hx => by
      rw [LinearMap.mem_ker]
      exact LinearMap.ext fun G => hx G)
    (fun y hy => by
      rw [LinearMap.mem_ker]
      exact LinearMap.ext fun F => (hsBilin_symm Λ F y).trans (hy F))

@[simp]
theorem hsForm_mk (Λ : HalfSpaceState) (F G : PositiveTimeAlgebra) :
    hsForm Λ (Submodule.Quotient.mk F) (Submodule.Quotient.mk G) = hsBilin Λ F G :=
  LinearMap.liftQ₂_mk _ _ _ _

theorem hsForm_add_left (Λ : HalfSpaceState)
    (x y z : PositiveTimeAlgebra ⧸ HsRadical Λ) :
    hsForm Λ (x + y) z = hsForm Λ x z + hsForm Λ y z := by
  rw [map_add]
  rfl

theorem hsForm_smul_left (Λ : HalfSpaceState) (c : ℝ)
    (x y : PositiveTimeAlgebra ⧸ HsRadical Λ) :
    hsForm Λ (c • x) y = c * hsForm Λ x y := by
  rw [map_smul]
  rfl

theorem hsForm_symm (Λ : HalfSpaceState) (x y : PositiveTimeAlgebra ⧸ HsRadical Λ) :
    hsForm Λ x y = hsForm Λ y x := by
  refine Submodule.Quotient.induction_on _ x fun F => ?_
  refine Submodule.Quotient.induction_on _ y fun G => ?_
  simp [hsBilin_symm Λ F G]

theorem hsForm_self_nonneg (Λ : HalfSpaceState)
    (x : PositiveTimeAlgebra ⧸ HsRadical Λ) : 0 ≤ hsForm Λ x x := by
  refine Submodule.Quotient.induction_on _ x fun F => ?_
  simpa using hsBilin_self_nonneg Λ F

/-- **Definiteness on the quotient**: `𝔑₊` is exactly the null set of the form, so the descended
form is an inner product. -/
theorem hsForm_self_eq_zero_iff (Λ : HalfSpaceState)
    (x : PositiveTimeAlgebra ⧸ HsRadical Λ) : hsForm Λ x x = 0 ↔ x = 0 := by
  constructor
  · refine Submodule.Quotient.induction_on _ x fun F => ?_
    intro hx
    have hF : F ∈ HsRadical Λ := mem_hsRadical_of_self_eq_zero Λ (by simpa using hx)
    exact (Submodule.Quotient.mk_eq_zero (HsRadical Λ) (x := F)).mpr hF
  · rintro rfl
    simp [hsForm]

/-- The expansion of the form of a difference on the quotient. -/
theorem hsForm_sub_sub (Λ : HalfSpaceState)
    (a b : PositiveTimeAlgebra ⧸ HsRadical Λ) :
    hsForm Λ (a - b) (a - b)
      = hsForm Λ a a - hsForm Λ a b - hsForm Λ b a + hsForm Λ b b := by
  simp only [map_sub, LinearMap.sub_apply]
  ring

/-! ## The inner-product structure and the completion -/

/-- The pre-inner-product core on `𝔄₊ / 𝔑₊`. -/
def hsPreCore (Λ : HalfSpaceState) :
    PreInnerProductSpace.Core ℝ (PositiveTimeAlgebra ⧸ HsRadical Λ) where
  inner x y := hsForm Λ x y
  conj_inner_symm x y := by
    rw [hsForm_symm Λ y x, RCLike.conj_to_real]
  re_inner_nonneg x := hsForm_self_nonneg Λ x
  add_left x y z := hsForm_add_left Λ x y z
  smul_left x y r := hsForm_smul_left Λ r x y

/-- The inner-product core on `𝔄₊ / 𝔑₊`, with definiteness. -/
def hsCore (Λ : HalfSpaceState) :
    InnerProductSpace.Core ℝ (PositiveTimeAlgebra ⧸ HsRadical Λ) where
  inner := (hsPreCore Λ).inner
  conj_inner_symm := (hsPreCore Λ).conj_inner_symm
  re_inner_nonneg := (hsPreCore Λ).re_inner_nonneg
  add_left := (hsPreCore Λ).add_left
  smul_left := (hsPreCore Λ).smul_left
  definite x hx := (hsForm_self_eq_zero_iff Λ x).1 hx

/-- The norm on `𝔄₊ / 𝔑₊` induced by the OS inner product. -/
abbrev hsSeminormed (Λ : HalfSpaceState) :
    SeminormedAddCommGroup (PositiveTimeAlgebra ⧸ HsRadical Λ) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℝ (PositiveTimeAlgebra ⧸ HsRadical Λ) _ _ _
    (hsPreCore Λ)

/-- **The OS inner-product space `𝔄₊ / 𝔑₊`**, via `InnerProductSpace.ofCore`. -/
def hsInnerProductSpace (Λ : HalfSpaceState) :
    @InnerProductSpace ℝ (PositiveTimeAlgebra ⧸ HsRadical Λ) _ (hsSeminormed Λ) :=
  InnerProductSpace.ofCore (hsPreCore Λ)

instance instSeminormedHsSpace (Λ : HalfSpaceState) :
    SeminormedAddCommGroup (PositiveTimeAlgebra ⧸ HsRadical Λ) :=
  hsSeminormed Λ

instance instInnerProductSpaceHsSpace (Λ : HalfSpaceState) :
    InnerProductSpace ℝ (PositiveTimeAlgebra ⧸ HsRadical Λ) :=
  hsInnerProductSpace Λ

/-- **The half-space carrier** `𝔄₊ / 𝔑₊` of the reconstruction. -/
abbrev HsSpace (Λ : HalfSpaceState) : Type := PositiveTimeAlgebra ⧸ HsRadical Λ

/-- The norm on the quotient is the square root of the OS form on the diagonal. -/
theorem hsNorm_eq (Λ : HalfSpaceState) (x : HsSpace Λ) :
    ‖x‖ = Real.sqrt (hsForm Λ x x) := rfl

/-- On the dense subspace, `‖mk F‖ = √⟨F,F⟩`. -/
theorem hsNorm_mk (Λ : HalfSpaceState) (F : PositiveTimeAlgebra) :
    ‖(Submodule.Quotient.mk F : HsSpace Λ)‖ = Real.sqrt (hsBilin Λ F F) := by
  rw [hsNorm_eq, hsForm_mk]

/-- The seminorm is a norm on the quotient. -/
theorem hsNorm_eq_zero_iff (Λ : HalfSpaceState) (x : HsSpace Λ) : ‖x‖ = 0 ↔ x = 0 := by
  rw [hsNorm_eq, Real.sqrt_eq_zero']
  constructor
  · intro h
    exact (hsForm_self_eq_zero_iff Λ x).1 (le_antisymm h (hsForm_self_nonneg Λ x))
  · rintro rfl
    simp [hsForm]

/-- **The half-space Hilbert space**: the completion of `𝔄₊ / 𝔑₊` in the OS norm. -/
abbrev Hhalf (Λ : HalfSpaceState) : Type := UniformSpace.Completion (HsSpace Λ)

instance instCompleteSpaceHhalf (Λ : HalfSpaceState) : CompleteSpace (Hhalf Λ) := inferInstance

instance instHilbertSpaceHhalf (Λ : HalfSpaceState) : HilbertSpace ℝ (Hhalf Λ) := ⟨⟩

/-- `𝔄₊ / 𝔑₊` is dense in its completion. -/
theorem denseRange_hsCoe (Λ : HalfSpaceState) : DenseRange ((↑) : HsSpace Λ → Hhalf Λ) :=
  UniformSpace.Completion.denseRange_coe

/-- The embedding of `𝔄₊ / 𝔑₊` into its completion, as a linear map. -/
def hsCoe (Λ : HalfSpaceState) : HsSpace Λ →ₗ[ℝ] Hhalf Λ where
  toFun x := (x : Hhalf Λ)
  map_add' := UniformSpace.Completion.coe_add
  map_smul' := UniformSpace.Completion.coe_smul

@[simp]
theorem hsCoe_apply (Λ : HalfSpaceState) (x : HsSpace Λ) : hsCoe Λ x = (x : Hhalf Λ) := rfl

/-- The quotient class of a half-space observable. -/
def hsMk (Λ : HalfSpaceState) (F : PositiveTimeAlgebra) : HsSpace Λ :=
  Submodule.Quotient.mk F

theorem hsCoe_hsMk (Λ : HalfSpaceState) (F : PositiveTimeAlgebra) :
    hsCoe Λ (hsMk Λ F) = ((Submodule.Quotient.mk F : HsSpace Λ) : Hhalf Λ) := rfl

/-! ## The vacuum `Ω_OS = [1]` -/

/-- **The reconstructed vacuum** `Ω_OS = [1]`.  The unit is available precisely because
`PositiveTimeAlgebra` is a *unital* subalgebra, and it bounds no observable. -/
def hsVacuum (Λ : HalfSpaceState) : HsSpace Λ :=
  Submodule.Quotient.mk (1 : PositiveTimeAlgebra)

/-- The OS form of the vacuum is the state on the unit. -/
theorem hsForm_vacuum (Λ : HalfSpaceState) : hsForm Λ (hsVacuum Λ) (hsVacuum Λ) = 1 := by
  rw [hsVacuum, hsForm_mk]
  have h : hsBilin Λ (1 : PositiveTimeAlgebra) (1 : PositiveTimeAlgebra)
      = Λ.ω.toFun (1 : Observable) := by
    simp [hsBilin, osBilin, osForm, thetaObs_one]
  rw [h, Λ.norm_one]

/-- **The vacuum is a unit vector**: `‖Ω_OS‖ = 1`.  This is where `ω 1 = 1` is consumed. -/
theorem hsVacuum_norm (Λ : HalfSpaceState) : ‖hsVacuum Λ‖ = 1 := by
  rw [hsNorm_eq, hsForm_vacuum, Real.sqrt_one]

/-- The vacuum is nonzero: `Ω_OS ≠ 0`. -/
theorem hsVacuum_ne_zero (Λ : HalfSpaceState) : hsVacuum Λ ≠ 0 := by
  intro h
  have hnorm := hsVacuum_norm Λ
  rw [h, norm_zero] at hnorm
  exact zero_ne_one hnorm

end

end BookProof.OSReconstruction
