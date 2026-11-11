import Mathlib
import BookProof.OSReconstruction.HalfSpaceState

/-!
# The complexification of the half-space Hilbert space and the complex OS form

Plan: `cftproof.md`, **E3** — the half-space OS form `hsForm` of `HalfSpaceState` is real
(the corpus's observables are real-valued).  The CFT needs a complex Hilbert space, and this module
builds the complexification `ℂ ⊗_ℝ Hhalf` and restates the OS form as a complex sesquilinear form.

Mathlib has no complexification of a real inner product space, so the carrier is built explicitly:

* `HhalfC Λ = Hhalf Λ × Hhalf Λ`, with `ofReal x = (x, 0)` and the complex structure
  `cSMul (a + bi) (x, y) = (a x − b y, b x + a y)`, together with its `Module ℂ` instance;
* **`hsComplexForm`** — the complex OS form
  `⟪z, w⟫_ℂ = ⟪z₁,w₁⟫ + ⟪z₂,w₂⟫ + i(⟪z₁,w₂⟫ − ⟪z₂,w₁⟫)`, where `⟪·,·⟫` is the real inner
  product of `Hhalf` (which is `hsForm` on the dense subspace, `hsInner_eq`);
* `hsComplexForm_add_left`, `hsComplexForm_smul_left` — `ℂ`-**sesquilinearity in the first
  argument** (`⟪c • z, w⟫ = c̄ ⟪z, w⟫`, Mathlib's convention), `hsComplexForm_add_right`,
  `hsComplexForm_smul_right` — `ℂ`-linearity in the second, and `hsComplexForm_conj_symm` —
  conjugate symmetry: the form is a genuine complex inner product;
* `hsComplexForm_self_re` — `(⟪z,z⟫_ℂ).re = ‖z₁‖² + ‖z₂‖²`, hence `hsComplexForm_self_nonneg`;
* `hsComplexForm_self_eq_zero_iff` — definiteness;
* `hsComplexForm_ofReal` — **the real OS form is the restriction of the complex one**:
  `⟪ofReal x, ofReal y⟫_ℂ = ⟪x, y⟫_ℝ`;
* `hsComplexPreCore` — the `PreInnerProductSpace.Core ℂ` on `HhalfC`, and
  `instInnerProductSpaceHhalfC` — the registered **complex inner product space** structure;
* `norm_sq_hhalfC` — `‖z‖² = ‖z₁‖² + ‖z₂‖²`, with `norm_fst_le`, `norm_snd_le` (each coordinate is
  bounded by the norm) and `norm_le_add_coord` (`‖z‖ ≤ ‖z₁‖ + ‖z₂‖`);
* `norm_eq_zero_iff_hhalfC`, `instNormedAddCommGroupHhalfC` — the core seminorm separates points,
  so the complexification is a **normed** group (not just seminormed);
* `cauchySeq_fst`, `cauchySeq_snd`, `exists_tendsto_of_cauchySeq`, **`hhalfC_complete`** — the
  induced uniform structure is complete: a Cauchy sequence has Cauchy coordinates (each bounded
  by the norm), `Hhalf` is a completion, and the `ℓ¹` bound reassembles the two limits;
* `instHilbertSpaceHhalfC` — the registered **`HilbertSpace ℂ`** instance.

## Boundary

* **The carrier is a `def`, not an `abbrev`.**  `HhalfC Λ` is definitionally `Hhalf Λ × Hhalf Λ`,
  but as an `abbrev` the product type's own Mathlib instances (`Norm`, `UniformSpace`, …) competed
  with the norm and uniform structure derived from the complex OS form, so a `‖·‖` on `HhalfC`
  silently meant the *max* norm of the product.  With `def`, instance search does not unfold
  `HhalfC`, and the core norm is the only candidate; the inherited algebraic structure is
  re-registered (`instAddCommGroupHhalfC`, `instModuleRealHhalfC`) and the tuple constructors get
  their projections (`ofPair`, `fst_add`, …).  Completeness is then proved for the OS-form norm —
  `hhalfC_complete` — not for a norm it does not use.
* The norm is `‖z‖ = √((⟪z,z⟫_ℂ).re) = √(‖z₁‖² + ‖z₂‖²)`, i.e. the `ℓ²` norm, not the `max` norm of
  the product; the two are equivalent (`norm_fst_le`, `norm_le_add_coord`), which is what makes the
  coordinatewise completeness argument go through.
* The complex structure is the standard one; no attempt is made to relate it to the time reflection
  `θ` or to a specific representation of `Hhalf` as a space of functions.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity
open Filter
open scoped Topology RealInnerProductSpace ComplexConjugate

noncomputable section

/-! ## The carrier and its complex structure -/

/-- **The complexification of the half-space Hilbert space**: the product `Hhalf Λ × Hhalf Λ`, with
`(x, y)` read as `x + i y`.  It is a `def`, not an `abbrev`, so that the product type's own
Mathlib instances (notably the ∥·∥-norm of `Prod`) do not compete with the norm and uniform
structure derived below from the complex OS form. -/
def HhalfC (Λ : HalfSpaceState) : Type := Hhalf Λ × Hhalf Λ

set_option maxHeartbeats 1000000 in
-- The product's algebraic structure is inherited definitionally and re-registered because `HhalfC`
-- is a `def`; the instance search for it exceeds the default budget in this file.
set_option synthInstance.maxHeartbeats 1000000 in
instance instAddCommGroupHhalfC (Λ : HalfSpaceState) : AddCommGroup (HhalfC Λ) :=
  inferInstanceAs (AddCommGroup (Hhalf Λ × Hhalf Λ))

set_option maxHeartbeats 1000000 in
-- Same reason: `Module ℝ (Hhalf Λ)` is a completion instance and its synthesis is expensive here.
set_option synthInstance.maxHeartbeats 1000000 in
instance instModuleRealHhalfC (Λ : HalfSpaceState) : Module ℝ (HhalfC Λ) :=
  inferInstanceAs (Module ℝ (Hhalf Λ × Hhalf Λ))

/-! ### Projection lemmas

Because `HhalfC` is a `def`, the `Prod`-projection simp lemmas do not match it syntactically.  The
lemmas below restate them for `HhalfC` (all by `rfl`). -/

variable {Λ : HalfSpaceState}

@[ext] theorem hhalfC_ext {z w : HhalfC Λ} (h1 : z.1 = w.1) (h2 : z.2 = w.2) : z = w :=
  Prod.ext h1 h2

@[simp] theorem fst_mk {x y : Hhalf Λ} : ((x, y) : HhalfC Λ).1 = x := rfl
@[simp] theorem snd_mk {x y : Hhalf Λ} : ((x, y) : HhalfC Λ).2 = y := rfl
@[simp] theorem fst_add (z w : HhalfC Λ) : (z + w).1 = z.1 + w.1 := rfl
@[simp] theorem snd_add (z w : HhalfC Λ) : (z + w).2 = z.2 + w.2 := rfl
@[simp] theorem fst_zero : (0 : HhalfC Λ).1 = 0 := rfl
@[simp] theorem snd_zero : (0 : HhalfC Λ).2 = 0 := rfl
@[simp] theorem fst_neg (z : HhalfC Λ) : (-z).1 = -z.1 := rfl
@[simp] theorem snd_neg (z : HhalfC Λ) : (-z).2 = -z.2 := rfl
@[simp] theorem fst_sub (z w : HhalfC Λ) : (z - w).1 = z.1 - w.1 := rfl
@[simp] theorem snd_sub (z w : HhalfC Λ) : (z - w).2 = z.2 - w.2 := rfl
@[simp] theorem fst_smul (c : ℝ) (z : HhalfC Λ) : (c • z).1 = c • z.1 := rfl
@[simp] theorem snd_smul (c : ℝ) (z : HhalfC Λ) : (c • z).2 = c • z.2 := rfl

/-- The real part embedding `x ↦ x + i 0`. -/
def ofReal (Λ : HalfSpaceState) (x : Hhalf Λ) : HhalfC Λ := (x, 0)

/-- The imaginary part embedding `y ↦ 0 + i y`. -/
def ofImag (Λ : HalfSpaceState) (y : Hhalf Λ) : HhalfC Λ := (0, y)

/-- The pair `x + i y`, with both entries typed as `Hhalf Λ` (the tuple notation alone would be
elaborated at the product type, which is only *definitionally* `HhalfC Λ`). -/
def ofPair (Λ : HalfSpaceState) (x y : Hhalf Λ) : HhalfC Λ := (x, y)

@[simp] theorem fst_ofPair (Λ : HalfSpaceState) (x y : Hhalf Λ) : (ofPair Λ x y).1 = x := rfl

@[simp] theorem snd_ofPair (Λ : HalfSpaceState) (x y : Hhalf Λ) : (ofPair Λ x y).2 = y := rfl

/-- The real part. -/
def rePart (Λ : HalfSpaceState) (z : HhalfC Λ) : Hhalf Λ := z.1

/-- The imaginary part. -/
def imPart (Λ : HalfSpaceState) (z : HhalfC Λ) : Hhalf Λ := z.2

/-- The complex scalar action: `(a + bi)(x + iy) = (ax − by) + i(bx + ay)`. -/
def cSMul (Λ : HalfSpaceState) (c : ℂ) (z : HhalfC Λ) : HhalfC Λ :=
  (c.re • z.1 - c.im • z.2, c.im • z.1 + c.re • z.2)

instance instSMulComplexHhalfC (Λ : HalfSpaceState) : SMul ℂ (HhalfC Λ) :=
  ⟨cSMul Λ⟩

theorem cSMul_apply (Λ : HalfSpaceState) (c : ℂ) (z : HhalfC Λ) :
    c • z = (c.re • z.1 - c.im • z.2, c.im • z.1 + c.re • z.2) := rfl

theorem fst_cSMul (Λ : HalfSpaceState) (c : ℂ) (z : HhalfC Λ) :
    (c • z).1 = c.re • z.1 - c.im • z.2 := rfl

theorem snd_cSMul (Λ : HalfSpaceState) (c : ℂ) (z : HhalfC Λ) :
    (c • z).2 = c.im • z.1 + c.re • z.2 := rfl

set_option maxHeartbeats 1000000 in
-- `Module ℝ (Hhalf Λ)` is a `UniformSpace.Completion` instance; its synthesis exceeds the default
-- instance-search budget in this file.
set_option synthInstance.maxHeartbeats 1000000 in
/-- **`HhalfC` is a complex vector space.**  Each field is checked componentwise through
`hhalfC_ext`, with `fst_cSMul`/`snd_cSMul` reducing the complex scalar action. -/
instance instModuleComplexHhalfC (Λ : HalfSpaceState) : Module ℂ (HhalfC Λ) where
  smul := cSMul Λ
  one_smul z := by
    apply hhalfC_ext <;> simp [fst_cSMul, snd_cSMul]
  mul_smul c d z := by
    apply hhalfC_ext <;>
      simp [fst_cSMul, snd_cSMul, Complex.mul_re, Complex.mul_im, sub_smul, add_smul, smul_sub,
        smul_add, mul_smul] <;>
      module
  smul_zero r := by
    apply hhalfC_ext <;> simp [fst_cSMul, snd_cSMul]
  smul_add c z w := by
    apply hhalfC_ext <;> simp [fst_cSMul, snd_cSMul, smul_add] <;> abel
  add_smul c d z := by
    apply hhalfC_ext <;>
      simp [fst_cSMul, snd_cSMul, Complex.add_re, Complex.add_im, add_smul] <;> abel
  zero_smul z := by
    apply hhalfC_ext <;> simp [fst_cSMul, snd_cSMul]

/-! ## The complex OS form -/

/-- **The complexification of the OS form**:
`⟪z, w⟫_ℂ = ⟪z₁,w₁⟫ + ⟪z₂,w₂⟫ + i(⟪z₁,w₂⟫ − ⟪z₂,w₁⟫)`, with `⟪·,·⟫` the real OS inner product. -/
def hsComplexForm (Λ : HalfSpaceState) (z w : HhalfC Λ) : ℂ :=
  (⟪z.1, w.1⟫ : ℝ) + (⟪z.2, w.2⟫ : ℝ)
    + Complex.I * ((⟪z.1, w.2⟫ : ℝ) - (⟪z.2, w.1⟫ : ℝ))

theorem hsComplexForm_apply (Λ : HalfSpaceState) (z w : HhalfC Λ) :
    hsComplexForm Λ z w
      = (⟪z.1, w.1⟫ : ℝ) + (⟪z.2, w.2⟫ : ℝ)
        + Complex.I * ((⟪z.1, w.2⟫ : ℝ) - (⟪z.2, w.1⟫ : ℝ)) := rfl

/-- **The real OS form is the complex form on the real axis**: `⟪ofReal x, ofReal y⟫_ℂ = ⟪x,y⟫`. -/
theorem hsComplexForm_ofReal (Λ : HalfSpaceState) (x y : Hhalf Λ) :
    hsComplexForm Λ (ofReal Λ x) (ofReal Λ y) = (⟪x, y⟫ : ℝ) := by
  simp [hsComplexForm, ofReal]

theorem hsComplexForm_add_left (Λ : HalfSpaceState) (z z' w : HhalfC Λ) :
    hsComplexForm Λ (z + z') w = hsComplexForm Λ z w + hsComplexForm Λ z' w := by
  simp only [hsComplexForm, fst_add, snd_add, inner_add_left]
  push_cast
  ring

theorem hsComplexForm_add_right (Λ : HalfSpaceState) (z w w' : HhalfC Λ) :
    hsComplexForm Λ z (w + w') = hsComplexForm Λ z w + hsComplexForm Λ z w' := by
  simp only [hsComplexForm, fst_add, snd_add, inner_add_right]
  push_cast
  ring

/-- **`ℂ`-sesquilinearity in the first argument**: `⟪c • z, w⟫ = c̄ ⟪z, w⟫`. -/
theorem hsComplexForm_smul_left (Λ : HalfSpaceState) (c : ℂ) (z w : HhalfC Λ) :
    hsComplexForm Λ (c • z) w = (starRingEnd ℂ) c * hsComplexForm Λ z w := by
  rw [cSMul_apply,
    show (starRingEnd ℂ) c = (↑c.re : ℂ) - ↑c.im * Complex.I from by
      apply Complex.ext <;> simp]
  simp only [hsComplexForm, inner_add_left, inner_sub_left, real_inner_smul_left]
  push_cast
  ring_nf
  simp only [pow_two, Complex.I_mul_I]
  ring

/-- **`ℂ`-linearity in the second argument**: `⟪z, c • w⟫ = c ⟪z, w⟫`. -/
theorem hsComplexForm_smul_right (Λ : HalfSpaceState) (c : ℂ) (z w : HhalfC Λ) :
    hsComplexForm Λ z (c • w) = c * hsComplexForm Λ z w := by
  rw [cSMul_apply]
  conv_rhs =>
    rw [show c = (↑c.re : ℂ) + ↑c.im * Complex.I from by apply Complex.ext <;> simp]
  simp only [hsComplexForm, inner_add_right, inner_sub_right, real_inner_smul_right]
  push_cast
  ring_nf
  simp only [pow_two, Complex.I_mul_I]
  ring

/-- **Conjugate symmetry**: `conj ⟪w, z⟫ = ⟪z, w⟫`. -/
theorem hsComplexForm_conj_symm (Λ : HalfSpaceState) (z w : HhalfC Λ) :
    (starRingEnd ℂ) (hsComplexForm Λ w z) = hsComplexForm Λ z w := by
  simp only [hsComplexForm, map_add, map_mul, map_sub, Complex.conj_I, Complex.conj_ofReal,
    real_inner_comm z.1 w.1, real_inner_comm z.2 w.2, real_inner_comm z.1 w.2,
    real_inner_comm z.2 w.1]
  ring_nf

/-- **The real part of the form of a vector is its norm squared**:
`(⟪z,z⟫_ℂ).re = ‖z₁‖² + ‖z₂‖²`. -/
theorem hsComplexForm_self_re (Λ : HalfSpaceState) (z : HhalfC Λ) :
    (hsComplexForm Λ z z).re = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  rw [hsComplexForm_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_re, Complex.sub_im, mul_zero, zero_mul, add_zero, sub_zero]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- Positivity of the real part on the diagonal. -/
theorem hsComplexForm_self_nonneg (Λ : HalfSpaceState) (z : HhalfC Λ) :
    0 ≤ (hsComplexForm Λ z z).re := by
  rw [hsComplexForm_self_re]
  positivity

/-- **Definiteness**: the complex form of a vector with itself vanishes only at zero. -/
theorem hsComplexForm_self_eq_zero_iff (Λ : HalfSpaceState) (z : HhalfC Λ) :
    hsComplexForm Λ z z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hre : (hsComplexForm Λ z z).re = 0 := by rw [h]; rfl
    rw [hsComplexForm_self_re] at hre
    have h1 : ‖z.1‖ = 0 := by
      nlinarith [norm_nonneg z.1, norm_nonneg z.2, sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
    have h2 : ‖z.2‖ = 0 := by
      nlinarith [norm_nonneg z.1, norm_nonneg z.2, sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
    exact hhalfC_ext (norm_eq_zero.1 h1) (norm_eq_zero.1 h2)
  · rintro rfl
    simp [hsComplexForm]

/-! ## The complex inner-product structure -/

/-- **The `ℂ`-pre-inner-product core** on the complexification.  Definiteness is not a field of
`PreInnerProductSpace.Core`; it is `hsComplexForm_self_eq_zero_iff`. -/
def hsComplexPreCore (Λ : HalfSpaceState) : PreInnerProductSpace.Core ℂ (HhalfC Λ) where
  inner := hsComplexForm Λ
  conj_inner_symm := hsComplexForm_conj_symm Λ
  re_inner_nonneg z := hsComplexForm_self_nonneg Λ z
  add_left := hsComplexForm_add_left Λ
  smul_left x y r := hsComplexForm_smul_left Λ r x y

/-- The seminormed group structure induced by the complex OS form. -/
abbrev hsComplexSeminormed (Λ : HalfSpaceState) : SeminormedAddCommGroup (HhalfC Λ) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ (HhalfC Λ) _ _ _ (hsComplexPreCore Λ)

/-- **The complexification, via `InnerProductSpace.ofCore`**. -/
def hsComplexInnerProductSpace (Λ : HalfSpaceState) :
    @InnerProductSpace ℂ (HhalfC Λ) _ (hsComplexSeminormed Λ) :=
  InnerProductSpace.ofCore (hsComplexPreCore Λ)

instance instSeminormedHhalfC (Λ : HalfSpaceState) : SeminormedAddCommGroup (HhalfC Λ) :=
  hsComplexSeminormed Λ

/-- **The complexified half-space space is a complex inner product space**, with the inner product
the complexification of the OS form. -/
instance instInnerProductSpaceHhalfC (Λ : HalfSpaceState) : InnerProductSpace ℂ (HhalfC Λ) :=
  hsComplexInnerProductSpace Λ

/-- On `HhalfC` the inner product is the complex OS form. -/
theorem inner_hhalfC_eq (Λ : HalfSpaceState) (z w : HhalfC Λ) :
    inner ℂ z w = hsComplexForm Λ z w := rfl

/-! ## The norm, definiteness and completeness

`InnerProductSpace.ofCore` gives `HhalfC` the norm `‖z‖ = √((⟪z,z⟫_ℂ).re) = √(‖z₁‖² + ‖z₂‖²)`.
Its uniformity is generated by that norm; the lemmas below show it is the product uniformity up to
the standard `max`/`ℓ²` equivalence, so the completed halves make `HhalfC` complete. -/

/-- **The norm in coordinates**: `‖z‖² = ‖z₁‖² + ‖z₂‖²`. -/
theorem norm_sq_hhalfC (Λ : HalfSpaceState) (z : HhalfC Λ) :
    ‖z‖ ^ 2 = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_hhalfC_eq]
  simpa using hsComplexForm_self_re Λ z

/-- Each coordinate is controlled by the norm. -/
theorem norm_fst_le (Λ : HalfSpaceState) (z : HhalfC Λ) : ‖z.1‖ ≤ ‖z‖ := by
  have h := norm_sq_hhalfC Λ z
  nlinarith [norm_nonneg z.1, norm_nonneg z, sq_nonneg ‖z.2‖]

/-- Each coordinate is controlled by the norm. -/
theorem norm_snd_le (Λ : HalfSpaceState) (z : HhalfC Λ) : ‖z.2‖ ≤ ‖z‖ := by
  have h := norm_sq_hhalfC Λ z
  nlinarith [norm_nonneg z.2, norm_nonneg z, sq_nonneg ‖z.1‖]

/-- The norm is controlled by the two coordinate norms (the `ℓ¹` bound). -/
theorem norm_le_add_coord (Λ : HalfSpaceState) (z : HhalfC Λ) :
    ‖z‖ ≤ ‖z.1‖ + ‖z.2‖ := by
  have h := norm_sq_hhalfC Λ z
  have h1 : ‖z‖ ^ 2 ≤ (‖z.1‖ + ‖z.2‖) ^ 2 := by
    nlinarith [mul_nonneg (norm_nonneg z.1) (norm_nonneg z.2)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg z) (by positivity) (by norm_num)).1 h1

/-- **The core norm is definite** (from definiteness of the complex OS form), so the seminormed
group of the complexification is a normed group. -/
theorem norm_eq_zero_iff_hhalfC (Λ : HalfSpaceState) (z : HhalfC Λ) : ‖z‖ = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h2 := norm_sq_hhalfC Λ z
    rw [h] at h2
    have h1 : ‖z.1‖ = 0 := by
      nlinarith [norm_nonneg z.1, sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
    have h3 : ‖z.2‖ = 0 := by
      nlinarith [norm_nonneg z.2, sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
    exact hhalfC_ext (norm_eq_zero.1 h1) (norm_eq_zero.1 h3)
  · rintro rfl
    simp

instance instNormedAddCommGroupHhalfC (Λ : HalfSpaceState) : NormedAddCommGroup (HhalfC Λ) :=
  NormedAddCommGroup.ofSeparation (fun z hz => (norm_eq_zero_iff_hhalfC Λ z).1 hz)

/-- A Cauchy sequence in the complexification has Cauchy coordinates. -/
theorem cauchySeq_fst (Λ : HalfSpaceState) {f : ℕ → HhalfC Λ} (hf : CauchySeq f) :
    CauchySeq fun n => (f n).1 := by
  rw [Metric.cauchySeq_iff] at hf ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hf ε hε
  refine ⟨N, fun m hm n hn => lt_of_le_of_lt ?_ (hN m hm n hn)⟩
  calc dist (f m).1 (f n).1
      = ‖(f m).1 - (f n).1‖ := dist_eq_norm _ _
    _ = ‖(f m - f n).1‖ := rfl
    _ ≤ ‖f m - f n‖ := norm_fst_le Λ (f m - f n)
    _ = dist (f m) (f n) := (dist_eq_norm _ _).symm

/-- A Cauchy sequence in the complexification has Cauchy coordinates. -/
theorem cauchySeq_snd (Λ : HalfSpaceState) {f : ℕ → HhalfC Λ} (hf : CauchySeq f) :
    CauchySeq fun n => (f n).2 := by
  rw [Metric.cauchySeq_iff] at hf ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hf ε hε
  refine ⟨N, fun m hm n hn => lt_of_le_of_lt ?_ (hN m hm n hn)⟩
  calc dist (f m).2 (f n).2
      = ‖(f m).2 - (f n).2‖ := dist_eq_norm _ _
    _ = ‖(f m - f n).2‖ := rfl
    _ ≤ ‖f m - f n‖ := norm_snd_le Λ (f m - f n)
    _ = dist (f m) (f n) := (dist_eq_norm _ _).symm

/-- **Cauchy sequences converge** in the complexification: the coordinate limits exist because
`Hhalf` is a completion, and the `ℓ¹` norm bound reassembles them. -/
theorem exists_tendsto_of_cauchySeq (Λ : HalfSpaceState) {f : ℕ → HhalfC Λ}
    (hf : CauchySeq f) :
    ∃ z, Tendsto f atTop (𝓝 z) := by
  obtain ⟨x1, hx1⟩ := cauchySeq_tendsto_of_complete (cauchySeq_fst Λ hf)
  obtain ⟨x2, hx2⟩ := cauchySeq_tendsto_of_complete (cauchySeq_snd Λ hf)
  refine ⟨ofPair Λ x1 x2, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsum : Tendsto (fun n => ‖(f n).1 - x1‖ + ‖(f n).2 - x2‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ‖(f n).1 - x1‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hx1
    have h2 : Tendsto (fun n => ‖(f n).2 - x2‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hx2
    simpa using h1.add h2
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsum
  calc ‖f n - ofPair Λ x1 x2‖
      ≤ ‖(f n - ofPair Λ x1 x2).1‖ + ‖(f n - ofPair Λ x1 x2).2‖ := norm_le_add_coord Λ _
    _ = ‖(f n).1 - x1‖ + ‖(f n).2 - x2‖ := rfl

/-- **The complexified half-space space is complete.** -/
theorem hhalfC_complete (Λ : HalfSpaceState) : CompleteSpace (HhalfC Λ) :=
  Metric.complete_of_cauchySeq_tendsto (fun _ hf => exists_tendsto_of_cauchySeq Λ hf)

instance instCompleteSpaceHhalfC (Λ : HalfSpaceState) : CompleteSpace (HhalfC Λ) :=
  hhalfC_complete Λ

/-- **The complexified half-space carrier is a complex Hilbert space**: the OS form is a definite
inner product (`hsComplexForm_self_eq_zero_iff`) and the induced uniform structure is complete
(`hhalfC_complete`). -/
instance instHilbertSpaceHhalfC (Λ : HalfSpaceState) : HilbertSpace ℂ (HhalfC Λ) := ⟨⟩

end

end BookProof.OSReconstruction
