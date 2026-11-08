import Mathlib
import BookProof.OSReconstruction.L2Multiplier
import BookProof.OSReconstruction.MultiplierGenerator

/-!
# The Hamiltonian of the multiplier model

`OSReconstruction.MultiplierGenerator` proved everything about the generator that can be seen from
the flow: `U (generatorRight y) = −M_f (U y)` on the multiplier domain, the range condition
`ran(λ − A) = ℋ`, and the a priori bound.  What it did **not** do is construct the self-adjoint
operator whose resolvent is the multiplier `(λ + f)⁻¹`; it recorded that gap in its boundary
paragraph.  This module closes it.

The construction is the classical shift-invert one, done in `ℝ`:

* `resolventMulModel` — the bounded operator `R = (λ + H)⁻¹`.  On the model side it is
  multiplication by `(λ + f)⁻¹`, so its norm is at most `1/λ` —
  `‖mulL2 W u‖ ≤ λ⁻¹‖u‖` because `‖(λ + f)⁻¹‖ ≤ 1/λ` in the essential supremum;
* `resolventMulModel_law` — the exact statement that makes `R` the inverse: applying the
  multiplier to the image gives back the vector,
  `λ·(U (R x)) + f·(U (R x)) = U x` in `L²(ν)`;
* `resolventMulModel_inner_comm` — `R` is symmetric, i.e. self-adjoint as a bounded operator: the
  multiplier is real, so multiplication by it commutes with the inner product;
* `resolventMulModel_injective` and `dense_range_resolventMulModel` — `R` has trivial kernel and
  dense range, both read off the shift law;
* `hamiltonianMulModel` — the Hamiltonian itself, `H = R⁻¹ − λ` on `ran R`:
  `hamiltonianMulModel_apply` reads `H (R x) = x − λ R x`, and `hamiltonianMulModel_image` gives
  `U (H (R x)) = mulImage D λ x`, the same image that `exists_generatorRight_mulModel` shows to be
  `−U (generatorRight (R x))`;
* `hamiltonianMulModel_isFormalAdjoint` and `hamiltonianMulModel_dense` — `H` is symmetric, and its
  domain `ran R` is dense;
* `le_adjoint_of_shift_surjective` — the abstract von Neumann criterion for a symmetric operator
  with `ran(λ + T) = ℋ` (`λ > 0`): `T† ≤ T`.  Fed `hamiltonianMulModel_resolvent`, it gives
  `hamiltonianMulModel_isSelfAdjoint`, i.e. `H† = H`;
* `hamiltonianMulModel_inner_nonneg` — `H ≥ 0`, quantitatively `⟪H y, y⟫ = ∫ f (U y)²`;
* `hamiltonianMulModel_resolvent` and `resolvent_hamiltonianMulModel` — `R` is *the* resolvent of
  `H` at `λ`: `λ x + H x` and `R` are mutually inverse on `ℋ` and on `dom H` respectively.

So the explicit family `(λ + f)⁻¹` is indeed the resolvent of a self-adjoint nonnegative operator.

## Boundary

The multiplier law `U (P(τ) x) = expFlow τ (U x)` is still a hypothesis: this module produces the
self-adjoint `H` *from the flow*, it does not produce the flow from the OS axioms.  It cannot do
so, and the reason is structural rather than technical: the OS axioms supply a contractive
semigroup on `ℋ` and its two-point functions, while the law says `U` diagonalizes its generator
with simple spectrum `f`; two different `f` satisfy the same axioms with different `H`, so the
identification is the choice of KL multiplier realization.  What is missing for a derivation is
the spectral theorem for the generator (equivalently Stone's theorem), which Mathlib does not have.

The identification `generatorRight = −H` is proved only up to the `MemLp` presentation: the two
modules carry the vector `f · U y` with different membership proofs, so `hamiltonianMulModel_image`
and `exists_generatorRight_mulModel` name the same `L²` class through `mulImage` rather than by a
single equality in this file.
-/

namespace BookProof.OSReconstruction

open Filter MeasureTheory
open scoped Topology RealInnerProductSpace ENNReal

noncomputable section

variable {Λ : OSState} {T : TimeTranslation}
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-! ## The model data -/

/-- **The data of the multiplier model**, bundled.  It is exactly the hypothesis list of
`exists_resolvent_mulModel`: positivity of `f`, the isometry `U`, its dense range, and the
multiplier law for the transfer semigroup. -/
structure MulModel (X : Type*) [MeasurableSpace X] (ν : Measure X) (Λ : OSState)
    (T : TimeTranslation) where
  /-- Time translations exist. -/
  hinv : HinvRight Λ T
  /-- The Hamiltonian density. -/
  f : X → ℝ
  /-- It is measurable. -/
  hf : Measurable f
  /-- It is nonnegative a.e. -/
  hpos : ∀ᵐ x ∂ν, 0 ≤ f x
  /-- The identification of `ℋ` with a subspace of `L²(ν)`. -/
  U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν
  /-- Its range is dense. -/
  hdense : DenseRange U
  /-- The multiplier law: the transfer semigroup is the flow of `−f`. -/
  hlaw : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
    U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x)

namespace MulModel

/-- The bridge carried by a multiplier model. -/
def bridge (D : MulModel X ν Λ T) :
    OsFockBridge (Lp ℝ 2 ν) (physEvolCompletionRightFun D.hinv)
      (expFlow D.f D.hf D.hpos) :=
  osFockBridgeOfMulModel Λ D.hf D.hpos (physEvolCompletionRightFun D.hinv) D.U D.hdense D.hlaw

/-- The bridge is the model's identification. -/
theorem bridge_U (D : MulModel X ν Λ T) : D.bridge.U = D.U := rfl

/-- The inverse identification, on model vectors. -/
theorem bridge_apply_symm (D : MulModel X ν Λ T) (u : Lp ℝ 2 ν) :
    D.U (D.bridge.toIsometryEquiv.symm u) = u :=
  D.bridge.apply_toIsometryEquiv_symm_apply u

end MulModel

/-! ## The scalar multiplier `(λ + f)⁻¹` -/

/-- The scalar multiplier `t ↦ (λ + f t)⁻¹`. -/
def resolventFun (D : MulModel X ν Λ T) (lam : ℝ) : X → ℝ := fun t => (lam + D.f t)⁻¹

/-- The elementary law `λ g + f g = 1` for `g = (λ + f)⁻¹`. -/
theorem law_resolventFun (D : MulModel X ν Λ T) {lam : ℝ} (_hlam : 0 < lam) :
    ∀ᵐ t ∂ν, lam * resolventFun D lam t + D.f t * resolventFun D lam t = 1 := by
  filter_upwards [D.hpos] with t ht
  have hq : lam + D.f t ≠ 0 := by linarith
  calc lam * resolventFun D lam t + D.f t * resolventFun D lam t
      = (lam + D.f t) * resolventFun D lam t := by ring
    _ = 1 := by
        rw [resolventFun]
        exact mul_inv_cancel₀ hq

/-- It is measurable. -/
theorem measurable_resolventFun (D : MulModel X ν Λ T) (lam : ℝ) :
    Measurable (resolventFun D lam) :=
  (D.hf.const_add lam).inv

/-- It is bounded by `1/λ`, because `f ≥ 0`. -/
theorem norm_resolventFun_le (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) :
    ∀ᵐ t ∂ν, ‖resolventFun D lam t‖ ≤ lam⁻¹ := by
  filter_upwards [D.hpos] with t ht
  have hpos' : 0 < lam + D.f t := by linarith
  rw [resolventFun, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos')]
  exact inv_anti₀ hlam (by linarith)

/-- Hence it is an `L^∞` element. -/
theorem memLp_resolventFun_top (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) :
    MemLp (resolventFun D lam) ⊤ ν :=
  memLp_top_of_bound (measurable_resolventFun D lam).aestronglyMeasurable lam⁻¹
    (norm_resolventFun_le D hlam)

/-- The product `f (λ + f)⁻¹` is bounded by one — this is what puts the image of `R` back in the
multiplier domain. -/
theorem memLp_f_mul_resolventFun_top (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) :
    MemLp (fun t => D.f t * resolventFun D lam t) ⊤ ν := by
  refine memLp_top_of_bound (D.hf.mul (measurable_resolventFun D lam)).aestronglyMeasurable 1 ?_
  filter_upwards [D.hpos] with t ht
  have hq : 0 < lam + D.f t := by linarith
  have hnn : 0 ≤ resolventFun D lam t := inv_nonneg.2 hq.le
  have hle : D.f t * resolventFun D lam t ≤ 1 := by
    calc D.f t * resolventFun D lam t ≤ (lam + D.f t) * resolventFun D lam t :=
          mul_le_mul_of_nonneg_right (by linarith) hnn
      _ = 1 := by
          rw [resolventFun]
          exact mul_inv_cancel₀ hq.ne'
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht hnn)]
  exact hle

/-- The multiplier, as an element of `L^∞(ν)`. -/
def resolventWeight (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) : Lp ℝ ⊤ ν :=
  (memLp_resolventFun_top D hlam).toLp (resolventFun D lam)

/-- Its representative is `(λ + f)⁻¹`. -/
theorem coeFn_resolventWeight (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) :
    (resolventWeight D hlam : X → ℝ) =ᵐ[ν] resolventFun D lam :=
  MemLp.coeFn_toLp (memLp_resolventFun_top D hlam)

/-- The essential-supremum bound, read on the `L^∞` representative. -/
theorem norm_coeFn_resolventWeight_le (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) :
    ∀ᵐ t ∂ν, ‖(resolventWeight D hlam : X → ℝ) t‖ ≤ lam⁻¹ := by
  filter_upwards [coeFn_resolventWeight D hlam, norm_resolventFun_le D hlam] with t h1 h2
  rw [h1]
  exact h2

/-! ## The operator norm of a multiplication -/

/-- Scaling a multiplier scales the multiplication, parenthetically. -/
theorem mulL2_smul_left (c : ℝ) (W : Lp ℝ ⊤ ν) (u : Lp ℝ 2 ν) :
    mulL2 (c • W) u = c • mulL2 W u := by
  have h1 := mulL2_coeFn (c • W) u
  have h2 := mulL2_coeFn W u
  have h3 := Lp.coeFn_smul c W
  have h4 := Lp.coeFn_smul c (mulL2 W u)
  refine Lp.ext ?_
  filter_upwards [h1, h2, h3, h4] with t e1 e2 e3 e4
  have hpt : ((c • W : Lp ℝ ⊤ ν) : X → ℝ) t = c * (W : X → ℝ) t := by
    rw [e3, Pi.smul_apply, smul_eq_mul]
  have hpt2 : ((c • mulL2 W u : Lp ℝ 2 ν) : X → ℝ) t
      = c * ((mulL2 W u : Lp ℝ 2 ν) : X → ℝ) t := by
    rw [e4, Pi.smul_apply, smul_eq_mul]
  rw [e1, hpt, hpt2, e2]
  ring

/-- **Multiplication by `W` is bounded by its essential supremum**: if `‖W‖ ≤ c⁻¹` a.e. then
`‖mulL2 W u‖ ≤ c⁻¹‖u‖`.  The proof normalises `W` so that `mulL2_contractive` applies. -/
theorem norm_mulL2_le (W : Lp ℝ ⊤ ν) {c : ℝ} (hc : 0 < c)
    (hW : ∀ᵐ t ∂ν, ‖(W : X → ℝ) t‖ ≤ c⁻¹) (u : Lp ℝ 2 ν) :
    ‖mulL2 W u‖ ≤ c⁻¹ * ‖u‖ := by
  have hWs : ∀ᵐ t ∂ν, ‖((c • W : Lp ℝ ⊤ ν) : X → ℝ) t‖ ≤ 1 := by
    filter_upwards [Lp.coeFn_smul c W, hW] with t h1 h2
    rw [h1, Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    calc c * ‖(W : X → ℝ) t‖ ≤ c * c⁻¹ := mul_le_mul_of_nonneg_left h2 hc.le
      _ = 1 := mul_inv_cancel₀ hc.ne'
  have h1 : ‖mulL2 (c • W) u‖ ≤ ‖u‖ := mulL2_contractive (c • W) hWs u
  rw [mulL2_smul_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at h1
  rw [le_inv_mul_iff₀ hc]
  exact h1

/-! ## The bounded resolvent `R = (λ + H)⁻¹` -/

/-- **The resolvent of the Hamiltonian, as a bounded operator**: multiplication by
`(λ + f)⁻¹` on the model side, transported back by the bridge.  It is bounded by `1/λ`, which is
the Hille–Yosida estimate for `H ≥ 0`. -/
def resolventMulModel (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) :
    Hphys Λ →L[ℝ] Hphys Λ :=
  (LinearMap.mkContinuous
      { toFun := fun x =>
          D.bridge.toIsometryEquiv.symm (mulL2 (resolventWeight D hlam) (D.U x))
        map_add' := by
          intro x y
          simp only [map_add]
        map_smul' := by
          intro c x
          simp only [map_smul, RingHom.id_apply] } lam⁻¹ (by
          intro x
          change ‖D.bridge.toIsometryEquiv.symm (mulL2 (resolventWeight D hlam) (D.U x))‖
            ≤ lam⁻¹ * ‖x‖
          rw [D.bridge.toIsometryEquiv.symm.norm_map]
          have h := norm_mulL2_le (resolventWeight D hlam) hlam
            (norm_coeFn_resolventWeight_le D hlam) (D.U x)
          simpa only [D.U.norm_map] using h))

/-- The resolvent is the multiplier, on the model side. -/
theorem resolventMulModel_apply_map (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    (x : Hphys Λ) :
    D.U (resolventMulModel D hlam x) = mulL2 (resolventWeight D hlam) (D.U x) := by
  have h : resolventMulModel D hlam x
      = D.bridge.toIsometryEquiv.symm (mulL2 (resolventWeight D hlam) (D.U x)) := by
    simp only [resolventMulModel]
    rw [LinearMap.mkContinuous_apply]
    rfl
  rw [h, D.bridge_apply_symm]

/-- Pointwise, the resolvent multiplies by `(λ + f)⁻¹`. -/
theorem resolventMulModel_coeFn (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    (x : Hphys Λ) :
    (D.U (resolventMulModel D hlam x) : X → ℝ) =ᵐ[ν]
      fun t => resolventFun D lam t * (D.U x : X → ℝ) t := by
  have h1 : (D.U (resolventMulModel D hlam x) : X → ℝ) =ᵐ[ν]
      fun t => (resolventWeight D hlam : X → ℝ) t * (D.U x : X → ℝ) t := by
    rw [resolventMulModel_apply_map D hlam x]
    exact mulL2_coeFn (resolventWeight D hlam) (D.U x)
  filter_upwards [h1, coeFn_resolventWeight D hlam] with t h2 h3
  rw [h2, h3]

/-- The membership of the multiplier applied to `U x`; it never mentions `R`. -/
theorem memLp_f_resolventFun_mul (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    (x : Hphys Λ) :
    MemLp (fun t => D.f t * resolventFun D lam t * (D.U x : X → ℝ) t) 2 ν :=
  (ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin 2 (memLp_f_mul_resolventFun_top D hlam)
    (Lp.memLp (D.U x))

/-- **The multiplier image** `f (λ + f)⁻¹ (U x)`, packaged as a definition so that rewriting
`U x` never has to unfold a dependent proof term. -/
def mulImage (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) (x : Hphys Λ) : Lp ℝ 2 ν :=
  (memLp_f_resolventFun_mul D hlam x).toLp
    (fun t => D.f t * resolventFun D lam t * (D.U x : X → ℝ) t)

/-- Its representative. -/
theorem mulImage_coeFn (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) (x : Hphys Λ) :
    (mulImage D hlam x : X → ℝ) =ᵐ[ν]
      fun t => D.f t * resolventFun D lam t * (D.U x : X → ℝ) t :=
  MemLp.coeFn_toLp (memLp_f_resolventFun_mul D hlam x)

/-- **The shift law**: `(λ + f)(U (R x)) = U x`.  This is the statement that `R` really is the
inverse of `λ + H`, and it is the only place where the arithmetic of `(λ + f)⁻¹` is used. -/
theorem resolventMulModel_law (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    (x : Hphys Λ) :
    lam • (D.U (resolventMulModel D hlam x)) + mulImage D hlam x = D.U x := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (lam • D.U (resolventMulModel D hlam x)) (mulImage D hlam x),
    Lp.coeFn_smul lam (D.U (resolventMulModel D hlam x)),
    mulImage_coeFn D hlam x, resolventMulModel_coeFn D hlam x, D.hpos] with t h1 h2 h3 h4 ht
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, h3, h4]
  have hq : lam + D.f t ≠ 0 := by linarith
  change lam * (resolventFun D lam t * (D.U x : X → ℝ) t)
      + D.f t * resolventFun D lam t * (D.U x : X → ℝ) t = (D.U x : X → ℝ) t
  calc lam * (resolventFun D lam t * (D.U x : X → ℝ) t)
        + D.f t * resolventFun D lam t * (D.U x : X → ℝ) t
      = ((lam + D.f t) * resolventFun D lam t) * (D.U x : X → ℝ) t := by ring
    _ = (D.U x : X → ℝ) t := by
        rw [resolventFun, mul_inv_cancel₀ hq, one_mul]

/-- The image of `x − λ R x` is the multiplier applied to `U x`. -/
theorem resolventMulModel_shift_image (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    (x : Hphys Λ) :
    D.U (x - lam • resolventMulModel D hlam x) = mulImage D hlam x := by
  have hL : D.U (x - lam • resolventMulModel D hlam x)
      = D.U x - lam • D.U (resolventMulModel D hlam x) := by
    rw [map_sub, map_smul]
  rw [hL]
  rw [← resolventMulModel_law D hlam x]
  abel

/-- **`R` inverts `λ + H`**: the `x` of the shift law, transported back. -/
theorem resolventMulModel_diff (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    (x : Hphys Λ) :
    x - lam • resolventMulModel D hlam x
      = D.bridge.toIsometryEquiv.symm (mulImage D hlam x) := by
  refine D.U.injective ?_
  rw [resolventMulModel_shift_image]
  exact (D.bridge_apply_symm _).symm

/-- **The quadratic form of `H`**, on the domain: `⟪H y, y⟫ = ∫ f (U y)²` with `y = R x`. -/
theorem inner_diff_resolventMulModel (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    (x : Hphys Λ) :
    ⟪x - lam • resolventMulModel D hlam x, resolventMulModel D hlam x⟫
      = ∫ t, D.f t * (D.U (resolventMulModel D hlam x) : X → ℝ) t
          * (D.U (resolventMulModel D hlam x) : X → ℝ) t ∂ν := by
  rw [resolventMulModel_diff D hlam x]
  have hinner : ⟪(D.bridge.toIsometryEquiv.symm (mulImage D hlam x) : Hphys Λ),
      (resolventMulModel D hlam x : Hphys Λ)⟫
      = ⟪(mulImage D hlam x : Lp ℝ 2 ν),
          (D.U (resolventMulModel D hlam x) : Lp ℝ 2 ν)⟫ := by
    rw [← D.U.inner_map_map, D.bridge_apply_symm]
  rw [hinner, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulImage_coeFn D hlam x, resolventMulModel_coeFn D hlam x] with t h1 h2
  rw [h1, h2, RCLike.inner_apply', RCLike.conj_to_real]
  ring

/-- **`R` is positive and coercive**: `λ‖R x‖² ≤ ⟪x, R x⟫`.  The difference is the nonnegative
integral `∫ f (U (R x))²`. -/
theorem resolventMulModel_coercive (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    (x : Hphys Λ) :
    lam * ‖resolventMulModel D hlam x‖ ^ 2 ≤ ⟪x, resolventMulModel D hlam x⟫ := by
  have h := inner_diff_resolventMulModel D hlam x
  have hnn : 0 ≤ ∫ t, D.f t * (D.U (resolventMulModel D hlam x) : X → ℝ) t
      * (D.U (resolventMulModel D hlam x) : X → ℝ) t ∂ν := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [D.hpos] with t ht
    have hsq : D.f t * (D.U (resolventMulModel D hlam x) : X → ℝ) t
        * (D.U (resolventMulModel D hlam x) : X → ℝ) t
        = D.f t * ((D.U (resolventMulModel D hlam x) : X → ℝ) t
          * (D.U (resolventMulModel D hlam x) : X → ℝ) t) := by ring
    rw [hsq]
    exact mul_nonneg ht (mul_self_nonneg _)
  have hexp : ⟪x - lam • resolventMulModel D hlam x, resolventMulModel D hlam x⟫
      = ⟪x, resolventMulModel D hlam x⟫ - lam * ‖resolventMulModel D hlam x‖ ^ 2 := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [hexp] at h
  linarith

/-- **`R` is symmetric**: the multiplier is real, so it commutes with the inner product. -/
theorem resolventMulModel_inner_comm (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    (x y : Hphys Λ) :
    ⟪resolventMulModel D hlam x, y⟫ = ⟪x, resolventMulModel D hlam y⟫ := by
  rw [← D.U.inner_map_map (resolventMulModel D hlam x) y,
    ← D.U.inner_map_map x (resolventMulModel D hlam y),
    resolventMulModel_apply_map D hlam x, resolventMulModel_apply_map D hlam y,
    L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulL2_coeFn (resolventWeight D hlam) (D.U x),
    mulL2_coeFn (resolventWeight D hlam) (D.U y)] with t h1 h2
  rw [h1, h2, RCLike.inner_apply', RCLike.inner_apply', RCLike.conj_to_real,
    RCLike.conj_to_real]
  ring

/-- `R` is self-adjoint as a bounded operator. -/
theorem resolventMulModel_isSelfAdjoint (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) :
    IsSelfAdjoint (resolventMulModel D hlam) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (resolventMulModel_inner_comm D hlam)

/-- **`R` has trivial kernel.**  If `R z = 0` then the shift law reads `U z = f (λ + f)⁻¹ (U z)`,
and `1 − f(λ+f)⁻¹ = λ(λ+f)⁻¹ ≠ 0` a.e., so `U z = 0`. -/
theorem resolventMulModel_injective (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) :
    Function.Injective (resolventMulModel D hlam) := by
  intro x y hxy
  have hsub : resolventMulModel D hlam (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hz0 : D.U (resolventMulModel D hlam (x - y)) = 0 := by
    rw [hsub, LinearIsometry.map_zero D.U]
  have hA : lam • D.U (resolventMulModel D hlam (x - y)) = 0 := by
    rw [hz0, smul_zero]
  have hUeq : D.U (x - y) = mulImage D hlam (x - y) := by
    calc D.U (x - y)
        = lam • D.U (resolventMulModel D hlam (x - y)) + mulImage D hlam (x - y) :=
          (resolventMulModel_law D hlam (x - y)).symm
      _ = 0 + mulImage D hlam (x - y) := by rw [hA]
      _ = mulImage D hlam (x - y) := zero_add _
  have hcoef : (D.U (x - y) : X → ℝ) =ᵐ[ν]
      fun t => D.f t * resolventFun D lam t * (D.U (x - y) : X → ℝ) t := by
    have h1 : (D.U (x - y) : X → ℝ) =ᵐ[ν] (mulImage D hlam (x - y) : X → ℝ) := by
      rw [hUeq]
    filter_upwards [h1, mulImage_coeFn D hlam (x - y)] with t e1 e2
    exact e1.trans e2
  have hzero : (D.U (x - y) : X → ℝ) =ᵐ[ν] (0 : X → ℝ) := by
    filter_upwards [hcoef, law_resolventFun D hlam, D.hpos] with t ht hl hp
    have hgpos : 0 < resolventFun D lam t := by
      have hq : 0 < lam + D.f t := by linarith
      rw [resolventFun]
      exact inv_pos.2 hq
    have hne : lam * resolventFun D lam t ≠ 0 := (mul_pos hlam hgpos).ne'
    have key : lam * resolventFun D lam t * (D.U (x - y) : X → ℝ) t
        + D.f t * resolventFun D lam t * (D.U (x - y) : X → ℝ) t
        = (D.U (x - y) : X → ℝ) t := by
      rw [← add_mul, hl, one_mul]
    have hzero' : lam * resolventFun D lam t * (D.U (x - y) : X → ℝ) t = 0 := by
      linarith [key, ht]
    exact (mul_eq_zero.mp hzero').resolve_left hne
  have hUz : D.U (x - y) = 0 := by
    refine Lp.ext ?_
    filter_upwards [hzero, Lp.coeFn_zero ℝ 2 ν] with t h1 h2
    rw [h1, h2]
  have h0 : x - y = 0 := D.U.injective (by rw [hUz, LinearIsometry.map_zero D.U])
  exact sub_eq_zero.mp h0

/-- **`R` has dense range.**  A vector orthogonal to `ran R` gives `⟪R v, v⟫ = 0`, so coercivity
forces `R v = 0`, and injectivity then forces `v = 0`. -/
theorem dense_range_resolventMulModel (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) :
    Dense (LinearMap.range (resolventMulModel D hlam : Hphys Λ →ₗ[ℝ] Hphys Λ) :
      Set (Hphys Λ)) := by
  have hbot : (LinearMap.range (resolventMulModel D hlam : Hphys Λ →ₗ[ℝ] Hphys Λ))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hinner : ⟪resolventMulModel D hlam v, v⟫ = 0 :=
      (Submodule.mem_orthogonal _ v).mp hv _ ⟨v, rfl⟩
    have hcoer := resolventMulModel_coercive D hlam v
    rw [resolventMulModel_inner_comm D hlam v v] at hinner
    rw [hinner] at hcoer
    have hsq : ‖resolventMulModel D hlam v‖ ^ 2 = 0 := by
      nlinarith [hcoer, hlam, sq_nonneg ‖resolventMulModel D hlam v‖]
    have hnorm : ‖resolventMulModel D hlam v‖ = 0 := sq_eq_zero_iff.mp hsq
    have hRv : resolventMulModel D hlam v = 0 := norm_eq_zero.mp hnorm
    refine resolventMulModel_injective D hlam ?_
    rw [hRv, map_zero]
  have hcl : (LinearMap.range (resolventMulModel D hlam : Hphys Λ →ₗ[ℝ] Hphys Λ)).topologicalClosure
      = ⊤ := by
    have h : (LinearMap.range (resolventMulModel D hlam : Hphys Λ →ₗ[ℝ] Hphys Λ))ᗮᗮ = ⊤ := by
      rw [hbot, Submodule.bot_orthogonal_eq_top]
    rwa [Submodule.orthogonal_orthogonal_eq_closure] at h
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hcl

/-! ## The Hamiltonian `H = R⁻¹ − λ` -/

/-- **The Hamiltonian**, as a partially defined operator: `H = R⁻¹ − λ` on `ran R`.  This is the
shift-invert form; the theorems below show that `R` is exactly the resolvent of `H` at `λ`, that
`H` is self-adjoint, and that `H ≥ 0`. -/
def hamiltonianMulModel (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) :
    Hphys Λ →ₗ.[ℝ] Hphys Λ where
  domain := LinearMap.range (resolventMulModel D hlam : Hphys Λ →ₗ[ℝ] Hphys Λ)
  toFun := ((LinearMap.id : Hphys Λ →ₗ[ℝ] Hphys Λ)
      - (lam : ℝ) • (resolventMulModel D hlam : Hphys Λ →ₗ[ℝ] Hphys Λ)) ∘ₗ
    (LinearEquiv.ofInjective (resolventMulModel D hlam : Hphys Λ →ₗ[ℝ] Hphys Λ)
      (resolventMulModel_injective D hlam)).symm.toLinearMap

/-- The range of the resolvent is the domain of `H`. -/
theorem mem_domain_hamiltonianMulModel (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    (x : Hphys Λ) :
    resolventMulModel D hlam x ∈ (hamiltonianMulModel D hlam).domain :=
  ⟨x, rfl⟩

/-- The action of `H` on the range of the resolvent: `H (R x) = x − λ R x`. -/
theorem hamiltonianMulModel_apply (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    (x : Hphys Λ) (hx : resolventMulModel D hlam x ∈ (hamiltonianMulModel D hlam).domain) :
    hamiltonianMulModel D hlam ⟨resolventMulModel D hlam x, hx⟩
      = x - lam • resolventMulModel D hlam x := by
  have hs : (LinearEquiv.ofInjective (resolventMulModel D hlam : Hphys Λ →ₗ[ℝ] Hphys Λ)
      (resolventMulModel_injective D hlam)).symm ⟨resolventMulModel D hlam x, hx⟩ = x :=
    (LinearEquiv.ofInjective _ _).symm_apply_eq.mpr rfl
  simp only [hamiltonianMulModel, LinearPMap.mk_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe]
  erw [hs]
  rfl

/-- The action of `H`, in terms of an arbitrary membership proof. -/
theorem hamiltonianMulModel_apply_of_eq (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    {a : Hphys Λ} {y : (hamiltonianMulModel D hlam).domain}
    (h : (y : Hphys Λ) = resolventMulModel D hlam a) :
    hamiltonianMulModel D hlam y = a - lam • resolventMulModel D hlam a := by
  have hy : y = ⟨resolventMulModel D hlam a, mem_domain_hamiltonianMulModel D hlam a⟩ :=
    Subtype.ext h
  rw [hy]
  exact hamiltonianMulModel_apply D hlam a (mem_domain_hamiltonianMulModel D hlam a)

/-- **`H` is multiplication by `f` on its domain**, at the level of the model: the image of
`H (R a)` is `mulImage D hlam a`, exactly the vector that `exists_generatorRight_mulModel`
identifies with `−U (generatorRight (R a))`. -/
theorem hamiltonianMulModel_image (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    (a : Hphys Λ) (ha : resolventMulModel D hlam a ∈ (hamiltonianMulModel D hlam).domain) :
    D.U (hamiltonianMulModel D hlam ⟨resolventMulModel D hlam a, ha⟩) = mulImage D hlam a := by
  rw [hamiltonianMulModel_apply D hlam a ha]
  exact resolventMulModel_shift_image D hlam a

/-- **`H` is formally self-adjoint**: on its domain, `⟪H y, z⟫ = ⟪y, H z⟫`. -/
theorem hamiltonianMulModel_isFormalAdjoint (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) :
    (hamiltonianMulModel D hlam).IsFormalAdjoint (hamiltonianMulModel D hlam) := by
  intro x y
  obtain ⟨a, ha⟩ := x.2
  obtain ⟨b, hb⟩ := y.2
  have hx : x = ⟨resolventMulModel D hlam a, mem_domain_hamiltonianMulModel D hlam a⟩ :=
    Subtype.ext ha.symm
  have hy : y = ⟨resolventMulModel D hlam b, mem_domain_hamiltonianMulModel D hlam b⟩ :=
    Subtype.ext hb.symm
  rw [hx, hy]
  rw [hamiltonianMulModel_apply D hlam a (mem_domain_hamiltonianMulModel D hlam a),
    hamiltonianMulModel_apply D hlam b (mem_domain_hamiltonianMulModel D hlam b)]
  rw [inner_sub_left, real_inner_smul_left, inner_sub_right, real_inner_smul_right,
    resolventMulModel_inner_comm D hlam a b]

/-- The domain of `H` is dense: it is the range of the injective self-adjoint `R`. -/
theorem hamiltonianMulModel_dense (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) :
    Dense ((hamiltonianMulModel D hlam).domain : Set (Hphys Λ)) :=
  dense_range_resolventMulModel D hlam

/-- **`(λ + H) (R x) = x`**: `R` is a right inverse of `λ + H`. -/
theorem hamiltonianMulModel_resolvent (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    (x : Hphys Λ) :
    lam • resolventMulModel D hlam x
        + hamiltonianMulModel D hlam ⟨resolventMulModel D hlam x,
            mem_domain_hamiltonianMulModel D hlam x⟩ = x := by
  rw [hamiltonianMulModel_apply]
  abel

/-! ## A symmetric operator with surjective `λ + T` is self-adjoint -/

section ShiftInvert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The von Neumann argument, abstractly.**  A symmetric operator `T` whose shifted range
`ran(λ + T)` is everything (`λ > 0`) cannot be a proper restriction of its adjoint.

Given `v ∈ dom T†`, choose `z ∈ dom T` with `λ z + T z = T† v + λ v`.  Symmetry turns
`⟪v − z, (λ + T) y⟫` into `⟪T† v, y⟫ + λ⟪v, y⟫ − ⟪T z, y⟫ − λ⟪z, y⟫`, which vanishes by the choice
of `z`; surjectivity of `λ + T` then makes `v − z` orthogonal to every vector, so `v = z`, and
`T† v = λ z + T z − λ v = T z`.  Hence `T† = T`.

This is the von Neumann/Hellinger–Toeplitz criterion, stated for real Hilbert spaces: it needs no
`λ`-resolvent calculus, only the range condition. -/
theorem le_adjoint_of_shift_surjective {T : E →ₗ.[ℝ] E} {lam : ℝ}
    (hDense : Dense (T.domain : Set E))
    (hsurj : ∀ x : E, ∃ y : T.domain, lam • (y : E) + T y = x)
    (hsymm : T.IsFormalAdjoint T) :
    LinearPMap.adjoint T ≤ T := by
  have hT : (LinearPMap.adjoint T).IsFormalAdjoint T :=
    LinearPMap.adjoint_isFormalAdjoint (T := T) hDense
  have hval : ∀ v : (LinearPMap.adjoint T).domain,
      ∃ z : T.domain, (v : E) = (z : E) ∧ LinearPMap.adjoint T v = T z := by
    intro v
    obtain ⟨z, hz⟩ := hsurj (LinearPMap.adjoint T v + lam • (v : E))
    have hsum : LinearPMap.adjoint T v + lam • (v : E) = T z + lam • (z : E) := by
      rw [← hz]
      abel
    have horth : ∀ y : T.domain, ⟪(v : E) - (z : E), lam • (y : E) + T y⟫ = 0 := by
      intro y
      have h1 : ⟪(v : E), T y⟫ = ⟪LinearPMap.adjoint T v, (y : E)⟫ := (hT v y).symm
      have h2 : ⟪(z : E), T y⟫ = ⟪T z, (y : E)⟫ := (hsymm z y).symm
      have h3 : ⟪LinearPMap.adjoint T v, (y : E)⟫ + lam * ⟪(v : E), (y : E)⟫
          = ⟪T z, (y : E)⟫ + lam * ⟪(z : E), (y : E)⟫ := by
        have hL : ⟪LinearPMap.adjoint T v + lam • (v : E), (y : E)⟫
            = ⟪T z + lam • (z : E), (y : E)⟫ := by
          rw [hsum]
        rw [inner_add_left, real_inner_smul_left] at hL
        rw [inner_add_left, real_inner_smul_left] at hL
        exact hL
      rw [inner_add_right, real_inner_smul_right, inner_sub_left, inner_sub_left, h1, h2]
      linarith [h3]
    have hcov : ∀ s : E, ⟪(v : E) - (z : E), s⟫ = 0 := by
      intro s
      obtain ⟨y, hy⟩ := hsurj s
      rw [← hy]
      exact horth y
    have hvz : (v : E) = (z : E) := by
      have h0 : (v : E) - (z : E) = 0 :=
        inner_self_eq_zero.mp (hcov ((v : E) - (z : E)))
      exact sub_eq_zero.mp h0
    refine ⟨z, hvz, ?_⟩
    calc LinearPMap.adjoint T v = (LinearPMap.adjoint T v + lam • (v : E)) - lam • (v : E) := by
          abel
      _ = (T z + lam • (z : E)) - lam • (z : E) := by rw [hsum, hvz]
      _ = T z := by abel
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨z, hvz, _⟩ := hval ⟨v, hv⟩
    have hv' : v = (z : E) := hvz
    rw [hv']
    exact z.2
  · intro v y hvy
    obtain ⟨z, hvz, hzv⟩ := hval v
    have hzy : z = y := Subtype.ext (by rw [← hvz, hvy])
    rw [hzv, hzy]

end ShiftInvert

/-- **`H` is self-adjoint**: it is symmetric (`hamiltonianMulModel_isFormalAdjoint`) and its
shifted range is everything (`hamiltonianMulModel_resolvent`), so the abstract von Neumann lemma
`le_adjoint_of_shift_surjective` closes the gap `H† ≤ H` left by `le_adjoint`. -/
theorem hamiltonianMulModel_isSelfAdjoint (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) :
    IsSelfAdjoint (hamiltonianMulModel D hlam) := by
  rw [LinearPMap.isSelfAdjoint_def]
  refine le_antisymm ?_ (LinearPMap.IsFormalAdjoint.le_adjoint
    (hamiltonianMulModel_dense D hlam) (hamiltonianMulModel_isFormalAdjoint D hlam))
  exact le_adjoint_of_shift_surjective (T := hamiltonianMulModel D hlam)
    (hamiltonianMulModel_dense D hlam)
    (fun x => ⟨⟨resolventMulModel D hlam x, mem_domain_hamiltonianMulModel D hlam x⟩,
      hamiltonianMulModel_resolvent D hlam x⟩)
    (hamiltonianMulModel_isFormalAdjoint D hlam)
/-! ## `H ≥ 0` -/

/-- **`H` is nonnegative**, with the quantitative form `⟪H y, y⟫ = ∫ f (U y)²`: the quadratic form
is the `f`-weighted mass of the model vector. -/
theorem hamiltonianMulModel_inner_nonneg (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    (y : (hamiltonianMulModel D hlam).domain) :
    0 ≤ ⟪hamiltonianMulModel D hlam y, (y : Hphys Λ)⟫ := by
  obtain ⟨a, ha⟩ := y.2
  have hy : y = ⟨resolventMulModel D hlam a, mem_domain_hamiltonianMulModel D hlam a⟩ :=
    Subtype.ext ha.symm
  rw [hy, hamiltonianMulModel_apply, inner_diff_resolventMulModel D hlam a]
  refine integral_nonneg_of_ae ?_
  filter_upwards [D.hpos] with t ht
  have hsq : D.f t * (D.U (resolventMulModel D hlam a) : X → ℝ) t
      * (D.U (resolventMulModel D hlam a) : X → ℝ) t
      = D.f t * ((D.U (resolventMulModel D hlam a) : X → ℝ) t
        * (D.U (resolventMulModel D hlam a) : X → ℝ) t) := by ring
  rw [hsq]
  exact mul_nonneg ht (mul_self_nonneg _)

/-! ## `R` is the resolvent of `H` -/


/-- **`R ((λ + H) y) = y`**: `R` is a left inverse of `λ + H`. -/
theorem resolvent_hamiltonianMulModel (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    (y : (hamiltonianMulModel D hlam).domain) :
    resolventMulModel D hlam (hamiltonianMulModel D hlam y + lam • (y : Hphys Λ))
      = (y : Hphys Λ) := by
  obtain ⟨a, ha⟩ := y.2
  have hy : y = ⟨resolventMulModel D hlam a, mem_domain_hamiltonianMulModel D hlam a⟩ :=
    Subtype.ext ha.symm
  rw [hy, hamiltonianMulModel_apply]
  have h1 : a - lam • resolventMulModel D hlam a + lam • resolventMulModel D hlam a
      = a := by abel
  rw [h1]

end

end BookProof.OSReconstruction
