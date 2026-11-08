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
  `H` at `λ`: `λ x + H x` and `R` are mutually inverse on `ℋ` and on `dom H` respectively;
* `flowOfH` — `e^{−τH}` on `ℋ`, built from the model rather than postulated, with `U_flowOfH`,
  `flowOfH_zero`, `flowOfH_add`, `flowOfH_contractive`, and `physEvol_eq_flowOfH` identifying it
  with the physical semigroup (that identification is the multiplier law, nothing more);
* `flowOfHCLM` — the same family as a bounded operator `ℋ →L[ℝ] ℋ` at every time, with
  `flowOfHCLM_apply`, `norm_flowOfHCLM_le_one` and the bundled
  `flowOfHCLM_isContractionSelfAdjointSemigroup`; `continuousOn_flowOfHCLM` is the strong
  continuity on `[0, ∞)` — it needs no generator-domain hypothesis, because the `L²` limit is
  dominated convergence (`tendsto_expFlow_nhdsGE_zero`);
* `isSelfAdjoint_flowOfHCLM` — each `e^{−τH}`, `τ ≥ 0`, is self-adjoint: the multiplier
  `e^{−τf}` is real, so `inner_mulL2_comm` makes the Fock side symmetric and the bridge is an
  isometry.  So the flow is a *contractive self-adjoint* semigroup;
* `tendsto_flowOfH_slope` — the flow's difference quotient converges to `−H` on `dom H`, proved
  from the model's own slope rather than from the transfer semigroup;
* `tendsto_flowOfH_slope_of_hasGenRight` and `hasGenRight_iff_tendsto_flowOfH_slope` — the same on
  the **whole forward domain**: the flow's forward domain *is* the transfer generator's, so the
  flow generates `generatorRight` and not a larger operator, and
  `tendsto_flowOfH_slope_of_mem_domainH`
  recovers the `dom H` value `−H` from that general statement;
* `flowOfH_nonneg` — positivity preservation: `e^{−τ f} ≥ 0` on the chart, so a vector with a.e.
  nonnegative chart image stays nonnegative, and `flowOfH_apply_le_of_nonneg` says it is pulled
  down (`e^{−τ f} ≤ 1`, i.e. `f ≥ 0`);
* `dense_flowForwardDomain` and `closed_flowForwardDomain` — the forward domain is dense (it
  contains the dense `dom H`), and the generator's graph is closed on it;
  `flowGenerator_dense_domain_closed` bundles the two.  The closedness half inherits
  `generatorRight_isClosed`'s matrix-element continuity hypothesis: `LinearFunctional` carries no
  continuity, so it is an OS input and not readable from the model;
* `expFlow_support`, `expFlow_apply_lt_of_pos`, `tendsto_expFlow_apply_atTop` — what large time does
  to a strictly positive vector: the flow is **not** positivity improving (the support is preserved
  exactly), a.e. positivity is preserved, the chart is strictly smaller where `f > 0` and decays to
  `0` there at rate `f`, while `expFlow_apply_of_f_eq_zero` freezes the part over `{f = 0}` — so the
  large-time limit is the projection onto the kernel of the density;
* `tendsto_norm_flowOfH_atTop` — the quantitative form, `‖e^{−τH}y‖ → 0` for every `y` when the
  density is a.e. strictly positive, by dominated convergence against the bound `(u x)²`;
* `generatorRight_eq_neg_hamiltonianMulModel` — `A = −H` as a single theorem: on `dom H` the
  forward generator exists and `U (A y) = −U (H y)`.  The two modules name the same class through
  `mulImage`, and `MemLp.toLp_congr` bridges the two presentations of `f · U y`.

So the explicit family `(λ + f)⁻¹` is indeed the resolvent of a self-adjoint nonnegative operator,
the flow it generates is a strongly continuous contraction semigroup of self-adjoint operators, and
the generator it produces is the transfer generator of `MultiplierGenerator`.

## Boundary

The multiplier law `U (P(τ) x) = expFlow τ (U x)` is still a hypothesis: this module produces the
self-adjoint `H` *from the flow*, it does not produce the flow from the OS axioms.  It cannot do
so, and the reason is structural rather than technical: the OS axioms supply a contractive
semigroup on `ℋ` and its two-point functions, while the law says `U` diagonalizes its generator
with simple spectrum `f`; two different `f` satisfy the same axioms with different `H`, so the
identification is the choice of KL multiplier realization.  What is missing for a derivation is
the spectral theorem for the generator (equivalently Stone's theorem), which Mathlib does not have.

`flowOfH` is defined by conjugating the multiplier flow, not by a functional calculus of the bounded
resolvent `R`, which would be the natural home: `R` is bounded, self-adjoint and nonnegative with
`‖R‖ ≤ λ⁻¹`, so `e^{−τH} = φ_τ(R)` for the bounded continuous `φ_τ r = exp(−τ(1/r − λ))`, but
Mathlib has no continuous functional calculus on a real Hilbert space.
-/

namespace BookProof.OSReconstruction

open Filter MeasureTheory
open BookProof.ReflectionPositivity
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

/-! ## The Euclidean flow of `H` -/

/-- **`e^{−τH}`, defined from the model instead of postulated.**  The bridge conjugates the
multiplier flow back to `ℋ`: `flowOfH D τ x = U⁻¹ (e^{−τ f} · U x)`.

The natural home for this family is the functional calculus of the *bounded* resolvent: `R` is
bounded, self-adjoint and nonnegative with `‖R‖ ≤ λ⁻¹`, so `e^{−τH} = φ_τ(R)` for the bounded
continuous `φ_τ : [0, λ⁻¹] → ℝ`, `φ_τ r = exp(−τ(1/r − λ))`.  Mathlib has no continuous functional
calculus for real Hilbert spaces, so that route is not available here; conjugating the model's
multiplier flow gives the same family, and the laws below verify the properties a flow of `H`
*has*: boundedness, the semigroup law, contractivity, strong continuity and self-adjointness.  What
is *not* removed by this definition is the multiplier law: identifying `flowOfH` with the physical
semigroup `physEvolCompletionRightFun` is exactly `MulModel.hlaw`. -/
def flowOfH (D : MulModel X ν Λ T) (τ : ℝ) (x : Hphys Λ) : Hphys Λ :=
  D.bridge.toIsometryEquiv.symm (expFlow D.f D.hf D.hpos τ (D.U x))

/-- The defining property: `U` intertwines `flowOfH` with the multiplier flow. -/
theorem U_flowOfH (D : MulModel X ν Λ T) (τ : ℝ) (x : Hphys Λ) :
    D.U (flowOfH D τ x) = expFlow D.f D.hf D.hpos τ (D.U x) :=
  D.bridge.apply_toIsometryEquiv_symm_apply _

/-- **`flowOfH` is the physical semigroup**: the multiplier law read back through the bridge. -/
theorem physEvol_eq_flowOfH (D : MulModel X ν Λ T) {τ : ℝ} (hτ : 0 ≤ τ) (x : Hphys Λ) :
    physEvolCompletionRightFun D.hinv τ x = flowOfH D τ x := by
  refine D.U.injective ?_
  rw [D.hlaw τ hτ, U_flowOfH]

/-- The flow starts at the identity. -/
theorem flowOfH_zero (D : MulModel X ν Λ T) (x : Hphys Λ) : flowOfH D 0 x = x := by
  refine D.U.injective ?_
  rw [U_flowOfH, expFlow_zero]
  rfl

/-- The semigroup law. -/
theorem flowOfH_add (D : MulModel X ν Λ T) {τ σ : ℝ} (hτ : 0 ≤ τ) (hσ : 0 ≤ σ)
    (x : Hphys Λ) : flowOfH D (τ + σ) x = flowOfH D τ (flowOfH D σ x) := by
  refine D.U.injective ?_
  simp only [U_flowOfH]
  exact (expFlow_comp D.hf D.hpos hτ hσ (D.U x)).symm

/-- The flow is contractive on nonnegative time. -/
theorem flowOfH_contractive (D : MulModel X ν Λ T) {τ : ℝ} (hτ : 0 ≤ τ) (x : Hphys Λ) :
    ‖flowOfH D τ x‖ ≤ ‖x‖ := by
  have h : ‖D.U (flowOfH D τ x)‖ ≤ ‖D.U x‖ := by
    rw [U_flowOfH]
    exact expFlow_contractive D.hf D.hpos hτ (D.U x)
  rwa [D.U.norm_map, D.U.norm_map] at h

/-! ## The generator of the semigroup is `−H` -/

/-- **`generatorRight = −H`**, as a single statement.  On the domain of `H` — the range of the
resolvent — the forward-time generator of the transfer semigroup exists, and its image is minus the
image of `H` under the same `L²` presentation: `U (A (R a)) = −U (H (R a))`.

Both sides are the class `mulImage D λ a`.  `hamiltonianMulModel_image` names it on the Hamiltonian
side, `exists_generatorRight_mulModel` on the semigroup side, and the two meet here because the two
`MemLp` presentations of `f · U (R a)` differ only by associativity of multiplication, so they are
a.e. equal and `MemLp.toLp_congr` identifies them. -/
theorem generatorRight_eq_neg_hamiltonianMulModel (D : MulModel X ν Λ T) {lam : ℝ}
    (hlam : 0 < lam) (a : Hphys Λ) :
    ∃ hz : HasGenRight D.hinv (resolventMulModel D hlam a),
      D.U (generatorRight D.hinv ⟨resolventMulModel D hlam a, hz⟩)
        = -D.U (hamiltonianMulModel D hlam
            ⟨resolventMulModel D hlam a, mem_domain_hamiltonianMulModel D hlam a⟩) := by
  have hcoef : (D.U (resolventMulModel D hlam a) : X → ℝ) =ᵐ[ν]
      fun t => resolventFun D lam t * (D.U a : X → ℝ) t :=
    resolventMulModel_coeFn D hlam a
  have hfzy : MemLp (fun t => D.f t * (D.U (resolventMulModel D hlam a) : X → ℝ) t) 2 ν :=
    MemLp.ae_eq (by
      filter_upwards [hcoef] with t ht
      rw [ht]
      ring) (memLp_f_resolventFun_mul D hlam a)
  have hzy : MemLp (fun t => (D.U (resolventMulModel D hlam a) : X → ℝ) t) 2 ν :=
    Lp.memLp (D.U (resolventMulModel D hlam a))
  have hUy : D.U (resolventMulModel D hlam a)
      = hzy.toLp (fun t => (D.U (resolventMulModel D hlam a) : X → ℝ) t) :=
    (Lp.toLp_coeFn (D.U (resolventMulModel D hlam a)) hzy).symm
  obtain ⟨hz, hgen⟩ := exists_generatorRight_mulModel D.hinv D.hf D.hpos D.U D.hdense
    D.hlaw (resolventMulModel D hlam a) hzy hUy hfzy
  have hclass : hfzy.toLp (fun t => D.f t * (D.U (resolventMulModel D hlam a) : X → ℝ) t)
      = mulImage D hlam a :=
    MemLp.toLp_congr hfzy (memLp_f_resolventFun_mul D hlam a) (by
      filter_upwards [hcoef] with t ht
      rw [ht]
      ring)
  refine ⟨hz, ?_⟩
  rw [hgen, hamiltonianMulModel_image D hlam a (mem_domain_hamiltonianMulModel D hlam a),
    hclass]

/-! ## The flow as a bounded operator -/

/-- The multiplier flow is contractive at *every* real time: for `τ ≥ 0` because the multiplier
`e^{−τf}` is bounded by one, and for `τ < 0` because the flow is extended there by the identity. -/
theorem norm_expFlow_apply_le (D : MulModel X ν Λ T) (τ : ℝ) (u : Lp ℝ 2 ν) :
    ‖expFlow D.f D.hf D.hpos τ u‖ ≤ ‖u‖ := by
  by_cases hτ : 0 ≤ τ
  · exact expFlow_contractive D.hf D.hpos hτ u
  · rw [expFlow, dif_neg hτ]
    simp

/-- **`e^{−τH}` as a bounded linear operator.**  The bridge is an isometry and the multiplier flow
is contractive in the essential supremum, so conjugating `expFlow τ` back to `ℋ` is bounded; the
bound proof is `1` because both factors are contractions. -/
def flowOfHCLM (D : MulModel X ν Λ T) (τ : ℝ) : Hphys Λ →L[ℝ] Hphys Λ :=
  LinearMap.mkContinuous
    { toFun := fun x => D.bridge.toIsometryEquiv.symm (expFlow D.f D.hf D.hpos τ (D.U x))
      map_add' := by intro x y; simp only [map_add]
      map_smul' := by intro c x; simp }
    1 (by
      intro x
      have h := norm_expFlow_apply_le D τ (D.U x)
      calc ‖D.bridge.toIsometryEquiv.symm (expFlow D.f D.hf D.hpos τ (D.U x))‖
          = ‖expFlow D.f D.hf D.hpos τ (D.U x)‖ := by simp
        _ ≤ ‖D.U x‖ := h
        _ = ‖x‖ := D.U.norm_map x
        _ = 1 * ‖x‖ := (one_mul _).symm)

/-- The bounded operator is the flow of `H`. -/
@[simp]
theorem flowOfHCLM_apply (D : MulModel X ν Λ T) (τ : ℝ) (x : Hphys Λ) :
    flowOfHCLM D τ x = flowOfH D τ x := rfl

/-- The flow is contractive as an operator, at every real time. -/
theorem flowOfHCLM_contractive (D : MulModel X ν Λ T) (τ : ℝ) (x : Hphys Λ) :
    ‖flowOfHCLM D τ x‖ ≤ ‖x‖ := by
  have h : ‖flowOfHCLM D τ x‖ = ‖expFlow D.f D.hf D.hpos τ (D.U x)‖ := by
    rw [flowOfHCLM_apply, ← U_flowOfH, D.U.norm_map]
  rw [h]
  calc ‖expFlow D.f D.hf D.hpos τ (D.U x)‖ ≤ ‖D.U x‖ := norm_expFlow_apply_le D τ _
    _ = ‖x‖ := D.U.norm_map x

/-- The operator norm is at most one. -/
theorem norm_flowOfHCLM_le_one (D : MulModel X ν Λ T) (τ : ℝ) : ‖flowOfHCLM D τ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using flowOfHCLM_contractive D τ x

/-! ## Strong continuity -/

/-- For a real `L²` class the square of the norm is the integral of the pointwise square.  This is
how the `L²` strong continuity below is read off an integral statement. -/
theorem norm_sq_eq_integral (v : Lp ℝ 2 ν) : ‖v‖ ^ 2 = ∫ x, (v x) ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq v, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  change (v x) * (v x) = (v x) ^ 2
  ring

/-- **Strong continuity of the multiplier flow at `0⁺`, for every `L²` class.**  No hypothesis on
`f·u` is needed: dominated convergence with the bound `4 (u x)²` gives `‖e^{−τf} u − u‖ → 0`. -/
theorem tendsto_expFlow_nhdsGE_zero (D : MulModel X ν Λ T) (u : Lp ℝ 2 ν) :
    Tendsto (fun τ : ℝ => expFlow D.f D.hf D.hpos τ u) (𝓝[Set.Ici 0] (0 : ℝ)) (𝓝 u) := by
  have hInt : Integrable (fun x => 4 * (u x) ^ 2) ν :=
    (MemLp.integrable_sq (Lp.memLp u)).const_mul 4
  have hF_meas : ∀ᶠ τ in 𝓝[Set.Ici 0] (0 : ℝ), AEStronglyMeasurable
      (fun x => ((Real.exp (-(τ * D.f x)) - 1) * u x) ^ 2) ν :=
    Eventually.of_forall fun τ =>
      ((((measurable_const.mul D.hf).neg.exp.sub_const 1).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable u))).pow 2
  have h_bound : ∀ᶠ τ in 𝓝[Set.Ici 0] (0 : ℝ), ∀ᵐ x ∂ν,
      ‖((Real.exp (-(τ * D.f x)) - 1) * u x) ^ 2‖ ≤ 4 * (u x) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    filter_upwards [D.hpos] with x hfx
    have hτ0 : 0 ≤ τ := hτ
    have h1 : Real.exp (-(τ * D.f x)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.2 (by nlinarith)
    have h3 : |Real.exp (-(τ * D.f x)) - 1| ≤ 2 := by
      rw [abs_le]
      constructor
      · linarith [Real.exp_pos (-(τ * D.f x))]
      · linarith [Real.exp_pos (-(τ * D.f x))]
    have hsq : (Real.exp (-(τ * D.f x)) - 1) ^ 2 ≤ 4 := by
      have h4 : (Real.exp (-(τ * D.f x)) - 1) ^ 2 ≤ (2 : ℝ) ^ 2 := by
        rw [sq_le_sq]
        simpa using h3
      norm_num at h4
      exact h4
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hsplit : ((Real.exp (-(τ * D.f x)) - 1) * u x) ^ 2
        = (Real.exp (-(τ * D.f x)) - 1) ^ 2 * (u x) ^ 2 := by ring
    rw [hsplit]
    nlinarith [sq_nonneg (u x)]
  have h_lim : ∀ᵐ x ∂ν, Tendsto (fun τ : ℝ => ((Real.exp (-(τ * D.f x)) - 1) * u x) ^ 2)
      (𝓝[Set.Ici 0] (0 : ℝ)) (𝓝 0) := by
    refine Eventually.of_forall fun x => ?_
    have hexp : Tendsto (fun τ : ℝ => Real.exp (-(τ * D.f x))) (𝓝[Set.Ici 0] (0 : ℝ)) (𝓝 1) := by
      have hc : Continuous fun τ : ℝ => Real.exp (-(τ * D.f x)) :=
        Real.continuous_exp.comp (continuous_id.mul continuous_const).neg
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have h := ((hexp.sub_const 1).mul_const (u x)).pow 2
    simpa using h
  have hint : Tendsto (fun τ : ℝ => ∫ x, ((Real.exp (-(τ * D.f x)) - 1) * u x) ^ 2 ∂ν)
      (𝓝[Set.Ici 0] (0 : ℝ)) (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := ν)
      (l := 𝓝[Set.Ici 0] (0 : ℝ)) (f := fun _ => (0 : ℝ)) (fun x => 4 * (u x) ^ 2)
      hF_meas h_bound hInt h_lim
    simpa using h
  have hsq : ∀ᶠ τ in 𝓝[Set.Ici 0] (0 : ℝ),
      ‖expFlow D.f D.hf D.hpos τ u - u‖ ^ 2
        = ∫ x, ((Real.exp (-(τ * D.f x)) - 1) * u x) ^ 2 ∂ν := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [expFlow_coeFn D.hf D.hpos hτ u,
      Lp.coeFn_sub (expFlow D.f D.hf D.hpos τ u) u] with x h1 h2
    rw [h2, Pi.sub_apply, h1]
    ring
  have hnorm2 : Tendsto (fun τ : ℝ => ‖expFlow D.f D.hf D.hpos τ u - u‖ ^ 2)
      (𝓝[Set.Ici 0] (0 : ℝ)) (𝓝 0) := hint.congr' (hsq.mono fun _ h => h.symm)
  have hnorm : Tendsto (fun τ : ℝ => ‖expFlow D.f D.hf D.hpos τ u - u‖)
      (𝓝[Set.Ici 0] (0 : ℝ)) (𝓝 0) := by
    have hsqrt : Tendsto (fun τ : ℝ => Real.sqrt (‖expFlow D.f D.hf D.hpos τ u - u‖ ^ 2))
        (𝓝[Set.Ici 0] (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hnorm2
    have hfun : (fun τ : ℝ => Real.sqrt (‖expFlow D.f D.hf D.hpos τ u - u‖ ^ 2))
        = fun τ : ℝ => ‖expFlow D.f D.hf D.hpos τ u - u‖ := by
      funext τ
      exact Real.sqrt_sq (norm_nonneg _)
    rw [hfun] at hsqrt
    simpa using hsqrt
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

/-- **Strong continuity of `e^{−τH}` at `0⁺`** for every vector of `ℋ`. -/
theorem tendsto_flowOfHCLM_nhdsGE_zero (D : MulModel X ν Λ T) (x : Hphys Λ) :
    Tendsto (fun τ : ℝ => flowOfHCLM D τ x) (𝓝[Set.Ici 0] (0 : ℝ)) (𝓝 x) := by
  have h := tendsto_expFlow_nhdsGE_zero D (D.U x)
  have h2 := (D.bridge.toIsometryEquiv.symm.continuous.tendsto (D.U x)).comp h
  have hx : D.bridge.toIsometryEquiv.symm (D.U x) = x :=
    D.bridge.toIsometryEquiv.symm_apply_apply x
  rw [hx] at h2
  simpa [flowOfHCLM, flowOfH, LinearMap.mkContinuous_apply] using h2

/-- **Continuity at a positive time**, from the semigroup law: a step of size `h` is
`e^{−(τ±h)H}` applied to `e^{−|h|H} x − x`, and the flow is contractive. -/
theorem continuousAt_flowOfHCLM_of_pos (D : MulModel X ν Λ T) {τ : ℝ} (hτ : 0 < τ)
    (x : Hphys Λ) :
    ContinuousAt (fun σ : ℝ => flowOfHCLM D σ x) τ := by
  have hsmall : ∀ᶠ h in 𝓝 (0 : ℝ), |h| < τ := by
    filter_upwards [Iio_mem_nhds hτ, Ioi_mem_nhds (neg_lt_zero.2 hτ)] with h h1 h2
    exact abs_lt.2 ⟨h2, h1⟩
  have hbound : ∀ᶠ h in 𝓝 (0 : ℝ),
      ‖flowOfHCLM D (τ + h) x - flowOfHCLM D τ x‖ ≤ ‖flowOfHCLM D |h| x - x‖ := by
    filter_upwards [hsmall] with h hh
    rcases le_or_gt 0 h with h0 | h0
    · have hstep : flowOfHCLM D (τ + h) x = flowOfHCLM D τ (flowOfHCLM D h x) := by
        rw [flowOfHCLM_apply, flowOfHCLM_apply, flowOfHCLM_apply,
          flowOfH_add D hτ.le h0 x]
      rw [hstep, abs_of_nonneg h0, ← map_sub]
      exact flowOfHCLM_contractive D τ (flowOfHCLM D h x - x)
    · have hpos : 0 < -h := by linarith
      have hτh : 0 ≤ τ + h := by linarith [(abs_lt.1 hh).1]
      have hstep : flowOfHCLM D τ x = flowOfHCLM D (τ + h) (flowOfHCLM D (-h) x) := by
        have hgen := flowOfH_add D hτh hpos.le x
        have harg : τ + h + -h = τ := by ring
        rw [harg] at hgen
        simpa only [flowOfHCLM_apply] using hgen
      rw [hstep, abs_of_neg h0, ← map_sub, norm_sub_rev]
      exact flowOfHCLM_contractive D (τ + h) (x - flowOfHCLM D (-h) x)
  have hcomp : Tendsto (fun h : ℝ => flowOfHCLM D (τ + h) x) (𝓝 (0 : ℝ))
      (𝓝 (flowOfHCLM D τ x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have ha : Tendsto (fun h : ℝ => |h|) (𝓝 (0 : ℝ)) (𝓝[Set.Ici 0] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨by simpa using continuous_abs.tendsto (0 : ℝ),
        Eventually.of_forall fun h => abs_nonneg h⟩
    have hb : Tendsto (fun h : ℝ => ‖flowOfHCLM D |h| x - x‖) (𝓝 (0 : ℝ)) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp ((tendsto_flowOfHCLM_nhdsGE_zero D x).comp ha)
    exact squeeze_zero' (Eventually.of_forall fun h => norm_nonneg _) hbound hb
  have hshift : 𝓝 (τ : ℝ) = map (fun h : ℝ => τ + h) (𝓝 (0 : ℝ)) := by
    rw [map_add_left_nhds_zero]
  have hgoal : Tendsto (fun σ : ℝ => flowOfHCLM D σ x) (𝓝 τ) (𝓝 (flowOfHCLM D τ x)) := by
    rw [hshift, tendsto_map'_iff]
    simpa using hcomp
  exact hgoal

/-- **Strong continuity on `[0, ∞)`**: `τ ↦ e^{−τH} x` is continuous at every `τ ≥ 0`, for every
`x`. -/
theorem continuousOn_flowOfHCLM (D : MulModel X ν Λ T) (x : Hphys Λ) :
    ContinuousOn (fun τ : ℝ => flowOfHCLM D τ x) (Set.Ici 0) := by
  intro τ hτ
  have hτ0 : 0 ≤ τ := hτ
  rcases eq_or_lt_of_le hτ0 with rfl | hpos
  · change Tendsto (fun τ : ℝ => flowOfHCLM D τ x) (𝓝[Set.Ici 0] (0 : ℝ))
      (𝓝 (flowOfHCLM D 0 x))
    simpa [flowOfH_zero] using tendsto_flowOfHCLM_nhdsGE_zero D x
  · exact (continuousAt_flowOfHCLM_of_pos D hpos x).continuousWithinAt

/-! ## The flow is self-adjoint -/

/-- **A real multiplier is symmetric on `L²(ν)`**: `⟪W u, v⟫ = ⟪u, W v⟫`.  This is where the
symmetry of the flow comes from — the multiplier `e^{−τ f}` is real, so it commutes with the
integral. -/
theorem inner_mulL2_comm (W : Lp ℝ (⊤ : ℝ≥0∞) ν) (u v : Lp ℝ 2 ν) :
    ⟪mulL2 W u, v⟫ = ⟪u, mulL2 W v⟫ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulL2_coeFn W u, mulL2_coeFn W v] with x h1 h2
  rw [h1, h2]
  change (v x) * (W x * u x) = (W x * v x) * (u x)
  ring

/-- **Each `e^{−τH}` is self-adjoint.**  The bridge is an isometry and the multiplier flow is
symmetric, so `⟪e^{−τH} x, y⟫ = ⟪x, e^{−τH} y⟫`. -/
theorem isSelfAdjoint_flowOfHCLM (D : MulModel X ν Λ T) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsSelfAdjoint (flowOfHCLM D τ) := by
  refine LinearMap.IsSymmetric.isSelfAdjoint fun x y => ?_
  calc ⟪flowOfHCLM D τ x, y⟫ = ⟪D.U (flowOfHCLM D τ x), D.U y⟫ := (D.U.inner_map_map _ _).symm
    _ = ⟪expFlow D.f D.hf D.hpos τ (D.U x), D.U y⟫ := by
        rw [flowOfHCLM_apply, U_flowOfH]
    _ = ⟪D.U x, expFlow D.f D.hf D.hpos τ (D.U y)⟫ := by
        rw [expFlow_of_nonneg D.hf D.hpos hτ]
        exact inner_mulL2_comm _ _ _
    _ = ⟪D.U x, D.U (flowOfHCLM D τ y)⟫ := by
        rw [flowOfHCLM_apply, U_flowOfH]
    _ = ⟪x, flowOfHCLM D τ y⟫ := D.U.inner_map_map _ _

/-- **The flow of `H` is a contractive self-adjoint semigroup.**  The identity at `0`, the
semigroup law, the operator-norm bound and self-adjointness at every `τ ≥ 0`, together. -/
theorem flowOfHCLM_isContractionSelfAdjointSemigroup (D : MulModel X ν Λ T) :
    flowOfHCLM D 0 = 1 ∧
      (∀ (τ σ : ℝ), 0 ≤ τ → 0 ≤ σ →
        flowOfHCLM D (τ + σ) = flowOfHCLM D τ ∘L flowOfHCLM D σ) ∧
      (∀ τ : ℝ, ‖flowOfHCLM D τ‖ ≤ 1) ∧
      (∀ τ : ℝ, 0 ≤ τ → IsSelfAdjoint (flowOfHCLM D τ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x
    simp [flowOfH_zero]
  · intro τ σ hτ hσ
    ext x
    simp [flowOfH_add D hτ hσ x]
  · exact norm_flowOfHCLM_le_one D
  · exact fun τ hτ => isSelfAdjoint_flowOfHCLM D hτ

/-! ## The flow's difference quotient is `−H` -/

/-- **The difference quotient of the flow tends to `−H` on `dom H`**, with no reference to the
transfer semigroup: `τ⁻¹ • (e^{−τH} y − y) → −H y` for `y = R a`.  The proof is the model's own
slope `tendsto_expFlow_slope` carried back through the bridge, so it closes the generator statement
from the flow side; the limit is `−(H y)` because `U (H y) = f (λ + f)⁻¹ (U a)` (`mulImage`). -/
theorem tendsto_flowOfH_slope (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) (a : Hphys Λ) :
    Tendsto (fun τ : ℝ => τ⁻¹ • (flowOfH D τ (resolventMulModel D hlam a)
        - resolventMulModel D hlam a)) (𝓝[>] 0)
      (𝓝 (-(hamiltonianMulModel D hlam
        ⟨resolventMulModel D hlam a, mem_domain_hamiltonianMulModel D hlam a⟩))) := by
  have hcoef : (D.U (resolventMulModel D hlam a) : X → ℝ) =ᵐ[ν]
      fun t => resolventFun D lam t * (D.U a : X → ℝ) t :=
    resolventMulModel_coeFn D hlam a
  set z : X → ℝ := fun t => (D.U (resolventMulModel D hlam a) : X → ℝ) t with hz_def
  have hz : MemLp z 2 ν := by
    rw [hz_def]
    simpa only using Lp.memLp (D.U (resolventMulModel D hlam a))
  have hfz : MemLp (fun t => D.f t * z t) 2 ν := by
    rw [hz_def]
    simpa only using
      (MemLp.ae_eq (by
        filter_upwards [hcoef] with t ht
        rw [ht]
        ring) (memLp_f_resolventFun_mul D hlam a) :
        MemLp (fun t => D.f t * (D.U (resolventMulModel D hlam a) : X → ℝ) t) 2 ν)
  have hUy : D.U (resolventMulModel D hlam a) = hz.toLp z := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp hz] with t ht
    rw [ht, hz_def]
  have hslope : Tendsto (fun τ : ℝ => τ⁻¹ • (expFlow D.f D.hf D.hpos τ
        (D.U (resolventMulModel D hlam a)) - D.U (resolventMulModel D hlam a)))
      (𝓝[>] 0) (𝓝 (-(hfz.toLp (fun t => D.f t * z t)))) := by
    have h := tendsto_expFlow_slope hz D.hf D.hpos hfz
    refine h.congr' (Eventually.of_forall fun τ => ?_)
    rw [hUy]
  have hconv : Tendsto (fun τ : ℝ => D.bridge.toIsometryEquiv.symm
      (τ⁻¹ • (expFlow D.f D.hf D.hpos τ (D.U (resolventMulModel D hlam a))
        - D.U (resolventMulModel D hlam a)))) (𝓝[>] 0)
      (𝓝 (D.bridge.toIsometryEquiv.symm (-(hfz.toLp (fun t => D.f t * z t))))) :=
    (D.bridge.toIsometryEquiv.symm.continuous.tendsto _).comp hslope
  have hclass : hfz.toLp (fun t => D.f t * z t) = mulImage D hlam a :=
    MemLp.toLp_congr hfz (memLp_f_resolventFun_mul D hlam a) (by
      rw [hz_def]
      filter_upwards [hcoef] with t ht
      rw [ht]
      ring)
  have hH : D.bridge.toIsometryEquiv.symm (mulImage D hlam a) =
      hamiltonianMulModel D hlam
        ⟨resolventMulModel D hlam a, mem_domain_hamiltonianMulModel D hlam a⟩ := by
    rw [← hamiltonianMulModel_image D hlam a (mem_domain_hamiltonianMulModel D hlam a)]
    exact D.bridge.toIsometryEquiv.symm_apply_apply _
  have hlim : D.bridge.toIsometryEquiv.symm (-(hfz.toLp (fun t => D.f t * z t)))
      = -(hamiltonianMulModel D hlam
        ⟨resolventMulModel D hlam a, mem_domain_hamiltonianMulModel D hlam a⟩) := by
    rw [map_neg, hclass, hH]
  rw [hlim] at hconv
  have hsymm : D.bridge.toIsometryEquiv.symm (D.U (resolventMulModel D hlam a))
      = resolventMulModel D hlam a :=
    D.bridge.toIsometryEquiv.symm_apply_apply _
  refine hconv.congr' (Eventually.of_forall fun τ => ?_)
  change D.bridge.toIsometryEquiv.symm
      (τ⁻¹ • (expFlow D.f D.hf D.hpos τ (D.U (resolventMulModel D hlam a))
        - D.U (resolventMulModel D hlam a)))
      = τ⁻¹ • (flowOfH D τ (resolventMulModel D hlam a) - resolventMulModel D hlam a)
  rw [map_smul, map_sub, hsymm]
  rfl

/-! ## The flow's generator on the whole forward domain

`tendsto_flowOfH_slope` proves the slope limit on `dom H = ran R`, which is where the multiplier
chart can compute it directly.  The forward domain of the transfer generator is larger than that:
it is every vector whose semigroup quotient converges.  The results below show that on that whole
domain the *flow's* quotient converges too, to the same value, so the generator of `e^{−τH}` is
the transfer generator — and on `dom H` that value is `−H`, by
`generatorRight_eq_neg_hamiltonianMulModel`.

The one ingredient that is not available on the model side is the multiplier law: for a vector
outside `dom H` the model slope `τ⁻¹ (e^{−τf}u − u)` need not converge, since `f · u` need not be
in `L²`.  So here the flow is identified with the transfer semigroup first
(`physEvol_eq_flowOfH`, which is `MulModel.hlaw` read back) and the domain comes from the
semigroup, not from the multiplier. -/

/-- **The flow's slope converges on the whole forward domain**, to the transfer generator's value.
-/
theorem tendsto_flowOfH_slope_of_hasGenRight (D : MulModel X ν Λ T) {z : Hphys Λ}
    (hz : HasGenRight D.hinv z) :
    Tendsto (fun τ : ℝ => τ⁻¹ • (flowOfH D τ z - z)) (𝓝[>] 0)
      (𝓝 (generatorRight D.hinv ⟨z, hz⟩)) := by
  refine (generatorRight_apply_tendsto D.hinv ⟨z, hz⟩).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hτ0 : 0 ≤ τ := le_of_lt hτ
  rw [diffQuot, physEvol_eq_flowOfH D hτ0]

/-- Conversely, convergence of the flow's slope puts the vector in the forward domain: the flow
generates the transfer generator, not a larger one. -/
theorem hasGenRight_of_tendsto_flowOfH_slope (D : MulModel X ν Λ T) {z y : Hphys Λ}
    (h : Tendsto (fun τ : ℝ => τ⁻¹ • (flowOfH D τ z - z)) (𝓝[>] 0) (𝓝 y)) :
    HasGenRight D.hinv z := by
  refine ⟨y, h.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hτ0 : 0 ≤ τ := le_of_lt hτ
  rw [diffQuot, physEvol_eq_flowOfH D hτ0]

/-- **The flow's forward domain is exactly the transfer generator's forward domain.** -/
theorem hasGenRight_iff_tendsto_flowOfH_slope (D : MulModel X ν Λ T) (z : Hphys Λ) :
    HasGenRight D.hinv z ↔ ∃ y : Hphys Λ,
      Tendsto (fun τ : ℝ => τ⁻¹ • (flowOfH D τ z - z)) (𝓝[>] 0) (𝓝 y) :=
  ⟨fun hz => ⟨_, tendsto_flowOfH_slope_of_hasGenRight D hz⟩,
    fun ⟨_, hy⟩ => hasGenRight_of_tendsto_flowOfH_slope D hy⟩

/-- **Agreement with `−H` on `dom H`, through the general statement.**  The limit of the slope at
`R a` is the transfer generator's value there, and `U` carries it to `−U (H (R a))`; injectivity
of `U` turns that into an equality of vectors. -/
theorem tendsto_flowOfH_slope_of_mem_domainH (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    (a : Hphys Λ) :
    Tendsto (fun τ : ℝ => τ⁻¹ • (flowOfH D τ (resolventMulModel D hlam a)
        - resolventMulModel D hlam a)) (𝓝[>] 0)
      (𝓝 (-(hamiltonianMulModel D hlam
        ⟨resolventMulModel D hlam a, mem_domain_hamiltonianMulModel D hlam a⟩))) := by
  obtain ⟨hz, hgen⟩ := generatorRight_eq_neg_hamiltonianMulModel D hlam a
  have hlim : generatorRight D.hinv ⟨resolventMulModel D hlam a, hz⟩
      = -(hamiltonianMulModel D hlam
        ⟨resolventMulModel D hlam a, mem_domain_hamiltonianMulModel D hlam a⟩) :=
    D.U.injective (by rw [hgen, map_neg])
  rw [← hlim]
  exact tendsto_flowOfH_slope_of_hasGenRight D hz

/-! ## Positivity preservation

On the multiplier chart the flow acts by the *nonnegative* multiplier `e^{−τ f}`, so it preserves
the nonnegative cone of `L²(ν)` and, since `f ≥ 0` and `τ ≥ 0` force `e^{−τ f} ≤ 1`, it pulls a
nonnegative vector down rather than up (`expFlow_apply_le_of_nonneg`).  Carried through `U` this is
positivity preservation on `ℋ` in the only cone the corpus has: the preimage of the a.e.
nonnegative cone.  `H` itself is a nonnegative operator (`hamiltonianMulModel_inner_nonneg`), and
these two facts are its semigroup form.
-/

/-- **The multiplier flow preserves nonnegativity**, at every time. -/
theorem expFlow_nonneg (D : MulModel X ν Λ T) (τ : ℝ) {u : Lp ℝ 2 ν}
    (hu : ∀ᵐ x ∂ν, 0 ≤ (u : X → ℝ) x) :
    ∀ᵐ x ∂ν, 0 ≤ (expFlow D.f D.hf D.hpos τ u : X → ℝ) x := by
  rcases le_or_gt 0 τ with hτ | hτ
  · filter_upwards [expFlow_coeFn D.hf D.hpos hτ u, hu] with x hx hu'
    rw [hx]
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) hu'
  · rw [expFlow, dif_neg (not_le.mpr hτ)]
    exact hu

/-- **`e^{−τH}` is positivity preserving** on `ℋ`: a vector whose chart image is a.e. nonnegative
has a chart image that stays a.e. nonnegative. -/
theorem flowOfH_nonneg (D : MulModel X ν Λ T) (τ : ℝ) {y : Hphys Λ}
    (hy : ∀ᵐ x ∂ν, 0 ≤ (D.U y : X → ℝ) x) :
    ∀ᵐ x ∂ν, 0 ≤ (D.U (flowOfH D τ y) : X → ℝ) x := by
  rw [U_flowOfH]
  exact expFlow_nonneg D τ hy

/-- **The flow decreases the cone**: on a nonnegative vector `e^{−τ f} u ≤ u` pointwise, because
`e^{−τ f} ≤ 1`.  This is the semigroup form of `f ≥ 0`. -/
theorem expFlow_apply_le_of_nonneg (D : MulModel X ν Λ T) {τ : ℝ} (hτ : 0 ≤ τ) {u : Lp ℝ 2 ν}
    (hu : ∀ᵐ x ∂ν, 0 ≤ (u : X → ℝ) x) :
    ∀ᵐ x ∂ν, (expFlow D.f D.hf D.hpos τ u : X → ℝ) x ≤ (u : X → ℝ) x := by
  filter_upwards [expFlow_coeFn D.hf D.hpos hτ u, D.hpos, hu] with x hx hf₀ hu'
  rw [hx]
  have hexp : Real.exp (-(τ * D.f x)) ≤ 1 := by
    have hle : -(τ * D.f x) ≤ 0 := by
      have hnn : 0 ≤ τ * D.f x := mul_nonneg hτ hf₀
      linarith
    simpa using Real.exp_le_exp.mpr hle
  calc Real.exp (-(τ * D.f x)) * u x ≤ 1 * u x := mul_le_mul_of_nonneg_right hexp hu'
    _ = u x := one_mul _

/-- The same domination on `ℋ`. -/
theorem flowOfH_apply_le_of_nonneg (D : MulModel X ν Λ T) {τ : ℝ} (hτ : 0 ≤ τ) {y : Hphys Λ}
    (hy : ∀ᵐ x ∂ν, 0 ≤ (D.U y : X → ℝ) x) :
    ∀ᵐ x ∂ν, (D.U (flowOfH D τ y) : X → ℝ) x ≤ (D.U y : X → ℝ) x := by
  rw [U_flowOfH]
  exact expFlow_apply_le_of_nonneg D hτ hy

/-! ## The forward domain is dense and the generator's graph is closed

`hasGenRight_iff_tendsto_flowOfH_slope` identifies the flow's forward domain with the transfer
generator's, so the two structural properties of a generator can be stated for the flow itself:
`dense_flowForwardDomain` (the domain contains `dom H = ran R`, which is dense because `R` has dense
range) and `closed_flowForwardDomain` (the quotient map has closed graph on it).

The closedness half is inherited from `generatorRight_isClosed` and therefore carries that theorem's
matrix-element continuity hypothesis.  `LinearFunctional` has no continuity field, so `hcont` is an
OS input that cannot be read off the model, and it is not something the flow's extra regularity can
replace: the strong continuity of `e^{−τH}` (`continuousOn_flowOfHCLM`) is available, but the graph
argument integrates the transfer integral representation, which assumes `hcont`. -/

/-- **The flow's forward domain is dense in `ℋ`.**  It is dense because it contains `dom H`, and
`dom H` is dense: on `dom H` the flow's slope converges (`tendsto_flowOfH_slope`), so `dom H` is
contained in the forward domain. -/
theorem dense_flowForwardDomain (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) :
    Dense (genDomainRight D.hinv : Set (Hphys Λ)) := by
  refine (hamiltonianMulModel_dense D hlam).mono ?_
  rintro z ⟨a, rfl⟩
  exact (mem_genDomainRight D.hinv _).mpr
    (hasGenRight_of_tendsto_flowOfH_slope D (tendsto_flowOfH_slope D hlam a))

/-- **The flow's generator has closed graph on the forward domain.**  If vectors of the forward
domain converge, and so do the generator's values, then the limit is again in the forward domain and
the flow's quotient converges there to the limit value.  The last conjunct is the flow-side reading:
closedness is inherited from `generatorRight_isClosed`, and
`tendsto_flowOfH_slope_of_hasGenRight` carries it back to the flow's own slopes. -/
theorem closed_flowForwardDomain (D : MulModel X ν Λ T)
    (hcont : ∀ F : Observable, Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F) :
    ∀ (u : ℕ → genDomainRight D.hinv) {z₀ y : Hphys Λ},
      Tendsto (fun n => (u n : Hphys Λ)) atTop (𝓝 z₀) →
      Tendsto (fun n => generatorRight D.hinv (u n)) atTop (𝓝 y) →
      ∃ h : HasGenRight D.hinv z₀, generatorRight D.hinv ⟨z₀, h⟩ = y ∧
        Tendsto (fun τ : ℝ => τ⁻¹ • (flowOfH D τ z₀ - z₀)) (𝓝[>] 0) (𝓝 y) := by
  intro u z₀ y hu hv
  obtain ⟨h, heq⟩ := generatorRight_isClosed D.hinv hcont u hu hv
  refine ⟨h, heq, ?_⟩
  rw [← heq]
  exact tendsto_flowOfH_slope_of_hasGenRight D h

/-- **The flow's generator is densely defined and closed on its forward domain.** -/
theorem flowGenerator_dense_domain_closed (D : MulModel X ν Λ T)
    (hcont : ∀ F : Observable, Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    {lam : ℝ} (hlam : 0 < lam) :
    Dense (genDomainRight D.hinv : Set (Hphys Λ)) ∧
      ∀ (u : ℕ → genDomainRight D.hinv) {z₀ y : Hphys Λ},
        Tendsto (fun n => (u n : Hphys Λ)) atTop (𝓝 z₀) →
        Tendsto (fun n => generatorRight D.hinv (u n)) atTop (𝓝 y) →
        ∃ h : HasGenRight D.hinv z₀, generatorRight D.hinv ⟨z₀, h⟩ = y ∧
          Tendsto (fun τ : ℝ => τ⁻¹ • (flowOfH D τ z₀ - z₀)) (𝓝[>] 0) (𝓝 y) :=
  ⟨dense_flowForwardDomain D hlam, closed_flowForwardDomain D hcont⟩

/-! ## Large time: strict positivity, no improving, and where the mass goes

The multiplier `e^{−τf}` is *strictly* positive everywhere (`Real.exp_pos`) and `≤ 1`, so the flow
never creates a zero and never fills one in: at every `τ ≥ 0` the chart of `e^{−τH}u` vanishes
exactly where the chart of `u` does (`expFlow_support`).  A diagonal flow cannot be positivity
improving, and this is the sharp form of that: the support is preserved exactly, so mass never
spreads into a set the initial vector vanished on.

What *does* happen at large time is pointwise and complete: where `f x > 0` the factor
`e^{−τ f x} → 0` (`tendsto_expFlow_mul_atTop`), and where `f x = 0` the value is frozen
(`expFlow_apply_of_f_eq_zero`).
So the large-time limit is the projection onto `{f = 0}`: the flow is ergodic on the part of the
space where the Hamiltonian density is strictly positive, and trivial on its kernel.  Read through
`expFlow_coeFn`, this is the a.e. law for a strictly positive multiplier
(`tendsto_expFlow_apply_atTop`).  The quantitative `L²` form, `‖e^{−τH}u‖ → 0`, then follows by
dominated convergence against the bound `(u x)²` — the same estimate as contractivity — and is
`tendsto_norm_flowOfH_atTop` below; the one hypothesis it adds is `0 < f` a.e., which is exactly
what rules out a surviving kernel. -/

/-- **The flow preserves strict positivity**: on the chart the multiplier is `e^{−τf} > 0`, so an
a.e. strictly positive class stays a.e. strictly positive at every `τ ≥ 0`. -/
theorem expFlow_pos_of_pos (D : MulModel X ν Λ T) {τ : ℝ} (hτ : 0 ≤ τ) {u : Lp ℝ 2 ν}
    (hu : ∀ᵐ x ∂ν, 0 < (u : X → ℝ) x) :
    ∀ᵐ x ∂ν, 0 < (expFlow D.f D.hf D.hpos τ u : X → ℝ) x := by
  filter_upwards [expFlow_coeFn D.hf D.hpos hτ u, hu] with x hx hu'
  rw [hx]
  exact mul_pos (Real.exp_pos _) hu'

/-- **The flow is not positivity improving**: it preserves the support exactly.  A chart value is
zero after the flow exactly when it was zero before, so `e^{−τH}` never spreads mass into a set the
initial vector vanished on. -/
theorem expFlow_support (D : MulModel X ν Λ T) {τ : ℝ} (hτ : 0 ≤ τ) (u : Lp ℝ 2 ν) :
    ∀ᵐ x ∂ν, ((expFlow D.f D.hf D.hpos τ u : X → ℝ) x = 0 ↔ (u : X → ℝ) x = 0) := by
  filter_upwards [expFlow_coeFn D.hf D.hpos hτ u] with x hx
  rw [hx, mul_eq_zero]
  simp

/-- The same two facts on `ℋ`, through the bridge. -/
theorem flowOfH_pos (D : MulModel X ν Λ T) {τ : ℝ} (hτ : 0 ≤ τ) {y : Hphys Λ}
    (hy : ∀ᵐ x ∂ν, 0 < (D.U y : X → ℝ) x) :
    ∀ᵐ x ∂ν, 0 < (D.U (flowOfH D τ y) : X → ℝ) x := by
  rw [U_flowOfH]
  exact expFlow_pos_of_pos D hτ hy

/-- **Strict decrease where the density is positive**: for `τ > 0` and `f x > 0` the chart value is
strictly smaller than it was, because `e^{−τ f x} < 1`.  Together with `expFlow_support` this is the
whole large-time picture on the chart. -/
theorem expFlow_apply_lt_of_pos (D : MulModel X ν Λ T) {τ : ℝ} (hτ : 0 < τ) {u : Lp ℝ 2 ν} :
    ∀ᵐ x ∂ν, 0 < D.f x → 0 < (u : X → ℝ) x →
      (expFlow D.f D.hf D.hpos τ u : X → ℝ) x < (u : X → ℝ) x := by
  filter_upwards [expFlow_coeFn D.hf D.hpos hτ.le u] with x hx hf₀ hu₀
  rw [hx]
  have hexp : Real.exp (-(τ * D.f x)) < 1 := by
    have hneg : -(τ * D.f x) < 0 := by nlinarith [mul_pos hτ hf₀]
    simpa using Real.exp_lt_exp.mpr hneg
  calc Real.exp (-(τ * D.f x)) * u x < 1 * u x := mul_lt_mul_of_pos_right hexp hu₀
    _ = u x := one_mul _

/-- **The flow freezes the kernel of the density**: where `f x = 0` the multiplier is `e^0 = 1`, so
the chart value is unchanged at every time. -/
theorem expFlow_apply_of_f_eq_zero (D : MulModel X ν Λ T) {τ : ℝ} (hτ : 0 ≤ τ) (u : Lp ℝ 2 ν) :
    ∀ᵐ x ∂ν, D.f x = 0 → (expFlow D.f D.hf D.hpos τ u : X → ℝ) x = (u : X → ℝ) x := by
  filter_upwards [expFlow_coeFn D.hf D.hpos hτ u] with x hx hf₀
  rw [hx, hf₀, mul_zero, neg_zero, Real.exp_zero, one_mul]

/-- **Pointwise decay where the density is positive**: `e^{−τ f x} · u x → 0` as `τ → ∞`.  This is
the large-time statement on the chart, exponential in `τ` at rate `f x`. -/
theorem tendsto_expFlow_mul_atTop (D : MulModel X ν Λ T) (u : Lp ℝ 2 ν) {x : X}
    (hfx : 0 < D.f x) :
    Tendsto (fun τ : ℝ => Real.exp (-(τ * D.f x)) * (u : X → ℝ) x) atTop (𝓝 0) := by
  have hneg : Tendsto (fun τ : ℝ => τ * (-D.f x)) atTop atBot :=
    tendsto_id.atTop_mul_const_of_neg' (by linarith)
  have hexp : Tendsto (fun τ : ℝ => Real.exp (τ * (-D.f x))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  simpa [mul_neg] using hexp.mul_const ((u : X → ℝ) x)

/-- **The chart of a strictly positive multiplier decays to `0` at large time**, a.e. in `x`.
With `expFlow_coeFn` this is the a.e. large-time law for the flow: every chart component over
`{f > 0}` decays to `0`, and `expFlow_apply_of_f_eq_zero` says the components over `{f = 0}` are
the ones that stay. -/
theorem tendsto_expFlow_apply_atTop (D : MulModel X ν Λ T)
    (hstrict : ∀ᵐ x ∂ν, 0 < D.f x) (u : Lp ℝ 2 ν) :
    ∀ᵐ x ∂ν, Tendsto (fun τ : ℝ => Real.exp (-(τ * D.f x)) * (u : X → ℝ) x) atTop (𝓝 0) := by
  filter_upwards [hstrict] with x hx
  exact tendsto_expFlow_mul_atTop D u hx

/-! ### The quantitative form: `‖e^{−τH}u‖ → 0`

The pointwise law upgrades to a norm statement by dominated convergence, and the domination is the
same estimate as contractivity: `e^{−τ f x} ≤ 1` for `τ ≥ 0`, so the integrand is dominated by
`(u x)²`, which is integrable because `u ∈ L²`.  Strict positivity of the density is exactly what
rules out a surviving kernel: if `f = 0` on a set of positive measure, `e^{−τH}u` freezes there
(`expFlow_apply_of_f_eq_zero`) and the norm has that part as a nonzero limit.  So `0 < f` a.e. is
not a technical convenience here — it is the hypothesis that makes the norm limit `0`. -/

/-- **The squared norm of the flow tends to `0` at large time**, by dominated convergence against
the bound `(u x)²`. -/
theorem tendsto_norm_sq_expFlow_atTop (D : MulModel X ν Λ T)
    (hstrict : ∀ᵐ x ∂ν, 0 < D.f x) (u : Lp ℝ 2 ν) :
    Tendsto (fun τ : ℝ => ‖expFlow D.f D.hf D.hpos τ u‖ ^ 2) atTop (𝓝 0) := by
  have hInt : Integrable (fun x => (u : X → ℝ) x ^ 2) ν := MemLp.integrable_sq (Lp.memLp u)
  have hF_meas : ∀ᶠ τ in atTop, AEStronglyMeasurable
      (fun x => (Real.exp (-(τ * D.f x)) * (u : X → ℝ) x) ^ 2) ν :=
    Eventually.of_forall fun τ =>
      (((measurable_const.mul D.hf).neg.exp.aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable u))).pow 2
  have h_bound : ∀ᶠ τ in atTop, ∀ᵐ x ∂ν,
      ‖(Real.exp (-(τ * D.f x)) * (u : X → ℝ) x) ^ 2‖ ≤ (u : X → ℝ) x ^ 2 := by
    filter_upwards [Ici_mem_atTop (0 : ℝ)] with τ hτ
    filter_upwards [D.hpos] with x hfx
    have hτ0 : 0 ≤ τ := hτ
    have hτf : 0 ≤ τ * D.f x := mul_nonneg hτ0 hfx
    have he0 : 0 ≤ Real.exp (-(τ * D.f x)) := (Real.exp_pos _).le
    have he1 : Real.exp (-(τ * D.f x)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.2 (by linarith)
    have he2 : Real.exp (-(τ * D.f x)) ^ 2 ≤ 1 := by
      have h := mul_le_mul he1 he1 he0 zero_le_one
      simpa [pow_two, mul_one] using h
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hsplit : (Real.exp (-(τ * D.f x)) * (u : X → ℝ) x) ^ 2
        = Real.exp (-(τ * D.f x)) ^ 2 * (u : X → ℝ) x ^ 2 := by ring
    rw [hsplit]
    calc Real.exp (-(τ * D.f x)) ^ 2 * (u : X → ℝ) x ^ 2
        ≤ 1 * (u : X → ℝ) x ^ 2 := by
          simpa using mul_le_of_le_one_left (sq_nonneg ((u : X → ℝ) x)) he2
      _ = (u : X → ℝ) x ^ 2 := one_mul _
  have h_lim : ∀ᵐ x ∂ν, Tendsto (fun τ : ℝ => (Real.exp (-(τ * D.f x)) * (u : X → ℝ) x) ^ 2)
      atTop (𝓝 0) := by
    filter_upwards [hstrict] with x hx
    simpa using (tendsto_expFlow_mul_atTop D u hx).pow 2
  have hint : Tendsto (fun τ : ℝ => ∫ x, (Real.exp (-(τ * D.f x)) * (u : X → ℝ) x) ^ 2 ∂ν)
      atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := atTop)
      (f := fun _ => (0 : ℝ)) (fun x => (u : X → ℝ) x ^ 2) hF_meas h_bound hInt h_lim
    simpa using h
  have hsq : ∀ᶠ τ in atTop, ‖expFlow D.f D.hf D.hpos τ u‖ ^ 2
      = ∫ x, (Real.exp (-(τ * D.f x)) * (u : X → ℝ) x) ^ 2 ∂ν := by
    filter_upwards [Ici_mem_atTop (0 : ℝ)] with τ hτ
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [expFlow_coeFn D.hf D.hpos hτ u] with x hx
    rw [hx]
  exact hint.congr' (hsq.mono fun _ h => h.symm)

/-- **The flow decays to zero in `L²`** for an a.e. strictly positive density. -/
theorem tendsto_norm_expFlow_atTop (D : MulModel X ν Λ T)
    (hstrict : ∀ᵐ x ∂ν, 0 < D.f x) (u : Lp ℝ 2 ν) :
    Tendsto (fun τ : ℝ => ‖expFlow D.f D.hf D.hpos τ u‖) atTop (𝓝 0) := by
  have h2 := tendsto_norm_sq_expFlow_atTop D hstrict u
  have hsqrt : Tendsto (fun τ : ℝ => Real.sqrt (‖expFlow D.f D.hf D.hpos τ u‖ ^ 2))
      atTop (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp h2
  have hfun : (fun τ : ℝ => Real.sqrt (‖expFlow D.f D.hf D.hpos τ u‖ ^ 2))
      = fun τ : ℝ => ‖expFlow D.f D.hf D.hpos τ u‖ := by
    funext τ
    exact Real.sqrt_sq (norm_nonneg _)
  rw [hfun] at hsqrt
  simpa using hsqrt

/-- **`‖e^{−τH}y‖ → 0` in `ℋ`**: the bridge is an isometry, so the `L²` decay transfers back. -/
theorem tendsto_norm_flowOfH_atTop (D : MulModel X ν Λ T)
    (hstrict : ∀ᵐ x ∂ν, 0 < D.f x) (y : Hphys Λ) :
    Tendsto (fun τ : ℝ => ‖flowOfH D τ y‖) atTop (𝓝 0) := by
  have h := tendsto_norm_expFlow_atTop D hstrict (D.U y)
  have hnorm : ∀ τ : ℝ, ‖flowOfH D τ y‖ = ‖expFlow D.f D.hf D.hpos τ (D.U y)‖ := by
    intro τ
    rw [← U_flowOfH, D.U.norm_map]
  simpa [hnorm] using h

end

end BookProof.OSReconstruction
