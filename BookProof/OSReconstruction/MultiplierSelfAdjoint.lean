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
* `limitProjection_isOrthogonalProjectionOntoDensity` — the sharper statement, needing **no**
  hypothesis on the density: the flow converges strongly to an orthogonal projection, multiplication
  by the indicator of `{f = 0}` (`limitProjection`, `limitMulL2`), idempotent and self-adjoint, with
  the subspace it projects onto identified (`limitProjection_eq_iff`: fixed exactly when the chart
  vanishes where `f ≠ 0`; `limitProjection_eq_zero_iff` for the kernel; and the residual orthogonal
  to the range).  `‖e^{−τH}y‖ → 0` is then the case where that kernel is negligible;
* `hamiltonianMulModel_eq_zero_iff_limitProjection` — the projection's range is `ker H`: on the
  domain of `H`, `H y = 0` exactly when the chart of `y` vanishes where `f ≠ 0`, i.e. exactly when
  the limit fixes `y`;
* `kerHamiltonianMulModel_eq_range_limitProjection` — the same at the level of **submodules**: with
  `kerHamiltonianMulModel` carrying the domain in its carrier, `ker H = range P` in
  `Submodule ℝ ℋ`.  The pointwise form is not enough, because `dom H = ran R` is dense but proper;
  what makes the submodule statement true is `range_limitProjection_subset_domain` — a chart living
  on `{f = 0}` satisfies `(λ + f)·U y = λ·U y`, and `λ • U y` is again a chart of `ℋ`;
* `tendsto_opNorm_flowOfHCLM_sub_limitProjection_atTop` — operator-norm convergence with rate
  `e^{−τδ}`, **given** a gap `δ > 0` above zero in the density.  Without such a gap it is false, and
  `not_tendsto_opNorm_flowOfHCLM_of_noGap` proves that: if every `δ > 0` has a set of positive
  finite measure carrying `0 < f < δ`, then testing on its indicator gives norm at least
  `e^{−τδ} = e^{−(log 2)/2} ≥ 1/2` at every time `τ ≥ 1`.  The two norms are equal
  (`norm_flowOfHCLM_sub_limitProjection_eq`, by density of `ran U`), so no-gap ⇒ no norm
  convergence, while strong convergence still holds;
* `norm_flowOfHCLM_sub_limitProjection_le_two_scale` and
  `norm_flowOfHCLM_sub_limitProjection_lt_of_time`, with
  `exists_time_norm_flowOfHCLM_sub_limitProjection_lt` — the quantitative **strong** convergence,
  with no hypothesis on the density: for every split `δ > 0`,
  `‖e^{−τH}y − P y‖ ≤ e^{−τδ}‖y‖ + ‖1_{0<f<δ}·U y‖`, so after the explicit time
  `max 0 (-log (ε / (2(‖y‖+1))) / δ)` the flow is within `ε` of the projection.  The unresolved tail
  is chosen first and vanishes as `δ ↓ 0` (`tendsto_norm_tailMul`, dominated convergence); the rate
  is therefore explicit in `δ, ε, ‖y‖`, and only `δ` is supplied by a limit;
* `norm_flowOfHCLM_sub_limitProjection_eq_two_scale` — the same bound is **attained**, not merely
  an upper estimate: if the density equals the split on the support of the vector
  (`(D.U y) x ≠ 0 → f x = δ`), the tail is empty (`tailMul_eq_zero_of_eq_on_support`) and the
  multiplier is exactly `e^{−τδ}` there, so the two-scale estimate is an equality
  (`norm_expFlow_sub_limitMulL2_eq_of_eq_on_support` on `L²(ν)`).  The explicit witness is
  `barrier_sharp`: the barrier density `δ` on `[0, 1]`, tested on the class of its own indicator,
  gives equality for every `τ ≥ 0`.  So the gapped rate is the truth wherever it applies, and the
  no-gap hypothesis above is a hypothesis on the density, not on the proof;
* `not_exists_uniform_rate_of_noGap` — the same failure in the form it is usually wanted: there is
  no rate function `r τ → 0` bounding `‖(e^{−τH} − P)y‖` for **all** `‖y‖ ≤ 1`.  A unit-ball bound
  is a bound on the operator norm (`opNorm_le_of_unit_ball_bound`, by homogeneity), so such an `r`
  would make the norm converge, which the no-gap theorem forbids.  The rate is therefore pointwise
  in `y` and cannot be made uniform;
* `tendsto_opNorm_flowOfHCLM_sub_limitProjection_iff_gap` — the criterion as an equivalence: the
  operator norm of `e^{−τH} − P` tends to zero **iff** the density is bounded away from zero off
  its zero set (`∃ δ > 0, ∀ᵐ x, f x ≠ 0 → δ ≤ f x`).  This is the general spectral fact in the
  normal form the spectral theorem supplies — for a self-adjoint `H ≥ 0` it reads "`‖e^{−τH} − P‖`
  tends to zero iff `σ(H)` has a gap above zero".  `σ`-finiteness of the measure is used exactly
  once, to turn the a.e. no-gap condition into the split form
  (`Measure.exists_subset_measure_lt_top`);
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
identification is the choice of KL multiplier realization. The repository already supplies
spectral and Stone machinery. What remains is its concrete application to a positive-time OS
quotient, with the appropriate real/complex representation, domains and physical intertwiner.

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

/-! ### The limit is an orthogonal projection

`tendsto_norm_flowOfH_atTop` said where the mass goes but wrote the limit as `0`.  The limit is
better than that, and the better statement needs no strict positivity: `e^{−τ f x} → 1` where
`f x = 0` and `→ 0` where `f x > 0`, so the multiplier converges pointwise to the indicator of
`{f = 0}`, and that indicator is bounded by one, so the same dominated-convergence argument
converges the flow *as an operator* to multiplication by it (strongly).  On `ℋ` this is
`limitProjection`, and it is an orthogonal projection — idempotent and self-adjoint — which is the
precise sense in which the large-time limit is "the projection onto the kernel of the density".
`tendsto_norm_flowOfH_atTop` is then the case where `{f = 0}` is negligible and the projection is
`0`. -/

/-- **The indicator of the kernel of the density is essentially bounded.** -/
theorem memLp_kernelIndicator (D : MulModel X ν Λ T) :
    MemLp (fun x => if D.f x = 0 then (1 : ℝ) else 0) (⊤ : ℝ≥0∞) ν := by
  refine memLp_top_of_bound ?_ 1 ?_
  · exact (Measurable.ite (D.hf (measurableSet_singleton 0)) measurable_const
      measurable_const).aestronglyMeasurable
  · filter_upwards with x
    split_ifs <;> simp

/-- The indicator class of `{f = 0}`, as an element of `L^∞(ν)`. -/
noncomputable def kernelIndicator (D : MulModel X ν Λ T) : Lp ℝ (⊤ : ℝ≥0∞) ν :=
  (memLp_kernelIndicator D).toLp _

/-- The indicator class is the indicator function. -/
theorem kernelIndicator_coeFn (D : MulModel X ν Λ T) :
    (kernelIndicator D : X → ℝ) =ᵐ[ν] fun x => if D.f x = 0 then (1 : ℝ) else 0 :=
  MemLp.coeFn_toLp _

/-- The indicator is bounded by one. -/
theorem norm_kernelIndicator_le_one (D : MulModel X ν Λ T) :
    ∀ᵐ x ∂ν, ‖(kernelIndicator D : X → ℝ) x‖ ≤ 1 := by
  filter_upwards [kernelIndicator_coeFn D] with x hx
  rw [hx]
  split_ifs <;> simp

/-- **The limit operator on `L²(ν)`**: multiplication by the indicator of `{f = 0}`. -/
noncomputable def limitMulL2 (D : MulModel X ν Λ T) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  mulL2 (kernelIndicator D)

/-- The limit operator acts pointwise by the indicator. -/
theorem limitMulL2_coeFn (D : MulModel X ν Λ T) (u : Lp ℝ 2 ν) :
    (limitMulL2 D u : X → ℝ) =ᵐ[ν]
      fun x => (if D.f x = 0 then (1 : ℝ) else 0) * (u : X → ℝ) x := by
  refine (mulL2_coeFn (kernelIndicator D) u).trans ?_
  filter_upwards [kernelIndicator_coeFn D] with x hx
  rw [hx]

/-- The limit operator is contractive. -/
theorem limitMulL2_contractive (D : MulModel X ν Λ T) (u : Lp ℝ 2 ν) :
    ‖limitMulL2 D u‖ ≤ ‖u‖ :=
  mulL2_contractive (kernelIndicator D) (norm_kernelIndicator_le_one D) u

/-- **The multiplier approaches the indicator of `{f = 0}`, uniformly in `x`.**  Where `f x = 0` the
multiplier is `1` at every time and the indicator is `1`; where `f x > 0` the multiplier decays to
`0` and the indicator is `0`.  The difference therefore lies in `[−1, 1]` always, which is the
bound that makes the dominated convergence in the next theorem work. -/
theorem abs_exp_neg_sub_kernelIndicator_le_one (D : MulModel X ν Λ T) {τ : ℝ} (hτ : 0 ≤ τ)
    {x : X} (hfx : 0 ≤ D.f x) :
    |Real.exp (-(τ * D.f x)) - (if D.f x = 0 then (1 : ℝ) else 0)| ≤ 1 := by
  have he0 : 0 ≤ Real.exp (-(τ * D.f x)) := (Real.exp_pos _).le
  have he1 : Real.exp (-(τ * D.f x)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 (by linarith [mul_nonneg hτ hfx])
  by_cases h : D.f x = 0
  · rw [if_pos h, h]
    simp
  · rw [if_neg h, sub_zero, abs_of_nonneg he0]
    exact he1

/-- **The flow converges to the projection in `L²`**, without any strict-positivity hypothesis: the
limit is the indicator of the kernel of the density in general. -/
theorem tendsto_norm_sq_expFlow_sub_limitMulL2_atTop (D : MulModel X ν Λ T) (u : Lp ℝ 2 ν) :
    Tendsto (fun τ : ℝ => ‖expFlow D.f D.hf D.hpos τ u - limitMulL2 D u‖ ^ 2)
      atTop (𝓝 0) := by
  have hInt : Integrable (fun x => (u : X → ℝ) x ^ 2) ν := MemLp.integrable_sq (Lp.memLp u)
  have hF_meas : ∀ᶠ τ in atTop, AEStronglyMeasurable
      (fun x => ((Real.exp (-(τ * D.f x)) - (if D.f x = 0 then (1 : ℝ) else 0))
        * (u : X → ℝ) x) ^ 2) ν :=
    Eventually.of_forall fun τ =>
      ((((measurable_const.mul D.hf).neg.exp.sub
        (Measurable.ite (D.hf (measurableSet_singleton 0)) measurable_const
          measurable_const)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable u))).pow 2
  have h_bound : ∀ᶠ τ in atTop, ∀ᵐ x ∂ν,
      ‖((Real.exp (-(τ * D.f x)) - (if D.f x = 0 then (1 : ℝ) else 0))
        * (u : X → ℝ) x) ^ 2‖ ≤ (u : X → ℝ) x ^ 2 := by
    filter_upwards [Ici_mem_atTop (0 : ℝ)] with τ hτ
    filter_upwards [D.hpos] with x hfx
    have hτ0 : 0 ≤ τ := hτ
    have habs := abs_exp_neg_sub_kernelIndicator_le_one D hτ0 hfx
    have hsq1 : (Real.exp (-(τ * D.f x)) - (if D.f x = 0 then (1 : ℝ) else 0)) ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) habs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hsplit : ((Real.exp (-(τ * D.f x)) - (if D.f x = 0 then (1 : ℝ) else 0))
        * (u : X → ℝ) x) ^ 2
        = (Real.exp (-(τ * D.f x)) - (if D.f x = 0 then (1 : ℝ) else 0)) ^ 2
          * (u : X → ℝ) x ^ 2 := by ring
    rw [hsplit]
    calc (Real.exp (-(τ * D.f x)) - (if D.f x = 0 then (1 : ℝ) else 0)) ^ 2
          * (u : X → ℝ) x ^ 2
        ≤ 1 * (u : X → ℝ) x ^ 2 := by
          simpa using mul_le_of_le_one_left (sq_nonneg ((u : X → ℝ) x)) hsq1
      _ = (u : X → ℝ) x ^ 2 := one_mul _
  have h_lim : ∀ᵐ x ∂ν, Tendsto (fun τ : ℝ =>
      ((Real.exp (-(τ * D.f x)) - (if D.f x = 0 then (1 : ℝ) else 0))
        * (u : X → ℝ) x) ^ 2) atTop (𝓝 0) := by
    filter_upwards [D.hpos] with x hfx
    by_cases h : D.f x = 0
    · rw [if_pos h, h]
      simp
    · rw [if_neg h]
      have hposx : 0 < D.f x := lt_of_le_of_ne hfx (Ne.symm h)
      simpa using (tendsto_expFlow_mul_atTop D u hposx).pow 2
  have hint : Tendsto (fun τ : ℝ => ∫ x, ((Real.exp (-(τ * D.f x))
      - (if D.f x = 0 then (1 : ℝ) else 0)) * (u : X → ℝ) x) ^ 2 ∂ν) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := atTop)
      (f := fun _ => (0 : ℝ)) (fun x => (u : X → ℝ) x ^ 2) hF_meas h_bound hInt h_lim
    simpa using h
  have hsq : ∀ᶠ τ in atTop, ‖expFlow D.f D.hf D.hpos τ u - limitMulL2 D u‖ ^ 2
      = ∫ x, ((Real.exp (-(τ * D.f x)) - (if D.f x = 0 then (1 : ℝ) else 0))
          * (u : X → ℝ) x) ^ 2 ∂ν := by
    filter_upwards [Ici_mem_atTop (0 : ℝ)] with τ hτ
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [expFlow_coeFn D.hf D.hpos hτ u, limitMulL2_coeFn D u,
      Lp.coeFn_sub (expFlow D.f D.hf D.hpos τ u) (limitMulL2 D u)] with x h1 h2 h3
    rw [h3, Pi.sub_apply, h1, h2, ← sub_mul]
  exact hint.congr' (hsq.mono fun _ h => h.symm)

/-- The same in norm form. -/
theorem tendsto_norm_expFlow_sub_limitMulL2_atTop (D : MulModel X ν Λ T) (u : Lp ℝ 2 ν) :
    Tendsto (fun τ : ℝ => ‖expFlow D.f D.hf D.hpos τ u - limitMulL2 D u‖) atTop (𝓝 0) := by
  have h2 := tendsto_norm_sq_expFlow_sub_limitMulL2_atTop D u
  have hsqrt : Tendsto (fun τ : ℝ =>
      Real.sqrt (‖expFlow D.f D.hf D.hpos τ u - limitMulL2 D u‖ ^ 2))
      atTop (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp h2
  have hfun : (fun τ : ℝ =>
      Real.sqrt (‖expFlow D.f D.hf D.hpos τ u - limitMulL2 D u‖ ^ 2))
      = fun τ : ℝ => ‖expFlow D.f D.hf D.hpos τ u - limitMulL2 D u‖ := by
    funext τ
    exact Real.sqrt_sq (norm_nonneg _)
  rw [hfun] at hsqrt
  simpa using hsqrt

/-- The limit operator is idempotent: the indicator of `{f = 0}` is a projection. -/
theorem limitMulL2_idem (D : MulModel X ν Λ T) (u : Lp ℝ 2 ν) :
    limitMulL2 D (limitMulL2 D u) = limitMulL2 D u := by
  refine Lp.ext ?_
  filter_upwards [limitMulL2_coeFn D (limitMulL2 D u), limitMulL2_coeFn D u] with x h1 h2
  rw [h1, h2]
  by_cases h : D.f x = 0 <;> simp [h]

/-- **The large-time limit operator on `ℋ`**: the limit of the flow, conjugated by the bridge. -/
noncomputable def limitProjection (D : MulModel X ν Λ T) : Hphys Λ →L[ℝ] Hphys Λ :=
  LinearMap.mkContinuous
    { toFun := fun x => D.bridge.toIsometryEquiv.symm (limitMulL2 D (D.U x))
      map_add' := by intro x y; simp only [map_add]
      map_smul' := by intro c x; simp }
    1 (by
      intro x
      calc ‖D.bridge.toIsometryEquiv.symm (limitMulL2 D (D.U x))‖
          = ‖limitMulL2 D (D.U x)‖ := by simp
        _ ≤ ‖D.U x‖ := limitMulL2_contractive D (D.U x)
        _ = ‖x‖ := D.U.norm_map x
        _ = 1 * ‖x‖ := (one_mul _).symm)

/-- The defining property: `U` intertwines the limit operator with the indicator. -/
theorem U_limitProjection (D : MulModel X ν Λ T) (x : Hphys Λ) :
    D.U (limitProjection D x) = limitMulL2 D (D.U x) :=
  D.bridge.apply_toIsometryEquiv_symm_apply _

/-- **The flow converges strongly to the limit operator on `ℋ`.**  The statement needs no
hypothesis on the density: the limit is the projection onto `{f = 0}`, whatever that set is. -/
theorem tendsto_flowOfHCLM_atTop (D : MulModel X ν Λ T) (y : Hphys Λ) :
    Tendsto (fun τ : ℝ => flowOfHCLM D τ y) atTop (𝓝 (limitProjection D y)) := by
  have hnorm : Tendsto (fun τ : ℝ => ‖flowOfHCLM D τ y - limitProjection D y‖)
      atTop (𝓝 0) := by
    have h := tendsto_norm_expFlow_sub_limitMulL2_atTop D (D.U y)
    have hdiff : ∀ τ : ℝ, ‖flowOfH D τ y - limitProjection D y‖
        = ‖expFlow D.f D.hf D.hpos τ (D.U y) - limitMulL2 D (D.U y)‖ := by
      intro τ
      rw [← D.U.norm_map (flowOfH D τ y - limitProjection D y), map_sub, U_flowOfH,
        U_limitProjection]
    simpa [hdiff] using h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact hnorm

/-- **The limit operator is self-adjoint** — the indicator is real, so the same symmetry argument
that gives `isSelfAdjoint_flowOfHCLM` applies. -/
theorem isSelfAdjoint_limitProjection (D : MulModel X ν Λ T) :
    IsSelfAdjoint (limitProjection D) := by
  refine LinearMap.IsSymmetric.isSelfAdjoint fun x y => ?_
  calc ⟪limitProjection D x, y⟫ = ⟪D.U (limitProjection D x), D.U y⟫ :=
        (D.U.inner_map_map _ _).symm
    _ = ⟪limitMulL2 D (D.U x), D.U y⟫ := by rw [U_limitProjection]
    _ = ⟪D.U x, limitMulL2 D (D.U y)⟫ := inner_mulL2_comm (kernelIndicator D) _ _
    _ = ⟪D.U x, D.U (limitProjection D y)⟫ := by rw [U_limitProjection]
    _ = ⟪x, limitProjection D y⟫ := D.U.inner_map_map _ _

/-- **The limit operator is idempotent**, read through the bridge from `limitMulL2_idem`. -/
theorem limitProjection_idem (D : MulModel X ν Λ T) (y : Hphys Λ) :
    limitProjection D (limitProjection D y) = limitProjection D y := by
  refine D.U.injective ?_
  rw [U_limitProjection, U_limitProjection, limitMulL2_idem]

/-- **The large-time limit is an orthogonal projection.**  It is self-adjoint and idempotent, and it
is the strong limit of the flow, so the flow's large-time behaviour is exactly the projection onto
the kernel of the Hamiltonian density. -/
theorem limitProjection_isOrthogonalProjection (D : MulModel X ν Λ T) :
    IsSelfAdjoint (limitProjection D) ∧
      (∀ y : Hphys Λ, limitProjection D (limitProjection D y) = limitProjection D y) ∧
      (∀ y : Hphys Λ, Tendsto (fun τ : ℝ => flowOfHCLM D τ y) atTop (𝓝 (limitProjection D y))) :=
  ⟨isSelfAdjoint_limitProjection D, limitProjection_idem D, tendsto_flowOfHCLM_atTop D⟩

/-! ### Which subspace it projects onto

Self-adjoint and idempotent do not yet say *where* the projection lands.  The chart identifies it:
a vector is fixed by the flow exactly when its chart vanishes where the density does not
(`limitProjection_eq_iff`), and is killed exactly when its chart vanishes where the density does
(`limitProjection_eq_zero_iff`).  The residual is orthogonal to the range
(`inner_sub_limitProjection_limitProjection`), so the two subspaces are orthogonal complements —
which is what "the orthogonal projection onto the kernel of the density" means. -/

/-- **The fixed points of the limit are the vectors living on `{f = 0}`.**  On the chart the
projection is multiplication by the indicator of `{f = 0}`, so it fixes `y` exactly when `U y`
vanishes where the density is nonzero. -/
theorem limitProjection_eq_iff (D : MulModel X ν Λ T) (y : Hphys Λ) :
    limitProjection D y = y ↔ ∀ᵐ x ∂ν, D.f x ≠ 0 → (D.U y : X → ℝ) x = 0 := by
  constructor
  · intro h
    have h2 : D.U y = limitMulL2 D (D.U y) := by
      calc D.U y = D.U (limitProjection D y) := (congrArg D.U h).symm
        _ = limitMulL2 D (D.U y) := U_limitProjection D y
    have hcoe : (D.U y : X → ℝ) =ᵐ[ν]
        fun x => (if D.f x = 0 then (1 : ℝ) else 0) * (D.U y : X → ℝ) x := by
      have h3 := limitMulL2_coeFn D (D.U y)
      rw [← h2] at h3
      exact h3
    filter_upwards [hcoe] with x hx hfx
    rw [hx, if_neg hfx, zero_mul]
  · intro h
    refine D.U.injective ?_
    rw [U_limitProjection]
    refine Lp.ext ?_
    filter_upwards [limitMulL2_coeFn D (D.U y), h] with x hx hy
    rw [hx]
    by_cases hf0 : D.f x = 0
    · rw [if_pos hf0, one_mul]
    · rw [if_neg hf0, zero_mul]
      exact (hy hf0).symm

/-- **The kernel of the limit is the part of `ℋ` living on `{f > 0}`.**  The projection kills `y`
exactly when `U y` vanishes where the density is zero. -/
theorem limitProjection_eq_zero_iff (D : MulModel X ν Λ T) (y : Hphys Λ) :
    limitProjection D y = 0 ↔ ∀ᵐ x ∂ν, D.f x = 0 → (D.U y : X → ℝ) x = 0 := by
  constructor
  · intro h
    have hU : limitMulL2 D (D.U y) = (0 : Lp ℝ 2 ν) := by
      rw [← U_limitProjection, h, map_zero]
    have hcoe : (fun x => (if D.f x = 0 then (1 : ℝ) else 0) * (D.U y : X → ℝ) x)
        =ᵐ[ν] fun _ => (0 : ℝ) := by
      have h1 := limitMulL2_coeFn D (D.U y)
      rw [hU] at h1
      simpa using h1.symm.trans (Lp.coeFn_zero (μ := ν) (p := 2) (E := ℝ))
    filter_upwards [hcoe] with x hx hf0
    rw [hf0, if_pos rfl, one_mul] at hx
    exact hx
  · intro h
    refine D.U.injective ?_
    rw [U_limitProjection, map_zero]
    refine Lp.ext ?_
    filter_upwards [limitMulL2_coeFn D (D.U y), h,
      Lp.coeFn_zero (μ := ν) (p := 2) (E := ℝ)] with x hx hy hz
    rw [hx, hz, Pi.zero_apply]
    by_cases hf0 : D.f x = 0
    · rw [if_pos hf0, one_mul]
      exact hy hf0
    · rw [if_neg hf0, zero_mul]

/-- **The residual is orthogonal to the range.**  On the chart the residual is multiplication by
`1 − 1_{f = 0}`, i.e. by the indicator of `{f ≠ 0}`, and the projection's value is multiplication by
`1_{f = 0}`, so their pointwise product vanishes. -/
theorem inner_sub_limitProjection_limitProjection (D : MulModel X ν Λ T) (y z : Hphys Λ) :
    ⟪y - limitProjection D y, limitProjection D z⟫ = 0 := by
  rw [← D.U.inner_map_map (y - limitProjection D y) (limitProjection D z)]
  have hres : D.U (y - limitProjection D y) = D.U y - limitMulL2 D (D.U y) := by
    rw [map_sub, U_limitProjection]
  have hcoe1 : (D.U (y - limitProjection D y) : X → ℝ) =ᵐ[ν]
      fun x => (if D.f x = 0 then (0 : ℝ) else 1) * (D.U y : X → ℝ) x := by
    rw [hres]
    filter_upwards [Lp.coeFn_sub (D.U y) (limitMulL2 D (D.U y)),
      limitMulL2_coeFn D (D.U y)] with x hx hy
    rw [hx, Pi.sub_apply, hy]
    by_cases h : D.f x = 0 <;> simp [h]
  have hcoe2 : (D.U (limitProjection D z) : X → ℝ) =ᵐ[ν]
      fun x => (if D.f x = 0 then (1 : ℝ) else 0) * (D.U z : X → ℝ) x := by
    rw [U_limitProjection]
    exact limitMulL2_coeFn D (D.U z)
  rw [L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hcoe1, hcoe2] with x hx hy
  rw [hx, hy]
  by_cases h : D.f x = 0 <;> simp [h]

/-- **Range and kernel are orthogonal.**  Read on the chart: a vector in the range vanishes where
`f ≠ 0`, one in the kernel vanishes where `f = 0`, so the pointwise product is zero everywhere. -/
theorem inner_limitProjection_ker (D : MulModel X ν Λ T) {y z : Hphys Λ}
    (hy : limitProjection D y = y) (hz : limitProjection D z = 0) : ⟪y, z⟫ = 0 := by
  have hy' := (limitProjection_eq_iff D y).mp hy
  have hz' := (limitProjection_eq_zero_iff D z).mp hz
  rw [← D.U.inner_map_map y z, L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hy', hz'] with x h1 h2
  by_cases h : D.f x = 0
  · rw [h2 h]
    simp
  · rw [h1 h]
    simp

/-- **The range of the limit is the part of `ℋ` living on the kernel of the density.** -/
theorem range_limitProjection (D : MulModel X ν Λ T) :
    Set.range (limitProjection D) = {y | ∀ᵐ x ∂ν, D.f x ≠ 0 → (D.U y : X → ℝ) x = 0} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact (limitProjection_eq_iff D (limitProjection D z)).mp (limitProjection_idem D z)
  · intro hy
    exact ⟨y, (limitProjection_eq_iff D y).mpr hy⟩

/-- **The kernel of the limit**, as a submodule. -/
theorem mem_ker_limitProjection (D : MulModel X ν Λ T) (y : Hphys Λ) :
    y ∈ LinearMap.ker (limitProjection D : Hphys Λ →ₗ[ℝ] Hphys Λ) ↔
      ∀ᵐ x ∂ν, D.f x = 0 → (D.U y : X → ℝ) x = 0 := by
  rw [LinearMap.mem_ker]
  exact limitProjection_eq_zero_iff D y

/-- **The residual lies in the kernel**, so every vector decomposes as `limitProjection D y` plus a
kernel vector: the two subspaces give `ℋ` as an orthogonal direct sum. -/
theorem residual_mem_ker_limitProjection (D : MulModel X ν Λ T) (y : Hphys Λ) :
    y - limitProjection D y ∈ LinearMap.ker (limitProjection D : Hphys Λ →ₗ[ℝ] Hphys Λ) := by
  rw [mem_ker_limitProjection]
  have hres : D.U (y - limitProjection D y) = D.U y - limitMulL2 D (D.U y) := by
    rw [map_sub, U_limitProjection]
  filter_upwards [limitMulL2_coeFn D (D.U y),
    Lp.coeFn_sub (D.U y) (limitMulL2 D (D.U y))] with x h1 h2 hfx
  rw [hres, h2, Pi.sub_apply, h1, if_pos hfx, one_mul, sub_self]

/-- **`mulImage` vanishes exactly on charts that vanish where the density is nonzero.** -/
theorem mulImage_eq_zero_iff (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) (a : Hphys Λ) :
    mulImage D hlam a = 0 ↔
      ∀ᵐ x ∂ν, D.f x ≠ 0 → (D.U (resolventMulModel D hlam a) : X → ℝ) x = 0 := by
  constructor
  · intro h
    have hcoe : (fun x => D.f x * resolventFun D lam x * (D.U a : X → ℝ) x)
        =ᵐ[ν] fun _ => (0 : ℝ) := by
      have h1 := mulImage_coeFn D hlam a
      rw [h] at h1
      exact h1.symm.trans (Lp.coeFn_zero (μ := ν) (p := 2) (E := ℝ))
    filter_upwards [hcoe, resolventMulModel_coeFn D hlam a] with x hx hr hfx
    rw [hr]
    rcases mul_eq_zero.mp hx with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hfx
      · rw [h2, zero_mul]
    · rw [h1, mul_zero]
  · intro h
    have hprod : (fun x => D.f x * (D.U (resolventMulModel D hlam a) : X → ℝ) x)
        =ᵐ[ν] fun _ => (0 : ℝ) := by
      filter_upwards [h] with x hx
      by_cases hfx : D.f x = 0
      · rw [hfx, zero_mul]
      · rw [hx hfx, mul_zero]
    refine Lp.ext ?_
    filter_upwards [mulImage_coeFn D hlam a, resolventMulModel_coeFn D hlam a, hprod,
      Lp.coeFn_zero (μ := ν) (p := 2) (E := ℝ)] with x hm hr hp h0
    rw [hm, mul_assoc, ← hr, hp, h0]
    rfl

/-- **The kernel of `H` is the kernel of the density**: a domain vector `R a` is annihilated by `H`
exactly when its chart vanishes where the density is nonzero.  This is `H = f` on the chart read at
zero: `U (H (R a)) = f · U (R a)`. -/
theorem hamiltonianMulModel_eq_zero_iff (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    (a : Hphys Λ) (ha : resolventMulModel D hlam a ∈ (hamiltonianMulModel D hlam).domain) :
    hamiltonianMulModel D hlam ⟨resolventMulModel D hlam a, ha⟩ = 0 ↔
      ∀ᵐ x ∂ν, D.f x ≠ 0 → (D.U (resolventMulModel D hlam a) : X → ℝ) x = 0 := by
  rw [← mulImage_eq_zero_iff D hlam a]
  constructor
  · intro h
    rw [← hamiltonianMulModel_image D hlam a ha, h, map_zero]
  · intro h
    refine D.U.injective ?_
    rw [hamiltonianMulModel_image D hlam a ha, h, map_zero]

/-- **The range of the projection is `ker H`**: on the domain of `H`, being annihilated by `H` is
the same as being fixed by the large-time limit.  So the subspace the flow projects onto is
exactly the kernel of the Hamiltonian. -/
theorem hamiltonianMulModel_eq_zero_iff_limitProjection (D : MulModel X ν Λ T) {lam : ℝ}
    (hlam : 0 < lam) (a : Hphys Λ)
    (ha : resolventMulModel D hlam a ∈ (hamiltonianMulModel D hlam).domain) :
    hamiltonianMulModel D hlam ⟨resolventMulModel D hlam a, ha⟩ = 0 ↔
      limitProjection D (resolventMulModel D hlam a) = resolventMulModel D hlam a :=
  (hamiltonianMulModel_eq_zero_iff D hlam a ha).trans (limitProjection_eq_iff D _).symm

/-! ### `ker H` is the range of the projection, as submodules

`hamiltonianMulModel_eq_zero_iff_limitProjection` matched `H y = 0` with `P y = y` for the domain
vectors `y = R a`.  That is a statement about `dom H`, and `dom H` is the range of a bounded
operator — dense in `ℋ` but *proper*, since `y ∈ dom H` asks the chart `(λ + f)·U y` to be a chart
of `ℋ` and `U` is only dense.  So the pointwise form does not yet say that the two submodules of
`ℋ` agree.

They do agree, and the missing half is one observation: if `U y` vanishes where `f ≠ 0` — which is
exactly `P y = y` — then `(λ + f)·U y = λ·U y`, and `λ • U y` is again a chart of `ℋ` because the
range of an isometry is a subspace.  Hence the range of `P` is contained in `dom H` after all, and
the comparison of the two submodules can be made with no intersection or closure:
`kerHamiltonianMulModel_eq_range_limitProjection` is an equality in `Submodule ℝ ℋ`.
-/

/-- **The resolvent multiplier undoes `λ •` on a chart living where `f = 0`.**  This is the
arithmetic that puts the range of the projection inside the domain of `H`. -/
theorem resolventFun_mul_smul_of_eq_zero {f lam v : ℝ} (hlam : lam ≠ 0)
    (h : f ≠ 0 → v = 0) : (lam + f)⁻¹ * (lam * v) = v := by
  by_cases hf : f = 0
  · rw [hf, add_zero, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  · rw [h hf, mul_zero, mul_zero]

/-- Conversely, a chart that is a fixed point of `λ (λ + f)⁻¹` away from `f = 0` vanishes there.
So `H y = 0` does force `U y` to live on `{f = 0}`. -/
theorem eq_zero_of_eq_mul_resolventFun {f lam v : ℝ} (hne : lam + f ≠ 0) (hf : f ≠ 0)
    (hv : v = (lam + f)⁻¹ * (lam * v)) : v = 0 := by
  have hmul : (lam + f) * v = lam * v := by
    conv_lhs => rw [hv]
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  have hfv : v * f = 0 := by nlinarith [hmul]
  rcases mul_eq_zero.mp hfv with h | h
  · exact h
  · exact absurd h hf

/-- **The kernel of `H` as a submodule of `ℋ`**: the vectors of the domain that `H` annihilates.
The domain is carried in the carrier instead of being intersected afterwards, so that the
comparison with the range of the projection is an equality of submodules of `ℋ`. -/
def kerHamiltonianMulModel (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam) :
    Submodule ℝ (Hphys Λ) where
  carrier := {y | ∃ hy : y ∈ (hamiltonianMulModel D hlam).domain,
    hamiltonianMulModel D hlam ⟨y, hy⟩ = 0}
  zero_mem' := ⟨(hamiltonianMulModel D hlam).domain.zero_mem, by
    rw [show (⟨0, (hamiltonianMulModel D hlam).domain.zero_mem⟩
      : (hamiltonianMulModel D hlam).domain) = 0 from rfl]
    exact LinearPMap.map_zero _⟩
  add_mem' := by
    rintro y z ⟨hy, hHy⟩ ⟨hz, hHz⟩
    refine ⟨(hamiltonianMulModel D hlam).domain.add_mem hy hz, ?_⟩
    have h : (⟨y + z, (hamiltonianMulModel D hlam).domain.add_mem hy hz⟩
        : (hamiltonianMulModel D hlam).domain) = ⟨y, hy⟩ + ⟨z, hz⟩ := by
      exact Subtype.ext rfl
    rw [h, LinearPMap.map_add, hHy, hHz, add_zero]
  smul_mem' := by
    rintro c y ⟨hy, hHy⟩
    refine ⟨(hamiltonianMulModel D hlam).domain.smul_mem c hy, ?_⟩
    have h : (⟨c • y, (hamiltonianMulModel D hlam).domain.smul_mem c hy⟩
        : (hamiltonianMulModel D hlam).domain) = c • ⟨y, hy⟩ := by
      exact Subtype.ext rfl
    rw [h, LinearPMap.map_smul, hHy, smul_zero]

/-- Membership in the kernel submodule, in the `dom H` form that the pointwise lemmas use. -/
theorem mem_kerHamiltonianMulModel (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    (y : Hphys Λ) :
    y ∈ kerHamiltonianMulModel D hlam ↔
      ∃ hy : y ∈ (hamiltonianMulModel D hlam).domain,
        hamiltonianMulModel D hlam ⟨y, hy⟩ = 0 :=
  Iff.rfl

/-- **An explicit preimage of a fixed point of the projection.**  If `P y = y` then the chart of `y`
vanishes where `f ≠ 0`, so `λ • U y` is still a chart of `ℋ` and `a := U⁻¹(λ • U y)` is a preimage
of `y` under the resolvent.  Both halves are recorded — the resolvent equation `R a = y` and the
chart equation `U a = λ • U y` — because together they say that `y` is in the domain of `H` *and*
that `H` annihilates it. -/
theorem exists_resolventMulModel_eq_of_limitProjection (D : MulModel X ν Λ T) {lam : ℝ}
    (hlam : 0 < lam) {y : Hphys Λ} (hy : limitProjection D y = y) :
    ∃ a : Hphys Λ, resolventMulModel D hlam a = y ∧ D.U a = lam • D.U y := by
  have hsupp : ∀ᵐ x ∂ν, D.f x ≠ 0 → (D.U y : X → ℝ) x = 0 :=
    (limitProjection_eq_iff D y).mp hy
  set a : Hphys Λ := D.bridge.toIsometryEquiv.symm (lam • D.U y) with ha_def
  have hUa : D.U a = lam • D.U y := D.bridge_apply_symm (lam • D.U y)
  have hsm : (D.U a : X → ℝ) =ᵐ[ν] fun x => lam * (D.U y : X → ℝ) x := by
    have h := Lp.coeFn_smul lam (D.U y)
    rw [← hUa] at h
    filter_upwards [h] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul]
  refine ⟨a, ?_, hUa⟩
  refine D.U.injective ?_
  refine Lp.ext ?_
  filter_upwards [resolventMulModel_coeFn D hlam a, hsm, hsupp] with x hx hc hs
  calc (D.U (resolventMulModel D hlam a) : X → ℝ) x
      = resolventFun D lam x * (D.U a : X → ℝ) x := hx
    _ = resolventFun D lam x * (lam * (D.U y : X → ℝ) x) := by rw [hc]
    _ = (D.U y : X → ℝ) x := resolventFun_mul_smul_of_eq_zero hlam.ne' hs

/-- **The range of the limit projection is contained in the domain of `H`.**  The witness is the
one `exists_resolventMulModel_eq_of_limitProjection` constructs, so this needs no extra work: the
chart `λ • U y` of a vector living on `{f = 0}` is again a chart of `ℋ`.  This is what makes the
kernel of `H` comparable with the range of `P` as submodules of `ℋ`, with no intersection with the
domain. -/
theorem range_limitProjection_subset_domain (D : MulModel X ν Λ T) {lam : ℝ} (hlam : 0 < lam)
    {y : Hphys Λ} (hy : limitProjection D y = y) :
    y ∈ (hamiltonianMulModel D hlam).domain := by
  obtain ⟨a, ha, _⟩ := exists_resolventMulModel_eq_of_limitProjection D hlam hy
  exact ⟨a, ha⟩

/-- **`ker H` is the range of the limit projection**, as an equality of submodules of `ℋ`.

Neither side needs an intersection with the domain: `range_limitProjection_subset_domain` places
the range inside `dom H`, and on `dom H` the two conditions `H y = 0` and `P y = y` are equivalent
(`hamiltonianMulModel_eq_zero_iff_limitProjection`).  So the subspace the flow projects onto in the
large-time limit is not merely "the same set on the domain" — it is `ker H`. -/
theorem kerHamiltonianMulModel_eq_range_limitProjection (D : MulModel X ν Λ T) {lam : ℝ}
    (hlam : 0 < lam) :
    kerHamiltonianMulModel D hlam = LinearMap.range (limitProjection D : Hphys Λ →ₗ[ℝ] Hphys Λ) :=
  Submodule.ext fun y => by
    rw [mem_kerHamiltonianMulModel, LinearMap.mem_range]
    constructor
    · rintro ⟨hy, hHy⟩
      -- `H y = 0` makes `λ • y` a fixed vector of the resolvent
      have hRy : resolventMulModel D hlam (lam • y) = y := by
        have h := resolvent_hamiltonianMulModel D hlam ⟨y, hy⟩
        rw [hHy, zero_add] at h
        exact h
      -- hence `U y = (λ + f)⁻¹ (λ U y)` and it vanishes where `f ≠ 0`
      have hsupp : ∀ᵐ x ∂ν, D.f x ≠ 0 → (D.U y : X → ℝ) x = 0 := by
        have h := resolventMulModel_coeFn D hlam (lam • y)
        rw [hRy] at h
        have hsm : (D.U (lam • y) : X → ℝ) =ᵐ[ν]
            fun x => lam * (D.U y : X → ℝ) x := by
          have h1 := Lp.coeFn_smul lam (D.U y)
          rw [← map_smul] at h1
          filter_upwards [h1] with x hx
          rw [hx, Pi.smul_apply, smul_eq_mul]
        filter_upwards [h, hsm, D.hpos] with x hx hc hposx
        intro hfx
        refine eq_zero_of_eq_mul_resolventFun (f := D.f x) (lam := lam)
          (v := (D.U y : X → ℝ) x) ?_ hfx ?_
        · nlinarith
        · calc (D.U y : X → ℝ) x
              = resolventFun D lam x * (D.U (lam • y) : X → ℝ) x := hx
            _ = resolventFun D lam x * (lam * (D.U y : X → ℝ) x) := by rw [hc]
            _ = (lam + D.f x)⁻¹ * (lam * (D.U y : X → ℝ) x) := by rw [resolventFun]
      exact ⟨y, show (limitProjection D : Hphys Λ →ₗ[ℝ] Hphys Λ) y = y from
        (limitProjection_eq_iff D y).mpr hsupp⟩
    · rintro ⟨z, hz⟩
      have hy' : y = limitProjection D z := hz.symm
      rw [hy']
      obtain ⟨a, ha, hUa⟩ := exists_resolventMulModel_eq_of_limitProjection D hlam
        (limitProjection_idem D z)
      have hdom : limitProjection D z ∈ (hamiltonianMulModel D hlam).domain := ⟨a, ha⟩
      have hay : a = lam • limitProjection D z := by
        refine D.U.injective ?_
        rw [hUa, map_smul]
      refine ⟨hdom, ?_⟩
      rw [hamiltonianMulModel_apply_of_eq D hlam (y := ⟨limitProjection D z, hdom⟩) ha.symm,
        ha, hay, sub_self]

/-! ### Operator-norm convergence needs a spectral gap

Strong convergence (`tendsto_flowOfHCLM_atTop`) does **not** upgrade to operator-norm convergence
without a hypothesis, and it is worth saying exactly why, because the naive statement is false.

The operator under consideration is multiplication by `g_τ = e^{−τ f} − 1_{f = 0}`, whose operator
norm is the essential supremum of `|g_τ|`.  If `f` has no gap above zero — say `ν` is Lebesgue
measure on `(0, 1)` and `f x = x` — then for every `τ` the multiplier is `≥ e^{−τ ε}` on the set
`{f < ε}` of positive measure, so testing against vectors supported there gives
`‖e^{−τH} − P‖ ≥ e^{−τ ε}` for every `ε > 0`, hence `‖e^{−τH} − P‖ = 1` for all `τ`, while still
`e^{−τH} y → P y` strongly for every `y`.

What *does* give operator-norm convergence, with a rate, is a gap: if `f` is bounded below by
`δ > 0` away from its zero set, then `|g_τ| ≤ e^{−τ δ}` everywhere, and the norm estimate
`‖e^{−τH} − P‖ ≤ e^{−τ δ}` follows from the pointwise one (`Lp.norm_le_norm_of_ae_le`).  So this
section proves the conditional statement `tendsto_flowOfHCLM_opNorm_atTop` and leaves the
unconditional one alone: it is not a gap in the proof but a false statement. -/

/-- **Pointwise `L²` estimate with rate**: a gap `δ` above zero bounds the flow's deviation from the
projection by `e^{−τδ}` on the chart, hence in norm on every vector. -/
theorem norm_flowOfHCLM_sub_limitProjection_le (D : MulModel X ν Λ T) {δ : ℝ}
    (hgap : ∀ᵐ x ∂ν, D.f x ≠ 0 → δ ≤ D.f x) {τ : ℝ} (hτ : 0 ≤ τ) (y : Hphys Λ) :
    ‖flowOfHCLM D τ y - limitProjection D y‖ ≤ Real.exp (-(τ * δ)) * ‖y‖ := by
  have hdiff : ‖flowOfHCLM D τ y - limitProjection D y‖
      = ‖expFlow D.f D.hf D.hpos τ (D.U y) - limitMulL2 D (D.U y)‖ := by
    rw [← D.U.norm_map (flowOfHCLM D τ y - limitProjection D y), map_sub, flowOfHCLM_apply,
      U_flowOfH, U_limitProjection]
  rw [hdiff]
  have hle : ‖expFlow D.f D.hf D.hpos τ (D.U y) - limitMulL2 D (D.U y)‖
      ≤ ‖Real.exp (-(τ * δ)) • (D.U y)‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [expFlow_coeFn D.hf D.hpos hτ (D.U y), limitMulL2_coeFn D (D.U y),
      Lp.coeFn_sub (expFlow D.f D.hf D.hpos τ (D.U y)) (limitMulL2 D (D.U y)),
      Lp.coeFn_smul (Real.exp (-(τ * δ))) (D.U y), hgap] with x h1 h2 h3 h4 hg
    rw [h3, Pi.sub_apply, h1, h2, ← sub_mul, h4, Pi.smul_apply, norm_mul, norm_smul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    by_cases hfx : D.f x = 0
    · rw [hfx]
      simpa using (Real.exp_pos (-(τ * δ))).le
    · rw [if_neg hfx, sub_zero, abs_of_nonneg (Real.exp_nonneg _)]
      refine Real.exp_le_exp.2 ?_
      have hle : τ * δ ≤ τ * D.f x := mul_le_mul_of_nonneg_left (hg hfx) hτ
      linarith
  calc ‖expFlow D.f D.hf D.hpos τ (D.U y) - limitMulL2 D (D.U y)‖
      ≤ ‖Real.exp (-(τ * δ)) • (D.U y)‖ := hle
    _ = Real.exp (-(τ * δ)) * ‖y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, D.U.norm_map]

/-- **Operator-norm estimate with rate `e^{−τδ}`.** -/
theorem norm_flowOfHCLM_sub_limitProjection (D : MulModel X ν Λ T) {δ : ℝ}
    (hgap : ∀ᵐ x ∂ν, D.f x ≠ 0 → δ ≤ D.f x) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖flowOfHCLM D τ - limitProjection D‖ ≤ Real.exp (-(τ * δ)) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun y => ?_
  exact norm_flowOfHCLM_sub_limitProjection_le D hgap hτ y

/-- **The flow converges to the projection in operator norm**, given a spectral gap `δ` above zero
in the density.  Without the gap the statement is false (see the section header). -/
theorem tendsto_opNorm_flowOfHCLM_sub_limitProjection_atTop (D : MulModel X ν Λ T) {δ : ℝ}
    (hδ : 0 < δ) (hgap : ∀ᵐ x ∂ν, D.f x ≠ 0 → δ ≤ D.f x) :
    Tendsto (fun τ : ℝ => ‖flowOfHCLM D τ - limitProjection D‖) atTop (𝓝 0) := by
  have hexp : Tendsto (fun τ : ℝ => Real.exp (-(τ * δ))) atTop (𝓝 0) := by
    have hneg : Tendsto (fun τ : ℝ => -(τ * δ)) atTop atBot := by
      have h1 : Tendsto (fun τ : ℝ => τ * (-δ)) atTop atBot :=
        tendsto_id.atTop_mul_const_of_neg' (by linarith)
      simpa [mul_neg] using h1
    simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp hneg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
    (Eventually.of_forall fun τ =>
      ContinuousLinearMap.opNorm_nonneg (flowOfHCLM D τ - limitProjection D)) ?_
  filter_upwards [Ici_mem_atTop (0 : ℝ)] with τ hτ
  exact norm_flowOfHCLM_sub_limitProjection D hgap hτ

/-! ### A quantitative rate for the strong convergence

Operator-norm convergence needs a gap, but the *strong* convergence has a two-scale rate with no
hypothesis at all.  On `{f ≥ δ}` the multiplier `g_τ = e^{−τ f} − 1_{f = 0}` is at most `e^{−τ δ}`;
on `{0 < f < δ}` it is at most one; on `{f = 0}` it vanishes.  So for every `δ > 0`

  `‖e^{−τH} y − P y‖ ≤ e^{−τ δ} ‖y‖ + ‖1_{0 < f < δ} · U y‖`,

the second term being the part of `y` that the split at `δ` cannot resolve.  It does not depend on
`τ` and disappears as `δ ↓ 0`, because `{0 < f < δ} ↓ ∅` and `U y ∈ L²` — dominated convergence,
so the tail is a modulus of continuity that the density itself supplies.  Choosing `δ` first and
then the time turns the rate into the explicit bound
`T = max 0 (-log (ε / (2 (‖y‖ + 1))) / δ)`: for `τ ≥ T` the flow is within `ε` of the projection.
This is what is left of the asymptotic statement once the operator norm is known to be out of
reach: pointwise in `y` there *is* a rate, and it is this one.
-/

/-- The indicator of `{0 < f < δ}` is bounded by one, so the tail is `L²`. -/
theorem memLp_tail_mul (D : MulModel X ν Λ T) (δ : ℝ) (u : Lp ℝ 2 ν) :
    MemLp (fun x => (if 0 < D.f x ∧ D.f x < δ then (1 : ℝ) else 0) * (u : X → ℝ) x) 2 ν := by
  have hs : MeasurableSet {x : X | 0 < D.f x ∧ D.f x < δ} :=
    (D.hf measurableSet_Ioi).inter (D.hf measurableSet_Iio)
  refine memLp_mul_of_abs_bound (Lp.memLp u) ?_ zero_le_one ?_
  · exact Measurable.ite hs measurable_const measurable_const
  · filter_upwards with x
    split_ifs <;> simp

/-- **The tail of a class at `δ`**: `1_{0 < f < δ} · u`. -/
noncomputable def tailMul (D : MulModel X ν Λ T) (δ : ℝ) (u : Lp ℝ 2 ν) : Lp ℝ 2 ν :=
  (memLp_tail_mul D δ u).toLp _

/-- The tail acts pointwise by the indicator. -/
theorem tailMul_coeFn (D : MulModel X ν Λ T) (δ : ℝ) (u : Lp ℝ 2 ν) :
    (tailMul D δ u : X → ℝ) =ᵐ[ν]
      fun x => (if 0 < D.f x ∧ D.f x < δ then (1 : ℝ) else 0) * (u : X → ℝ) x :=
  MemLp.coeFn_toLp _

/-- **The pointwise two-scale bound.**  Above the split the multiplier is at most `e^{−τ δ}`, below
it it is at most one, and on `{f = 0}` both sides vanish. -/
theorem abs_exp_neg_sub_kernelIndicator_le_two_scale (D : MulModel X ν Λ T) {δ : ℝ}
    {τ : ℝ} (hτ : 0 ≤ τ) {x : X} (hfx0 : 0 ≤ D.f x) :
    |Real.exp (-(τ * D.f x)) - (if D.f x = 0 then (1 : ℝ) else 0)|
      ≤ Real.exp (-(τ * δ)) + (if 0 < D.f x ∧ D.f x < δ then (1 : ℝ) else 0) := by
  have hexpδ : 0 ≤ Real.exp (-(τ * δ)) := (Real.exp_pos _).le
  by_cases h : D.f x = 0
  · rw [if_pos h, h, mul_zero, neg_zero, Real.exp_zero, sub_self, abs_zero,
      show (if 0 < (0 : ℝ) ∧ (0 : ℝ) < δ then (1 : ℝ) else 0) = 0 by simp, add_zero]
    exact hexpδ
  · rw [if_neg h, sub_zero, abs_of_nonneg (Real.exp_nonneg _)]
    by_cases hlt : D.f x < δ
    · have hcond : 0 < D.f x ∧ D.f x < δ := ⟨lt_of_le_of_ne hfx0 (Ne.symm h), hlt⟩
      rw [if_pos hcond]
      have h1 : Real.exp (-(τ * D.f x)) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.2 (by nlinarith)
      linarith
    · have hcond : ¬ (0 < D.f x ∧ D.f x < δ) := fun hc => hlt hc.2
      rw [if_neg hcond, add_zero]
      refine Real.exp_le_exp.2 ?_
      have hge : δ ≤ D.f x := le_of_not_gt hlt
      nlinarith [mul_le_mul_of_nonneg_left hge hτ]

/-- **The two-scale estimate on `L²(ν)`**: the deviation from the limit is bounded by the gapped
term plus the tail below the split. -/
theorem norm_expFlow_sub_limitMulL2_le_two_scale (D : MulModel X ν Λ T) {δ : ℝ}
    {τ : ℝ} (hτ : 0 ≤ τ) (u : Lp ℝ 2 ν) :
    ‖expFlow D.f D.hf D.hpos τ u - limitMulL2 D u‖
      ≤ Real.exp (-(τ * δ)) * ‖u‖ + ‖tailMul D δ u‖ := by
  have hnorm : ‖expFlow D.f D.hf D.hpos τ u - limitMulL2 D u‖
      ≤ ‖Real.exp (-(τ * δ)) • u + tailMul D δ u‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [expFlow_coeFn D.hf D.hpos hτ u, limitMulL2_coeFn D u,
      Lp.coeFn_sub (expFlow D.f D.hf D.hpos τ u) (limitMulL2 D u),
      Lp.coeFn_add (Real.exp (-(τ * δ)) • u) (tailMul D δ u),
      Lp.coeFn_smul (Real.exp (-(τ * δ))) u, tailMul_coeFn D δ u, D.hpos]
      with x h1 h2 h3 h4 h5 h6 h7
    have hpt : ((expFlow D.f D.hf D.hpos τ u - limitMulL2 D u : Lp ℝ 2 ν) : X → ℝ) x
        = (Real.exp (-(τ * D.f x)) - (if D.f x = 0 then (1 : ℝ) else 0)) * (u : X → ℝ) x := by
      rw [h3, Pi.sub_apply, h1, h2, sub_mul]
    have hptw : ((Real.exp (-(τ * δ)) • u + tailMul D δ u : Lp ℝ 2 ν) : X → ℝ) x
        = (Real.exp (-(τ * δ)) + (if 0 < D.f x ∧ D.f x < δ then (1 : ℝ) else 0))
            * (u : X → ℝ) x := by
      rw [h4, Pi.add_apply, h5, Pi.smul_apply, smul_eq_mul, h6]
      ring
    have hnn : (0 : ℝ) ≤ Real.exp (-(τ * δ)) + (if 0 < D.f x ∧ D.f x < δ then (1 : ℝ) else 0) := by
      split_ifs
      · have := (Real.exp_pos (-(τ * δ))).le
        linarith
      · simpa using (Real.exp_pos (-(τ * δ))).le
    rw [hpt, hptw, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_right (abs_exp_neg_sub_kernelIndicator_le_two_scale D hτ h7)
      (abs_nonneg _)
  calc ‖expFlow D.f D.hf D.hpos τ u - limitMulL2 D u‖
      ≤ ‖Real.exp (-(τ * δ)) • u + tailMul D δ u‖ := hnorm
    _ ≤ ‖Real.exp (-(τ * δ)) • u‖ + ‖tailMul D δ u‖ := norm_add_le _ _
    _ = Real.exp (-(τ * δ)) * ‖u‖ + ‖tailMul D δ u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]

/-- **The two-scale estimate on `ℋ`**, through the isometry. -/
theorem norm_flowOfHCLM_sub_limitProjection_le_two_scale (D : MulModel X ν Λ T) {δ : ℝ}
    {τ : ℝ} (hτ : 0 ≤ τ) (y : Hphys Λ) :
    ‖flowOfHCLM D τ y - limitProjection D y‖
      ≤ Real.exp (-(τ * δ)) * ‖y‖ + ‖tailMul D δ (D.U y)‖ := by
  have hdiff : ‖flowOfHCLM D τ y - limitProjection D y‖
      = ‖expFlow D.f D.hf D.hpos τ (D.U y) - limitMulL2 D (D.U y)‖ := by
    rw [← D.U.norm_map (flowOfHCLM D τ y - limitProjection D y), map_sub, flowOfHCLM_apply,
      U_flowOfH, U_limitProjection]
  rw [hdiff, ← D.U.norm_map y]
  exact norm_expFlow_sub_limitMulL2_le_two_scale D hτ (D.U y)

/-- **The tail vanishes as `δ ↓ 0`.**  Pointwise `1_{0 < f < δ} → 0` (on `{f = 0}` it is already
zero, and on `{f > 0}` it is zero once `δ < f`), and it is dominated by `u²`, so the squared tail
norm tends to zero. -/
theorem tendsto_norm_sq_tailMul (D : MulModel X ν Λ T) (u : Lp ℝ 2 ν) :
    Tendsto (fun δ : ℝ => ‖tailMul D δ u‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hInt : Integrable (fun x => (u : X → ℝ) x ^ 2) ν := MemLp.integrable_sq (Lp.memLp u)
  have hfun : ∀ δ : ℝ, ‖tailMul D δ u‖ ^ 2
      = ∫ x, (if 0 < D.f x ∧ D.f x < δ then (1 : ℝ) else 0) * (u : X → ℝ) x ^ 2 ∂ν := by
    intro δ
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [tailMul_coeFn D δ u] with x hx
    rw [hx]
    by_cases h : 0 < D.f x ∧ D.f x < δ
    · rw [if_pos h]; ring
    · rw [if_neg h]; ring
  have hF_meas : ∀ᶠ δ in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun x => (if 0 < D.f x ∧ D.f x < δ then (1 : ℝ) else 0) * (u : X → ℝ) x ^ 2) ν :=
    Eventually.of_forall fun δ =>
      (Measurable.ite ((D.hf measurableSet_Ioi).inter (D.hf measurableSet_Iio))
        measurable_const measurable_const).aestronglyMeasurable.mul
        ((Lp.aestronglyMeasurable u).pow 2)
  have h_bound : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂ν,
      ‖(if 0 < D.f x ∧ D.f x < δ then (1 : ℝ) else 0) * (u : X → ℝ) x ^ 2‖
        ≤ (u : X → ℝ) x ^ 2 := by
    filter_upwards with δ
    filter_upwards with x
    by_cases h : 0 < D.f x ∧ D.f x < δ
    · rw [if_pos h, one_mul, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg ((u : X → ℝ) x))]
    · rw [if_neg h, zero_mul, Real.norm_eq_abs, abs_zero]
      exact sq_nonneg _
  have h_lim : ∀ᵐ x ∂ν, Tendsto (fun δ : ℝ =>
      (if 0 < D.f x ∧ D.f x < δ then (1 : ℝ) else 0) * (u : X → ℝ) x ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    filter_upwards [D.hpos] with x hfx0
    by_cases h : D.f x = 0
    · have hzero : (fun δ : ℝ => (if 0 < D.f x ∧ D.f x < δ then (1 : ℝ) else 0)
          * (u : X → ℝ) x ^ 2) = fun _ => (0 : ℝ) := by
        funext δ
        rw [h]
        simp
      rw [hzero]
      exact tendsto_const_nhds
    · have hposx : 0 < D.f x := lt_of_le_of_ne hfx0 (Ne.symm h)
      have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ¬ (0 < D.f x ∧ D.f x < δ) := by
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hposx)] with δ hδ
        exact fun hc => absurd hc.2 (not_lt.mpr hδ.le)
      have heq : (fun δ : ℝ => (if 0 < D.f x ∧ D.f x < δ then (1 : ℝ) else 0)
          * (u : X → ℝ) x ^ 2) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (0 : ℝ) := by
        filter_upwards [hev] with δ hδ
        rw [if_neg hδ, zero_mul]
      rw [tendsto_congr' heq]
      exact tendsto_const_nhds
  simp_rw [hfun]
  have h := tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := 𝓝[>] (0 : ℝ))
    (f := fun _ => (0 : ℝ)) (fun x => (u : X → ℝ) x ^ 2) hF_meas h_bound hInt h_lim
  simpa using h

/-- The tail norm itself tends to zero at `0⁺`. -/
theorem tendsto_norm_tailMul (D : MulModel X ν Λ T) (u : Lp ℝ 2 ν) :
    Tendsto (fun δ : ℝ => ‖tailMul D δ u‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h2 := tendsto_norm_sq_tailMul D u
  have hsqrt : Tendsto (fun δ : ℝ => Real.sqrt (‖tailMul D δ u‖ ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp h2
  have hfun : (fun δ : ℝ => Real.sqrt (‖tailMul D δ u‖ ^ 2))
      = fun δ : ℝ => ‖tailMul D δ u‖ := by
    funext δ
    exact Real.sqrt_sq (norm_nonneg _)
  rw [hfun] at hsqrt
  simpa using hsqrt

/-- **A tail smaller than `η` exists at some positive split.** -/
theorem exists_tailMul_norm_lt (D : MulModel X ν Λ T) (u : Lp ℝ 2 ν) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ‖tailMul D δ u‖ < η := by
  have h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ‖tailMul D δ u‖ < η :=
    (tendsto_norm_tailMul D u).eventually (Iio_mem_nhds hη)
  have hpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδlt, hδpos⟩ := (h.and hpos).exists
  exact ⟨δ, hδpos, hδlt⟩

/-- **An explicit time.**  If the split `δ` resolves all but `ε/2` of the tail, then from
`T = max 0 (-log (ε / (2 (‖y‖ + 1))) / δ)` on, the flow is within `ε` of the projection.  The
time is explicit in `δ`, `ε` and `‖y‖`; the only non-explicit ingredient is the split itself,
which the density supplies through `exists_tailMul_norm_lt`. -/
theorem norm_flowOfHCLM_sub_limitProjection_lt_of_time (D : MulModel X ν Λ T) {δ : ℝ}
    (hδ : 0 < δ) (y : Hphys Λ) {ε : ℝ} (hε : 0 < ε) {τ : ℝ}
    (hτ : max 0 (-(Real.log (ε / (2 * (‖y‖ + 1)))) / δ) ≤ τ)
    (htail : ‖tailMul D δ (D.U y)‖ < ε / 2) :
    ‖flowOfHCLM D τ y - limitProjection D y‖ < ε := by
  have hτ0 : 0 ≤ τ := le_trans (le_max_left _ _) hτ
  have hτT : -(Real.log (ε / (2 * (‖y‖ + 1)))) / δ ≤ τ := le_trans (le_max_right _ _) hτ
  have hc : 0 < ε / (2 * (‖y‖ + 1)) := by positivity
  have hexp : Real.exp (-(τ * δ)) ≤ ε / (2 * (‖y‖ + 1)) := by
    rw [← Real.exp_log hc]
    refine Real.exp_le_exp.2 ?_
    have hmul := mul_le_mul_of_nonneg_right hτT hδ.le
    rw [div_mul_cancel₀ _ hδ.ne'] at hmul
    nlinarith
  have hstep : Real.exp (-(τ * δ)) * ‖y‖ ≤ ε / 2 := by
    calc Real.exp (-(τ * δ)) * ‖y‖ ≤ (ε / (2 * (‖y‖ + 1))) * ‖y‖ :=
          mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
      _ ≤ ε / 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [norm_nonneg y, hε.le]
  have hmain := norm_flowOfHCLM_sub_limitProjection_le_two_scale (δ := δ) D hτ0 y
  linarith

/-- **Strong convergence with an explicit time.**  For every `ε > 0` the flow is within `ε` of the
projection after a time that the proof names: `max 0 (-log (ε / (2 (‖y‖ + 1))) / δ)`, where `δ > 0`
is any split for which the unresolved tail `1_{0 < f < δ} · U y` has norm below `ε/2`.  Such a
split exists because the tail tends to zero as `δ ↓ 0` — so the asymptotic statement is quantified,
not merely asserted. -/
theorem exists_time_norm_flowOfHCLM_sub_limitProjection_lt (D : MulModel X ν Λ T) (y : Hphys Λ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ τ : ℝ, T ≤ τ → ‖flowOfHCLM D τ y - limitProjection D y‖ < ε := by
  obtain ⟨δ, hδpos, hδtail⟩ := exists_tailMul_norm_lt D (D.U y) (η := ε / 2) (by linarith)
  exact ⟨max 0 (-(Real.log (ε / (2 * (‖y‖ + 1)))) / δ), fun τ hτ =>
    norm_flowOfHCLM_sub_limitProjection_lt_of_time D hδpos y hε hτ hδtail⟩

/-- **The operator norms agree.**  The flow and the projection are conjugates of their model-side
counterparts by the isometry `U`, so `‖S‖ ≤ ‖T‖` is immediate; density of the range of `U` is what
turns it into an equality, because every `L²` vector is a limit of charts and the two operators
agree on charts. -/
theorem norm_flowOfHCLM_sub_limitProjection_eq (D : MulModel X ν Λ T) (τ : ℝ) :
    ‖flowOfHCLM D τ - limitProjection D‖ = ‖expFlow D.f D.hf D.hpos τ - limitMulL2 D‖ := by
  have hUfun : ∀ y : Hphys Λ, D.U ((flowOfHCLM D τ - limitProjection D) y)
      = (expFlow D.f D.hf D.hpos τ - limitMulL2 D) (D.U y) := by
    intro y
    rw [ContinuousLinearMap.sub_apply, map_sub, ContinuousLinearMap.sub_apply, flowOfHCLM_apply,
      U_flowOfH, U_limitProjection]
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
    calc ‖(flowOfHCLM D τ - limitProjection D) y‖
        = ‖D.U ((flowOfHCLM D τ - limitProjection D) y)‖ := (D.U.norm_map _).symm
      _ = ‖(expFlow D.f D.hf D.hpos τ - limitMulL2 D) (D.U y)‖ := by rw [hUfun y]
      _ ≤ ‖expFlow D.f D.hf D.hpos τ - limitMulL2 D‖ * ‖D.U y‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖expFlow D.f D.hf D.hpos τ - limitMulL2 D‖ * ‖y‖ := by rw [D.U.norm_map]
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
    have happrox : ∀ n : ℕ, ∃ y : Hphys Λ, ‖D.U y - u‖ < 1 / (n + 1) := by
      intro n
      have hmem : u ∈ closure (Set.range D.U) := by
        rw [D.hdense.closure_range]
        exact Set.mem_univ u
      obtain ⟨v, ⟨y, rfl⟩, hv⟩ := Metric.mem_closure_iff.mp hmem (1 / (n + 1)) (by positivity)
      exact ⟨y, by simpa [dist_eq_norm, norm_sub_rev] using hv⟩
    choose y hy using happrox
    have hcont : Tendsto (fun n : ℕ => D.U (y n)) atTop (𝓝 u) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hy n).le) ?_
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h1 : Tendsto (fun n : ℕ =>
        ‖(expFlow D.f D.hf D.hpos τ - limitMulL2 D) (D.U (y n))‖) atTop
        (𝓝 ‖(expFlow D.f D.hf D.hpos τ - limitMulL2 D) u‖) :=
      (((expFlow D.f D.hf D.hpos τ - limitMulL2 D).continuous.tendsto u).norm).comp hcont
    have h2 : Tendsto (fun n : ℕ => ‖flowOfHCLM D τ - limitProjection D‖ * ‖D.U (y n)‖)
        atTop (𝓝 (‖flowOfHCLM D τ - limitProjection D‖ * ‖u‖)) :=
      tendsto_const_nhds.mul hcont.norm
    refine le_of_tendsto_of_tendsto' h1 h2 fun n => ?_
    calc ‖(expFlow D.f D.hf D.hpos τ - limitMulL2 D) (D.U (y n))‖
        = ‖(flowOfHCLM D τ - limitProjection D) (y n)‖ := by
          rw [← D.U.norm_map ((flowOfHCLM D τ - limitProjection D) (y n)), hUfun]
      _ ≤ ‖flowOfHCLM D τ - limitProjection D‖ * ‖y n‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖flowOfHCLM D τ - limitProjection D‖ * ‖D.U (y n)‖ := by rw [D.U.norm_map]

/-- **The model-side lower bound.**  On a set where `0 < f < δ` the multiplier is at least
`e^{−τ δ}`, so the indicator of that set is a test vector on which the operator is large; since the
indicator is a nonzero `L²` class, the operator norm is at least `e^{−τ δ}`. -/
theorem norm_expFlow_sub_limitMulL2_ge (D : MulModel X ν Λ T) {δ : ℝ}
    {s : Set X} (hs : MeasurableSet s) (hs0 : ν s ≠ 0) (hsf : ν s ≠ ∞)
    (hgs : ∀ x ∈ s, 0 < D.f x ∧ D.f x < δ) {τ : ℝ} (hτ : 0 ≤ τ) :
    Real.exp (-(τ * δ)) ≤ ‖expFlow D.f D.hf D.hpos τ - limitMulL2 D‖ := by
  set u : Lp ℝ 2 ν := indicatorConstLp 2 hs hsf (1 : ℝ) with hu_def
  have hu_coe : (u : X → ℝ) =ᵐ[ν] s.indicator (fun _ => (1 : ℝ)) :=
    indicatorConstLp_coeFn
  have hpos : 0 < ν.real s := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hs0 hsf
  have hu_pos : 0 < ‖u‖ := by
    rw [hu_def, norm_indicatorConstLp' (p := (2 : ℝ≥0∞)) (by norm_num) hs0]
    simp only [Real.norm_eq_abs, abs_one, one_mul]
    exact Real.rpow_pos_of_pos hpos _
  have hlow : Real.exp (-(τ * δ)) * ‖u‖
      ≤ ‖(expFlow D.f D.hf D.hpos τ - limitMulL2 D) u‖ := by
    rw [ContinuousLinearMap.sub_apply]
    have hnorm : Real.exp (-(τ * δ)) * ‖u‖ = ‖Real.exp (-(τ * δ)) • u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    rw [hnorm]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [expFlow_coeFn D.hf D.hpos hτ u, limitMulL2_coeFn D u,
      Lp.coeFn_sub (expFlow D.f D.hf D.hpos τ u) (limitMulL2 D u),
      Lp.coeFn_smul (Real.exp (-(τ * δ))) u, hu_coe] with x h1 h2 h3 h4 h5
    have hpt : (((expFlow D.f D.hf D.hpos τ u - limitMulL2 D u) : Lp ℝ 2 ν) : X → ℝ) x
        = (Real.exp (-(τ * D.f x)) - (if D.f x = 0 then (1 : ℝ) else 0)) * (u : X → ℝ) x := by
      rw [h3, Pi.sub_apply, h1, h2, sub_mul]
    have hptsmul : (((Real.exp (-(τ * δ)) • u) : Lp ℝ 2 ν) : X → ℝ) x
        = Real.exp (-(τ * δ)) * (u : X → ℝ) x := by
      rw [h4, Pi.smul_apply, smul_eq_mul]
    rw [hpt, hptsmul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    by_cases hmem : x ∈ s
    · have hx := hgs x hmem
      have hge : Real.exp (-(τ * δ)) ≤ Real.exp (-(τ * D.f x)) :=
        Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hx.2.le hτ])
      rw [h5, Set.indicator_of_mem hmem, if_neg (ne_of_gt hx.1), sub_zero,
        abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg (Real.exp_nonneg _)]
      simpa using hge
    · rw [h5, Set.indicator_of_notMem hmem]
      simp
  exact le_of_mul_le_mul_right
    (hlow.trans (ContinuousLinearMap.le_opNorm
      (expFlow D.f D.hf D.hpos τ - limitMulL2 D) u)) hu_pos

/-- **Without a gap, the operator norm does not converge to zero.**  The hypothesis says the density
has no gap above its zero set — for every `δ > 0` some set of positive finite measure carries
`0 < f < δ` — and then the norm is at least `1/2` at every time `τ ≥ 1` (take `δ = log 2 / (2τ)`),
so it cannot tend to zero.  Strong convergence is unaffected: this is a failure of the *uniform*
statement only. -/
theorem not_tendsto_opNorm_flowOfHCLM_of_noGap (D : MulModel X ν Λ T)
    (hno : ∀ δ : ℝ, 0 < δ → ∃ s : Set X, MeasurableSet s ∧ ν s ≠ 0 ∧ ν s ≠ ∞ ∧
      ∀ x ∈ s, 0 < D.f x ∧ D.f x < δ) :
    ¬ Tendsto (fun τ : ℝ => ‖flowOfHCLM D τ - limitProjection D‖) atTop (𝓝 0) := by
  intro hconv
  have hev : ∀ᶠ τ : ℝ in atTop, ‖flowOfHCLM D τ - limitProjection D‖ < 1 / 2 :=
    hconv.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨τ, hτlt, hτ1⟩ := (hev.and (eventually_ge_atTop (1 : ℝ))).exists
  have hτ0 : 0 ≤ τ := by linarith
  set δ : ℝ := Real.log 2 / (2 * τ) with hδ_def
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδpos : 0 < δ := by
    rw [hδ_def]
    exact div_pos hlog (by linarith)
  obtain ⟨s, hs, hs0, hsf, hgs⟩ := hno δ hδpos
  have hlower := norm_expFlow_sub_limitMulL2_ge D hs hs0 hsf hgs hτ0
  rw [norm_flowOfHCLM_sub_limitProjection_eq D τ] at hτlt
  have hτδ : τ * δ = Real.log 2 / 2 := by
    rw [hδ_def]
    have : τ ≠ 0 := by linarith
    field_simp
  have hexp : (1 / 2 : ℝ) ≤ Real.exp (-(τ * δ)) := by
    rw [hτδ]
    calc (1 / 2 : ℝ) = Real.exp (-(Real.log 2)) := by
          rw [Real.exp_neg, Real.exp_log (by norm_num)]
          norm_num
      _ ≤ Real.exp (-(Real.log 2 / 2)) := Real.exp_le_exp.2 (by linarith)
  linarith

/-! ### Without a gap the operator norm does not converge

The counterexample promised in the section header, as a theorem.  The hypothesis is exactly the
negation of a gap: for every `δ > 0` there is a set of positive finite measure on which
`0 < f < δ`.  There the multiplier `e^{−τ f}` is at least `e^{−τ δ}`, so testing the model-side
operator on the indicator of that set gives operator norm at least `e^{−τ δ}`; with
`δ = log 2 / (2τ)` that is `1/2`.  The two operator norms agree
(`norm_flowOfHCLM_sub_limitProjection_eq`, by density of the range of `U`), so the norm on `ℋ` is
at least `1/2` at every time `τ ≥ 1`: it cannot converge to `0`, even though the flow does converge
to the projection *strongly* (`tendsto_flowOfHCLM_atTop`).  The gap in the rate theorem is
therefore not an artefact of the proof — without it the statement is false.
-/

/-! ### Sharpness of the rate, and the absence of a uniform one

The two-scale bound is *attained*, and it is the only uniform statement available.  Sharpness: when
the density is exactly the split `δ` on the support of the vector, nothing carries `0 < f < δ`, so
the tail vanishes, and the multiplier is exactly `e^{−τ δ}` there — the estimate becomes an
identity.  The barrier density `δ` on `[0, 1]`, tested on its own indicator, is an explicit
witness.  Non-uniformity: a rate on the unit ball is a rate on the operator norm, so the absence
of norm convergence is exactly the absence of a uniform schedule of accuracy; the last theorem
states that without mentioning operator norms at all.
-/

/-- The indicator of `{f = 0}` for an arbitrary measurable density. -/
theorem memLp_kernelIndicator_of_measurable {f : X → ℝ} (hf : Measurable f) :
    MemLp (fun x => if f x = 0 then (1 : ℝ) else 0) (⊤ : ℝ≥0∞) ν := by
  refine memLp_top_of_bound ?_ 1 ?_
  · exact (Measurable.ite (hf (measurableSet_singleton 0)) measurable_const
      measurable_const).aestronglyMeasurable
  · filter_upwards with x
    split_ifs <;> simp

/-- The kernel indicator of a measurable density, as an `L^∞` class. -/
noncomputable def kernelWeight {f : X → ℝ} (hf : Measurable f) : Lp ℝ (⊤ : ℝ≥0∞) ν :=
  (memLp_kernelIndicator_of_measurable hf).toLp _

/-- It acts as the indicator function. -/
theorem kernelWeight_coeFn {f : X → ℝ} (hf : Measurable f) :
    (kernelWeight (ν := ν) hf : X → ℝ) =ᵐ[ν] fun x => if f x = 0 then (1 : ℝ) else 0 :=
  MemLp.coeFn_toLp _

/-- **The limit operator is multiplication by the kernel weight.**  The two presentations differ
only in the proof that the indicator is essentially bounded, which is not definitional, so the
identification is propositional. -/
theorem limitMulL2_eq_mulL2_kernelWeight (D : MulModel X ν Λ T) :
    limitMulL2 D = mulL2 (kernelWeight (ν := ν) D.hf) := by
  refine ContinuousLinearMap.ext fun u => Lp.ext ?_
  filter_upwards [limitMulL2_coeFn D u, mulL2_coeFn (kernelWeight (ν := ν) D.hf) u,
    kernelWeight_coeFn D.hf] with x h1 h2 h3
  rw [h1, h2, h3]

/-- **The two-scale bound is attained on a density constant at the split.**  If every nonzero value
of the vector sits where `f = δ`, the tail is empty and the multiplier equals `e^{−τ δ}` there, so
the deviation is exactly `e^{−τ δ}‖u‖` at every time. -/
theorem norm_expFlow_sub_mulL2_kernel_eq_of_eq_on_support {f : X → ℝ} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂ν, 0 ≤ f x) {δ τ : ℝ} (hδ : 0 < δ) (hτ : 0 ≤ τ) (u : Lp ℝ 2 ν)
    (hu : ∀ᵐ x ∂ν, (u : X → ℝ) x ≠ 0 → f x = δ) :
    ‖expFlow f hf hpos τ u - mulL2 (kernelWeight (ν := ν) hf) u‖
      = Real.exp (-(τ * δ)) * ‖u‖ := by
  have hEq : expFlow f hf hpos τ u - mulL2 (kernelWeight (ν := ν) hf) u
      = Real.exp (-(τ * δ)) • u := by
    refine Lp.ext ?_
    filter_upwards [expFlow_coeFn hf hpos hτ u, mulL2_coeFn (kernelWeight (ν := ν) hf) u,
      kernelWeight_coeFn hf, Lp.coeFn_sub (expFlow f hf hpos τ u)
        (mulL2 (kernelWeight (ν := ν) hf) u), Lp.coeFn_smul (Real.exp (-(τ * δ))) u, hu]
      with x h1 h2 h3 h4 h5 h6
    rw [h4, Pi.sub_apply, h1, h2, h3, ← sub_mul, h5, Pi.smul_apply, smul_eq_mul]
    by_cases hx : (u : X → ℝ) x = 0
    · rw [hx, mul_zero, mul_zero]
    · have hfδ : f x = δ := h6 hx
      rw [hfδ, if_neg (ne_of_gt hδ), sub_zero]
  rw [hEq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]

/-- **Sharpness in the multiplier model.** -/
theorem norm_expFlow_sub_limitMulL2_eq_of_eq_on_support (D : MulModel X ν Λ T) {δ τ : ℝ}
    (hδ : 0 < δ) (hτ : 0 ≤ τ) (u : Lp ℝ 2 ν)
    (hu : ∀ᵐ x ∂ν, (u : X → ℝ) x ≠ 0 → D.f x = δ) :
    ‖expFlow D.f D.hf D.hpos τ u - limitMulL2 D u‖ = Real.exp (-(τ * δ)) * ‖u‖ := by
  rw [limitMulL2_eq_mulL2_kernelWeight]
  exact norm_expFlow_sub_mulL2_kernel_eq_of_eq_on_support D.hf D.hpos hδ hτ u hu

/-- **The tail is empty when the density is constant on the support.** -/
theorem tailMul_eq_zero_of_eq_on_support (D : MulModel X ν Λ T) {δ : ℝ} (_hδ : 0 < δ)
    (u : Lp ℝ 2 ν) (hu : ∀ᵐ x ∂ν, (u : X → ℝ) x ≠ 0 → D.f x = δ) :
    tailMul D δ u = 0 := by
  refine Lp.ext ?_
  filter_upwards [tailMul_coeFn D δ u, hu, Lp.coeFn_zero ℝ 2 ν] with x hx h h0
  rw [hx, h0]
  by_cases hux : (u : X → ℝ) x = 0
  · rw [hux, mul_zero]
    simp
  · have hfδ : D.f x = δ := h hux
    have hnot : ¬ (0 < D.f x ∧ D.f x < δ) := by
      rw [hfδ]
      exact fun hc => lt_irrefl δ hc.2
    rw [if_neg hnot, zero_mul]
    simp

/-- **The two-scale estimate is an equality**, not merely an inequality, on such a density. -/
theorem norm_expFlow_sub_limitMulL2_eq_two_scale_of_eq_on_support (D : MulModel X ν Λ T)
    {δ τ : ℝ} (hδ : 0 < δ) (hτ : 0 ≤ τ) (u : Lp ℝ 2 ν)
    (hu : ∀ᵐ x ∂ν, (u : X → ℝ) x ≠ 0 → D.f x = δ) :
    ‖expFlow D.f D.hf D.hpos τ u - limitMulL2 D u‖
      = Real.exp (-(τ * δ)) * ‖u‖ + ‖tailMul D δ u‖ := by
  rw [norm_expFlow_sub_limitMulL2_eq_of_eq_on_support D hδ hτ u hu,
    tailMul_eq_zero_of_eq_on_support D hδ u hu, norm_zero, add_zero]

/-- **Sharpness on `ℋ`**, through the isometry: the rate is attained by any `y` whose chart sits
where the density equals the split. -/
theorem norm_flowOfHCLM_sub_limitProjection_eq_two_scale (D : MulModel X ν Λ T) {δ τ : ℝ}
    (hδ : 0 < δ) (hτ : 0 ≤ τ) (y : Hphys Λ)
    (hy : ∀ᵐ x ∂ν, (D.U y : X → ℝ) x ≠ 0 → D.f x = δ) :
    ‖flowOfHCLM D τ y - limitProjection D y‖
      = Real.exp (-(τ * δ)) * ‖y‖ + ‖tailMul D δ (D.U y)‖ := by
  have hdiff : ‖flowOfHCLM D τ y - limitProjection D y‖
      = ‖expFlow D.f D.hf D.hpos τ (D.U y) - limitMulL2 D (D.U y)‖ := by
    rw [← D.U.norm_map (flowOfHCLM D τ y - limitProjection D y), map_sub, flowOfHCLM_apply,
      U_flowOfH, U_limitProjection]
  rw [hdiff, norm_expFlow_sub_limitMulL2_eq_two_scale_of_eq_on_support D hδ hτ (D.U y) hy,
    D.U.norm_map]

/-- **A bound on the unit ball is a bound on the operator norm.**  The unit ball controls the
operator norm by homogeneity, so a pointwise-in-`y` estimate with a constant `r` is an estimate of
`‖S‖` by `r`. -/
theorem opNorm_le_of_unit_ball_bound (D : MulModel X ν Λ T) {r τ : ℝ} (hr : 0 ≤ r)
    (h : ∀ y : Hphys Λ, ‖y‖ ≤ 1 →
      ‖(flowOfHCLM D τ - limitProjection D) y‖ ≤ r) :
    ‖flowOfHCLM D τ - limitProjection D‖ ≤ r := by
  refine ContinuousLinearMap.opNorm_le_bound _ hr fun y => ?_
  rcases eq_or_ne y 0 with h0 | hy
  · subst h0
    rw [map_zero, norm_zero]
    simp
  · have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy
    have hunit : ‖(‖y‖⁻¹ : ℝ) • y‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hypos)]
      exact inv_mul_cancel₀ hypos.ne'
    have h1 := h ((‖y‖⁻¹ : ℝ) • y) hunit.le
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hypos)] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hypos.le
    calc ‖(flowOfHCLM D τ - limitProjection D) y‖
        = ‖y‖ * (‖y‖⁻¹ * ‖(flowOfHCLM D τ - limitProjection D) y‖) :=
          (mul_inv_cancel_left₀ hypos.ne' _).symm
      _ ≤ ‖y‖ * r := h2
      _ = r * ‖y‖ := mul_comm _ _

/-- **There is no uniform rate on the unit ball without a gap.**  A function `r` with `r τ → 0`
bounding the deviation on the unit ball would drive the operator norm to zero, which
`not_tendsto_opNorm_flowOfHCLM_of_noGap` forbids.  This is the form the failure is usually wanted
in: not "the operator norm does not converge", but "no schedule of accuracy `r` works uniformly
in the vector". -/
theorem not_exists_uniform_rate_of_noGap (D : MulModel X ν Λ T)
    (hno : ∀ δ : ℝ, 0 < δ → ∃ s : Set X, MeasurableSet s ∧ ν s ≠ 0 ∧ ν s ≠ ∞ ∧
      ∀ x ∈ s, 0 < D.f x ∧ D.f x < δ) :
    ¬ ∃ r : ℝ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ (τ : ℝ), 0 ≤ τ → ∀ y : Hphys Λ, ‖y‖ ≤ 1 →
      ‖(flowOfHCLM D τ - limitProjection D) y‖ ≤ r τ := by
  rintro ⟨r, hr, hbound⟩
  apply not_tendsto_opNorm_flowOfHCLM_of_noGap D hno
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hr
    (Eventually.of_forall fun τ => norm_nonneg _) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
  have h0 : 0 ≤ r τ := by
    have hle := hbound τ hτ 0 (by simp)
    have hnn : (0 : ℝ) ≤ ‖(flowOfHCLM D τ - limitProjection D) 0‖ := norm_nonneg _
    linarith
  exact opNorm_le_of_unit_ball_bound D h0 fun y hy => hbound τ hτ y hy

/-! #### A density and a vector where the bound is attained

The barrier density `δ` on `[0, 1]` and zero elsewhere, tested on the class of its own indicator.
Nothing carries `0 < f < δ`, so the tail is zero, and on the support the multiplier is exactly
`e^{−τ δ}`: the two-scale bound is an equality for every `τ ≥ 0`.  The density does have a gap,
which is the point — the gapped rate is the truth when it applies, and the no-gap regime is
exactly where no rate can be uniform. -/

/-- The barrier density: `δ` on `[0, 1]`, zero elsewhere. -/
def barrierDensity (δ : ℝ) : ℝ → ℝ := Set.indicator (Set.Icc (0 : ℝ) 1) fun _ => δ

/-- It is measurable. -/
theorem measurable_barrierDensity (δ : ℝ) : Measurable (barrierDensity δ) :=
  measurable_const.indicator measurableSet_Icc

/-- It is nonnegative for `δ ≥ 0`. -/
theorem barrierDensity_nonneg {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ barrierDensity δ x := by
  filter_upwards with x
  unfold barrierDensity
  by_cases h : x ∈ Set.Icc (0 : ℝ) 1
  · rw [Set.indicator_of_mem h]
    simpa using hδ
  · rw [Set.indicator_of_notMem h]

/-- The indicator of `[0, 1]` is in `L²` of Lebesgue measure. -/
theorem memLp_barrierIndicator :
    MemLp (Set.indicator (Set.Icc (0 : ℝ) 1) fun _ => (1 : ℝ)) 2 (volume : Measure ℝ) := by
  refine memLp_indicator_const 2 measurableSet_Icc (1 : ℝ) (Or.inr ?_)
  simp [Real.volume_Icc]

/-- The test vector: the class of the indicator of `[0, 1]`. -/
noncomputable def barrierVector : Lp ℝ 2 (volume : Measure ℝ) :=
  memLp_barrierIndicator.toLp _

/-- It is the indicator function. -/
theorem barrierVector_coeFn : (barrierVector : ℝ → ℝ) =ᵐ[volume]
    Set.indicator (Set.Icc (0 : ℝ) 1) fun _ => (1 : ℝ) :=
  MemLp.coeFn_toLp _

/-- **The two-scale bound is attained by this density and vector**: equality for every `τ ≥ 0`. -/
theorem barrier_sharp {δ : ℝ} (hδ : 0 < δ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖expFlow (barrierDensity δ) (measurable_barrierDensity δ) (barrierDensity_nonneg hδ.le) τ
        barrierVector - mulL2 (kernelWeight (ν := volume) (measurable_barrierDensity δ))
          barrierVector‖
      = Real.exp (-(τ * δ)) * ‖barrierVector‖ := by
  refine norm_expFlow_sub_mulL2_kernel_eq_of_eq_on_support (ν := volume)
    (measurable_barrierDensity δ) (barrierDensity_nonneg hδ.le) hδ hτ barrierVector ?_
  filter_upwards [barrierVector_coeFn] with x hx hne
  unfold barrierDensity
  by_cases h : x ∈ Set.Icc (0 : ℝ) 1
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h] at hx
    exact absurd hx hne

/-- **The large-time limit is the orthogonal projection onto the kernel of the density.**  The
operator statement: the flow converges strongly to `limitProjection`, which is self-adjoint and
idempotent, is the identity exactly on the vectors whose chart lives on `{f = 0}`, is zero exactly
on those whose chart lives on `{f ≠ 0}`, and whose residual is orthogonal to its range.  So the
asymptotic state of any vector is its part supported where the Hamiltonian density vanishes, and
nothing else survives. -/
theorem limitProjection_isOrthogonalProjectionOntoDensity (D : MulModel X ν Λ T) :
    IsSelfAdjoint (limitProjection D) ∧
      (∀ y : Hphys Λ, limitProjection D (limitProjection D y) = limitProjection D y) ∧
      (∀ y : Hphys Λ, Tendsto (fun τ : ℝ => flowOfHCLM D τ y) atTop (𝓝 (limitProjection D y))) ∧
      (∀ y : Hphys Λ, limitProjection D y = y ↔
        ∀ᵐ x ∂ν, D.f x ≠ 0 → (D.U y : X → ℝ) x = 0) ∧
      (∀ y : Hphys Λ, limitProjection D y = 0 ↔
        ∀ᵐ x ∂ν, D.f x = 0 → (D.U y : X → ℝ) x = 0) ∧
      (∀ y z : Hphys Λ, limitProjection D y = 0 → limitProjection D z = z → ⟪y, z⟫ = 0) ∧
      Set.range (limitProjection D) = {y | ∀ᵐ x ∂ν, D.f x ≠ 0 → (D.U y : X → ℝ) x = 0} :=
  ⟨isSelfAdjoint_limitProjection D, limitProjection_idem D, tendsto_flowOfHCLM_atTop D,
    limitProjection_eq_iff D, limitProjection_eq_zero_iff D,
    fun _ _ hy hz => by
      rw [real_inner_comm _ _]
      exact inner_limitProjection_ker D hz hy,
    range_limitProjection D⟩

/-! ### The gap criterion: norm convergence `⟺` gap

`tendsto_opNorm_flowOfHCLM_sub_limitProjection_atTop` gives gap `⟹` convergence, and
`not_tendsto_opNorm_flowOfHCLM_of_noGap` the contrapositive of the converse, with the no-gap
hypothesis in the split form "every `δ > 0` is realised on a set of positive finite measure".  The
two together give the criterion, and only one measure-theoretic step is missing: the a.e. form of
no-gap has to produce such a set.  Under `σ`-finiteness a set of positive measure contains a set of
positive *finite* measure (`Measure.exists_subset_measure_lt_top`), so the split form follows — and
that is the only place where `σ`-finiteness is used.

**This is the general spectral fact, in the normal form the spectral theorem supplies.**  A
self-adjoint `H ≥ 0` on a Hilbert space is unitarily equivalent to multiplication by a nonnegative
measurable `f` on some `L²(X, ν)`; under that equivalence `e^{−τH}` becomes multiplication by
`e^{−τ f}`, the projection `P` onto `ker H` becomes multiplication by `1_{f = 0}`, and operator
norms are unchanged.  The spectrum of the multiplication operator is the essential range of `f`, so
the criterion below reads

  `‖e^{−τH} − P‖ → 0` as `τ → ∞`  `⟺`  `∃ δ > 0, σ(H) ∩ (0, δ) = ∅`,

which is the general statement: the semigroup converges to its limit *in norm* exactly when the
Hamiltonian has a gap above zero.  Without a gap the norm stays bounded away from zero at every
time, while the strong convergence (and the pointwise two-scale rate above) is unaffected.

What is formal here is the normal form, not the spectral theorem itself: the corpus's
`BookProof.ChapterSpectralMultiplication` proves the multiplication model for a *bounded* normal
operator with a cyclic vector; `ChapterUnboundedSpectralModel` supplies an unbounded route.
Neither result automatically constructs this `MulModel` for the interacting physical theory.
The criterion is stated for `MulModel`; applying it requires the particular multiplier
representation and the identification of its complete zero space.
-/

section GapCriterion

variable [SigmaFinite ν]

/-- **The gap criterion.**  The operator norm of `e^{−τH} − P` tends to zero if and only if the
density is bounded away from zero off its zero set.  The forward direction is the contrapositive of
`not_tendsto_opNorm_flowOfHCLM_of_noGap`, made available by extracting a set of positive finite
measure from `{0 < f < δ}` — which is where `σ`-finiteness enters. -/
theorem tendsto_opNorm_flowOfHCLM_sub_limitProjection_iff_gap (D : MulModel X ν Λ T) :
    Tendsto (fun τ : ℝ => ‖flowOfHCLM D τ - limitProjection D‖) atTop (𝓝 0) ↔
      ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ x ∂ν, D.f x ≠ 0 → δ ≤ D.f x := by
  refine ⟨?_, fun ⟨δ, hδ, hgap⟩ =>
    tendsto_opNorm_flowOfHCLM_sub_limitProjection_atTop D hδ hgap⟩
  intro hconv
  by_contra hnoGap
  refine not_tendsto_opNorm_flowOfHCLM_of_noGap D (fun δ hδ => ?_) hconv
  have hnot : ¬ ∀ᵐ x ∂ν, (D.f x ≠ 0 → δ ≤ D.f x) := fun hae => hnoGap ⟨δ, hδ, hae⟩
  have hne : ν {x : X | ¬(D.f x ≠ 0 → δ ≤ D.f x)} ≠ 0 :=
    fun h0 => hnot (MeasureTheory.ae_iff.mpr h0)
  have hset : {x : X | ¬(D.f x ≠ 0 → δ ≤ D.f x)} =ᵐ[ν]
      {x : X | 0 < D.f x ∧ D.f x < δ} := by
    filter_upwards [D.hpos] with x hx
    apply propext
    constructor
    · intro h
      have hne0 : D.f x ≠ 0 := fun h0 => h fun hp => absurd h0 hp
      have hlt : ¬ (δ ≤ D.f x) := fun hle => h fun _ => hle
      exact ⟨lt_of_le_of_ne hx (Ne.symm hne0), not_le.mp hlt⟩
    · intro h hq
      exact not_le.mpr h.2 (hq (ne_of_gt h.1))
  have hpos : ν {x : X | 0 < D.f x ∧ D.f x < δ} ≠ 0 := by
    rw [← MeasureTheory.measure_congr hset]
    exact hne
  have hmeas : MeasurableSet {x : X | 0 < D.f x ∧ D.f x < δ} :=
    (D.hf measurableSet_Ioi).inter (D.hf measurableSet_Iio)
  have hpos' : (0 : ℝ≥0∞) < ν {x : X | 0 < D.f x ∧ D.f x < δ} :=
    lt_of_le_of_ne (zero_le _) (Ne.symm hpos)
  obtain ⟨t, htm, hts, htpos, htfin⟩ :=
    Measure.exists_subset_measure_lt_top (μ := ν) (r := 0) hmeas hpos'
  exact ⟨t, htm, htpos.ne', htfin.ne, fun x hx => hts hx⟩

end GapCriterion

end

end BookProof.OSReconstruction
