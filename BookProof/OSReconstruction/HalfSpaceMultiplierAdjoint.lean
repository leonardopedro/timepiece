import Mathlib
import BookProof.OSReconstruction.HalfSpaceUnboundedExp
import BookProof.OSReconstruction.L2Multiplier

/-!
# Density and self-adjointness of the unbounded half-space Hamiltonian

Plan: `cftproof.md`, **E3**.  `HalfSpaceUnboundedExp` constructs the unbounded Hamiltonian
`H = −M_f` on its natural domain `M.domain = {z | f · e z ∈ L²(ν)}` and proves the generator
statement `d/dτ P(τ)z = −M_f z` there.  It leaves open the two facts a self-adjointness claim needs,
and this module proves both, for **every** measurable real `f` — no boundedness, no positivity, and
no use of the multiplier law, `HinvRight`, or the OS axioms:

* `dense_domain` — the domain is dense in `Hhalf Λ`;
* `isFormalAdjoint_hamiltonian` — symmetry (`⟪H x, y⟫ = ⟪x, H y⟫`);
* `hamiltonian_isSelfAdjoint` — `H† = H`.

## Density

On `L²(ν)` the domain is `{u | f · u ∈ L²}`.  The truncations `u_n = 1_{|f| ≤ n} · u` lie in it
(`f · u_n` is bounded by `n |u|`), and `u_n → u` in `L²`: the integrands `(u_n − u)²` are dominated
by `4 u² ∈ L¹` and converge to zero *everywhere*, because `f` is real-valued and therefore finite at
every point.  Dominated convergence gives `∫ (u_n − u)² → 0`, and `‖v‖² = ∫ v²` turns that into
`‖u_n − u‖ → 0`.  The isometric equivalence `e` carries the dense set back to `M.domain`.

## Self-adjointness

Symmetry is `∫ (f u) v = ∫ u (f v)`.  For the reverse inclusion take `v ∈ dom H†`, `w = H† v`, and
the comparison multiplier `φ = (1 + |f|)⁻¹`, which is bounded by one, strictly positive, and has
`f φ` bounded by one.  For every `u ∈ L²` the vector `g = e⁻¹ (φ · u)` lies in `dom H`, so the
adjoint relation `⟪w, g⟫ = ⟪v, H g⟫` reads, in `L²(ν)` coefficients,

`∫ u · (φ · (e w) + φ · (f · e v)) = 0`  for all `u ∈ L²`.

The bracket `ψ` is in `L²` (each summand is a bounded factor times an `L²` vector), so testing on
`u = ψ` gives `∫ ψ² = 0`, hence `ψ = 0` a.e.; as `φ > 0` a.e. this yields `f · e v = −(e w)` a.e.
Thus `f · e v ∈ L²`, i.e. `v ∈ dom H`, and `H v = e⁻¹ (−f · e v) = w`.  So `dom H† ⊆ dom H` with
matching values, while `H ⊆ H†` follows from symmetry and density.

## Boundary

What remains an input is that `Hhalf Λ` *is* `L²(ν)` at all: `HsMulModel.e` is datum, not derived
from `ν`.  The theorems below are conditional on that equivalence and on nothing else.  In the
corpus's other multiplier model (`MultiplierSelfAdjoint.MulModel`) the corresponding facts
(`hamiltonianMulModel_dense`, `hamiltonianMulModel_isSelfAdjoint`) are proved from a *dense-range*
isometry plus the multiplier law; here no flow is needed at all, because the equivalence already
supplies the carrier and `f` is real.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal RealInnerProductSpace

namespace BookProof.OSReconstruction

variable {X : Type*} [MeasurableSpace X]

/-- Scalar multiples of an `L²` class: `[c · g] = c • [g]`. -/
theorem memLp_toLp_const_mul {ν : Measure X} {g : X → ℝ} {c : ℝ} (hg : MemLp g 2 ν) :
    (hg.const_mul c).toLp (fun x => c * g x) = c • hg.toLp g := by
  refine Lp.ext ?_
  filter_upwards [MemLp.coeFn_toLp (hg.const_mul c), Lp.coeFn_smul c (hg.toLp g),
    MemLp.coeFn_toLp hg] with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]

variable {Λ : HalfSpaceState}

namespace HsMulModel

variable (M : HsMulModel Λ X)

/-! ## The norm-square identity -/

/-- `‖v‖² = ∫ v²` on real `L²(ν)`, in the form the density argument needs. -/
theorem norm_sq_eq_integral (v : Lp ℝ 2 M.ν) :
    ‖v‖ ^ 2 = ∫ x, (v : X → ℝ) x * (v : X → ℝ) x ∂M.ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [RCLike.inner_apply', RCLike.conj_to_real]

/-! ## The bounded comparison multiplier `φ = (1 + |f|)⁻¹` -/

/-- The comparison multiplier.  Bounded by one, strictly positive, and `f φ` bounded by one: those
three facts are all the adjoint argument uses. -/
def weight : X → ℝ := fun x => (1 + |M.f x|)⁻¹

theorem measurable_weight : Measurable M.weight :=
  (measurable_const.add M.hf.abs).inv

theorem weight_pos : ∀ᵐ x ∂M.ν, 0 < M.weight x := by
  filter_upwards with x
  exact inv_pos.mpr (by positivity)

theorem abs_weight_le_one : ∀ᵐ x ∂M.ν, |M.weight x| ≤ 1 := by
  filter_upwards with x
  have hpos : (0 : ℝ) < 1 + |M.f x| := by positivity
  rw [weight, abs_inv, abs_of_pos hpos, inv_le_one₀ hpos]
  linarith [abs_nonneg (M.f x)]

theorem abs_f_mul_weight_le_one : ∀ᵐ x ∂M.ν, |M.f x * M.weight x| ≤ 1 := by
  filter_upwards with x
  have hpos : (0 : ℝ) < 1 + |M.f x| := by positivity
  have hmul : |M.f x * M.weight x| = |M.f x| / (1 + |M.f x|) := by
    rw [weight, abs_mul, abs_inv, abs_of_pos hpos, ← div_eq_mul_inv]
  rw [hmul, div_le_one hpos]
  linarith [abs_nonneg (M.f x)]

/-- The comparison multiplier as an `L^∞` class, for `mulL2`. -/
theorem memLp_weight_top : MemLp M.weight (⊤ : ℝ≥0∞) M.ν :=
  memLp_top_of_bound M.measurable_weight.aestronglyMeasurable 1 M.abs_weight_le_one

/-- The comparison multiplier as an element of `L^∞(ν)`. -/
def weightLp : Lp ℝ (⊤ : ℝ≥0∞) M.ν := M.memLp_weight_top.toLp M.weight

theorem coeFn_weightLp : (M.weightLp : X → ℝ) =ᵐ[M.ν] M.weight :=
  MemLp.coeFn_toLp M.memLp_weight_top

theorem mulL2_weightLp_coeFn (u : Lp ℝ 2 M.ν) :
    (mulL2 M.weightLp u : X → ℝ) =ᵐ[M.ν] fun x => M.weight x * u x :=
  (mulL2_coeFn M.weightLp u).trans (by
    filter_upwards [M.coeFn_weightLp] with x hx
    rw [hx])

/-- `φ · u ∈ L²` for every `u ∈ L²`, since `φ` is bounded by one. -/
theorem memLp_weight_mul (u : Lp ℝ 2 M.ν) :
    MemLp (fun x => M.weight x * u x) 2 M.ν := by
  refine MemLp.of_le (p := 2) (Lp.memLp u)
    (M.measurable_weight.aestronglyMeasurable.mul
      (Lp.memLp u).aestronglyMeasurable) ?_
  filter_upwards [M.abs_weight_le_one] with x hx
  rw [Real.norm_eq_abs, abs_mul]
  calc |M.weight x| * |u x| ≤ 1 * |u x| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    _ = |u x| := one_mul _

/-- `f · (φ · u) ∈ L²`, since `f φ` is bounded by one.  This is what puts `e⁻¹ (φ · u)` in the
domain of the Hamiltonian at every `u`. -/
theorem memLp_f_mul_weight_mul (u : Lp ℝ 2 M.ν) :
    MemLp (fun x => M.f x * (M.weight x * u x)) 2 M.ν := by
  have hmeas : AEStronglyMeasurable (fun x => M.f x * (M.weight x * u x)) M.ν := by
    have h : AEStronglyMeasurable ((fun x => M.f x * M.weight x) * (u : X → ℝ)) M.ν :=
      (M.hf.mul M.measurable_weight).aestronglyMeasurable.mul
        (Lp.memLp u).aestronglyMeasurable
    convert h using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  refine MemLp.of_le (p := 2) (Lp.memLp u) hmeas ?_
  filter_upwards [M.abs_f_mul_weight_le_one] with x hx
  rw [Real.norm_eq_abs]
  calc |M.f x * (M.weight x * u x)| = |M.f x * M.weight x| * |u x| := by
        rw [← abs_mul]
        ring_nf
    _ ≤ 1 * |u x| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    _ = |u x| := one_mul _

/-! ## The domain is dense -/

/-- The truncation set `{|f| ≤ n}`. -/
def truncSet (n : ℕ) : Set X := {x | |M.f x| ≤ n}

theorem measurableSet_truncSet (n : ℕ) : MeasurableSet (M.truncSet n) :=
  measurableSet_le M.hf.abs measurable_const

/-- The truncation `1_{|f| ≤ n} · u`. -/
def truncFun (n : ℕ) (u : Lp ℝ 2 M.ν) : X → ℝ := (M.truncSet n).indicator (u : X → ℝ)

theorem truncFun_memLp (n : ℕ) (u : Lp ℝ 2 M.ν) : MemLp (M.truncFun n u) 2 M.ν :=
  MemLp.indicator (M.measurableSet_truncSet n) (Lp.memLp u)

/-- **The truncations lie in the domain**: `f · truncFun` is bounded by `n |u|`. -/
theorem truncFun_f_memLp (n : ℕ) (u : Lp ℝ 2 M.ν) :
    MemLp (fun x => M.f x * M.truncFun n u x) 2 M.ν := by
  refine MemLp.of_le (p := 2) ((Lp.memLp u).const_mul (n : ℝ)) ?_ ?_
  · exact M.hf.aestronglyMeasurable.mul (M.truncFun_memLp n u).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hx : x ∈ M.truncSet n
    · rw [truncFun, Set.indicator_of_mem hx, abs_mul]
      calc |M.f x| * |u x| ≤ (n : ℝ) * |u x| :=
            mul_le_mul_of_nonneg_right hx (abs_nonneg _)
        _ = |(n : ℝ) * u x| := by rw [abs_mul]; simp
    · rw [truncFun, Set.indicator_of_notMem hx, mul_zero, abs_zero]
      exact abs_nonneg _

/-- The truncations converge to `u` in `L²(ν)`. -/
theorem tendsto_truncFun_toLp (u : Lp ℝ 2 M.ν) :
    Tendsto (fun n : ℕ => (M.truncFun_memLp n u).toLp (M.truncFun n u)) atTop (𝓝 u) := by
  have hpt : ∀ x : X, Tendsto (fun n : ℕ => M.truncFun n u x) atTop (𝓝 ((u : X → ℝ) x)) := by
    intro x
    have hev : ∀ᶠ n : ℕ in atTop, x ∈ M.truncSet n :=
      (tendsto_atTop.1 tendsto_natCast_atTop_atTop) |M.f x|
    exact tendsto_const_nhds.congr' (hev.mono fun n hn => by
      simp only [truncFun, Set.indicator_of_mem hn])
  have hInt : Tendsto (fun n : ℕ => ∫ x, (M.truncFun n u x - (u : X → ℝ) x) ^ 2 ∂M.ν)
      atTop (𝓝 0) := by
    have hF : ∀ n : ℕ, AEStronglyMeasurable
        (fun x => (M.truncFun n u x - (u : X → ℝ) x) ^ 2) M.ν := by
      intro n
      have h := (M.truncFun_memLp n u).aestronglyMeasurable.sub
        (Lp.memLp u).aestronglyMeasurable
      simpa [pow_two] using h.mul h
    have hbound : ∀ n : ℕ, ∀ᵐ x ∂M.ν,
        ‖(M.truncFun n u x - (u : X → ℝ) x) ^ 2‖ ≤ 4 * (u : X → ℝ) x ^ 2 := by
      intro n
      filter_upwards with x
      have hle : |M.truncFun n u x| ≤ |(u : X → ℝ) x| := by
        by_cases hx : x ∈ M.truncSet n
        · rw [truncFun, Set.indicator_of_mem hx]
        · rw [truncFun, Set.indicator_of_notMem hx]
          simp only [abs_zero]
          exact abs_nonneg _
      have h2 : |M.truncFun n u x - (u : X → ℝ) x| ≤ 2 * |(u : X → ℝ) x| := by
        calc |M.truncFun n u x - (u : X → ℝ) x|
            ≤ |M.truncFun n u x| + |(u : X → ℝ) x| := abs_sub _ _
          _ ≤ |(u : X → ℝ) x| + |(u : X → ℝ) x| := by linarith
          _ = 2 * |(u : X → ℝ) x| := by ring
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc (M.truncFun n u x - (u : X → ℝ) x) ^ 2
          = |M.truncFun n u x - (u : X → ℝ) x| ^ 2 := by rw [sq_abs]
        _ ≤ (2 * |(u : X → ℝ) x|) ^ 2 := by
              nlinarith [h2, abs_nonneg (M.truncFun n u x - (u : X → ℝ) x),
                abs_nonneg ((u : X → ℝ) x)]
        _ = 4 * (u : X → ℝ) x ^ 2 := by rw [mul_pow, sq_abs]; ring
    have hlim : ∀ᵐ x ∂M.ν, Tendsto
        (fun n : ℕ => (M.truncFun n u x - (u : X → ℝ) x) ^ 2) atTop (𝓝 ((fun _ => 0) x)) := by
      refine Eventually.of_forall fun x => ?_
      have h1 : Tendsto (fun n : ℕ => M.truncFun n u x - (u : X → ℝ) x) atTop
          (𝓝 ((u : X → ℝ) x - (u : X → ℝ) x)) :=
        (hpt x).sub tendsto_const_nhds
      have h2 : Tendsto (fun n : ℕ => (M.truncFun n u x - (u : X → ℝ) x) ^ 2)
          atTop (𝓝 0) := by
        simpa using h1.pow 2
      simpa using h2
    have h := tendsto_integral_of_dominated_convergence (μ := M.ν)
      (F := fun n x => (M.truncFun n u x - (u : X → ℝ) x) ^ 2) (f := fun _ => 0)
      (fun x => 4 * (u : X → ℝ) x ^ 2) hF ((Lp.memLp u).integrable_sq.const_mul 4) hbound hlim
    simpa using h
  have hsq : Tendsto
      (fun n : ℕ => ‖(M.truncFun_memLp n u).toLp (M.truncFun n u) - u‖ ^ 2) atTop (𝓝 0) := by
    refine hInt.congr' (Eventually.of_forall fun n => ?_)
    dsimp only
    rw [M.norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (M.truncFun_memLp n u),
      Lp.coeFn_sub ((M.truncFun_memLp n u).toLp (M.truncFun n u)) u] with x h1 h2
    rw [h2, Pi.sub_apply, h1]
    ring
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (‖(M.truncFun_memLp n u).toLp
      (M.truncFun n u) - u‖ ^ 2)) atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa [Function.comp_def] using h
  have hnorm : Tendsto
      (fun n : ℕ => ‖(M.truncFun_memLp n u).toLp (M.truncFun n u) - u‖) atTop (𝓝 0) :=
    hsqrt.congr' (Eventually.of_forall fun n => Real.sqrt_sq (norm_nonneg _))
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr hnorm

/-- **The domain of the multiplier is dense in `L²(ν)`.** -/
theorem dense_memLp_mul_l2 :
    Dense {u : Lp ℝ 2 M.ν | MemLp (fun x => M.f x * u x) 2 M.ν} := by
  rw [Metric.dense_iff]
  intro u r hr
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (M.tendsto_truncFun_toLp u)) r hr
  set v : Lp ℝ 2 M.ν := (M.truncFun_memLp N u).toLp (M.truncFun N u)
  have hmem : MemLp (fun x => M.f x * (v : X → ℝ) x) 2 M.ν := by
    refine (M.truncFun_f_memLp N u).ae_eq ?_
    filter_upwards [MemLp.coeFn_toLp (M.truncFun_memLp N u)] with x hx
    rw [hx]
  exact ⟨v, ⟨Metric.mem_ball.mpr (hN N le_rfl), hmem⟩⟩

/-- **The domain of the unbounded Hamiltonian is dense in `Hhalf Λ`**, for any measurable `f`.  The
isometric equivalence `e` carries the dense set of truncations back to the half-space carrier. -/
theorem dense_domain : Dense (M.domain : Set (Hhalf Λ)) := by
  have hS := M.dense_memLp_mul_l2
  have himg : M.e.symm '' {u : Lp ℝ 2 M.ν | MemLp (fun x => M.f x * u x) 2 M.ν}
      = (M.domain : Set (Hhalf Λ)) := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      change MemLp (fun x => M.f x * (M.e (M.e.symm u) : X → ℝ) x) 2 M.ν
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact hu
    · intro hz
      exact ⟨M.e z, hz, LinearIsometryEquiv.symm_apply_apply M.e z⟩
  have hd : Dense (M.e.symm '' {u : Lp ℝ 2 M.ν | MemLp (fun x => M.f x * u x) 2 M.ν}) := by
    rw [Metric.dense_iff] at hS ⊢
    intro z r hr
    obtain ⟨u, hu⟩ := hS (M.e z) r hr
    obtain ⟨hu_ball, hu_mem⟩ := hu
    have hdist : dist u (M.e z) < r := Metric.mem_ball.mp hu_ball
    refine ⟨M.e.symm u, Metric.mem_ball.mpr ?_, ⟨u, hu_mem, rfl⟩⟩
    have hz : M.e.symm u - z = M.e.symm (u - M.e z) := by
      rw [map_sub, LinearIsometryEquiv.symm_apply_apply]
    rw [dist_eq_norm, hz, LinearIsometryEquiv.norm_map, ← dist_eq_norm]
    exact hdist
  rw [← himg]
  exact hd

/-! ## The Hamiltonian as a partially defined operator -/

/-- The multiplication part: `z ↦ [f · e z]` in `L²(ν)`. -/
def mulImageMap : M.domain →ₗ[ℝ] Lp ℝ 2 M.ν where
  toFun z := z.2.toLp (fun x => M.f x * (M.e (z : Hhalf Λ) : X → ℝ) x)
  map_add' z w := by
    have hcoe : ((M.e ((z + w : M.domain) : Hhalf Λ) : Lp ℝ 2 M.ν) : X → ℝ) =ᵐ[M.ν]
        fun x => (M.e (z : Hhalf Λ) : X → ℝ) x + (M.e (w : Hhalf Λ) : X → ℝ) x := by
      rw [Submodule.coe_add, map_add]
      exact Lp.coeFn_add _ _
    have hfun : (fun x => M.f x * (M.e ((z + w : M.domain) : Hhalf Λ) : X → ℝ) x) =ᵐ[M.ν]
        fun x => M.f x * (M.e (z : Hhalf Λ) : X → ℝ) x
          + M.f x * (M.e (w : Hhalf Λ) : X → ℝ) x := by
      filter_upwards [hcoe] with x hx
      rw [hx]
      ring
    calc (z + w).2.toLp _
        = (z.2.add w.2).toLp (fun x => M.f x * (M.e (z : Hhalf Λ) : X → ℝ) x
            + M.f x * (M.e (w : Hhalf Λ) : X → ℝ) x) :=
          MemLp.toLp_congr _ _ hfun
      _ = z.2.toLp _ + w.2.toLp _ := MemLp.toLp_add z.2 w.2
  map_smul' c z := by
    have hcoe : ((M.e ((c • z : M.domain) : Hhalf Λ) : Lp ℝ 2 M.ν) : X → ℝ) =ᵐ[M.ν]
        fun x => c * (M.e (z : Hhalf Λ) : X → ℝ) x := by
      rw [Submodule.coe_smul, map_smul]
      simpa [Pi.smul_apply, smul_eq_mul] using Lp.coeFn_smul c (M.e (z : Hhalf Λ))
    have hfun : (fun x => M.f x * (M.e ((c • z : M.domain) : Hhalf Λ) : X → ℝ) x) =ᵐ[M.ν]
        fun x => c * (M.f x * (M.e (z : Hhalf Λ) : X → ℝ) x) := by
      filter_upwards [hcoe] with x hx
      rw [hx]
      ring
    calc (c • z).2.toLp _
        = (z.2.const_mul c).toLp
            (fun x => c * (M.f x * (M.e (z : Hhalf Λ) : X → ℝ) x)) :=
          MemLp.toLp_congr _ _ hfun
      _ = c • z.2.toLp _ := memLp_toLp_const_mul z.2

/-- **The unbounded Hamiltonian as a partially defined operator**: multiplication by `−f` on the
natural domain.  Its domain is `M.domain`. -/
def hamiltonian : Hhalf Λ →ₗ.[ℝ] Hhalf Λ where
  domain := M.domain
  toFun := (M.e.symm.toLinearEquiv : Lp ℝ 2 M.ν →ₗ[ℝ] Hhalf Λ).comp (-M.mulImageMap)

/-- **`e` turns the Hamiltonian into multiplication by `−f`.** -/
theorem e_hamiltonian (z : M.domain) :
    M.e (M.hamiltonian z)
      = -(z.2.toLp (fun x => M.f x * (M.e (z : Hhalf Λ) : X → ℝ) x)) := by
  change M.e (M.e.symm (-(M.mulImageMap z))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-! ## Symmetry -/

/-- The matrix element of `H` against an arbitrary vector, as an integral in `L²` coefficients. -/
theorem inner_hamiltonian_left (z : M.domain) (z' : Hhalf Λ) :
    ⟪M.hamiltonian z, z'⟫
      = -∫ t, (M.f t * (M.e (z : Hhalf Λ) : X → ℝ) t) * (M.e z' : X → ℝ) t ∂M.ν := by
  rw [← LinearIsometryEquiv.inner_map_map M.e (M.hamiltonian z) z', M.e_hamiltonian,
    inner_neg_left, L2.inner_def]
  refine congrArg Neg.neg ?_
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp z.2] with t ht
  rw [ht, RCLike.inner_apply', RCLike.conj_to_real]

/-- The same matrix element with the Hamiltonian on the right. -/
theorem inner_hamiltonian_right (z : Hhalf Λ) (z' : M.domain) :
    ⟪z, M.hamiltonian z'⟫
      = -∫ t, (M.e z : X → ℝ) t * (M.f t * (M.e (z' : Hhalf Λ) : X → ℝ) t) ∂M.ν := by
  rw [← LinearIsometryEquiv.inner_map_map M.e z (M.hamiltonian z'), M.e_hamiltonian,
    inner_neg_right, L2.inner_def]
  refine congrArg Neg.neg ?_
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp z'.2] with t ht
  rw [ht, RCLike.inner_apply', RCLike.conj_to_real]

/-- **The Hamiltonian is symmetric**: `⟪H x, y⟫ = ⟪x, H y⟫`.  Only reality of `f` is used. -/
theorem isFormalAdjoint_hamiltonian : M.hamiltonian.IsFormalAdjoint M.hamiltonian := by
  intro x y
  rw [M.inner_hamiltonian_left x y, M.inner_hamiltonian_right (x : Hhalf Λ) y]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun t => by ring)

/-! ## The adjoint is no larger -/

/-- **The hard half of self-adjointness**: `dom H† ⊆ dom H`.  The comparison multiplier turns the
adjoint relation into `∫ u ψ = 0` for all `u ∈ L²`, which forces `f · e v = −(e (H† v))`. -/
theorem mem_domain_of_mem_adjoint_domain {v : Hhalf Λ}
    (hv : v ∈ M.hamiltonian.adjoint.domain) : v ∈ M.domain := by
  set w : Hhalf Λ := M.hamiltonian.adjoint ⟨v, hv⟩ with hw
  set psi : X → ℝ := fun x => M.weight x * (M.e w : X → ℝ) x
    + M.weight x * (M.f x * (M.e v : X → ℝ) x) with hpsi
  have hAd := LinearPMap.adjoint_isFormalAdjoint (T := M.hamiltonian) M.dense_domain
  -- the integral identity
  have hkey : ∀ u : Lp ℝ 2 M.ν, ∫ x, u x * psi x ∂M.ν = 0 := by
    intro u
    have hcoe : ((mulL2 M.weightLp u : Lp ℝ 2 M.ν) : X → ℝ) =ᵐ[M.ν]
        fun x => M.weight x * u x := M.mulL2_weightLp_coeFn u
    have hg : (M.e.symm (mulL2 M.weightLp u)) ∈ M.domain := by
      change MemLp (fun x => M.f x
        * (M.e (M.e.symm (mulL2 M.weightLp u)) : X → ℝ) x) 2 M.ν
      rw [LinearIsometryEquiv.apply_symm_apply]
      refine (M.memLp_f_mul_weight_mul u).ae_eq ?_
      filter_upwards [hcoe] with x hx
      rw [hx]
    have hrel : ⟪w, M.e.symm (mulL2 M.weightLp u)⟫
        = ⟪v, M.hamiltonian ⟨M.e.symm (mulL2 M.weightLp u), hg⟩⟫ :=
      hAd ⟨v, hv⟩ ⟨_, hg⟩
    have hleft : ⟪w, M.e.symm (mulL2 M.weightLp u)⟫
        = ∫ x, u x * (M.weight x * (M.e w : X → ℝ) x) ∂M.ν := by
      rw [← LinearIsometryEquiv.inner_map_map M.e w (M.e.symm (mulL2 M.weightLp u)),
        LinearIsometryEquiv.apply_symm_apply, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hcoe] with x h2
      rw [h2, RCLike.inner_apply', RCLike.conj_to_real]
      ring
    have hright : ⟪v, M.hamiltonian ⟨M.e.symm (mulL2 M.weightLp u), hg⟩⟫
        = -∫ x, u x * (M.weight x * (M.f x * (M.e v : X → ℝ) x)) ∂M.ν := by
      have hev : M.e (↑(⟨M.e.symm (mulL2 M.weightLp u), hg⟩ : M.domain) : Hhalf Λ)
          = mulL2 M.weightLp u := by
        change M.e (M.e.symm (mulL2 M.weightLp u)) = _
        rw [LinearIsometryEquiv.apply_symm_apply]
      rw [M.inner_hamiltonian_right v ⟨_, hg⟩, hev]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hcoe] with x hx
      rw [hx]
      ring
    rw [hleft, hright] at hrel
    -- combine the two integrals
    have hfirst : Integrable (fun x => u x * (M.weight x * (M.e w : X → ℝ) x)) M.ν :=
      (Lp.memLp u).integrable_mul (M.memLp_weight_mul (M.e w))
    have hsecond : Integrable (fun x => u x * (M.weight x * (M.f x * (M.e v : X → ℝ) x)))
        M.ν := by
      have hm : MemLp (fun x => M.weight x * (M.f x * (M.e v : X → ℝ) x)) 2 M.ν :=
        (M.memLp_f_mul_weight_mul (M.e v)).ae_eq
          (Eventually.of_forall fun x => by ring)
      exact (Lp.memLp u).integrable_mul hm
    have hadd : ∫ x, u x * psi x ∂M.ν
        = ∫ x, u x * (M.weight x * (M.e w : X → ℝ) x) ∂M.ν
          + ∫ x, u x * (M.weight x * (M.f x * (M.e v : X → ℝ) x)) ∂M.ν := by
      rw [← integral_add hfirst hsecond]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      change u x * (M.weight x * (M.e w : X → ℝ) x
          + M.weight x * (M.f x * (M.e v : X → ℝ) x)) = _
      ring
    rw [hadd, hrel]
    ring
  -- `ψ ∈ L²`
  have hpsi_memLp : MemLp psi 2 M.ν := by
    have h1 : MemLp (fun x => M.weight x * (M.e w : X → ℝ) x) 2 M.ν :=
      M.memLp_weight_mul (M.e w)
    have h2 : MemLp (fun x => M.weight x * (M.f x * (M.e v : X → ℝ) x)) 2 M.ν := by
      have hb : ∀ᵐ x ∂M.ν, |M.f x * M.weight x| ≤ 1 := M.abs_f_mul_weight_le_one
      refine MemLp.of_le (p := 2) (Lp.memLp (M.e v)) ?_ ?_
      · have h : AEStronglyMeasurable
            ((fun x => M.weight x * M.f x) * (M.e v : X → ℝ)) M.ν :=
          (M.measurable_weight.mul M.hf).aestronglyMeasurable.mul
            (Lp.memLp (M.e v)).aestronglyMeasurable
        convert h using 1
        funext x
        simp only [Pi.mul_apply]
        ring
      · filter_upwards [hb] with x hx
        rw [Real.norm_eq_abs]
        calc |M.weight x * (M.f x * (M.e v : X → ℝ) x)|
            = |M.f x * M.weight x| * |(M.e v : X → ℝ) x| := by
              rw [← abs_mul]
              ring_nf
          _ ≤ 1 * |(M.e v : X → ℝ) x| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
          _ = |(M.e v : X → ℝ) x| := one_mul _
    have hsum : psi = fun x => M.weight x * (M.e w : X → ℝ) x
        + M.weight x * (M.f x * (M.e v : X → ℝ) x) := rfl
    rw [hsum]
    exact h1.add h2
  -- `∫ ψ² = 0`, so `ψ = 0`
  have hpsi_zero : psi =ᵐ[M.ν] 0 := by
    have hsq : ∫ x, psi x * psi x ∂M.ν = 0 := by
      have h := hkey (hpsi_memLp.toLp psi)
      rw [← h]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp hpsi_memLp] with x hx
      rw [hx]
    have hint : Integrable (fun x => psi x * psi x) M.ν :=
      hpsi_memLp.integrable_sq.congr (Eventually.of_forall fun x => by ring)
    have hzero := (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (psi x)) hint).mp hsq
    filter_upwards [hzero] with x hx
    exact mul_self_eq_zero.mp hx
  -- so `f · e v = −(e w)` a.e.
  have hfv : (fun x => M.f x * (M.e v : X → ℝ) x) =ᵐ[M.ν]
      fun x => -((M.e w : X → ℝ) x) := by
    filter_upwards [hpsi_zero, M.weight_pos] with x hx hw
    have hx' : M.weight x * (M.e w : X → ℝ) x
        + M.weight x * (M.f x * (M.e v : X → ℝ) x) = 0 := hx
    have hpos : M.weight x ≠ 0 := ne_of_gt hw
    have hfac : M.weight x * ((M.e w : X → ℝ) x + M.f x * (M.e v : X → ℝ) x) = 0 := by
      linear_combination hx'
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h hpos
    · linarith
  change MemLp (fun x => M.f x * (M.e v : X → ℝ) x) 2 M.ν
  exact (Lp.memLp (M.e w)).neg.ae_eq hfv.symm

/-- **`H† v = H v`** when `v` is in the domain: the adjoint value is characterised by symmetry and
the density of the domain. -/
theorem hamiltonian_adjoint_apply_eq {v : Hhalf Λ} (hv : v ∈ M.hamiltonian.adjoint.domain)
    (hv' : v ∈ M.domain) :
    M.hamiltonian.adjoint ⟨v, hv⟩ = M.hamiltonian ⟨v, hv'⟩ := by
  refine LinearPMap.adjoint_apply_eq (T := M.hamiltonian) M.dense_domain ⟨v, hv⟩ ?_
  intro x
  rw [M.inner_hamiltonian_left ⟨v, hv'⟩ (x : Hhalf Λ), M.inner_hamiltonian_right v x]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun t => by ring)

/-- **The adjoint is contained in the operator**: `H† ≤ H`. -/
theorem le_adjoint_hamiltonian : M.hamiltonian.adjoint ≤ M.hamiltonian := by
  constructor
  · intro v hv
    exact M.mem_domain_of_mem_adjoint_domain hv
  · intro x y hxy
    have hx : (x : Hhalf Λ) ∈ M.domain := M.mem_domain_of_mem_adjoint_domain x.2
    have hval := M.hamiltonian_adjoint_apply_eq x.2 hx
    have hy : (⟨(x : Hhalf Λ), hx⟩ : M.domain) = y := Subtype.ext hxy
    rw [hval, hy]

/-- **The unbounded half-space Hamiltonian is self-adjoint** on its natural domain: symmetry plus
density gives `H ≤ H†`, and the truncation argument gives `H† ≤ H`. -/
theorem hamiltonian_isSelfAdjoint : IsSelfAdjoint M.hamiltonian := by
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm M.le_adjoint_hamiltonian
    (LinearPMap.IsFormalAdjoint.le_adjoint (T := M.hamiltonian) M.dense_domain
      M.isFormalAdjoint_hamiltonian)

end HsMulModel

end BookProof.OSReconstruction
