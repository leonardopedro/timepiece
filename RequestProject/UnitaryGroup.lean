module

public import RequestProject.HeatSemigroup

/-!
# The unitary group `exp(itH)` of an unbounded self-adjoint Hamiltonian

`H` is a (possibly unbounded) self-adjoint operator bounded below, given through its bounded
resolvent `R = (H - σ)⁻¹` (`IsSemibounded H m σ R`). Since `H - σ = R⁻¹`, the unitary group
should be `exp(itσ) · exp(it R⁻¹)`. The function `r ↦ exp(it/r)` is not continuous at `r = 0`,
which lies in the spectrum of `R` exactly when `H` is unbounded, so the continuous functional
calculus of `R` does not give `exp(itR⁻¹)` directly. The function `r ↦ r · exp(it/r)` *is*
continuous, and the unitary group is the unique contraction `U t` with
`U t (R y) = (r ↦ r e^{it/r})(R) y`. It is obtained as the strong limit of the bounded functions
`exp(it / max(r, 1/(n+1)))` of `R`.

Main results:
* `unitaryGroup σ R t` — the operator `exp(itH)`;
* `unitaryGroup_zero`, `unitaryGroup_add`, `norm_unitaryGroup_apply` — group law and isometry;
* `unitaryGroup_isUnitaryGroupOf` — for `x ∈ D(H)`, `t ↦ exp(itH) x` stays in `D(H)` and solves
  the Schrödinger equation `dψ/dt = iHψ`;
* `IsSchrodingerSolution.unique`, `IsUnitaryGroupOf.unique` — solutions of the Schrödinger
  equation of a symmetric operator are unique, so `exp(itH)` depends only on `H`.
-/

@[expose] public section

open scoped InnerProductSpace

noncomputable section

namespace CftCheck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ### Complex-valued functions of a bounded self-adjoint operator -/

/-- `ccfc g R = g(R)` for a complex-valued function `g` of a real variable. -/
def ccfc (g : ℝ → ℂ) (R : E →L[ℂ] E) : E →L[ℂ] E := cfc (fun z : ℂ => g z.re) R

variable {H : E →ₗ.[ℂ] E} {m σ : ℝ} {R : E →L[ℂ] E}

theorem re_mem_of_mem_spectrum (hR : IsSelfAdjoint R) {z : ℂ} (hz : z ∈ spectrum ℂ R) :
    z.re ∈ spectrum ℝ R := by
  have h := hR.mem_spectrum_eq_re hz
  rw [h] at hz
  exact (hR.coe_mem_spectrum_complex).mp hz

theorem ccfc_mul (g h : ℝ → ℂ) (hg : Continuous g) (hh : Continuous h) :
    ccfc (fun r => g r * h r) R = ccfc g R * ccfc h R := by
  unfold ccfc
  exact cfc_mul (fun z : ℂ => g z.re) (fun z : ℂ => h z.re) R
    (hg.comp Complex.continuous_re).continuousOn (hh.comp Complex.continuous_re).continuousOn

theorem ccfc_sub (g h : ℝ → ℂ) (hg : Continuous g) (hh : Continuous h) :
    ccfc (fun r => g r - h r) R = ccfc g R - ccfc h R := by
  unfold ccfc
  exact cfc_sub (fun z : ℂ => g z.re) (fun z : ℂ => h z.re) R
    (hg.comp Complex.continuous_re).continuousOn (hh.comp Complex.continuous_re).continuousOn

theorem ccfc_smul (c : ℂ) (g : ℝ → ℂ) (hg : Continuous g) :
    ccfc (fun r => c * g r) R = c • ccfc g R := by
  unfold ccfc
  exact cfc_const_mul c (fun z : ℂ => g z.re) R (hg.comp Complex.continuous_re).continuousOn

theorem ccfc_id (hR : IsSelfAdjoint R) : ccfc (fun r => (r : ℂ)) R = R := by
  unfold ccfc
  rw [cfc_congr (g := fun z : ℂ => z) (fun z hz => (hR.mem_spectrum_eq_re hz).symm)]
  exact cfc_id' ℂ R

theorem ccfc_one (hR : IsSelfAdjoint R) : ccfc (fun _ => (1 : ℂ)) R = 1 := by
  unfold ccfc
  exact cfc_const_one ℂ R

theorem ccfc_commute {O : E →L[ℂ] E} (hR : IsSelfAdjoint R) (hO : Commute R O) (g : ℝ → ℂ) :
    Commute (ccfc g R) O := by
  unfold ccfc
  exact Commute.cfc hO (by rw [hR.star_eq]; exact hO) _

theorem norm_ccfc_le (hH : IsSemibounded H m σ R) {g : ℝ → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hg : ∀ r, 0 ≤ r → r ≤ (m - σ)⁻¹ → ‖g r‖ ≤ c) : ‖ccfc g R‖ ≤ c := by
  unfold ccfc
  refine norm_cfc_le hc (fun z hz => ?_)
  have h := hH.spectrum_R_subset (re_mem_of_mem_spectrum hH.isSelfAdjoint_R hz)
  exact hg _ h.1 h.2

/-! ### The functions `r ↦ r e^{it/r}` and `r ↦ e^{it/max(r, 1/(n+1))}` -/

/-- `schrKer t r = r · exp(it/r)` (and `0` at `r = 0`). Applied to `R = (H - σ)⁻¹` it gives
`exp(it(H - σ)) R`. It is continuous, unlike `r ↦ exp(it/r)`. -/
def schrKer (t r : ℝ) : ℂ := (r : ℂ) * Complex.exp (Complex.I * ((t / r : ℝ) : ℂ))

/-- Continuous unimodular approximants of `r ↦ exp(it/r)`. -/
def schrApprox (n : ℕ) (t r : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((t / max r ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ))

theorem norm_schrKer (t r : ℝ) : ‖schrKer t r‖ = |r| := by
  rw [schrKer, norm_mul, Complex.norm_exp_I_mul_ofReal, Complex.norm_real, Real.norm_eq_abs,
    mul_one]

theorem norm_schrApprox (n : ℕ) (t r : ℝ) : ‖schrApprox n t r‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _

theorem continuous_schrApprox (n : ℕ) (t : ℝ) : Continuous (schrApprox n t) := by
  unfold schrApprox
  have hpos : ∀ r : ℝ, max r ((n : ℝ) + 1)⁻¹ ≠ 0 := fun r =>
    (lt_of_lt_of_le (by positivity) (le_max_right _ _)).ne'
  have : Continuous (fun r : ℝ => t / max r ((n : ℝ) + 1)⁻¹) :=
    continuous_const.div (continuous_id.max continuous_const) hpos
  fun_prop

theorem continuous_schrKer (t : ℝ) : Continuous (schrKer t) := by
  rw [continuous_iff_continuousAt]
  intro r0
  rcases eq_or_ne r0 0 with rfl | h0
  · have h00 : schrKer t 0 = 0 := by simp [schrKer]
    rw [ContinuousAt, h00, tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_schrKer]
    have := (continuous_abs (G := ℝ)).tendsto 0
    simpa using this
  · unfold schrKer
    have : ContinuousAt (fun r : ℝ => t / r) r0 := continuousAt_const.div continuousAt_id h0
    have h2 : ContinuousAt (fun r : ℝ => ((t / r : ℝ) : ℂ)) r0 :=
      Complex.continuous_ofReal.continuousAt.comp this
    exact (Complex.continuous_ofReal.continuousAt).mul
      ((continuousAt_const.mul h2).cexp)

theorem schrKer_zero (r : ℝ) : schrKer 0 r = r := by simp [schrKer]

theorem schrKer_mul (s t r : ℝ) : schrKer s r * schrKer t r = schrKer (s + t) r * r := by
  unfold schrKer
  have : Complex.exp (Complex.I * ((s / r : ℝ) : ℂ)) * Complex.exp (Complex.I * ((t / r : ℝ) : ℂ))
      = Complex.exp (Complex.I * (((s + t) / r : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  calc (r : ℂ) * Complex.exp (Complex.I * ((s / r : ℝ) : ℂ)) *
        ((r : ℂ) * Complex.exp (Complex.I * ((t / r : ℝ) : ℂ)))
      = (r : ℂ) * (Complex.exp (Complex.I * ((s / r : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ((t / r : ℝ) : ℂ))) * r := by ring
    _ = _ := by rw [this]

theorem schrApprox_mul_sub (n : ℕ) (t : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ‖schrApprox n t r * r - schrKer t r‖ ≤ 2 * ((n : ℝ) + 1)⁻¹ := by
  rcases le_or_gt ((n : ℝ) + 1)⁻¹ r with h | h
  · have : schrApprox n t r * r = schrKer t r := by
      simp only [schrApprox, schrKer, max_eq_left h]; ring
    rw [this, sub_self, norm_zero]; positivity
  · calc ‖schrApprox n t r * r - schrKer t r‖
        ≤ ‖schrApprox n t r * r‖ + ‖schrKer t r‖ := norm_sub_le _ _
      _ = r + r := by
        rw [norm_mul, norm_schrApprox, norm_schrKer, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hr, one_mul]
      _ ≤ 2 * ((n : ℝ) + 1)⁻¹ := by linarith

/-! ### Construction of `exp(it R⁻¹)` as a strong limit -/

/-- Uniformly bounded operators that converge on the dense range of `R` converge everywhere. -/
theorem exists_tendsto_of_dense (K : ℕ → E →L[ℂ] E) {C : ℝ} (hK : ∀ n, ‖K n‖ ≤ C)
    (hR : DenseRange R) (h : ∀ y, ∃ l, Filter.Tendsto (fun n => K n (R y)) Filter.atTop (nhds l))
    (x : E) : ∃ l, Filter.Tendsto (fun n => K n x) Filter.atTop (nhds l) := by
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hC1 : 0 < |C| + 1 := by positivity
  obtain ⟨y, hy⟩ : ∃ y, dist x (R y) < ε / 4 / (|C| + 1) :=
    hR.exists_dist_lt x (by positivity)
  obtain ⟨l, hl⟩ := h y
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hl.cauchySeq (ε / 2) (by positivity)
  refine ⟨N, fun a ha b hb => ?_⟩
  have hb' : ∀ n, ‖K n x - K n (R y)‖ ≤ ε / 4 := by
    intro n
    rw [← map_sub]
    calc ‖K n (x - R y)‖ ≤ ‖K n‖ * ‖x - R y‖ := (K n).le_opNorm _
      _ ≤ (|C| + 1) * (ε / 4 / (|C| + 1)) := by
          rw [dist_eq_norm] at hy
          exact mul_le_mul ((hK n).trans ((le_abs_self C).trans (by linarith))) hy.le
            (norm_nonneg _) hC1.le
      _ = ε / 4 := by field_simp
  have h1 := hN a ha b hb
  rw [dist_eq_norm] at h1 ⊢
  calc ‖K a x - K b x‖ = ‖(K a x - K a (R y)) + (K a (R y) - K b (R y))
        - (K b x - K b (R y))‖ := by congr 1; abel
    _ ≤ ‖K a x - K a (R y)‖ + ‖K a (R y) - K b (R y)‖ + ‖K b x - K b (R y)‖ :=
        norm_sub_le_of_le (norm_add_le _ _) le_rfl
    _ < ε / 4 + ε / 2 + ε / 4 := by
        have := hb' a; have := hb' b; linarith
    _ = ε := by ring

/-- The approximants `exp(it / max(R, 1/(n+1)))`. -/
def schrOp (n : ℕ) (t : ℝ) (R : E →L[ℂ] E) : E →L[ℂ] E := ccfc (schrApprox n t) R

open Classical in
/-- `U0 R t = exp(it R⁻¹)`: the strong limit of `schrOp n t R` (and `0` if the limit does not
exist, which does not happen when `R` is the resolvent of a semibounded operator). -/
def U0 (R : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  if h : ∀ x, ∃ l, Filter.Tendsto (fun n => schrOp n t R x) Filter.atTop (nhds l) then
    continuousLinearMapOfTendsto (fun n => schrOp n t R) (f := fun x => (h x).choose)
      (tendsto_pi_nhds.2 fun x => (h x).choose_spec)
  else 0

theorem norm_schrOp_le (hH : IsSemibounded H m σ R) (n : ℕ) (t : ℝ) : ‖schrOp n t R‖ ≤ 1 :=
  norm_ccfc_le hH zero_le_one (fun r _ _ => (norm_schrApprox n t r).le)

theorem schrOp_R (hH : IsSemibounded H m σ R) (n : ℕ) (t : ℝ) (y : E) :
    schrOp n t R (R y) = ccfc (fun r => schrApprox n t r * r) R y := by
  rw [ccfc_mul _ _ (continuous_schrApprox n t) Complex.continuous_ofReal,
    ccfc_id hH.isSelfAdjoint_R]
  rfl

theorem tendsto_schrOp_R (hH : IsSemibounded H m σ R) (t : ℝ) (y : E) :
    Filter.Tendsto (fun n => schrOp n t R (R y)) Filter.atTop (nhds (ccfc (schrKer t) R y)) := by
  have hlim : Filter.Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)⁻¹ * ‖y‖) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have := (h0.const_mul 2).mul_const ‖y‖
    simpa [one_div] using this
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    hlim)
  rw [schrOp_R hH, ← sub_apply, ← ccfc_sub (fun r => schrApprox n t r * r) (schrKer t)
    ((continuous_schrApprox n t).mul Complex.continuous_ofReal) (continuous_schrKer t)]
  refine ((ccfc _ R).le_opNorm y).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact norm_ccfc_le hH (by positivity) (fun r hr _ => schrApprox_mul_sub n t hr)

theorem exists_tendsto_schrOp (hH : IsSemibounded H m σ R) (t : ℝ) (x : E) :
    ∃ l, Filter.Tendsto (fun n => schrOp n t R x) Filter.atTop (nhds l) :=
  exists_tendsto_of_dense _ (norm_schrOp_le hH · t) hH.denseRange_R
    (fun y => ⟨_, tendsto_schrOp_R hH t y⟩) x

theorem tendsto_U0 (hH : IsSemibounded H m σ R) (t : ℝ) (x : E) :
    Filter.Tendsto (fun n => schrOp n t R x) Filter.atTop (nhds (U0 R t x)) := by
  have h : ∀ x, ∃ l, Filter.Tendsto (fun n => schrOp n t R x) Filter.atTop (nhds l) :=
    exists_tendsto_schrOp hH t
  rw [U0, dite_eq_left h]
  exact (h x).choose_spec

/-- The characterising identity `exp(it R⁻¹) R = (r ↦ r e^{it/r})(R)`. -/
theorem U0_R (hH : IsSemibounded H m σ R) (t : ℝ) (y : E) :
    U0 R t (R y) = ccfc (schrKer t) R y :=
  tendsto_nhds_unique (tendsto_U0 hH t (R y)) (tendsto_schrOp_R hH t y)

theorem norm_U0_apply_le (hH : IsSemibounded H m σ R) (t : ℝ) (x : E) : ‖U0 R t x‖ ≤ ‖x‖ := by
  refine le_of_tendsto (tendsto_U0 hH t x).norm (Filter.Eventually.of_forall (fun n => ?_))
  exact ((schrOp n t R).le_opNorm x).trans (by
    simpa using mul_le_mul_of_nonneg_right (norm_schrOp_le hH n t) (norm_nonneg x))

/-! ### Algebraic properties of `exp(it R⁻¹)` -/

/-- Two bounded operators that agree on the range of `R` are equal. -/
theorem ext_of_R (hH : IsSemibounded H m σ R) {A B : E →L[ℂ] E} (h : ∀ y, A (R y) = B (R y)) :
    A = B := by
  have : (A : E → E) = B :=
    hH.denseRange_R.equalizer A.continuous B.continuous (funext h)
  exact ContinuousLinearMap.ext (congrFun this)

theorem ccfc_R_apply (hH : IsSemibounded H m σ R) (g : ℝ → ℂ) (y : E) :
    ccfc g R (R y) = R (ccfc g R y) :=
  congrArg (fun T : E →L[ℂ] E => T y) (ccfc_commute hH.isSelfAdjoint_R (Commute.refl R) g).eq

theorem ccfc_mul_R_apply (hH : IsSemibounded H m σ R) {g : ℝ → ℂ} (hg : Continuous g) (y : E) :
    ccfc g R (R y) = ccfc (fun r => g r * r) R y := by
  rw [ccfc_mul _ _ hg Complex.continuous_ofReal, ccfc_id hH.isSelfAdjoint_R]; rfl

/-- `exp(it R⁻¹)` commutes with every bounded operator commuting with `R`. -/
theorem U0_commute (hH : IsSemibounded H m σ R) {O : E →L[ℂ] E} (hO : Commute R O) (t : ℝ) :
    Commute (U0 R t) O := by
  refine ext_of_R hH (fun y => ?_)
  have hOy : O (R y) = R (O y) := (congrArg (fun T : E →L[ℂ] E => T y) hO.eq).symm
  simp only [mul_apply_eq_comp]
  rw [hOy, U0_R hH, U0_R hH]
  exact (congrArg (fun T : E →L[ℂ] E => T y)
    (ccfc_commute hH.isSelfAdjoint_R hO (schrKer t)).eq)

theorem U0_zero (hH : IsSemibounded H m σ R) : U0 R 0 = 1 := by
  refine ext_of_R hH (fun y => ?_)
  rw [U0_R hH]
  have : schrKer 0 = fun r : ℝ => (r : ℂ) := funext schrKer_zero
  rw [this, ccfc_id hH.isSelfAdjoint_R]; rfl

theorem U0_add (hH : IsSemibounded H m σ R) (s t : ℝ) : U0 R (s + t) = U0 R s * U0 R t := by
  refine ext_of_R hH (fun y => ?_)
  have hc : Continuous (fun y => U0 R (s + t) (R y)) := ((U0 R (s + t)).comp R).continuous
  have hc' : Continuous (fun y => (U0 R s * U0 R t) (R y)) :=
    ((U0 R s * U0 R t).comp R).continuous
  have : (fun y => U0 R (s + t) (R y)) = (fun y => (U0 R s * U0 R t) (R y)) := by
    refine hH.denseRange_R.equalizer hc hc' (funext (fun z => ?_))
    simp only [Function.comp_apply, mul_apply_eq_comp]
    rw [U0_R hH, U0_R hH, ccfc_R_apply hH (schrKer t) z, U0_R hH,
      ccfc_mul_R_apply hH (continuous_schrKer _)]
    rw [← mul_apply_eq_comp, ← ccfc_mul _ _ (continuous_schrKer s) (continuous_schrKer t)]
    congr 2
    funext r
    exact (schrKer_mul s t r).symm
  exact congrFun this y

/-! ### The generator -/

theorem schrKer_sub_eq (h r : ℝ) :
    schrKer h r - r = (r : ℂ) * (Complex.exp (Complex.I * ((h / r : ℝ) : ℂ)) - 1) := by
  rw [schrKer]; ring

theorem norm_schrKer_sub_le (h : ℝ) {r : ℝ} (hr : 0 ≤ r) : ‖schrKer h r - r‖ ≤ |h| := by
  rw [schrKer_sub_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  rcases eq_or_lt_of_le hr with rfl | hr'
  · simp
  calc r * ‖Complex.exp (Complex.I * ((h / r : ℝ) : ℂ)) - 1‖ ≤ r * ‖h / r‖ :=
        mul_le_mul_of_nonneg_left Real.norm_exp_I_mul_ofReal_sub_one_le hr
    _ = |h| := by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hr']; field_simp

theorem gen_bound1 {h r : ℝ} (hh : h ≠ 0) (hr : 0 ≤ r) :
    ‖(h : ℂ)⁻¹ * (schrKer h r - r) - Complex.I‖ ≤ 2 := by
  have h1 : ‖(h : ℂ)⁻¹ * (schrKer h r - r)‖ ≤ 1 := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    calc |h|⁻¹ * ‖schrKer h r - r‖ ≤ |h|⁻¹ * |h| :=
          mul_le_mul_of_nonneg_left (norm_schrKer_sub_le h hr) (by positivity)
      _ = 1 := inv_mul_cancel₀ (abs_pos.mpr hh).ne'
  calc ‖(h : ℂ)⁻¹ * (schrKer h r - r) - Complex.I‖
      ≤ ‖(h : ℂ)⁻¹ * (schrKer h r - r)‖ + ‖Complex.I‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by rw [Complex.norm_I]; linarith
    _ = 2 := by norm_num

theorem gen_bound2 {h r : ℝ} (hh : h ≠ 0) (hr : 0 ≤ r) :
    ‖((h : ℂ)⁻¹ * (schrKer h r - r) - Complex.I) * r‖ ≤ 2 * |h| := by
  have hpos : 0 < |h| := abs_pos.mpr hh
  rcases le_or_gt r |h| with hrh | hrh
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    calc ‖(h : ℂ)⁻¹ * (schrKer h r - r) - Complex.I‖ * r ≤ 2 * r :=
          mul_le_mul_of_nonneg_right (gen_bound1 hh hr) hr
      _ ≤ 2 * |h| := by linarith
  · have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg h) hrh
    set a : ℝ := h / r with ha
    have key : ((h : ℂ)⁻¹ * (schrKer h r - r) - Complex.I) * r
        = ((r ^ 2 / h : ℝ) : ℂ) * (Complex.exp (Complex.I * (a : ℂ)) - 1 - Complex.I * a) := by
      rw [schrKer_sub_eq, ← ha]
      have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
      have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
      have : (a : ℂ) = (h : ℂ) / r := by rw [ha]; push_cast; ring
      rw [this]; push_cast; field_simp
    have ha1 : ‖Complex.I * (a : ℂ)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, ha, abs_div,
        abs_of_pos hr0, div_le_one hr0]
      exact hrh.le
    have hb := Complex.norm_exp_sub_one_sub_id_le ha1
    rw [key, norm_mul]
    have hn : ‖Complex.I * (a : ℂ)‖ ^ 2 = h ^ 2 / r ^ 2 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, ha,
        div_pow]
    rw [hn] at hb
    calc ‖((r ^ 2 / h : ℝ) : ℂ)‖ * ‖Complex.exp (Complex.I * (a : ℂ)) - 1 - Complex.I * a‖
        ≤ (r ^ 2 / |h|) * (h ^ 2 / r ^ 2) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg r)]
          exact mul_le_mul_of_nonneg_left hb (by positivity)
      _ = |h| := by
          rw [← sq_abs h]; field_simp
      _ ≤ 2 * |h| := by linarith

theorem continuous_genFun (h : ℝ) :
    Continuous (fun r : ℝ => (h : ℂ)⁻¹ * (schrKer h r - r) - Complex.I) :=
  (continuous_const.mul ((continuous_schrKer h).sub Complex.continuous_ofReal)).sub
    continuous_const

theorem ccfc_genFun (hH : IsSemibounded H m σ R) (h : ℝ) :
    ccfc (fun r : ℝ => (h : ℂ)⁻¹ * (schrKer h r - r) - Complex.I) R
      = (h : ℂ)⁻¹ • (ccfc (schrKer h) R - R) - Complex.I • 1 := by
  have hc1 : Continuous (fun r : ℝ => schrKer h r - r) :=
    (continuous_schrKer h).sub Complex.continuous_ofReal
  rw [ccfc_sub (fun r : ℝ => (h : ℂ)⁻¹ * (schrKer h r - r)) (fun _ => Complex.I)
    (continuous_const.mul hc1) continuous_const,
    ccfc_smul _ (fun r : ℝ => schrKer h r - r) hc1,
    ccfc_sub (schrKer h) (fun r : ℝ => (r : ℂ)) (continuous_schrKer h) Complex.continuous_ofReal,
    ccfc_id hH.isSelfAdjoint_R]
  congr 1
  have : (fun _ : ℝ => Complex.I) = (fun _ : ℝ => Complex.I * 1) := by funext; ring
  rw [this, ccfc_smul Complex.I (fun _ => (1 : ℂ)) continuous_const, ccfc_one hH.isSelfAdjoint_R]

/-- **The generator of `exp(itR⁻¹)` on the range of `R`:**
`(exp(ihR⁻¹)(Ry) - Ry)/h → iy` as `h → 0`. -/
theorem tendsto_U0_gen (hH : IsSemibounded H m σ R) (y : E) :
    Filter.Tendsto (fun h : ℝ => (h : ℂ)⁻¹ • (U0 R h (R y) - R y)) (nhdsWithin 0 {0}ᶜ)
      (nhds (Complex.I • y)) := by
  let K : ℝ → E →L[ℂ] E := fun h =>
    ccfc (fun r : ℝ => (h : ℂ)⁻¹ * (schrKer h r - r) - Complex.I) R
  have key := tendsto_apply_of_dense (l := nhdsWithin (0 : ℝ) {0}ᶜ) K 2 ?_ hH.denseRange_R ?_ y
  · have := key.add (tendsto_const_nhds (x := Complex.I • y))
    rw [zero_add] at this
    refine this.congr (fun h => ?_)
    simp only [K, ccfc_genFun hH, U0_R hH]
    simp
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact norm_ccfc_le hH zero_le_two (fun r hr _ => gen_bound1 hh hr)
  · intro z
    have hlim : Filter.Tendsto (fun h : ℝ => 2 * |h| * ‖z‖) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      have : Filter.Tendsto (fun h : ℝ => 2 * |h| * ‖z‖) (nhds 0) (nhds (2 * |0| * ‖z‖)) :=
        ((continuous_const.mul continuous_abs).mul continuous_const).tendsto 0
      rw [abs_zero, mul_zero, zero_mul] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [K]
    rw [ccfc_mul_R_apply hH (continuous_genFun h)]
    refine ((ccfc _ R).le_opNorm z).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact norm_ccfc_le hH (by positivity) (fun r hr _ => gen_bound2 hh hr)

theorem U0_R_apply (hH : IsSemibounded H m σ R) (t : ℝ) (y : E) : U0 R t (R y) = R (U0 R t y) :=
  congrArg (fun T : E →L[ℂ] E => T y) (U0_commute hH (Commute.refl R) t).eq

theorem hasDerivAt_U0 (hH : IsSemibounded H m σ R) (y : E) (t : ℝ) :
    HasDerivAt (fun s => U0 R s (R y)) (Complex.I • U0 R t y) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have h1 := ((U0 R t).continuous.tendsto _).comp (tendsto_U0_gen hH y)
  rw [map_smul] at h1
  refine h1.congr (fun h => ?_)
  simp only [Function.comp_apply, map_smul, map_sub]
  rw [U0_add hH, mul_apply_eq_comp, ← Complex.ofReal_inv, Complex.coe_smul]

/-! ### The unitary group `exp(itH)` -/

/-- **The unitary group** `exp(itH) = exp(itσ) · exp(it R⁻¹)` of the semibounded operator `H`
with resolvent `R = (H - σ)⁻¹`. -/
def unitaryGroup (σ : ℝ) (R : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  Complex.exp (Complex.I * ((t * σ : ℝ) : ℂ)) • U0 R t

theorem unitaryGroup_zero (hH : IsSemibounded H m σ R) : unitaryGroup σ R 0 = 1 := by
  simp [unitaryGroup, U0_zero hH]

theorem unitaryGroup_add (hH : IsSemibounded H m σ R) (s t : ℝ) :
    unitaryGroup σ R (s + t) = unitaryGroup σ R s * unitaryGroup σ R t := by
  simp only [unitaryGroup, U0_add hH, smul_mul_smul_comm, ← Complex.exp_add]
  congr 2; push_cast; ring

theorem unitaryGroup_neg_mul (hH : IsSemibounded H m σ R) (t : ℝ) :
    unitaryGroup σ R (-t) * unitaryGroup σ R t = 1 := by
  rw [← unitaryGroup_add hH, neg_add_cancel, unitaryGroup_zero hH]

theorem unitaryGroup_mul_neg (hH : IsSemibounded H m σ R) (t : ℝ) :
    unitaryGroup σ R t * unitaryGroup σ R (-t) = 1 := by
  rw [← unitaryGroup_add hH, add_neg_cancel, unitaryGroup_zero hH]

theorem norm_unitaryGroup_apply_le (hH : IsSemibounded H m σ R) (t : ℝ) (x : E) :
    ‖unitaryGroup σ R t x‖ ≤ ‖x‖ := by
  rw [unitaryGroup, smul_apply, norm_smul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact norm_U0_apply_le hH t x

/-- `exp(itH)` is an isometry. -/
theorem norm_unitaryGroup_apply (hH : IsSemibounded H m σ R) (t : ℝ) (x : E) :
    ‖unitaryGroup σ R t x‖ = ‖x‖ := by
  refine le_antisymm (norm_unitaryGroup_apply_le hH t x) ?_
  have := norm_unitaryGroup_apply_le hH (-t) (unitaryGroup σ R t x)
  rwa [← mul_apply_eq_comp, unitaryGroup_neg_mul hH, one_apply_eq_self] at this

/-- `exp(itH)` commutes with every bounded operator that commutes with the resolvent `R`. -/
theorem unitaryGroup_commute (hH : IsSemibounded H m σ R) {O : E →L[ℂ] E} (hO : Commute R O)
    (t : ℝ) : Commute (unitaryGroup σ R t) O :=
  (U0_commute hH hO t).smul_left _

theorem unitaryGroup_R_apply (hH : IsSemibounded H m σ R) (t : ℝ) (y : E) :
    unitaryGroup σ R t (R y) = R (unitaryGroup σ R t y) := by
  simp only [unitaryGroup, smul_apply, U0_R_apply hH, map_smul]

/-- `exp(itH)` maps the domain of `H` into itself. -/
theorem unitaryGroup_mem_domain (hH : IsSemibounded H m σ R) (t : ℝ) (x : H.domain) :
    unitaryGroup σ R t x ∈ H.domain := by
  have hx := hH.inv.left_inv x
  rw [← hx, unitaryGroup_R_apply hH]
  exact hH.inv.mem_domain _

/-- `ψ` is a strong solution of the Schrödinger equation `dψ/dt = iHψ` on `ℝ`. -/
structure IsSchrodingerSolution (H : E →ₗ.[ℂ] E) (ψ : ℝ → E) : Prop where
  mem : ∀ t, ψ t ∈ H.domain
  deriv : ∀ t, HasDerivAt ψ (Complex.I • H ⟨ψ t, mem t⟩) t

/-- `U` is a unitary group generated by `H` in the sense of the Schrödinger equation:
`U 0 = 1`, and for every `x` in the domain of `H`, `t ↦ U t x` solves `dψ/dt = iHψ`. -/
structure IsUnitaryGroupOf (H : E →ₗ.[ℂ] E) (U : ℝ → E →L[ℂ] E) : Prop where
  zero : U 0 = 1
  sol : ∀ x : H.domain, IsSchrodingerSolution H (fun t => U t x)

/-- **Existence.** For `x` in the domain of `H`, `t ↦ exp(itH) x` solves `dψ/dt = iHψ`. -/
theorem unitaryGroup_isUnitaryGroupOf (hH : IsSemibounded H m σ R) :
    IsUnitaryGroupOf H (unitaryGroup σ R) := by
  refine ⟨unitaryGroup_zero hH, fun x => ⟨fun t => unitaryGroup_mem_domain hH t x, fun t => ?_⟩⟩
  set y : E := H x - (σ : ℂ) • (x : E) with hy
  have hx : R y = x := hH.inv.left_inv x
  set e : ℝ → ℂ := fun s => Complex.exp (Complex.I * ((s * σ : ℝ) : ℂ)) with he
  have hde : HasDerivAt e (e t * (Complex.I * σ)) t := by
    have h1 : HasDerivAt (fun s : ℝ => Complex.I * ((s * σ : ℝ) : ℂ)) (Complex.I * σ) t := by
      have := ((hasDerivAt_id t).mul_const σ).ofReal_comp.const_mul Complex.I
      simpa using this
    exact h1.cexp
  have hd := hde.smul (hasDerivAt_U0 hH y t)
  have hfun : (fun s => unitaryGroup σ R s x) = fun s => e s • U0 R s (R y) := by
    funext s; rw [hx]; rfl
  rw [hfun]
  convert hd using 1
  -- compute `H (exp(itH) x)`
  set w := U0 R t y with hw
  have hUx : unitaryGroup σ R t x = e t • R w := by
    rw [← hx, ← U0_R_apply hH]; rfl
  have e1 : (⟨unitaryGroup σ R t x, unitaryGroup_mem_domain hH t x⟩ : H.domain)
      = e t • (⟨R w, hH.inv.mem_domain w⟩ : H.domain) := by
    ext; simp only [SetLike.val_smul]; exact hUx
  have h2 := hH.inv.right_inv w
  rw [sub_eq_iff_eq_add] at h2
  rw [e1, LinearPMap.map_smul, h2, U0_R_apply hH]
  module

/-- **Strong continuity:** `t ↦ exp(itH) x` is continuous for every `x`. -/
theorem continuous_unitaryGroup_apply (hH : IsSemibounded H m σ R) (x : E) :
    Continuous (fun t => unitaryGroup σ R t x) := by
  refine continuous_of_uniform_approx_of_continuous (fun u hu => ?_)
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
  obtain ⟨y, hy⟩ : ∃ y, dist x (R y) < ε := hH.denseRange_R.exists_dist_lt x hε
  refine ⟨fun t => unitaryGroup σ R t (R y), ?_, fun t => hεu ?_⟩
  · have := (unitaryGroup_isUnitaryGroupOf hH).sol ⟨R y, hH.inv.mem_domain y⟩
    exact continuous_iff_continuousAt.mpr (fun t => (this.deriv t).continuousAt)
  · rw [dist_eq_norm, ← map_sub, norm_unitaryGroup_apply hH, ← dist_eq_norm]
    exact hy

/-! ### Invariant subspaces -/

theorem ccfc_eq_real (hH : IsSemibounded H m σ R) {g : ℝ → ℂ} (hg : Continuous g) :
    ccfc g R = cfc (fun r => (g r).re) R + Complex.I • cfc (fun r => (g r).im) R := by
  have hR := hH.isSelfAdjoint_R
  rw [cfc_real_eq_complex (fun r => (g r).re) hR, cfc_real_eq_complex (fun r => (g r).im) hR]
  have hre : Continuous (fun z : ℂ => (((g z.re).re : ℝ) : ℂ)) := by fun_prop
  have him : Continuous (fun z : ℂ => (((g z.re).im : ℝ) : ℂ)) := by fun_prop
  rw [← cfc_const_mul Complex.I _ R him.continuousOn, ← cfc_add (a := R)
    (fun z : ℂ => (((g z.re).re : ℝ) : ℂ)) (fun z : ℂ => Complex.I * (((g z.re).im : ℝ) : ℂ))
    hre.continuousOn (continuous_const.mul him).continuousOn]
  unfold ccfc
  refine cfc_congr (fun z _ => ?_)
  exact (Complex.re_add_im _).symm.trans (by ring)

/-- `g(R)` preserves every closed subspace that `R` preserves. -/
theorem ccfc_apply_mem (hH : IsSemibounded H m σ R) {g : ℝ → ℂ} (hg : Continuous g)
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E)) (hRV : ∀ v ∈ V, R v ∈ V) {v : E}
    (hv : v ∈ V) : ccfc g R v ∈ V := by
  rw [ccfc_eq_real hH hg, add_apply, smul_apply]
  have hre : Continuous (fun r => (g r).re) := Complex.continuous_re.comp hg
  have him : Continuous (fun r => (g r).im) := Complex.continuous_im.comp hg
  exact V.add_mem (cfc_apply_mem hH.isSelfAdjoint_R hH.spectrum_R_subset hre.continuousOn V hV hRV hv)
    (V.smul_mem _ (cfc_apply_mem hH.isSelfAdjoint_R hH.spectrum_R_subset him.continuousOn V hV hRV
      hv))

/-- `exp(itH)` preserves every closed subspace that the resolvent `R` preserves. -/
theorem unitaryGroup_apply_mem (hH : IsSemibounded H m σ R) (t : ℝ) (V : Submodule ℂ E)
    (hV : IsClosed (V : Set E)) (hRV : ∀ v ∈ V, R v ∈ V) {v : E} (hv : v ∈ V) :
    unitaryGroup σ R t v ∈ V := by
  have h0 : U0 R t v ∈ V := hV.mem_of_tendsto (tendsto_U0 hH t v)
    (Filter.Eventually.of_forall (fun n => ccfc_apply_mem hH (continuous_schrApprox n t) V hV hRV hv))
  exact V.smul_mem _ h0

/-! ### Uniqueness -/

omit [CompleteSpace E] in
theorem IsSchrodingerSolution.sub {ψ φ : ℝ → E} (hψ : IsSchrodingerSolution H ψ)
    (hφ : IsSchrodingerSolution H φ) : IsSchrodingerSolution H (fun t => ψ t - φ t) where
  mem t := H.domain.sub_mem (hψ.mem t) (hφ.mem t)
  deriv t := by
    have := (hψ.deriv t).sub (hφ.deriv t)
    convert this using 1
    have e : (⟨ψ t - φ t, H.domain.sub_mem (hψ.mem t) (hφ.mem t)⟩ : H.domain)
        = ⟨ψ t, hψ.mem t⟩ - ⟨φ t, hφ.mem t⟩ := rfl
    rw [e, LinearPMap.map_sub, smul_sub]

omit [CompleteSpace E] in
/-- **Uniqueness for the Schrödinger equation.** If `H` is symmetric, two solutions of
`dψ/dt = iHψ` with the same initial value agree for all times (the norm of their difference is
conserved). -/
theorem IsSchrodingerSolution.unique (hsymm : ∀ x y : H.domain, ⟪H x, (y : E)⟫_ℂ = ⟪(x : E), H y⟫_ℂ)
    {ψ φ : ℝ → E} (hψ : IsSchrodingerSolution H ψ) (hφ : IsSchrodingerSolution H φ)
    (h0 : ψ 0 = φ 0) (t : ℝ) : ψ t = φ t := by
  have hd := hψ.sub hφ
  set d := fun t => ψ t - φ t with hd_def
  have hder : ∀ s, HasDerivAt (fun s => ⟪d s, d s⟫_ℂ) 0 s := by
    intro s
    have h1 := (hd.deriv s).inner ℂ (hd.deriv s)
    convert h1 using 1
    have hs := hsymm ⟨d s, hd.mem s⟩ ⟨d s, hd.mem s⟩
    simp only at hs
    rw [inner_smul_right, inner_smul_left, hs, Complex.conj_I]
    ring
  have hconst := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt)
    (fun s => (hder s).deriv) t 0
  simp only [hd_def, h0, sub_self, inner_zero_left] at hconst
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hconst)

omit [CompleteSpace E] in
/-- **The unitary group depends only on `H`:** a symmetric, densely defined `H` generates at
most one unitary group in the sense of `IsUnitaryGroupOf`. -/
theorem IsUnitaryGroupOf.unique (hsymm : ∀ x y : H.domain, ⟪H x, (y : E)⟫_ℂ = ⟪(x : E), H y⟫_ℂ)
    (hdense : Dense (H.domain : Set E)) {U V : ℝ → E →L[ℂ] E} (hU : IsUnitaryGroupOf H U)
    (hV : IsUnitaryGroupOf H V) : U = V := by
  funext t
  have h : ∀ x : H.domain, U t x = V t x := fun x =>
    IsSchrodingerSolution.unique hsymm (hU.sol x) (hV.sol x) (by simp [hU.zero, hV.zero]) t
  have : (U t : E → E) = V t := by
    have hd : DenseRange (fun x : H.domain => (x : E)) := hdense.denseRange_val
    exact hd.equalizer (U t).continuous (V t).continuous (funext h)
  exact ContinuousLinearMap.ext (congrFun this)

theorem IsSemibounded.dense_domain (hH : IsSemibounded H m σ R) : Dense (H.domain : Set E) :=
  hH.denseRange_R.mono (by rintro _ ⟨y, rfl⟩; exact hH.inv.mem_domain y)

/-- Every unitary group generated by a semibounded `H` is `unitaryGroup σ R`. -/
theorem IsUnitaryGroupOf.eq_unitaryGroup (hH : IsSemibounded H m σ R) {U : ℝ → E →L[ℂ] E}
    (hU : IsUnitaryGroupOf H U) : U = unitaryGroup σ R :=
  hU.unique hH.symm hH.dense_domain (unitaryGroup_isUnitaryGroupOf hH)

end CftCheck
