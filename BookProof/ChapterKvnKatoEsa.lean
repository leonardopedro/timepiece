import Mathlib
import BookProof.ChapterKvnKatoEnergy
import BookProof.ChapterKvnKatoFriedrichs

/-!
# Kato's argument for `N = H_G² + E`: deficiency vectors vanish

Let `X = G·∇ + ½ div G` with a smooth real vector field `G`, and let `E ≥ 1` be a smooth real
function.  If `u ∈ L²` solves `(−X² + E − z̄) u = 0` weakly against compactly supported smooth
test functions, with `Re z = 0`, then

* for every real compactly supported smooth cut-off `χ` with `|χ| ≤ 1`,
  `‖χ u‖ ≤ ‖(G·∇χ) u‖` (`kato_cutoff_ineq`) — the limit of the energy inequality for the
  mollifications of `u`, the commutator terms vanishing by Friedrichs' lemma;
* if moreover `G` admits a proper Lyapunov function `L ≥ ‖x‖` with `|G·∇L| ≤ c L`, then
  `u = 0` (`eq_zero_of_lyapunov`) — take `χ = θ(L/R)` and let `R → ∞`.
-/

namespace BookProof.KvnKato

open MeasureTheory Filter Topology
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegEnergy
open BookProof.ConvolutionCalc BookProof.DegKatoEsa
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. `L²` bookkeeping -/

theorem l2n_eq_toReal {f : Vd d → ℂ} (hf : MemLp f 2 (volume : Measure (Vd d))) :
    l2n f = (eLpNorm f 2 volume).toReal := by
  rw [l2n_eq_norm_toLp hf, Lp.norm_toLp]

theorem abs_l2n_sub_le {f g : Vd d → ℂ} (hf : MemLp f 2 (volume : Measure (Vd d)))
    (hg : MemLp g 2 (volume : Measure (Vd d))) :
    |l2n f - l2n g| ≤ (eLpNorm (f - g) 2 volume).toReal := by
  rw [l2n_eq_norm_toLp hf, l2n_eq_norm_toLp hg, ← Lp.norm_toLp _ (hf.sub hg),
    MemLp.toLp_sub hf hg]
  exact abs_norm_sub_norm_le _ _

/-- A real sequence dominated by the real parts of an `ℝ≥0∞`-sequence tending to zero tends
to zero. -/
theorem tendsto_zero_of_le_toReal {r : ℕ → ℝ} {e : ℕ → ℝ≥0∞} (he : Tendsto e atTop (𝓝 0))
    (h0 : ∀ n, 0 ≤ r n) (hle : ∀ n, r n ≤ (e n).toReal) : Tendsto r atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he
  rw [ENNReal.toReal_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h h0 hle

/-- Multiplying by a function bounded by `1` and vanishing off `K` is dominated by the
indicator of `K`. -/
theorem eLpNorm_mul_le_indicator {b f : Vd d → ℂ} {K : Set (Vd d)} (hb : ∀ x, ‖b x‖ ≤ 1)
    (hbK : ∀ x, x ∉ K → b x = 0) :
    eLpNorm (fun x => b x * f x) 2 volume ≤ eLpNorm (K.indicator f) 2 volume := by
  refine eLpNorm_mono fun x => ?_
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb x)
  · rw [Set.indicator_of_notMem hx, hbK x hx, zero_mul]

/-! ## 2. The cut-off inequality -/

variable (S : KvnData d)

set_option maxHeartbeats 1000000 in
-- the limit argument assembles many convergence statements
/-- **The cut-off inequality** `‖χ u‖ ≤ ‖(G·∇χ) u‖` for a deficiency vector `u`. -/
theorem kato_cutoff_ineq {E : Vd d → ℂ} (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E)
    (hEr : ∀ y, (starRingEnd ℂ) (E y) = E y) (hE1 : ∀ y, 1 ≤ (E y).re)
    {u : Vd d → ℂ} (hu2 : MemLp u 2 (volume : Measure (Vd d))) (hum : StronglyMeasurable u)
    {z : ℂ} (hz : z.re = 0)
    (hweak : ∀ φ : Vd d → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∫ y, (starRingEnd ℂ) (Af S E φ y) * u y = z * ∫ y, (starRingEnd ℂ) (φ y) * u y)
    {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχ1 : ∀ x, |χ x| ≤ 1)
    {R : ℝ} (hχR : ∀ x, x ∉ Metric.closedBall (0 : Vd d) R → χ x = 0) :
    l2n (fun x => cx χ x * u x) ≤ l2n (fun x => Df S (cx χ) x * u x) := by
  have hloc : LocallyIntegrable u (volume : Measure (Vd d)) := hu2.locallyIntegrable one_le_two
  set K := Metric.closedBall (0 : Vd d) R with hK
  have hχc : HasCompactSupport χ :=
    HasCompactSupport.intro (isCompact_closedBall 0 R) fun x hx => hχR x hx
  have hcx := contDiff_cx hχ
  have hcxc : HasCompactSupport (cx χ) := hasCompactSupport_cx hχc
  have hcxb : ∀ x, ‖cx χ x‖ ≤ 1 := fun x => by rw [norm_cx]; exact hχ1 x
  have hcxK : ∀ x, x ∉ K → cx χ x = 0 := fun x hx => by simp [cx, hχR x hx]
  obtain ⟨B, hB⟩ := (contDiff_Df S hcx).continuous.bounded_above_of_compact_support
    (hasCompactSupport_Df S hcxc)
  -- the sequences
  set ρ : ℕ → Vd d → ℂ := fun n => rhoS (sN n) with hρ
  have hρs : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n => contDiff_rhoS _
  have hρz : ∀ n, ∀ z : Vd d, 1 / 2 < ‖z‖ → ρ n z = 0 :=
    fun n _ hz => rhoS_eq_zero (one_le_sN n) hz
  set v : ℕ → Vd d → ℂ := fun n => kint u (kz (ρ n)) with hv
  set w1 : ℕ → Vd d → ℂ := fun n => kint u (k1 S (ρ n)) with hw1
  set w2 : ℕ → Vd d → ℂ := fun n => fun x => kint u (k2 S (ρ n)) x + kint u (ek E (ρ n)) x
    with hw2
  have hvs : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (v n) := fun n =>
    contDiff_kint (goodKernel_kz (hρs n) (hρz n)) hloc
  have hw1s : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (w1 n) := fun n =>
    contDiff_kint (goodKernel_k1 S (hρs n) (hρz n)) hloc
  have hw2c : ∀ n, Continuous (w2 n) := fun n =>
    (contDiff_kint (goodKernel_k2 S (hρs n) (hρz n)) hloc).continuous.add
      (contDiff_kint (goodKernel_ek hE (hρs n) (hρz n)) hloc).continuous
  have hid : ∀ n x, Af S E (v n) x - z * v n x = -2 * Xf S (w1 n) x + w2 n x := by
    intro n x
    rw [mollified_identity S hE hEr hloc hweak (hρs n) (hρz n) (fun z => rhoS_real _ z) x]
    simp only [hw2]
    ring
  have hen := fun n => energy_ineq S hE hE1 hz (hvs n) (hw1s n) (hw2c n) (hid n) hχ hχc
  -- membership in `L²`
  have hcxC : Continuous (cx χ) := hcx.continuous
  have hDC : Continuous (Df S (cx χ)) := (contDiff_Df S hcx).continuous
  have mV : ∀ n, MemLp (fun x => cx χ x * v n x) 2 volume := fun n =>
    memLp_of_cc' (hcxC.mul (hvs n).continuous) hcxc.mul_right
  have mQ : ∀ n, MemLp (fun x => Df S (cx χ) x * v n x) 2 volume := fun n =>
    memLp_of_cc' (hDC.mul (hvs n).continuous) (hasCompactSupport_Df S hcxc).mul_right
  have mA : ∀ n, MemLp (fun x => cx χ x * w1 n x) 2 volume := fun n =>
    memLp_of_cc' (hcxC.mul (hw1s n).continuous) hcxc.mul_right
  have mB : ∀ n, MemLp (fun x => cx χ x * w2 n x) 2 volume := fun n =>
    memLp_of_cc' (hcxC.mul (hw2c n)) hcxc.mul_right
  have mVu : MemLp (fun x => cx χ x * u x) 2 volume := memLp_bdd_mul hcxC hcxb hu2
  have mQu : MemLp (fun x => Df S (cx χ) x * u x) 2 volume := memLp_bdd_mul hDC hB hu2
  -- convergence of the mollifications
  have hconv := tendsto_kint_rhoS hum hu2
  have ennsq : ∀ {e f : ℕ → ℝ≥0∞}, Tendsto f atTop (𝓝 0) → (∀ n, e n ≤ f n) →
      Tendsto e atTop (𝓝 0) := fun hf hle =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hf (fun n => zero_le _) hle
  have tV : Tendsto (fun n => l2n (fun x => cx χ x * v n x)) atTop
      (𝓝 (l2n (fun x => cx χ x * u x))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have he : Tendsto (fun n => eLpNorm ((fun x => cx χ x * v n x) - fun x => cx χ x * u x) 2
        volume) atTop (𝓝 0) := by
      refine ennsq hconv fun n => eLpNorm_mono fun x => ?_
      simp only [Pi.sub_apply, ← mul_sub, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hcxb x)
    exact tendsto_zero_of_le_toReal he (fun n => norm_nonneg _) fun n =>
      abs_l2n_sub_le (mV n) mVu
  have tQ : Tendsto (fun n => l2n (fun x => Df S (cx χ) x * v n x)) atTop
      (𝓝 (l2n (fun x => Df S (cx χ) x * u x))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hB' : Tendsto (fun n => ENNReal.ofReal B * eLpNorm (fun x => v n x - u x) 2 volume)
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hconv (Or.inr ENNReal.ofReal_ne_top)
    have he : Tendsto (fun n => eLpNorm ((fun x => Df S (cx χ) x * v n x)
        - fun x => Df S (cx χ) x * u x) 2 volume) atTop (𝓝 0) := by
      refine ennsq hB' fun n => eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (Filter.Eventually.of_forall fun x => ?_) 2
      simp only [Pi.sub_apply, ← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)
    exact tendsto_zero_of_le_toReal he (fun n => norm_nonneg _) fun n =>
      abs_l2n_sub_le (mQ n) mQu
  have tA : Tendsto (fun n => l2n (fun x => cx χ x * w1 n x)) atTop (𝓝 0) := by
    have he : Tendsto (fun n => eLpNorm (fun x => cx χ x * w1 n x) 2 volume) atTop (𝓝 0) :=
      ennsq (tendsto_delta_k1 (S := S) hu2 R) fun n => eLpNorm_mul_le_indicator hcxb hcxK
    exact tendsto_zero_of_le_toReal he (fun n => l2n_nonneg _) fun n =>
      (l2n_eq_toReal (mA n)).le
  have tB : Tendsto (fun n => l2n (fun x => cx χ x * w2 n x)) atTop (𝓝 0) := by
    have hsum := (tendsto_delta_k2 (S := S) hu2 R).add (tendsto_delta_ek S hE hu2 R)
    rw [add_zero] at hsum
    have he : Tendsto (fun n => eLpNorm (fun x => cx χ x * w2 n x) 2 volume) atTop (𝓝 0) := by
      refine ennsq hsum fun n => (eLpNorm_mul_le_indicator hcxb hcxK).trans ?_
      have hsplit : K.indicator (w2 n) = K.indicator (kint u (k2 S (ρ n)))
          + K.indicator (kint u (ek E (ρ n))) := by
        rw [← Set.indicator_add']
        rfl
      rw [hsplit]
      exact eLpNorm_add_le
        ((contDiff_kint (goodKernel_k2 S (hρs n) (hρz n)) hloc).continuous.aestronglyMeasurable.indicator
          measurableSet_closedBall)
        ((contDiff_kint (goodKernel_ek hE (hρs n) (hρz n)) hloc).continuous.aestronglyMeasurable.indicator
          measurableSet_closedBall) (by norm_num)
    exact tendsto_zero_of_le_toReal he (fun n => l2n_nonneg _) fun n =>
      (l2n_eq_toReal (mB n)).le
  -- pass to the limit in the energy inequality
  set a := l2n (fun x => cx χ x * u x)
  set b := l2n (fun x => Df S (cx χ) x * u x)
  have hlimL : Tendsto (fun n => l2n (fun x => cx χ x * v n x) ^ 2
      - l2n (fun x => cx χ x * v n x) * l2n (fun x => cx χ x * w2 n x)) atTop
      (𝓝 (a ^ 2 - a * 0)) := (tV.pow 2).sub (tV.mul tB)
  have hlimR : Tendsto (fun n => (l2n (fun x => Df S (cx χ) x * v n x)
      + l2n (fun x => cx χ x * w1 n x)) ^ 2
      + 4 * l2n (fun x => Df S (cx χ) x * v n x) * l2n (fun x => cx χ x * w1 n x)) atTop
      (𝓝 ((b + 0) ^ 2 + 4 * b * 0)) := ((tQ.add tA).pow 2).add ((tQ.const_mul 4).mul tA)
  have hle : a ^ 2 - a * 0 ≤ (b + 0) ^ 2 + 4 * b * 0 :=
    le_of_tendsto_of_tendsto' hlimL hlimR fun n => by linarith [hen n]
  have ha : 0 ≤ a := l2n_nonneg _
  have hb : 0 ≤ b := l2n_nonneg _
  nlinarith

/-! ## 3. The Lyapunov cut-off -/

/-- The profile of the cut-off: `1` on `[−1, 1]`, `0` outside `(−2, 2)`. -/
def thetaB : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := one_pos
  rIn_lt_rOut := one_lt_two

/-- The cut-off profile as a function. -/
def theta (t : ℝ) : ℝ := thetaB t

theorem contDiff_theta : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) theta := thetaB.contDiff

theorem theta_mem (t : ℝ) : 0 ≤ theta t ∧ theta t ≤ 1 := ⟨thetaB.nonneg, thetaB.le_one⟩

theorem theta_eq_one {t : ℝ} (ht : |t| ≤ 1) : theta t = 1 :=
  thetaB.one_of_mem_closedBall (by simpa [Real.dist_eq] using ht)

theorem theta_eq_zero {t : ℝ} (ht : 2 ≤ |t|) : theta t = 0 :=
  thetaB.zero_of_le_dist (by simpa [Real.dist_eq] using ht)

theorem deriv_theta_eq_zero {t : ℝ} (ht : |t| < 1 ∨ 2 < |t|) : deriv theta t = 0 := by
  rcases ht with ht | ht
  · have hev : theta =ᶠ[𝓝 t] fun _ => 1 := by
      have hopen : IsOpen {s : ℝ | |s| < 1} := isOpen_lt continuous_abs continuous_const
      exact Filter.eventually_of_mem (hopen.mem_nhds ht) fun s hs => theta_eq_one (le_of_lt hs)
    rw [hev.deriv_eq]; simp
  · have hev : theta =ᶠ[𝓝 t] fun _ => 0 := by
      have hopen : IsOpen {s : ℝ | 2 < |s|} := isOpen_lt continuous_const continuous_abs
      exact Filter.eventually_of_mem (hopen.mem_nhds ht) fun s hs => theta_eq_zero (le_of_lt hs)
    rw [hev.deriv_eq]; simp

theorem exists_deriv_theta_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |deriv theta t| ≤ M := by
  have hc : Continuous (deriv theta) :=
    contDiff_theta.continuous_deriv (by exact_mod_cast le_top)
  have hcs : HasCompactSupport (deriv theta) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 3) fun t ht => ?_
    refine deriv_theta_eq_zero (Or.inr ?_)
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at ht
    linarith
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hcs
  exact ⟨|M|, abs_nonneg _, fun t => (hM t).trans (le_abs_self M)⟩

/-- The coordinate derivative of a complexified real function. -/
theorem dcoord_cx {f : Vd d → ℝ} (hf : Differentiable ℝ f) (i : Fin d) (x : Vd d) :
    dcoord i (cx f) x = ((fderiv ℝ f x (kinDir d i) : ℝ) : ℂ) := by
  have h : HasFDerivAt (cx f) (Complex.ofRealCLM.comp (fderiv ℝ f x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hf x).hasFDerivAt
  simp only [dcoord]
  rw [h.fderiv]
  rfl

/-- The Lyapunov cut-off `χ_R = θ(L/R)`. -/
def lyapCut (L : Vd d → ℝ) (R : ℝ) (x : Vd d) : ℝ := theta (L x / R)

theorem contDiff_lyapCut {L : Vd d → ℝ} (hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L) (R : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lyapCut L R) :=
  contDiff_theta.comp (hL.div_const R)

/-- `G·∇χ_R = θ'(L/R)/R · G·∇L`. -/
theorem Df_lyapCut {L : Vd d → ℝ} (hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L) (R : ℝ)
    (x : Vd d) :
    Df S (cx (lyapCut L R)) x = ((deriv theta (L x / R) / R : ℝ) : ℂ) * Df S (cx L) x := by
  have hLd : Differentiable ℝ L := hL.differentiable (by simp)
  have hθd : Differentiable ℝ theta := contDiff_theta.differentiable (by simp)
  have hcd : Differentiable ℝ (lyapCut L R) := (contDiff_lyapCut hL R).differentiable (by simp)
  have hfd : ∀ i, fderiv ℝ (lyapCut L R) x (kinDir d i)
      = deriv theta (L x / R) / R * fderiv ℝ L x (kinDir d i) := by
    intro i
    have h1 : HasFDerivAt (fun y => L y / R) ((1 / R) • fderiv ℝ L x) x := by
      have := ((hLd x).hasFDerivAt).const_smul (1 / R)
      convert this using 1
      funext y; simp [div_eq_inv_mul, smul_eq_mul]
    have h2 := (hθd (L x / R)).hasDerivAt.comp_hasFDerivAt x h1
    have h3 : lyapCut L R = theta ∘ fun y => L y / R := rfl
    rw [h3, h2.fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  simp only [Df, dcoord_cx hcd, dcoord_cx hLd, hfd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

theorem integrable_normSq {f : Vd d → ℂ} (hf : MemLp f 2 (volume : Measure (Vd d))) :
    Integrable (fun x => ‖f x‖ ^ 2) volume :=
  hf.integrable_norm_pow (p := 2) two_ne_zero

set_option maxHeartbeats 1000000 in
-- the final assembly of the cut-off argument
/-- **Deficiency vectors vanish** when `G` has a proper Lyapunov function `L ≥ ‖x‖` with
`|G·∇L| ≤ c L`. -/
theorem eq_zero_of_lyapunov {E : Vd d → ℂ} (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E)
    (hEr : ∀ y, (starRingEnd ℂ) (E y) = E y) (hE1 : ∀ y, 1 ≤ (E y).re)
    {u : Vd d → ℂ} (hu2 : MemLp u 2 (volume : Measure (Vd d))) (hum : StronglyMeasurable u)
    {z : ℂ} (hz : z.re = 0)
    (hweak : ∀ φ : Vd d → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∫ y, (starRingEnd ℂ) (Af S E φ y) * u y = z * ∫ y, (starRingEnd ℂ) (φ y) * u y)
    {L : Vd d → ℝ} (hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L) (hLn : ∀ x, ‖x‖ ≤ L x)
    {c₀ : ℝ} (hLf : ∀ x, ‖Df S (cx L) x‖ ≤ c₀ * L x) :
    u =ᵐ[volume] 0 := by
  obtain ⟨M, hM0, hM⟩ := exists_deriv_theta_bound
  set K0 : ℝ := 2 * M * |c₀| with hK0
  have hK0n : 0 ≤ K0 := by positivity
  have hL0 : ∀ x, 0 ≤ L x := fun x => (norm_nonneg x).trans (hLn x)
  have hLm : Measurable L := hL.continuous.measurable
  set T : ℕ → Vd d → ℝ := fun n => {x | (n : ℝ) + 1 ≤ L x}.indicator (fun x => ‖u x‖ ^ 2)
    with hT
  have hu2i := integrable_normSq hu2
  have hTi : ∀ n, Integrable (T n) volume := fun n =>
    hu2i.indicator (measurableSet_le measurable_const hLm)
  -- the bound for each `n`
  have hbound : ∀ n, ∫ x, ‖u x‖ ^ 2 ≤ (2 * K0 ^ 2 + 2) * ∫ x, T n x := by
    intro n
    set R : ℝ := (n : ℝ) + 1 with hR
    have hR0 : 0 < R := by positivity
    set χ := lyapCut L R with hχ
    have hχs := contDiff_lyapCut hL R
    have hχ1 : ∀ x, |χ x| ≤ 1 := fun x => by
      have := theta_mem (L x / R)
      rw [abs_le]; constructor <;> simp only [hχ, lyapCut] <;> linarith
    have hχR : ∀ x, x ∉ Metric.closedBall (0 : Vd d) (2 * R) → χ x = 0 := by
      intro x hx
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
      simp only [hχ, lyapCut]
      refine theta_eq_zero ?_
      rw [abs_of_nonneg (div_nonneg (hL0 x) hR0.le), le_div_iff₀ hR0]
      linarith [hLn x]
    have hkato := kato_cutoff_ineq S hE hEr hE1 hu2 hum hz hweak hχs hχ1 hχR
    have hcxb : ∀ x, ‖cx χ x‖ ≤ 1 := fun x => by rw [norm_cx]; exact hχ1 x
    -- the derivative of the cut-off lives where `L ≥ R` and is bounded by `K0`
    have hD : ∀ x, ‖Df S (cx χ) x‖ ≤ {x | R ≤ L x}.indicator (fun _ => K0) x := by
      intro x
      rw [hχ, Df_lyapCut S hL R x, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      by_cases hx : R ≤ L x
      · rw [Set.indicator_of_mem (show x ∈ {x | R ≤ L x} from hx)]
        by_cases hx2 : L x ≤ 2 * R
        · rw [abs_div, abs_of_pos hR0]
          have h1 := hM (L x / R)
          have h2 := hLf x
          have h3 : c₀ * L x ≤ |c₀| * (2 * R) := by
            calc c₀ * L x ≤ |c₀| * L x := mul_le_mul_of_nonneg_right (le_abs_self _) (hL0 x)
              _ ≤ |c₀| * (2 * R) := mul_le_mul_of_nonneg_left hx2 (abs_nonneg _)
          calc |deriv theta (L x / R)| / R * ‖Df S (cx L) x‖
              ≤ M / R * (|c₀| * (2 * R)) := by
                gcongr
                exact h2.trans h3
            _ = K0 := by rw [hK0]; field_simp
        · rw [deriv_theta_eq_zero (Or.inr ?_)]
          · simp [hK0n]
          · rw [abs_of_nonneg (div_nonneg (hL0 x) hR0.le), lt_div_iff₀ hR0]
            linarith
      · rw [Set.indicator_of_notMem (show x ∉ {x | R ≤ L x} from hx)]
        rw [deriv_theta_eq_zero (Or.inl ?_)]
        · simp
        · rw [abs_of_nonneg (div_nonneg (hL0 x) hR0.le), div_lt_one hR0]
          linarith
    have hDC : Continuous (Df S (cx χ)) := (contDiff_Df S (contDiff_cx hχs)).continuous
    have hDb : ∀ x, ‖Df S (cx χ) x‖ ≤ K0 := fun x => (hD x).trans (by
      by_cases hx : x ∈ {x | R ≤ L x}
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]; exact hK0n)
    have mV : MemLp (fun x => cx χ x * u x) 2 volume :=
      memLp_bdd_mul (contDiff_cx hχs).continuous hcxb hu2
    have mQ : MemLp (fun x => Df S (cx χ) x * u x) 2 volume := memLp_bdd_mul hDC hDb hu2
    have hsq : l2n (fun x => cx χ x * u x) ^ 2 ≤ l2n (fun x => Df S (cx χ) x * u x) ^ 2 :=
      pow_le_pow_left₀ (l2n_nonneg _) hkato 2
    rw [l2n_sq mV, l2n_sq mQ] at hsq
    have hTn : T n = {x | R ≤ L x}.indicator (fun x => ‖u x‖ ^ 2) := rfl
    -- pointwise bounds
    have hp1 : ∀ x, ‖Df S (cx χ) x * u x‖ ^ 2 ≤ K0 ^ 2 * T n x := by
      intro x
      rw [hTn, norm_mul, mul_pow]
      by_cases hx : x ∈ {x | R ≤ L x}
      · rw [Set.indicator_of_mem hx]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hDb x) 2)
          (by positivity)
      · have h0 : ‖Df S (cx χ) x‖ = 0 := le_antisymm
          ((hD x).trans (by rw [Set.indicator_of_notMem hx])) (norm_nonneg _)
        rw [Set.indicator_of_notMem hx, h0]; simp
    have hp2 : ∀ x, ‖u x‖ ^ 2 ≤ 2 * ‖cx χ x * u x‖ ^ 2 + 2 * T n x := by
      intro x
      have hsplit : u x = cx χ x * u x + (1 - cx χ x) * u x := by ring
      have h1 : ‖(1 - cx χ x) * u x‖ ^ 2 ≤ T n x := by
        rw [hTn]
        by_cases hx : x ∈ {x | R ≤ L x}
        · rw [Set.indicator_of_mem hx, norm_mul, mul_pow]
          have : ‖1 - cx χ x‖ ≤ 1 := by
            have hm := theta_mem (L x / R)
            simp only [hχ, cx, lyapCut]
            rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
              Real.norm_of_nonneg (by linarith)]
            linarith
          have : ‖1 - cx χ x‖ ^ 2 ≤ 1 := by
            calc ‖1 - cx χ x‖ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
              _ = 1 := one_pow 2
          nlinarith [sq_nonneg ‖u x‖]
        · rw [Set.indicator_of_notMem hx]
          have hx' : L x < R := lt_of_not_ge hx
          have h1 : cx χ x = 1 := by
            simp only [hχ, cx, lyapCut]
            rw [theta_eq_one]
            · simp
            · rw [abs_of_nonneg (div_nonneg (hL0 x) hR0.le), div_le_one hR0]
              exact hx'.le
          rw [h1]; simp
      calc ‖u x‖ ^ 2 = ‖cx χ x * u x + (1 - cx χ x) * u x‖ ^ 2 := by rw [← hsplit]
        _ ≤ (‖cx χ x * u x‖ + ‖(1 - cx χ x) * u x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
        _ ≤ 2 * ‖cx χ x * u x‖ ^ 2 + 2 * ‖(1 - cx χ x) * u x‖ ^ 2 := by
          nlinarith [sq_nonneg (‖cx χ x * u x‖ - ‖(1 - cx χ x) * u x‖)]
        _ ≤ 2 * ‖cx χ x * u x‖ ^ 2 + 2 * T n x := by linarith
    have iV := integrable_normSq mV
    have iQ := integrable_normSq mQ
    have hI1 : ∫ x, ‖u x‖ ^ 2 ≤ ∫ x, (2 * ‖cx χ x * u x‖ ^ 2 + 2 * T n x) :=
      integral_mono hu2i ((iV.const_mul 2).add ((hTi n).const_mul 2)) hp2
    have hI2 : ∫ x, ‖Df S (cx χ) x * u x‖ ^ 2 ≤ ∫ x, K0 ^ 2 * T n x :=
      integral_mono iQ ((hTi n).const_mul _) hp1
    rw [integral_add (iV.const_mul 2) ((hTi n).const_mul 2), integral_const_mul,
      integral_const_mul] at hI1
    rw [integral_const_mul] at hI2
    nlinarith
  -- the tails tend to zero
  have htail : Tendsto (fun n => ∫ x, T n x) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun x => ‖u x‖ ^ 2)
      (F := T) (f := fun _ => (0 : ℝ)) (fun n => (hTi n).aestronglyMeasurable) hu2i
      (fun n => Filter.Eventually.of_forall fun x => by
        simp only [hT, Real.norm_eq_abs]
        by_cases hx : x ∈ {x | (n : ℝ) + 1 ≤ L x}
        · rw [Set.indicator_of_mem hx, abs_of_nonneg (by positivity)]
        · rw [Set.indicator_of_notMem hx, abs_zero]; positivity)
      (Filter.Eventually.of_forall fun x => by
        refine tendsto_const_nhds.congr' ?_
        obtain ⟨N, hN⟩ := exists_nat_gt (L x)
        filter_upwards [Filter.eventually_ge_atTop N] with n hn
        have : L x < (n : ℝ) + 1 := by
          have : (N : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        simp only [hT]
        rw [Set.indicator_of_notMem (show x ∉ {x | (n : ℝ) + 1 ≤ L x} by
          simp only [Set.mem_setOf_eq, not_le]; exact this)])
    simpa using h
  have hlim : Tendsto (fun n => (2 * K0 ^ 2 + 2) * ∫ x, T n x) atTop (𝓝 0) := by
    simpa using htail.const_mul (2 * K0 ^ 2 + 2)
  have hle : ∫ x, ‖u x‖ ^ 2 ≤ 0 := ge_of_tendsto' hlim hbound
  have h0 : ∫ x, ‖u x‖ ^ 2 = 0 := le_antisymm hle (integral_nonneg fun x => by positivity)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hu2i).1 h0
  filter_upwards [hae] with x hx
  simpa using hx

end

end BookProof.KvnKato
