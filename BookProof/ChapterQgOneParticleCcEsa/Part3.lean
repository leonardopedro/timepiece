import Mathlib
import BookProof.ChapterScalaronCoreEsa
import BookProof.ChapterHermiteQuadraticEsa
import BookProof.ChapterDirectSumEsa
import BookProof.ChapterQgOneParticleCcEsa.Part2

/-!
# The one-particle `R + αR²` Hamiltonian on the compactly supported smooth core

`CONSOLIDATED_PLAN.md` §10.6.1 asks for essential self-adjointness of the one-particle
gauge-fixed Hamiltonian `−Δ + W` on a dense core of `L²(ℝᵈ)`, and its §10.6.3 "definition of
done" names the Gauss–polynomial (Hermite) core.  For the *physics* the natural core is the
smaller one of **smooth compactly supported** functions: essential self-adjointness there is
strictly stronger (a smaller core means fewer test vectors in the deficiency equation), it
implies the statement on every larger core, and it is the core one uses when second
quantizing, since the finite-particle Fock core is built from it.

This module proves that statement, by transporting the Gauss-core theorems of
`BookProof.ChapterHermiteQuadraticEsa` down to the compactly supported core.

## The mechanism

`deficiencyTrivialAt_of_graphApprox` is the abstract step: if every vector of a domain `D₁`
is approximated, in the graph norm, by vectors of a *possibly unrelated* domain `D₂`, then
triviality of the deficiency spaces on `D₁` implies triviality on `D₂`.  (The corresponding
statement for `D₂ ≤ D₁` is `FarisLavine.essentiallySelfAdjointOn_restrict_of_graph_core`;
here neither core contains the other, since a Gauss polynomial is never compactly
supported.)

The analytic input is the cut-off estimate: for `ψ = p(x)e^{−‖x‖²/4}` and `χ_R(x) = χ(x/R)`
a scaled bump,

`(−Δ + W)(χ_R ψ) − (−Δ + W)ψ = (χ_R − 1)(−Δψ + Wψ) − 2∑ⱼ ∂ⱼχ_R ∂ⱼψ − (Δχ_R) ψ`,

whose three terms are `o(1)` in `L²`: the first by dominated convergence, the second and
third because `‖∂χ_R‖ ≤ C/R` and `‖∂²χ_R‖ ≤ C/R²` while `∂ⱼψ, ψ ∈ L²`.

## What is proved

* `ccHam` — the Hamiltonian `−Δ + W` on the compactly supported smooth core `ccDomain`,
  with `ccHam_symmetricOn`;
* `exists_cc_graph_approx` — the cut-off approximation;
* `ccHam_essentiallySelfAdjoint_of_core` — the transfer theorem;
* **`qgOneParticleCc_esa`** — `−Δ + ‖x‖²/4 + V` is essentially self-adjoint on the compactly
  supported smooth core of `L²(ℝᵈ)` for every smooth `V` with `|V| ≤ a‖x‖²/4 + b`, `a < 1`,
  with **`qgOneParticleCc_stone_flow`** its unitary group;
* `confVCc_esa`, `sectorQuadCc_esa` — the conformal-mode (`d = 1`) and reduced
  two-variable-sector (`d = 2`) instances of the gauge-fixed `R + αR²` Hamiltonian;
* `qgFockCc_esa` — the finite-particle statement: the `n`-particle Hamiltonian
  `∑ₖ (−Δ_k + W(x_k))` on `L²((ℝᵈ)ⁿ)` is of the same form, so it too is essentially
  self-adjoint on the compactly supported smooth core.

**Honest boundary.**  The potential class is the quadratic one of
`BookProof.ChapterHermiteQuadraticEsa` (the harmonic conformal-mode parabola plus a
strictly subquadratic perturbation).  The exponentially growing scalaron wall is *not*
covered: what is transported here is exactly what the Gauss core provides.
-/

namespace BookProof.QgOneParticleCc

open MeasureTheory SchwartzMap Complex MvPolynomial
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.HermiteQuadraticEsa
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.DirectSumEsa

noncomputable section

variable {d : ℕ}
/-! ## 6. The cut-off approximation of a Gauss-core vector -/

/-- The cut-off of a core vector. -/
def cutFun (R : ℝ) (p : MvPolynomial (Fin d) ℂ) : Vd d → ℂ :=
  fun x => ((cut d R x : ℝ) : ℂ) * pgFun p x

theorem contDiff_cutFun (R : ℝ) (p : MvPolynomial (Fin d) ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutFun R p) :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_cut R)).mul (contDiff_pgFun p)

theorem hasCompactSupport_cutFun {R : ℝ} (hR : 0 < R) (p : MvPolynomial (Fin d) ℂ) :
    HasCompactSupport (cutFun R p) := by
  have h : HasCompactSupport (fun x : Vd d => ((cut d R x : ℝ) : ℂ)) :=
    (hasCompactSupport_cut hR).comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  exact h.mul_right

/-- The cut-off of a core vector, as an element of the compactly supported smooth core. -/
def cutCore (R : ℝ) (hR : 0 < R) (p : MvPolynomial (Fin d) ℂ) : ccSchwartz (Vd d) :=
  ⟨(hasCompactSupport_cutFun hR p).toSchwartzMap (contDiff_cutFun R p),
    hasCompactSupport_cutFun hR p⟩

@[simp] theorem cutCore_apply (R : ℝ) (hR : 0 < R) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    ((cutCore R hR p : ccSchwartz (Vd d)) : 𝓢(Vd d, ℂ)) x
      = ((cut d R x : ℝ) : ℂ) * pgFun p x := rfl

/-! ### `L²` tails -/

/-- **The `L²` tail of a square-integrable function vanishes**: `∫_{‖x‖ > n} |g|² → 0`. -/
theorem tendsto_tailNorm {g : Vd d → ℝ} (hg : MemLp g 2 (volume : Measure (Vd d))) :
    Filter.Tendsto
      (fun n : ℕ => (eLpNorm (({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) 2
        (volume : Measure (Vd d))).toReal) Filter.atTop (nhds 0) := by
  set μ : Measure (Vd d) := volume with hμ
  have hmeasS : ∀ n : ℕ, MeasurableSet ({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ) :=
    fun n => (measurableSet_le (by fun_prop) measurable_const).compl
  have hrw : ∀ n : ℕ, eLpNorm (({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) 2 μ
      = (∫⁻ z, ‖(({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      show ((2 : ENNReal).toReal) = (2 : ℝ) by norm_num]
  have hlim : Filter.Tendsto
      (fun n : ℕ => ∫⁻ z, ‖(({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) z‖ₑ ^ (2 : ℝ) ∂μ)
      Filter.atTop (nhds 0) := by
    have hdom : ∀ n : ℕ,
        (fun z => ‖(({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) z‖ₑ ^ (2 : ℝ))
          ≤ᵐ[μ] fun z => ‖g z‖ₑ ^ (2 : ℝ) := by
      intro n
      filter_upwards with z
      by_cases h : z ∈ ({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ)
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h]; simp
    have hbdd : ∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ) ∂μ ≠ ⊤ := by
      intro hcon
      have h := hg.2
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at h
      rw [show ((2 : ENNReal).toReal) = (2 : ℝ) by norm_num, hcon] at h
      simp [ENNReal.top_rpow_of_pos] at h
    have hae : ∀ᵐ z ∂μ, Filter.Tendsto
        (fun n : ℕ => ‖(({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) z‖ₑ ^ (2 : ℝ))
        Filter.atTop (nhds 0) := by
      filter_upwards with z
      obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds (f₁ := fun _ : ℕ => (0 : ENNReal))
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hz : z ∈ {z : Vd d | ‖z‖ ≤ (n : ℝ)} := le_trans hN (by exact_mod_cast hn)
      rw [Set.indicator_of_notMem (by simpa using hz)]
      simp
    have hdct := tendsto_lintegral_of_dominated_convergence' (μ := μ) (f := fun _ => (0 : ENNReal))
      (fun z => ‖g z‖ₑ ^ (2 : ℝ))
      (fun n => ((hg.1.indicator (hmeasS n)).enorm).pow_const _)
      hdom hbdd hae
    simpa using hdct
  have h2 : Filter.Tendsto
      (fun n : ℕ => eLpNorm (({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) 2 μ)
      Filter.atTop (nhds 0) := by
    simp_rw [hrw]
    simpa using ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hlim
  simpa using (ENNReal.tendsto_toReal (by simp)).comp h2

/-- A vector dominated by the tail of a square-integrable majorant has small norm. -/
theorem norm_le_tailNorm {u : L2d d} {S : Set (Vd d)} {g : Vd d → ℝ}
    (hg : MemLp g 2 (volume : Measure (Vd d)))
    (h : ∀ᵐ z ∂(volume : Measure (Vd d)), ‖(u : Vd d → ℂ) z‖ ≤ ‖S.indicator g z‖) :
    ‖u‖ ≤ (eLpNorm (S.indicator g) 2 (volume : Measure (Vd d))).toReal := by
  rw [Lp.norm_def]
  exact ENNReal.toReal_mono ((eLpNorm_indicator_le g).trans_lt hg.2).ne (eLpNorm_mono_ae h)

/-! ### The cut-off is locally constant inside the ball -/

theorem cut_eventuallyEq_one {R : ℝ} {x : Vd d} (hx : ‖x‖ < R) :
    (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) =ᶠ[nhds x] fun _ => (1 : ℂ) := by
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg x) hx
  have hopen : IsOpen {y : Vd d | ‖y‖ < R} := isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds hx] with y hy
  rw [cut_eq_one hRpos (le_of_lt hy)]
  norm_num

theorem dcoord_cut_eq_zero {R : ℝ} {x : Vd d} (hx : ‖x‖ < R) (j : Fin d) :
    dcoord j (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) x = 0 := by
  simp only [dcoord]
  rw [(cut_eventuallyEq_one hx).fderiv_eq]
  simp

theorem lapC_cut_eq_zero {R : ℝ} {x : Vd d} (hx : ‖x‖ < R) :
    lapC (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) x = 0 := by
  have hopen : IsOpen {y : Vd d | ‖y‖ < R} := isOpen_lt (by fun_prop) continuous_const
  refine Finset.sum_eq_zero fun j _ => ?_
  have hev : dcoord j (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact dcoord_cut_eq_zero hy j
  simp only [dcoord]
  rw [hev.fderiv_eq]
  simp

/-! ### Representatives of the two Hamiltonians -/

theorem kinCc_apply (f : ccSchwartz (Vd d)) :
    kinCc d (ccEquiv (Vd d) f)
      = (kinOp d (f : 𝓢(Vd d, ℂ))).toLp 2 (volume : Measure (Vd d)) := by
  have hincl : Submodule.inclusion (ccDomain_le_schwartzDomain (E := Vd d)) (ccEquiv (Vd d) f)
      = schwartzEquiv (Vd d) ((f : 𝓢(Vd d, ℂ))) := Subtype.ext rfl
  simp only [kinCc, LinearMap.coe_comp, Function.comp_apply, hincl, opL2_apply]

theorem ccHam_coeFn (W : Vd d → ℝ) (hWs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (f : ccSchwartz (Vd d)) :
    ((ccHam W hWs (ccEquiv (Vd d) f) : L2d d) : Vd d → ℂ)
      =ᵐ[volume] fun z => -lapC (fun y : Vd d => (f : 𝓢(Vd d, ℂ)) y) z
        + ((W z : ℝ) : ℂ) * (f : 𝓢(Vd d, ℂ)) z := by
  have h1 : ccHam W hWs (ccEquiv (Vd d) f)
      = (kinOp d (f : 𝓢(Vd d, ℂ))).toLp 2 (volume : Measure (Vd d))
        + (mulCc W hWs f).toLp 2 (volume : Measure (Vd d)) := by
    simp only [ccHam, LinearMap.add_apply, kinCc_apply, opCc_apply]
  rw [h1]
  filter_upwards [Lp.coeFn_add ((kinOp d (f : 𝓢(Vd d, ℂ))).toLp 2 (volume : Measure (Vd d)))
      ((mulCc W hWs f).toLp 2 (volume : Measure (Vd d))),
    (kinOp d (f : 𝓢(Vd d, ℂ))).coeFn_toLp 2 (volume : Measure (Vd d)),
    (mulCc W hWs f).coeFn_toLp 2 (volume : Measure (Vd d))] with z hz h2 h3
  rw [hz, Pi.add_apply, h2, h3, kinOp_apply_eq, mulCc_apply]

theorem hamCore_coeFn (W : Vd d → ℝ) (hWc : Continuous W) (hWb : ExpBounded W)
    (p : MvPolynomial (Fin d) ℂ) :
    ((hamCore W hWc hWb ⟨pgLp p, pgLp_mem_core p⟩ : L2d d) : Vd d → ℂ)
      =ᵐ[volume] fun z => pgFun (kinPoly p) z + ((W z : ℝ) : ℂ) * pgFun p z := by
  rw [hamCore_pgLp]
  simp only [hamPoly]
  filter_upwards [Lp.coeFn_add (pgLp (kinPoly p)) (potLp W hWc hWb p), pgLp_coeFn (kinPoly p),
    potLp_coeFn W hWc hWb p] with z hz h2 h3
  rw [hz, Pi.add_apply, h2, h3]

/-! ### The pointwise error of the cut-off -/

/-- The square-integrable majorant of all the cut-off error terms. -/
def majorant (W : Vd d → ℝ) (K : ℝ) (p : MvPolynomial (Fin d) ℂ) (z : Vd d) : ℝ :=
  ‖pgFun (kinPoly p) z‖ + K * ‖pgFun p z‖
    + 2 * K * (∑ j : Fin d, ‖pgFun (coreD j p) z‖) + ‖((W z : ℝ) : ℂ) * pgFun p z‖

theorem sum_norm_coreD_nonneg (p : MvPolynomial (Fin d) ℂ) (z : Vd d) :
    0 ≤ ∑ j : Fin d, ‖pgFun (coreD j p) z‖ :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem majorant_nonneg (W : Vd d → ℝ) {K : ℝ} (hK : 0 ≤ K) (p : MvPolynomial (Fin d) ℂ)
    (z : Vd d) : 0 ≤ majorant W K p z :=
  add_nonneg (add_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg hK (norm_nonneg _)))
    (mul_nonneg (by linarith) (sum_norm_coreD_nonneg p z))) (norm_nonneg _)

theorem memLp_majorant (W : Vd d → ℝ) (hWc : Continuous W) (hWb : ExpBounded W) (K : ℝ)
    (p : MvPolynomial (Fin d) ℂ) :
    MemLp (majorant W K p) 2 (volume : Measure (Vd d)) := by
  have h1 : MemLp (fun z : Vd d => ‖pgFun (kinPoly p) z‖) 2 (volume : Measure (Vd d)) :=
    (memLp_pgFun (kinPoly p)).norm
  have h2 : MemLp (fun z : Vd d => K * ‖pgFun p z‖) 2 (volume : Measure (Vd d)) :=
    (memLp_pgFun p).norm.const_mul K
  have h3 : MemLp (fun z : Vd d => ∑ j : Fin d, ‖pgFun (coreD j p) z‖) 2
      (volume : Measure (Vd d)) := by
    have h := memLp_finset_sum' (μ := (volume : Measure (Vd d))) (p := 2)
      (Finset.univ : Finset (Fin d))
      (f := fun (j : Fin d) (z : Vd d) => ‖pgFun (coreD j p) z‖)
      (fun j _ => (memLp_pgFun (coreD j p)).norm)
    have heq : (fun z : Vd d => ∑ j : Fin d, ‖pgFun (coreD j p) z‖)
        = ∑ j : Fin d, (fun z : Vd d => ‖pgFun (coreD j p) z‖) := by
      funext z
      simp
    rw [heq]
    exact h
  have h4 : MemLp (fun z : Vd d => ‖((W z : ℝ) : ℂ) * pgFun p z‖) 2
      (volume : Measure (Vd d)) := (memLp_mul_pgFun_of_expBounded hWc hWb p).norm
  exact ((h1.add h2).add (h3.const_mul (2 * K))).add h4

/-- The pointwise graph error made by cutting a Gauss-core vector off at radius `R`. -/
def cutErr (W : Vd d → ℝ) (R : ℝ) (p : MvPolynomial (Fin d) ℂ) (z : Vd d) : ℂ :=
  (((cut d R z : ℝ) : ℂ) - 1) * pgFun (kinPoly p) z
    - pgFun p z * lapC (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z
    - 2 * ∑ j : Fin d,
        dcoord j (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z * pgFun (coreD j p) z
    + (((cut d R z : ℝ) : ℂ) - 1) * (((W z : ℝ) : ℂ) * pgFun p z)

/-- The pointwise commutator identity for the cut-off. -/
theorem cut_error_eq (W : Vd d → ℝ) {R : ℝ} (p : MvPolynomial (Fin d) ℂ) (z : Vd d) :
    -lapC (cutFun R p) z + ((W z : ℝ) : ℂ) * cutFun R p z
        - (pgFun (kinPoly p) z + ((W z : ℝ) : ℂ) * pgFun p z)
      = cutErr W R p z := by
  have hcutC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_cut R)
  have hlap := lapC_mul hcutC (contDiff_pgFun p) z
  have hpsi : lapC (pgFun p) z = -pgFun (kinPoly p) z := congrFun (lapC_pgFun p) z
  have hcutFun : cutFun R p = fun y : Vd d => ((cut d R y : ℝ) : ℂ) * pgFun p y := rfl
  rw [hcutFun, hlap, hpsi]
  simp only [dcoord_pgFun, cutErr]
  ring

/-- Inside the ball of radius `R` the cut-off does nothing at all. -/
theorem cutErr_eq_zero (W : Vd d → ℝ) {R : ℝ} (p : MvPolynomial (Fin d) ℂ) {z : Vd d}
    (hz : ‖z‖ < R) : cutErr W R p z = 0 := by
  have h1 : ((cut d R z : ℝ) : ℂ) = 1 := by
    rw [cut_eq_one (lt_of_le_of_lt (norm_nonneg z) hz) (le_of_lt hz)]
    norm_num
  have h2 : lapC (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z = 0 := lapC_cut_eq_zero hz
  have h3 : ∑ j : Fin d,
      dcoord j (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z * pgFun (coreD j p) z = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [dcoord_cut_eq_zero hz j, zero_mul]
  simp only [cutErr, h1, h2, h3]
  ring

/-- **The pointwise error estimate.** -/
theorem norm_cutErr_le (W : Vd d → ℝ) {C K R : ℝ} (hC0 : 0 ≤ C) (hCK : C ≤ K) (hR1 : 1 ≤ R)
    (p : MvPolynomial (Fin d) ℂ) (z : Vd d)
    (hd1 : ∀ j : Fin d, ‖dcoord j (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z‖ ≤ C / R)
    (hd2 : ‖lapC (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z‖ ≤ C / R ^ 2) :
    ‖cutErr W R p z‖ ≤ majorant W K p z := by
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
  have hCRK : C / R ≤ K := by
    have h : C / R ≤ C := by
      rw [div_le_iff₀ hRpos]
      nlinarith
    linarith
  have hCR2K : C / R ^ 2 ≤ K := by
    have hR2 : (1 : ℝ) ≤ R ^ 2 := by nlinarith
    have h : C / R ^ 2 ≤ C := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  obtain ⟨hc0, hc1⟩ := cut_mem_Icc (d := d) (R := R) z
  have habs : |cut d R z - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hcoe : ((cut d R z : ℝ) : ℂ) - 1 = (((cut d R z - 1 : ℝ)) : ℂ) := by push_cast; ring
  set e1 : ℂ := (((cut d R z : ℝ) : ℂ) - 1) * pgFun (kinPoly p) z with he1
  set e2 : ℂ := pgFun p z * lapC (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z with he2
  set e3 : ℂ := 2 * ∑ j : Fin d,
      dcoord j (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z * pgFun (coreD j p) z with he3
  set e4 : ℂ := (((cut d R z : ℝ) : ℂ) - 1) * (((W z : ℝ) : ℂ) * pgFun p z) with he4
  have hsplit : ‖e1 - e2 - e3 + e4‖ ≤ ‖e1‖ + ‖e2‖ + ‖e3‖ + ‖e4‖ := by
    have s1 := norm_add_le (e1 - e2 - e3) e4
    have s2 := norm_sub_le (e1 - e2) e3
    have s3 := norm_sub_le e1 e2
    linarith
  have hb1 : ‖e1‖ ≤ ‖pgFun (kinPoly p) z‖ := by
    rw [he1, hcoe, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [norm_nonneg (pgFun (kinPoly p) z)]
  have hb2 : ‖e2‖ ≤ K * ‖pgFun p z‖ := by
    rw [he2, norm_mul]
    have h := mul_le_mul_of_nonneg_left (le_trans hd2 hCR2K) (norm_nonneg (pgFun p z))
    calc ‖pgFun p z‖ * ‖lapC (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z‖
        ≤ ‖pgFun p z‖ * K := h
      _ = K * ‖pgFun p z‖ := by ring
  have hb3 : ‖e3‖ ≤ 2 * K * (∑ j : Fin d, ‖pgFun (coreD j p) z‖) := by
    have hinner : ‖∑ j : Fin d,
        dcoord j (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z * pgFun (coreD j p) z‖
          ≤ ∑ j : Fin d, K * ‖pgFun (coreD j p) z‖ := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (le_trans (hd1 j) hCRK) (norm_nonneg _)
    rw [← Finset.mul_sum] at hinner
    rw [he3, norm_mul]
    have h2c : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2c]
    nlinarith [sum_norm_coreD_nonneg p z]
  have hb4 : ‖e4‖ ≤ ‖((W z : ℝ) : ℂ) * pgFun p z‖ := by
    rw [he4, hcoe, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [norm_nonneg (((W z : ℝ) : ℂ) * pgFun p z)]
  have hgoal : cutErr W R p z = e1 - e2 - e3 + e4 := rfl
  rw [hgoal, majorant]
  linarith

/-- The vector itself moves by at most the majorant. -/
theorem norm_cutFun_sub_le (W : Vd d → ℝ) {K R : ℝ} (hK1 : 1 ≤ K)
    (p : MvPolynomial (Fin d) ℂ) (z : Vd d) :
    ‖cutFun R p z - pgFun p z‖ ≤ majorant W K p z := by
  obtain ⟨hc0, hc1⟩ := cut_mem_Icc (d := d) (R := R) z
  have hfac : cutFun R p z - pgFun p z = (((cut d R z - 1 : ℝ)) : ℂ) * pgFun p z := by
    simp only [cutFun]
    push_cast
    ring
  have hle : ‖cutFun R p z - pgFun p z‖ ≤ ‖pgFun p z‖ := by
    rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have habs : |cut d R z - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    nlinarith [norm_nonneg (pgFun p z)]
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hrest : 0 ≤ 2 * K * (∑ j : Fin d, ‖pgFun (coreD j p) z‖) :=
    mul_nonneg (by linarith) (sum_norm_coreD_nonneg p z)
  have hKmul : ‖pgFun p z‖ ≤ K * ‖pgFun p z‖ := by nlinarith [norm_nonneg (pgFun p z)]
  rw [majorant]
  have hn1 : 0 ≤ ‖pgFun (kinPoly p) z‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖((W z : ℝ) : ℂ) * pgFun p z‖ := norm_nonneg _
  linarith

/-- **The cut-off approximation.**  Every Gauss–polynomial core vector is approximated, in
the graph norm of `−Δ + W`, by compactly supported smooth functions. -/
theorem exists_cc_graph_approx (W : Vd d → ℝ) (hWs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hWc : Continuous W) (hWb : ExpBounded W)
    (x : polyGaussCore (d := d)) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ccDomain (Vd d), ‖(y : L2d d) - (x : L2d d)‖ < ε ∧
      ‖ccHam W hWs y - hamCore W hWc hWb x‖ < ε := by
  classical
  obtain ⟨p, hp⟩ := x.2
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  subst hx
  obtain ⟨C, hC0, hCbound⟩ := exists_cut_derivative_bounds d
  have hK1 : (1 : ℝ) ≤ C + 1 := by linarith
  have hGmem := memLp_majorant W hWc hWb (C + 1) p
  have hGnn := majorant_nonneg W (K := C + 1) (by linarith) p
  -- choose a radius beyond which the tail of the majorant is small
  obtain ⟨n, hnlt, hn1⟩ :=
    (((tendsto_tailNorm hGmem).eventually (gt_mem_nhds hε)).and
      (Filter.eventually_ge_atTop 1)).exists
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hRpos : (0 : ℝ) < 2 * (n : ℝ) := by linarith
  have hR1 : (1 : ℝ) ≤ 2 * (n : ℝ) := by linarith
  have hball : ∀ z : Vd d, ‖z‖ ≤ (n : ℝ) → ‖z‖ < 2 * (n : ℝ) := by
    intro z hz
    linarith
  refine ⟨ccEquiv (Vd d) (cutCore (2 * (n : ℝ)) hRpos p), ?_, ?_⟩
  · -- the vectors themselves are close
    refine lt_of_le_of_lt
      (norm_le_tailNorm (S := {z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ) hGmem ?_) hnlt
    filter_upwards [Lp.coeFn_sub
        ((ccEquiv (Vd d) (cutCore (2 * (n : ℝ)) hRpos p) : ccDomain (Vd d)) : L2d d) (pgLp p),
      ((cutCore (2 * (n : ℝ)) hRpos p : ccSchwartz (Vd d)) : 𝓢(Vd d, ℂ)).coeFn_toLp 2
        (volume : Measure (Vd d)),
      pgLp_coeFn p] with z h1 h2 h3
    have hstep : ((((ccEquiv (Vd d) (cutCore (2 * (n : ℝ)) hRpos p) : ccDomain (Vd d)) : L2d d)
        - (pgLp p) : L2d d) : Vd d → ℂ) z = cutFun (2 * (n : ℝ)) p z - pgFun p z := by
      rw [h1, Pi.sub_apply, h3]
      rw [show (((ccEquiv (Vd d) (cutCore (2 * (n : ℝ)) hRpos p) : ccDomain (Vd d)) : L2d d) :
          Vd d → ℂ) z = cutFun (2 * (n : ℝ)) p z from h2]
    rw [hstep]
    by_cases hz : ‖z‖ ≤ (n : ℝ)
    · have hzero : cutFun (2 * (n : ℝ)) p z - pgFun p z = 0 := by
        simp only [cutFun]
        rw [cut_eq_one hRpos (le_of_lt (hball z hz))]
        push_cast
        ring
      rw [hzero, Set.indicator_of_notMem (by simpa using hz)]
      simp
    · rw [Set.indicator_of_mem (by simpa using hz), Real.norm_eq_abs, abs_of_nonneg (hGnn z)]
      exact norm_cutFun_sub_le W hK1 p z
  · -- the images are close
    refine lt_of_le_of_lt
      (norm_le_tailNorm (S := {z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ) hGmem ?_) hnlt
    filter_upwards [Lp.coeFn_sub
        (ccHam W hWs (ccEquiv (Vd d) (cutCore (2 * (n : ℝ)) hRpos p)))
        (hamCore W hWc hWb ⟨pgLp p, pgLp_mem_core p⟩),
      ccHam_coeFn W hWs (cutCore (2 * (n : ℝ)) hRpos p),
      hamCore_coeFn W hWc hWb p] with z h1 h2 h3
    have hstep : ((ccHam W hWs (ccEquiv (Vd d) (cutCore (2 * (n : ℝ)) hRpos p))
        - hamCore W hWc hWb ⟨pgLp p, pgLp_mem_core p⟩ : L2d d) : Vd d → ℂ) z
        = cutErr W (2 * (n : ℝ)) p z := by
      rw [h1, Pi.sub_apply, h2, h3]
      exact cut_error_eq W p z
    rw [hstep]
    by_cases hz : ‖z‖ ≤ (n : ℝ)
    · rw [cutErr_eq_zero W p (hball z hz), Set.indicator_of_notMem (by simpa using hz)]
      simp
    · rw [Set.indicator_of_mem (by simpa using hz), Real.norm_eq_abs, abs_of_nonneg (hGnn z)]
      obtain ⟨hd1, hd2⟩ := hCbound (2 * (n : ℝ)) hR1 z
      exact norm_cutErr_le W hC0 (by linarith) hR1 p z hd1 hd2

end

end BookProof.QgOneParticleCc
