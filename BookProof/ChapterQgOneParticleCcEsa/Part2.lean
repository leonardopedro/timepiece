import Mathlib
import BookProof.ChapterScalaronCoreEsa
import BookProof.ChapterHermiteQuadraticEsa
import BookProof.ChapterDirectSumEsa
import BookProof.ChapterQgOneParticleCcEsa.Part1

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
/-! ## 5. The scaled cut-off family -/

/-- A fixed smooth bump: `1` on the unit ball, `0` outside the ball of radius `2`. -/
def bump (d : ℕ) : Vd d → ℝ := Classical.choose (exists_smooth_cutoff (V := Vd d) 1)

theorem bump_spec (d : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bump d) ∧ HasCompactSupport (bump d) ∧
      (∀ x : Vd d, ‖x‖ ≤ 1 → bump d x = 1) ∧ (∀ x : Vd d, bump d x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x : Vd d, 1 + 1 ≤ ‖x‖ → bump d x = 0) ∧ ∃ C : ℝ, ∀ x, ‖gradient (bump d) x‖ ≤ C :=
  Classical.choose_spec (exists_smooth_cutoff (V := Vd d) 1)

/-- The rescaled cut-off `χ_R(x) = χ(x/R)`. -/
def cut (d : ℕ) (R : ℝ) : Vd d → ℝ := fun x => bump d (R⁻¹ • x)

theorem contDiff_cut (R : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cut d R) :=
  (bump_spec d).1.comp (contDiff_id.const_smul (R⁻¹))

theorem hasCompactSupport_cut {R : ℝ} (hR : 0 < R) : HasCompactSupport (cut d R) := by
  have h := (bump_spec d).2.1
  have hne : (R⁻¹ : ℝ) ≠ 0 := by positivity
  simpa [cut] using h.comp_smul hne

theorem cut_eq_one {R : ℝ} (hR : 0 < R) {x : Vd d} (hx : ‖x‖ ≤ R) : cut d R x = 1 := by
  refine (bump_spec d).2.2.1 _ ?_
  rw [norm_smul]
  have : ‖(R⁻¹ : ℝ)‖ = R⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [this]
  rw [inv_mul_le_iff₀ hR]
  simpa using hx

theorem cut_mem_Icc {R : ℝ} (x : Vd d) : cut d R x ∈ Set.Icc (0 : ℝ) 1 := bump_spec d |>.2.2.2.1 _

/-- The scaling `x ↦ x/R`, as a continuous linear map. -/
def scaleCLM (d : ℕ) (R : ℝ) : Vd d →L[ℝ] Vd d := R⁻¹ • ContinuousLinearMap.id ℝ (Vd d)

@[simp] theorem scaleCLM_apply (R : ℝ) (x : Vd d) : scaleCLM d R x = R⁻¹ • x := rfl

theorem norm_scaleCLM_le {R : ℝ} (hR : 0 < R) : ‖scaleCLM d R‖ ≤ R⁻¹ := by
  refine (norm_smul_le (R⁻¹) (ContinuousLinearMap.id ℝ (Vd d))).trans ?_
  have h1 : ‖ContinuousLinearMap.id ℝ (Vd d)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h2 : ‖(R⁻¹ : ℝ)‖ = R⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h2]
  nlinarith [norm_nonneg (ContinuousLinearMap.id ℝ (Vd d)), inv_pos.mpr hR]

theorem cut_eq_comp (R : ℝ) : cut d R = fun y => bump d (scaleCLM d R y) := rfl

/-- The derivative of a real function, read through the complexification. -/
theorem dcoord_ofReal {u : Vd d → ℝ} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (j : Fin d)
    (x : Vd d) :
    dcoord j (fun y => ((u y : ℝ) : ℂ)) x = ((fderiv ℝ u x (kinDir d j) : ℝ) : ℂ) := by
  have hdiff : DifferentiableAt ℝ u x := (hu.differentiable (by simp)).differentiableAt
  have h : HasFDerivAt (fun y => ((u y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ u x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hdiff.hasFDerivAt
  simp [dcoord, h.fderiv]

/-- The first derivative of the scaled cut-off. -/
theorem fderiv_cut (R : ℝ) (x : Vd d) :
    fderiv ℝ (cut d R) x = (fderiv ℝ (bump d) (scaleCLM d R x)).comp (scaleCLM d R) := by
  have h1 : HasFDerivAt (bump d) (fderiv ℝ (bump d) (scaleCLM d R x)) (scaleCLM d R x) :=
    (((bump_spec d).1.differentiable (by simp)) _).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Vd d => scaleCLM d R y) (scaleCLM d R) x :=
    (scaleCLM d R).hasFDerivAt
  have h := h1.comp x h2
  rw [cut_eq_comp]
  exact h.fderiv

/-- The second derivative of the scaled cut-off, as a composition. -/
theorem fderiv_fderiv_cut (R : ℝ) (x : Vd d) :
    fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y) x
      = (((ContinuousLinearMap.compL ℝ (Vd d) (Vd d) ℝ).flip (scaleCLM d R)).comp
          ((fderiv ℝ (fun y : Vd d => fderiv ℝ (bump d) y) (scaleCLM d R x)).comp
            (scaleCLM d R))) := by
  have hfun : (fun y : Vd d => fderiv ℝ (cut d R) y)
      = fun y : Vd d =>
          ((ContinuousLinearMap.compL ℝ (Vd d) (Vd d) ℝ).flip (scaleCLM d R))
            (fderiv ℝ (bump d) (scaleCLM d R y)) := by
    funext y
    rw [fderiv_cut]
    rfl
  rw [hfun]
  have hbd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Vd d => fderiv ℝ (bump d) y) :=
    (bump_spec d).1.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl
  have h1 : HasFDerivAt (fun y : Vd d => fderiv ℝ (bump d) y)
      (fderiv ℝ (fun y : Vd d => fderiv ℝ (bump d) y) (scaleCLM d R x)) (scaleCLM d R x) :=
    ((hbd.differentiable (by simp)) _).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Vd d => scaleCLM d R y) (scaleCLM d R) x :=
    (scaleCLM d R).hasFDerivAt
  have h3 := h1.comp x h2
  have h4 := (((ContinuousLinearMap.compL ℝ (Vd d) (Vd d) ℝ).flip
    (scaleCLM d R)).hasFDerivAt).comp x h3
  exact h4.fderiv

/-- **The derivative bounds of the scaled cut-off**: `|∂ⱼχ_R| ≤ C/R` and `|Δχ_R| ≤ C/R²`,
with a constant that does not depend on `R`. -/
theorem exists_cut_derivative_bounds (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ x : Vd d,
      (∀ j : Fin d, ‖dcoord j (fun y => ((cut d R y : ℝ) : ℂ)) x‖ ≤ C / R) ∧
        ‖lapC (fun y => ((cut d R y : ℝ) : ℂ)) x‖ ≤ C / R ^ 2 := by
  classical
  -- bounds on the first and second derivative of the fixed bump
  have hbump := bump_spec d
  have hcs1 : HasCompactSupport (fun y : Vd d => fderiv ℝ (bump d) y) := hbump.2.1.fderiv ℝ
  have hcont1 : Continuous (fun y : Vd d => fderiv ℝ (bump d) y) :=
    hbump.1.continuous_fderiv (by simp)
  obtain ⟨C₁, hC₁⟩ := hcs1.exists_bound_of_continuous hcont1
  have hcs2 : HasCompactSupport (fun y : Vd d => fderiv ℝ (fun z : Vd d => fderiv ℝ (bump d) z) y)
    := hcs1.fderiv ℝ
  have hbd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Vd d => fderiv ℝ (bump d) y) :=
    hbump.1.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl
  have hcont2 : Continuous (fun y : Vd d => fderiv ℝ (fun z : Vd d => fderiv ℝ (bump d) z) y) :=
    hbd.continuous_fderiv (by simp)
  obtain ⟨C₂, hC₂⟩ := hcs2.exists_bound_of_continuous hcont2
  have hC₁nn : 0 ≤ C₁ := le_trans (norm_nonneg _) (hC₁ 0)
  have hC₂nn : 0 ≤ C₂ := le_trans (norm_nonneg _) (hC₂ 0)
  refine ⟨max C₁ (d * C₂), le_trans hC₁nn (le_max_left _ _), fun R hR x => ?_⟩
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hcutC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cut d R) := contDiff_cut R
  -- the first-derivative bound
  have hfirst : ∀ j : Fin d, ‖dcoord j (fun y => ((cut d R y : ℝ) : ℂ)) x‖ ≤ C₁ / R := by
    intro j
    rw [dcoord_ofReal hcutC j x]
    have hnorm : ‖kinDir d j‖ = 1 := by
      simp [kinDir, EuclideanSpace.norm_single]
    have hle : ‖fderiv ℝ (cut d R) x (kinDir d j)‖ ≤ ‖fderiv ℝ (cut d R) x‖ := by
      simpa [hnorm] using (fderiv ℝ (cut d R) x).le_opNorm (kinDir d j)
    have hcomp : ‖fderiv ℝ (cut d R) x‖ ≤ C₁ * R⁻¹ := by
      rw [fderiv_cut]
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      exact mul_le_mul (hC₁ _) (norm_scaleCLM_le hRpos) (norm_nonneg _) hC₁nn
    have : ‖((fderiv ℝ (cut d R) x (kinDir d j) : ℝ) : ℂ)‖
        = ‖fderiv ℝ (cut d R) x (kinDir d j)‖ := by
      simp [Complex.norm_real]
    rw [this]
    calc ‖fderiv ℝ (cut d R) x (kinDir d j)‖ ≤ ‖fderiv ℝ (cut d R) x‖ := hle
      _ ≤ C₁ * R⁻¹ := hcomp
      _ = C₁ / R := by field_simp
  -- the second-derivative (Laplacian) bound
  have hsecond : ∀ j : Fin d,
      ‖dcoord j (dcoord j (fun y => ((cut d R y : ℝ) : ℂ))) x‖ ≤ C₂ / R ^ 2 := by
    intro j
    have hcoe : dcoord j (fun z : Vd d => ((cut d R z : ℝ) : ℂ))
        = fun y : Vd d => ((fderiv ℝ (cut d R) y (kinDir d j) : ℝ) : ℂ) := by
      funext y
      exact dcoord_ofReal hcutC j y
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) := by
      have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Vd d => fderiv ℝ (cut d R) y) :=
        hcutC.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl
      exact (ContinuousLinearMap.apply ℝ ℝ (kinDir d j)).contDiff.comp hfd
    rw [hcoe, dcoord_ofReal hsm j x]
    have hnorm : ‖kinDir d j‖ = 1 := by
      simp [kinDir, EuclideanSpace.norm_single]
    have hev : fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) x
        = (ContinuousLinearMap.apply ℝ ℝ (kinDir d j)).comp
            (fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y) x) := by
      have hfd : DifferentiableAt ℝ (fun y : Vd d => fderiv ℝ (cut d R) y) x := by
        have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Vd d => fderiv ℝ (cut d R) y) :=
          hcutC.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl
        exact (h.differentiable (by simp)) x
      exact (((ContinuousLinearMap.apply ℝ ℝ
        (kinDir d j)).hasFDerivAt).comp x hfd.hasFDerivAt).fderiv
    have hb : ‖fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y) x‖ ≤ C₂ * (R⁻¹ * R⁻¹) := by
      rw [fderiv_fderiv_cut]
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      have hflip : ‖((ContinuousLinearMap.compL ℝ (Vd d) (Vd d) ℝ).flip (scaleCLM d R))‖ ≤ R⁻¹ := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun L => ?_
        have h1 : ‖L.comp (scaleCLM d R)‖ ≤ ‖L‖ * ‖scaleCLM d R‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        have h2 : ‖L‖ * ‖scaleCLM d R‖ ≤ ‖L‖ * R⁻¹ :=
          mul_le_mul_of_nonneg_left (norm_scaleCLM_le hRpos) (norm_nonneg _)
        calc ‖((ContinuousLinearMap.compL ℝ (Vd d) (Vd d) ℝ).flip (scaleCLM d R)) L‖
            = ‖L.comp (scaleCLM d R)‖ := rfl
          _ ≤ ‖L‖ * R⁻¹ := le_trans h1 h2
          _ = R⁻¹ * ‖L‖ := by ring
      have hinner : ‖(fderiv ℝ (fun y : Vd d => fderiv ℝ (bump d) y)
          (scaleCLM d R x)).comp (scaleCLM d R)‖ ≤ C₂ * R⁻¹ := by
        refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
        exact mul_le_mul (hC₂ _) (norm_scaleCLM_le hRpos) (norm_nonneg _) hC₂nn
      have := mul_le_mul hflip hinner (norm_nonneg _) (by positivity)
      calc ‖((ContinuousLinearMap.compL ℝ (Vd d) (Vd d) ℝ).flip (scaleCLM d R))‖ *
            ‖(fderiv ℝ (fun y : Vd d => fderiv ℝ (bump d) y)
              (scaleCLM d R x)).comp (scaleCLM d R)‖
          ≤ R⁻¹ * (C₂ * R⁻¹) := this
        _ = C₂ * (R⁻¹ * R⁻¹) := by ring
    have hfin : ‖fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) x (kinDir d j)‖
        ≤ C₂ * (R⁻¹ * R⁻¹) := by
      have h1 : ‖fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) x (kinDir d j)‖
          ≤ ‖fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) x‖ := by
        simpa [hnorm] using
          (fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) x).le_opNorm (kinDir d j)
      have h2 : ‖fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) x‖
          ≤ ‖fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y) x‖ := by
        rw [hev]
        refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
        have : ‖ContinuousLinearMap.apply ℝ ℝ (kinDir d j)‖ ≤ 1 := by
          refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L => ?_
          simpa [hnorm] using L.le_opNorm (kinDir d j)
        nlinarith [norm_nonneg (fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y) x),
          norm_nonneg (ContinuousLinearMap.apply ℝ ℝ (kinDir d j))]
      linarith
    have hcast : ‖((fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) x (kinDir d j)
        : ℝ) : ℂ)‖
        = ‖fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) x (kinDir d j)‖ := by
      simp [Complex.norm_real]
    rw [hcast]
    calc ‖fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) x (kinDir d j)‖
        ≤ C₂ * (R⁻¹ * R⁻¹) := hfin
      _ = C₂ / R ^ 2 := by field_simp
  refine ⟨fun j => le_trans (hfirst j) (by gcongr; exact le_max_left _ _), ?_⟩
  have hsum : ‖lapC (fun y => ((cut d R y : ℝ) : ℂ)) x‖ ≤ ∑ _j : Fin d, C₂ / R ^ 2 := by
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum fun j _ => hsecond j
  have hsimp : ∑ _j : Fin d, C₂ / R ^ 2 = (d : ℝ) * C₂ / R ^ 2 := by
    simp [Finset.sum_const, mul_div_assoc]
  rw [hsimp] at hsum
  refine le_trans hsum ?_
  gcongr
  exact le_max_right _ _

end

end BookProof.QgOneParticleCc
