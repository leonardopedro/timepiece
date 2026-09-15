import Mathlib
import BookProof.ChapterScalaronCoreEsa
import BookProof.ChapterHermiteQuadraticEsa
import BookProof.ChapterDirectSumEsa

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

/-! ## 1. The abstract transfer step -/

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **Deficiency transfer by graph approximation.**  If every vector of `D₁` is approximated,
together with its image, by vectors of `D₂`, then a deficiency vector for `T₂` is one for
`T₁`; so triviality of the deficiency space of `T₁` at `z` forces that of `T₂`.  Neither
domain need contain the other. -/
theorem deficiencyTrivialAt_of_graphApprox {D₁ D₂ : Submodule ℂ F}
    (T₁ : D₁ →ₗ[ℂ] F) (T₂ : D₂ →ₗ[ℂ] F) {z : ℂ}
    (happrox : ∀ (x : D₁) (ε : ℝ), 0 < ε →
      ∃ y : D₂, ‖(y : F) - (x : F)‖ < ε ∧ ‖T₂ y - T₁ x‖ < ε)
    (h₁ : DeficiencyTrivialAt D₁ T₁ z) :
    DeficiencyTrivialAt D₂ T₂ z := by
  intro w hw
  refine h₁ w fun x => ?_
  have hzero : ∀ ε : ℝ, 0 < ε →
      ‖(inner ℂ (T₁ x) w : ℂ) - z * inner ℂ (x : F) w‖ ≤ ε * (1 + ‖z‖) * ‖w‖ := by
    intro ε hε
    obtain ⟨y, hy1, hy2⟩ := happrox x ε hε
    have hwy := hw y
    have hsplit : (inner ℂ (T₁ x) w : ℂ) - z * inner ℂ (x : F) w
        = (inner ℂ (T₁ x - T₂ y) w : ℂ) + z * inner ℂ ((y : F) - (x : F)) w := by
      rw [inner_sub_left, inner_sub_left, hwy]
      ring
    calc ‖(inner ℂ (T₁ x) w : ℂ) - z * inner ℂ (x : F) w‖
        ≤ ‖(inner ℂ (T₁ x - T₂ y) w : ℂ)‖ + ‖z * (inner ℂ ((y : F) - (x : F)) w : ℂ)‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ ‖T₁ x - T₂ y‖ * ‖w‖ + ‖z‖ * (‖(y : F) - (x : F)‖ * ‖w‖) := by
          gcongr
          · exact norm_inner_le_norm _ _
          · rw [norm_mul]
            gcongr
            exact norm_inner_le_norm _ _
      _ ≤ ε * (1 + ‖z‖) * ‖w‖ := by
          have h1 : ‖T₁ x - T₂ y‖ ≤ ε := by
            rw [← norm_neg]; simpa [neg_sub] using hy2.le
          have hA : ‖T₁ x - T₂ y‖ * ‖w‖ ≤ ε * ‖w‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg w)
          have hB : ‖z‖ * (‖(y : F) - (x : F)‖ * ‖w‖) ≤ ‖z‖ * (ε * ‖w‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hy1.le (norm_nonneg w))
              (norm_nonneg z)
          nlinarith [norm_nonneg w, norm_nonneg z]
  have hnn : ‖(inner ℂ (T₁ x) w : ℂ) - z * inner ℂ (x : F) w‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hpos : 0 < δ / ((1 + ‖z‖) * (1 + ‖w‖)) := by positivity
    have hb := hzero _ hpos
    have hbound : δ / ((1 + ‖z‖) * (1 + ‖w‖)) * (1 + ‖z‖) * ‖w‖ ≤ δ := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg w, norm_nonneg z, hδ.le]
    linarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hnn)

/-- Essential self-adjointness transfers along a graph approximation. -/
theorem essentiallySelfAdjointOn_of_graphApprox {D₁ D₂ : Submodule ℂ F}
    (T₁ : D₁ →ₗ[ℂ] F) (T₂ : D₂ →ₗ[ℂ] F)
    (happrox : ∀ (x : D₁) (ε : ℝ), 0 < ε →
      ∃ y : D₂, ‖(y : F) - (x : F)‖ < ε ∧ ‖T₂ y - T₁ x‖ < ε)
    (h₁ : EssentiallySelfAdjointOn D₁ T₁) :
    EssentiallySelfAdjointOn D₂ T₂ :=
  ⟨deficiencyTrivialAt_of_graphApprox T₁ T₂ happrox h₁.1,
    deficiencyTrivialAt_of_graphApprox T₁ T₂ happrox h₁.2⟩

end Abstract

/-! ## 2. The Hamiltonian on the compactly supported smooth core -/

variable {d : ℕ}

/-- The `j`-th coordinate direction of `ℝᵈ`. -/
def kinDir (d : ℕ) (j : Fin d) : Vd d := EuclideanSpace.single j (1 : ℝ)

/-- The (negative) Laplacian `−Δ = −∑ⱼ ∂ⱼ²` as an operator on Schwartz space. -/
def kinOp (d : ℕ) : 𝓢(Vd d, ℂ) →L[ℂ] 𝓢(Vd d, ℂ) :=
  constCoeffOp (fun _ : Fin d => (-1 : ℝ)) (kinDir d) 0

/-- The kinetic term on the compactly supported smooth core. -/
def kinCc (d : ℕ) : ccDomain (Vd d) →ₗ[ℂ] L2d d :=
  opL2 (kinOp d) ∘ₗ Submodule.inclusion (ccDomain_le_schwartzDomain (E := Vd d))

/-- **The one-particle Hamiltonian `−Δ + W` on the compactly supported smooth core** of
`L²(ℝᵈ)`, for an arbitrary smooth real potential `W`. -/
def ccHam (W : Vd d → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    ccDomain (Vd d) →ₗ[ℂ] L2d d :=
  kinCc d + opCc W hW

theorem kinCc_symmetricOn : SymmetricOn (ccDomain (Vd d)) (kinCc d) :=
  symmetricOn_inclusion _ _ (constCoeffOp_symmetric _ _ _)

theorem ccHam_symmetricOn (W : Vd d → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    SymmetricOn (ccDomain (Vd d)) (ccHam W hW) := by
  intro x y
  have h1 := kinCc_symmetricOn (d := d) x y
  have h2 := smoothPotential_symmetric W hW x y
  simp only [ccHam, LinearMap.add_apply, inner_add_left, inner_add_right]
  linear_combination h1 + h2

/-! ## 3. Pointwise calculus: the Laplacian in coordinates -/

/-- The `j`-th coordinate derivative of a function on `ℝᵈ`. -/
def dcoord (j : Fin d) (u : Vd d → ℂ) (x : Vd d) : ℂ := fderiv ℝ u x (kinDir d j)

/-- The Laplacian in coordinates. -/
def lapC (u : Vd d → ℂ) (x : Vd d) : ℂ := ∑ j : Fin d, dcoord j (dcoord j u) x

theorem secondDeriv_apply_eq (m : Vd d) (f : 𝓢(Vd d, ℂ)) (x : Vd d) :
    (secondDeriv m f) x = fderiv ℝ (fun y => fderiv ℝ (f : Vd d → ℂ) y m) x m := rfl

/-- On a Schwartz map the operator `kinOp` is the pointwise `−Δ`. -/
theorem kinOp_apply_eq (f : 𝓢(Vd d, ℂ)) (x : Vd d) :
    (kinOp d f) x = -lapC (f : Vd d → ℂ) x := by
  have h : (kinOp d f)
      = (∑ i : Fin d, ((-1 : ℝ) : ℂ) • secondDeriv (kinDir d i) f)
        + ((0 : ℝ) : ℂ) • f := by
    simp [kinOp, constCoeffOp]
  rw [h]
  simp only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero, zero_mul, add_zero,
    secondDeriv_apply_eq, lapC, dcoord, neg_one_mul, ← Finset.sum_neg_distrib]
  rfl

/-- Smoothness passes to the coordinate derivative. -/
theorem contDiff_dcoord {u : Vd d → ℂ} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (j : Fin d) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dcoord j u) := by
  have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Vd d => fderiv ℝ u y) :=
    hu.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl
  exact (ContinuousLinearMap.apply ℝ ℂ (kinDir d j)).contDiff.comp hfd

theorem differentiableAt_of_contDiffTop {u : Vd d → ℂ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (x : Vd d) : DifferentiableAt ℝ u x :=
  (hu.differentiable (by simp)).differentiableAt

theorem dcoord_add {u v : Vd d → ℂ} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (j : Fin d) :
    dcoord j (fun y => u y + v y) = fun x => dcoord j u x + dcoord j v x := by
  funext x
  simp only [dcoord]
  have h := ((differentiableAt_of_contDiffTop hu x).hasFDerivAt.add
    (differentiableAt_of_contDiffTop hv x).hasFDerivAt).fderiv
  change (fderiv ℝ (u + v) x) (kinDir d j) = _
  rw [h]
  simp

theorem dcoord_mul {u v : Vd d → ℂ} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (j : Fin d) :
    dcoord j (fun y => u y * v y) = fun x => u x * dcoord j v x + v x * dcoord j u x := by
  funext x
  simp only [dcoord]
  have h := ((differentiableAt_of_contDiffTop hu x).hasFDerivAt.mul
    (differentiableAt_of_contDiffTop hv x).hasFDerivAt).fderiv
  change (fderiv ℝ (u * v) x) (kinDir d j) = _
  rw [h]
  simp

/-- **Leibniz for the Laplacian.** -/
theorem lapC_mul {u v : Vd d → ℂ} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (x : Vd d) :
    lapC (fun y => u y * v y) x
      = u x * lapC v x + v x * lapC u x
        + 2 * ∑ j : Fin d, dcoord j u x * dcoord j v x := by
  have hstep : ∀ j : Fin d, dcoord j (dcoord j (fun y => u y * v y)) x
      = u x * dcoord j (dcoord j v) x + v x * dcoord j (dcoord j u) x
        + 2 * (dcoord j u x * dcoord j v x) := by
    intro j
    rw [dcoord_mul hu hv j]
    rw [dcoord_add (hu.mul (contDiff_dcoord hv j)) (hv.mul (contDiff_dcoord hu j)) j]
    rw [dcoord_mul hu (contDiff_dcoord hv j) j, dcoord_mul hv (contDiff_dcoord hu j) j]
    ring
  simp only [lapC, hstep, Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ## 4. The Gauss–polynomial core is smooth, with algebraic derivatives -/

theorem contDiff_polyEval (p : MvPolynomial (Fin d) ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Vd d => MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      refine hp.mul ?_
      exact Complex.ofRealCLM.contDiff.comp
        ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff)

theorem contDiff_gaussD (d : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gaussD (d := d)) := by
  unfold gaussD
  exact Real.contDiff_exp.comp (((contDiff_norm_sq ℝ).neg).div_const 4)

theorem contDiff_pgFun (p : MvPolynomial (Fin d) ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pgFun p) :=
  (contDiff_polyEval p).mul (Complex.ofRealCLM.contDiff.comp (contDiff_gaussD d))

/-- Moving along the `j`-th coordinate direction is moving along the coordinate line. -/
theorem coordLine_add_smul (x : Vd d) (j : Fin d) (t : ℝ) :
    x + t • kinDir d j = coordLine x j (x j + t) := by
  ext i
  by_cases h : i = j
  · subst h
    simp [kinDir, coordLine_apply, EuclideanSpace.single_apply]
  · simp only [PiLp.add_apply, PiLp.smul_apply, coordLine_apply, Function.update_of_ne h,
      kinDir, EuclideanSpace.single_apply, smul_eq_mul]
    simp [h]

theorem coordLine_self_eq (x : Vd d) (j : Fin d) : coordLine x j (x j) = x := by
  ext i
  by_cases h : i = j
  · subst h; simp [coordLine_apply]
  · simp [coordLine_apply, Function.update_of_ne h]

/-- Differentiating the core in a coordinate is the twisted derivative `coreD`. -/
theorem dcoord_pgFun (p : MvPolynomial (Fin d) ℂ) (j : Fin d) :
    dcoord j (pgFun p) = pgFun (coreD j p) := by
  funext x
  have h0 := hasDerivAt_pgFun_coord p j x (x j)
  have hshift : HasDerivAt (fun t : ℝ => x j + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (x j)
  have h0' : HasDerivAt (fun s : ℝ => pgFun p (coordLine x j s)) (pgFun (coreD j p) x)
      (x j + 0) := by
    simpa [coordLine_self_eq] using h0
  have hcomp := HasDerivAt.scomp (0 : ℝ) h0' hshift
  simp only [Function.comp_def, one_smul] at hcomp
  have hfun : (fun t : ℝ => pgFun p (coordLine x j (x j + t)))
      = fun t : ℝ => pgFun p (x + t • kinDir d j) := by
    funext t
    rw [coordLine_add_smul]
  rw [hfun] at hcomp
  have hld : HasLineDerivAt ℝ (pgFun p) (pgFun (coreD j p) x) x (kinDir d j) := by
    simpa [HasLineDerivAt] using hcomp
  have hdiff : DifferentiableAt ℝ (pgFun p) x :=
    differentiableAt_of_contDiffTop (contDiff_pgFun p) x
  have hfd : fderiv ℝ (pgFun p) x (kinDir d j) = pgFun (coreD j p) x := by
    rw [← hdiff.lineDeriv_eq_fderiv]
    exact hld.lineDeriv
  simpa [dcoord] using hfd

/-- Hence the Laplacian on the core is `−kinPoly`. -/
theorem lapC_pgFun (p : MvPolynomial (Fin d) ℂ) :
    lapC (pgFun p) = fun x => -pgFun (kinPoly p) x := by
  funext x
  simp only [lapC, dcoord_pgFun]
  simp only [pgFun, kinPoly, map_neg, map_sum, Finset.sum_mul, neg_mul, neg_neg]

end

end BookProof.QgOneParticleCc
