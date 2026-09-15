import Mathlib
import BookProof.ChapterScalaronCoreEsa
import BookProof.ChapterHermiteQuadraticEsa
import BookProof.ChapterDirectSumEsa
import BookProof.ChapterQgOneParticleCcEsa.Part3

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
/-! ## 7. The transfer theorem and the `R + αR²` instances -/

/-- **Transfer.**  Essential self-adjointness on the Gauss–polynomial core implies it on the
compactly supported smooth core. -/
theorem ccHam_essentiallySelfAdjoint_of_core (W : Vd d → ℝ)
    (hWs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (hWc : Continuous W) (hWb : ExpBounded W)
    (hcore : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (hamCore W hWc hWb)) :
    EssentiallySelfAdjointOn (ccDomain (Vd d)) (ccHam W hWs) :=
  essentiallySelfAdjointOn_of_graphApprox _ _
    (fun x _ hε => exists_cc_graph_approx W hWs hWc hWb x hε) hcore

theorem contDiff_harmW (d : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (harmW (d := d)) := by
  unfold harmW
  exact (contDiff_norm_sq ℝ).div_const 4

/-- **The one-particle `R + αR²` Hamiltonian on the compactly supported smooth core.**
`−Δ + ‖x‖²/4 + V` is essentially self-adjoint there for every smooth `V` dominated by
`a‖x‖²/4 + b` with `a < 1`. -/
theorem qgOneParticleCc_esa {V : Vd d → ℝ} {a b : ℝ}
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hV : ∀ x, |V x| ≤ a * harmW x + b) :
    EssentiallySelfAdjointOn (ccDomain (Vd d))
      (ccHam (fun x => harmW x + V x) ((contDiff_harmW d).add hVs)) := by
  have hVc : Continuous V := hVs.continuous
  have hsc : Continuous fun x : Vd d => harmW x + V x := continuous_harmW.add hVc
  have hsb : ExpBounded fun x : Vd d => harmW x + V x := by
    refine expBounded_of_le_harm (a := 1 + a) (b := b) (by linarith) hb fun x => ?_
    have hharm : (0 : ℝ) ≤ harmW x := by unfold harmW; positivity
    have h := hV x
    have h2 := abs_add_le (harmW x) (V x)
    have h3 : |harmW x| = harmW x := abs_of_nonneg hharm
    rw [h3] at h2
    nlinarith
  exact ccHam_essentiallySelfAdjoint_of_core _ _ hsc hsb
    (harmonic_add_subquadratic_essentiallySelfAdjoint hVc ha ha1 hb hV hsc hsb)

/-- The unitary group of the one-particle Hamiltonian, on the compactly supported core. -/
theorem qgOneParticleCc_stone_flow {V : Vd d → ℝ} {a b : ℝ}
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hV : ∀ x, |V x| ≤ a * harmW x + b) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (ccHam (fun x => harmW x + V x) ((contDiff_harmW d).add hVs)) T.op ∧
        IsStoneFlow T U :=
  exists_stone_flow_of_esa _ ccDomain_dense (ccHam_symmetricOn _ _)
    (qgOneParticleCc_esa hVs ha ha1 hb hV)

/-! ## 8. The gauge-fixed `R + αR²` instances on the compactly supported core -/

/-- Equal potentials give the same Hamiltonian on the compactly supported core. -/
theorem ccHam_congr {W W' : Vd d → ℝ} (h : W = W')
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (hW' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W') :
    ccHam W hW = ccHam W' hW' := by
  subst h; rfl

theorem contDiff_coord (d : ℕ) (i : Fin d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Vd d => x i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

theorem contDiff_confW (M alpha : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (confW M alpha) := by
  have h : confW M alpha
      = fun x : Vd 1 => -(M ^ 2 / 2) * (x 0) + alpha * (x 0) ^ 2 := rfl
  rw [h]
  exact ((contDiff_coord 1 0).const_smul (-(M ^ 2 / 2))).add
    (((contDiff_coord 1 0).pow 2).const_smul alpha)

/-- **The regularized conformal mode of the `R + αR²` Hamiltonian is essentially
self-adjoint on the compactly supported smooth core of `L²(ℝ)`**, for `0 < α < 1/2`. -/
theorem confVCc_esa (M alpha : ℝ) (h0 : 0 < alpha) (h2 : alpha < 1 / 2) :
    EssentiallySelfAdjointOn (ccDomain (Vd 1)) (ccHam (confW M alpha) (contDiff_confW M alpha)) :=
  ccHam_essentiallySelfAdjoint_of_core _ _ (continuous_confW M alpha) (expBounded_confW M alpha)
    (confV_essentiallySelfAdjoint M alpha h0 h2)

/-- The unitary group of the conformal mode on the compactly supported core. -/
theorem confVCc_stone_flow (M alpha : ℝ) (h0 : 0 < alpha) (h2 : alpha < 1 / 2) :
    ∃ (T : UnboundedSelfAdjoint (L2d 1)) (U : ℝ → (L2d 1 →L[ℂ] L2d 1)),
      IsSelfAdjointExtension (ccHam (confW M alpha) (contDiff_confW M alpha)) T.op ∧
        IsStoneFlow T U :=
  exists_stone_flow_of_esa _ ccDomain_dense (ccHam_symmetricOn _ _) (confVCc_esa M alpha h0 h2)

theorem contDiff_sectorQuadW (M alpha mu : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sectorQuadW M alpha mu) := by
  have h : sectorQuadW M alpha mu
      = fun x : Vd 2 => (-(M ^ 2 / 2) * (x 0) + alpha * (x 0) ^ 2) + mu * (x 1) ^ 2 := rfl
  rw [h]
  exact (((contDiff_coord 2 0).const_smul (-(M ^ 2 / 2))).add
    (((contDiff_coord 2 0).pow 2).const_smul alpha)).add
      (((contDiff_coord 2 1).pow 2).const_smul mu)

/-- **The reduced `(R_c, φ)` sector with a quadratic scalaron term is essentially
self-adjoint on the compactly supported smooth core of `L²(ℝ²)`**, for `0 < α < 1/2` and
`0 < μ < 1/2`. -/
theorem sectorQuadCc_esa (M alpha mu : ℝ) (ha0 : 0 < alpha) (ha2 : alpha < 1 / 2)
    (hm0 : 0 < mu) (hm2 : mu < 1 / 2) :
    EssentiallySelfAdjointOn (ccDomain (Vd 2))
      (ccHam (sectorQuadW M alpha mu) (contDiff_sectorQuadW M alpha mu)) :=
  ccHam_essentiallySelfAdjoint_of_core _ _ (continuous_sectorQuadW M alpha mu)
    (expBounded_sectorQuadW M alpha mu)
    (sectorQuad_essentiallySelfAdjoint M alpha mu ha0 ha2 hm0 hm2)

/-- The unitary group of the reduced sector on the compactly supported core. -/
theorem sectorQuadCc_stone_flow (M alpha mu : ℝ) (ha0 : 0 < alpha) (ha2 : alpha < 1 / 2)
    (hm0 : 0 < mu) (hm2 : mu < 1 / 2) :
    ∃ (T : UnboundedSelfAdjoint (L2d 2)) (U : ℝ → (L2d 2 →L[ℂ] L2d 2)),
      IsSelfAdjointExtension (ccHam (sectorQuadW M alpha mu) (contDiff_sectorQuadW M alpha mu))
        T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ ccDomain_dense (ccHam_symmetricOn _ _)
    (sectorQuadCc_esa M alpha mu ha0 ha2 hm0 hm2)

/-! ## 9. The `n`-particle sector and the finite-particle Fock space

The `n`-particle configuration space is `(ℝᵈ)ⁿ = ℝ^{n·d}`, and the `n`-particle Hamiltonian
is `∑ₖ (−Δ_k + U(x_k))`.  Its kinetic part is the full Laplacian of `ℝ^{n·d}` and, when
`U = ‖·‖²/4 + V`, its potential is again `‖x‖²/4 + (a subquadratic perturbation)` — with the
*same* constant `a` — so the one-particle theorem applies verbatim in dimension `n·d`.  The
finite-particle Fock space is the `ℓ²`-direct sum of the sectors, and essential
self-adjointness is fibrewise (`BookProof.DirectSumEsa`). -/

/-- The `k`-th particle's coordinates, as a linear map `ℝ^{n·d} → ℝᵈ`. -/
def partLM (n d : ℕ) (k : Fin n) : Vd (n * d) →ₗ[ℝ] Vd d where
  toFun x := (WithLp.toLp 2 (fun i : Fin d => x (finProdFinEquiv (k, i))) : Vd d)
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

@[simp] theorem partLM_apply (n d : ℕ) (k : Fin n) (x : Vd (n * d)) (i : Fin d) :
    (partLM n d k x) i = x (finProdFinEquiv (k, i)) := rfl

theorem contDiff_partLM (n d : ℕ) (k : Fin n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (partLM n d k) :=
  (LinearMap.toContinuousLinearMap (partLM n d k)).contDiff

/-- **The harmonic term is exactly additive over the particles.** -/
theorem sum_harmW_partLM (n d : ℕ) (x : Vd (n * d)) :
    ∑ k : Fin n, harmW (partLM n d k x) = harmW x := by
  have hsq : ∑ k : Fin n, ‖partLM n d k x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp only [norm_sq_eq_sum, partLM_apply]
    have h : ∑ ki : Fin n × Fin d, (x (finProdFinEquiv ki)) ^ 2
        = ∑ k : Fin n, ∑ i : Fin d, (x (finProdFinEquiv (k, i))) ^ 2 :=
      Fintype.sum_prod_type _
    rw [← h]
    exact Fintype.sum_equiv finProdFinEquiv _ _ (fun a => rfl)
  simp only [harmW, ← Finset.sum_div, hsq]

/-- The `n`-particle potential built from a one-particle potential `U`. -/
def nParticleW (U : Vd d → ℝ) (n : ℕ) : Vd (n * d) → ℝ :=
  fun x => ∑ k : Fin n, U (partLM n d k x)

theorem contDiff_nParticleW {U : Vd d → ℝ} (hU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U)
    (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (nParticleW U n) := by
  exact ContDiff.sum fun k _ => hU.comp (contDiff_partLM n d k)

/-- The `n`-particle potential of `‖·‖²/4 + V` is the `n·d`-dimensional harmonic potential
plus the sum of the one-particle perturbations. -/
theorem nParticleW_harm_add (V : Vd d → ℝ) (n : ℕ) :
    nParticleW (fun y => harmW y + V y) n
      = fun x : Vd (n * d) => harmW x + nParticleW V n x := by
  funext x
  simp only [nParticleW, Finset.sum_add_distrib, sum_harmW_partLM]

/-- The perturbation stays subquadratic, with the *same* coefficient `a`. -/
theorem abs_nParticleW_le {V : Vd d → ℝ} {a b : ℝ}
    (hV : ∀ y, |V y| ≤ a * harmW y + b) (n : ℕ) (x : Vd (n * d)) :
    |nParticleW V n x| ≤ a * harmW x + n * b := by
  have hstep : |∑ k : Fin n, V (partLM n d k x)| ≤ ∑ k : Fin n, |V (partLM n d k x)| :=
    Finset.abs_sum_le_sum_abs _ _
  have hbound : ∑ k : Fin n, |V (partLM n d k x)|
      ≤ ∑ k : Fin n, (a * harmW (partLM n d k x) + b) :=
    Finset.sum_le_sum fun k _ => hV _
  have hsum : ∑ k : Fin n, (a * harmW (partLM n d k x) + b)
      = a * harmW x + n * b := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_harmW_partLM]
    simp [mul_comm]
  rw [nParticleW]
  linarith [hstep, hbound, hsum.le, hsum.ge]

/-- **The `n`-particle `R + αR²` Hamiltonian on the compactly supported smooth core.**
`∑ₖ (−Δ_k + ‖x_k‖²/4 + V(x_k))` is essentially self-adjoint on the compactly supported
smooth core of `L²((ℝᵈ)ⁿ)` for every smooth `V` dominated by `a‖x‖²/4 + b` with `a < 1`. -/
theorem qgNParticleCc_esa {V : Vd d → ℝ} {a b : ℝ}
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hV : ∀ y, |V y| ≤ a * harmW y + b) (n : ℕ) :
    EssentiallySelfAdjointOn (ccDomain (Vd (n * d)))
      (ccHam (nParticleW (fun y => harmW y + V y) n)
        (contDiff_nParticleW ((contDiff_harmW d).add hVs) n)) := by
  have hfun := nParticleW_harm_add V n
  have hone := qgOneParticleCc_esa (d := n * d) (V := nParticleW V n) (a := a) (b := n * b)
    (contDiff_nParticleW hVs n) ha ha1 (by positivity) (abs_nParticleW_le hV n)
  rw [ccHam_congr hfun (contDiff_nParticleW ((contDiff_harmW d).add hVs) n)
    ((contDiff_harmW (n * d)).add (contDiff_nParticleW hVs n))]
  exact hone

/-- **The finite-particle Fock space** over the `d`-dimensional one-particle sector. -/
abbrev qgFock (d : ℕ) := lp (fun n : ℕ => L2d (n * d)) 2

/-- The Fock core: the algebraic direct sum of the compactly supported smooth sector
cores. -/
def qgFockCore (d : ℕ) : Submodule ℂ (qgFock d) :=
  dsCore (fun n : ℕ => ccDomain (Vd (n * d)))

theorem qgFockCore_dense : Dense ((qgFockCore d : Submodule ℂ (qgFock d)) : Set (qgFock d)) :=
  dsCore_dense fun _ => ccDomain_dense

/-- **The second-quantised `R + αR²` Hamiltonian** on the finite-particle Fock space: on the
`n`-particle sector it is `∑ₖ (−Δ_k + ‖x_k‖²/4 + V(x_k))`. -/
def qgFockHam {V : Vd d → ℝ} (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) :
    qgFockCore d →ₗ[ℂ] qgFock d :=
  dsOp fun n : ℕ => ccHam (nParticleW (fun y => harmW y + V y) n)
    (contDiff_nParticleW ((contDiff_harmW d).add hVs) n)

theorem qgFockHam_symmetricOn {V : Vd d → ℝ} (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) :
    SymmetricOn (qgFockCore d) (qgFockHam hVs) :=
  dsOp_symmetricOn _ fun _ => ccHam_symmetricOn _ _

/-- **The finite-particle Fock statement.**  The second-quantised `R + αR²` Hamiltonian is
essentially self-adjoint on the algebraic direct sum of the compactly supported smooth
sector cores — the finite-particle core built from the one-particle core. -/
theorem qgFockCc_esa {V : Vd d → ℝ} {a b : ℝ}
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hV : ∀ y, |V y| ≤ a * harmW y + b) :
    EssentiallySelfAdjointOn (qgFockCore d) (qgFockHam hVs) :=
  dsOp_essentiallySelfAdjointOn _ fun n => qgNParticleCc_esa hVs ha ha1 hb hV n

/-- The unitary group of the second-quantised Hamiltonian. -/
theorem qgFockCc_stone_flow {V : Vd d → ℝ} {a b : ℝ}
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hV : ∀ y, |V y| ≤ a * harmW y + b) :
    ∃ (T : UnboundedSelfAdjoint (qgFock d)) (U : ℝ → (qgFock d →L[ℂ] qgFock d)),
      IsSelfAdjointExtension (qgFockHam hVs) T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ qgFockCore_dense (qgFockHam_symmetricOn hVs)
    (qgFockCc_esa hVs ha ha1 hb hV)

end

end BookProof.QgOneParticleCc
