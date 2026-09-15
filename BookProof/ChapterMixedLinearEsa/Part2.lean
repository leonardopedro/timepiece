import Mathlib
import BookProof.ChapterFourierMultiplierEsa
import BookProof.ChapterWaveUnboundedPotential
import BookProof.ChapterMixedLinearEsa.Part1

/-!
# The mixed first-order operator `⟪x, b⟫ − i ∂_m`

`BookProof.ChapterShiftedQuadraticDegenerate` proves essential self-adjointness of the
inhomogeneous quadratic Hamiltonian `H_A + ∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` whenever the first-order
coefficients are orthogonal to the kernel of `A`, and records the residual case: in a
kernel direction the Hamiltonian degenerates to the *first-order* operator
`b x + b' π`, which has no `L²` eigenvector, so the Hermite-eigenbasis route cannot see
it.  `BookProof.ChapterFourierMultiplierEsa` settles the purely-momentum part `b' π` by
the Plancherel route.  This module settles the remaining, genuinely mixed case
`b x + b' π` with **both** coefficients non-zero.

## What is proved

* `posOp_essentiallySelfAdjoint` — **the position operator** (multiplication by the real
  linear function `x ↦ ⟪x, b⟫`) is symmetric and essentially self-adjoint on the Schwartz
  core of `L²(V)`.  The deficiency equation is killed by dividing a *compactly supported*
  test function by `⟪x, b⟫ − z̄`, so no Fourier transform is needed;
* `momentum_test_compactSupport_extend` — **compactly supported test functions suffice**
  for the momentum operator: if the deficiency identity of `π_m = −i ∂_m` holds against
  every smooth compactly supported test function, it holds against every Schwartz
  function.  The proof is a cut-off argument: `χ(x/n) f → f` and
  `π_m (χ(·/n) f) → π_m f` pointwise, with a uniform integrable dominating function;
* `gaugeFun`, `hasDerivAt_gaugeFun_line`, `mixedLinearOp_gauge` — **the gauge**: with the
  quadratic phase `θ(x) = −⟪x,b⟫⟪x,m⟫/‖m‖² + ⟪b,m⟫⟪x,m⟫²/(2‖m‖⁴)`, which satisfies
  `∂_m θ = −⟪x, b⟫`, the unimodular factor `e^{iθ}` intertwines the mixed operator with
  the pure momentum operator: `(⟪·,b⟫ − i∂_m)(e^{iθ}φ) = e^{iθ}(−i∂_m φ)`;
* `mixedLinearOp_essentiallySelfAdjoint` — **the headline**: for arbitrary `b, m ∈ V` the
  operator `⟪x, b⟫ − i ∂_m` is symmetric and essentially self-adjoint on the Schwartz core
  of `L²(V)`.  Multiplying a compactly supported test function by `e^{iθ}` keeps it
  compactly supported, which is why the previous item is exactly what the gauge argument
  needs (`e^{iθ}` is *not* known to preserve Schwartz space here).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.MixedLinearEsa

open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
/-! ## 4. The gauge -/

/-- The quadratic phase `θ(x) = −⟪x,b⟫⟪x,m⟫/‖m‖² + ⟪b,m⟫⟪x,m⟫²/(2‖m‖⁴)`, whose derivative
along `m` is `−⟪x, b⟫`. -/
noncomputable def gaugePhase (b m : V) (x : V) : ℝ :=
  -(inner ℝ x b) * (inner ℝ x m) / ‖m‖ ^ 2
    + (inner ℝ b m) * (inner ℝ x m) ^ 2 / (2 * ‖m‖ ^ 4)

/-- The unimodular gauge factor `e^{iθ}`. -/
noncomputable def gaugeFun (b m : V) (x : V) : ℂ :=
  Complex.exp (Complex.I * ((gaugePhase b m x : ℝ) : ℂ))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The phase has directional derivative `−⟪x, b⟫` along `m`. -/
lemma hasDerivAt_gaugePhase_line (b m : V) (hm : m ≠ 0) (x : V) :
    HasDerivAt (fun t : ℝ => gaugePhase b m (x + t • m)) (-(inner ℝ x b : ℝ)) 0 := by
  set A : ℝ := inner ℝ x b with hA
  set B : ℝ := inner ℝ m b with hB
  set C : ℝ := inner ℝ x m with hC
  set D : ℝ := ‖m‖ ^ 2 with hD
  have hD0 : D ≠ 0 := by positivity
  have hbm : (inner ℝ b m : ℝ) = B := (real_inner_comm b m).symm
  have hfun : (fun t : ℝ => gaugePhase b m (x + t • m))
      = fun t : ℝ => (-(A + t * B)) * (C + t * D) / D + B * (C + t * D) ^ 2 / (2 * D ^ 2) := by
    funext t
    rw [gaugePhase, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      hbm, real_inner_self_eq_norm_sq]
    simp only [hA, hB, hC, hD]
    ring
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => A + t * B) B 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const B).const_add A
  have h1n : HasDerivAt (fun t : ℝ => -(A + t * B)) (-B) 0 := h1.neg
  have h2 : HasDerivAt (fun t : ℝ => C + t * D) D 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const D).const_add C
  have h3 := ((h1n.mul h2).div_const D).add (((h2.pow 2).const_mul B).div_const (2 * D ^ 2))
  simp only [Nat.cast_ofNat] at h3
  convert h3 using 1
  field_simp
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma hasDerivAt_gaugeFun_line (b m : V) (hm : m ≠ 0) (x : V) :
    HasDerivAt (fun t : ℝ => gaugeFun b m (x + t • m))
      (gaugeFun b m x * (Complex.I * ((-(inner ℝ x b : ℝ) : ℝ) : ℂ))) 0 := by
  have h := hasDerivAt_gaugePhase_line b m hm x
  have h1 : HasDerivAt (fun t : ℝ => ((gaugePhase b m (x + t • m) : ℝ) : ℂ))
      (((-(inner ℝ x b : ℝ) : ℝ) : ℂ)) 0 := h.ofReal_comp
  have h2 : HasDerivAt (fun t : ℝ => Complex.I * ((gaugePhase b m (x + t • m) : ℝ) : ℂ))
      (Complex.I * ((-(inner ℝ x b : ℝ) : ℝ) : ℂ)) 0 := h1.const_mul _
  simpa [gaugeFun] using h2.cexp

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma contDiff_gaugePhase (b m : V) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gaugePhase b m) := by
  unfold gaugePhase
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : V => (inner ℝ x b : ℝ)) :=
    ((innerSL ℝ).flip b).contDiff
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : V => (inner ℝ x m : ℝ)) :=
    ((innerSL ℝ).flip m).contDiff
  exact ((h1.neg.mul h2).div_const _).add ((contDiff_const.mul (h2.pow 2)).div_const _)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma contDiff_gaugeFun (b m : V) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gaugeFun b m) := by
  unfold gaugeFun
  exact ((Complex.contDiff_exp (𝕜 := ℂ)).restrict_scalars ℝ).comp
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_gaugePhase b m)))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The gauge factor is unimodular. -/
lemma norm_gaugeFun (b m : V) (x : V) : ‖gaugeFun b m x‖ = 1 := by
  rw [gaugeFun, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The gauged test function `e^{iθ}φ`: still smooth and compactly supported, hence still a
Schwartz function.  (Multiplication by `e^{iθ}` is *not* claimed to preserve Schwartz space
in general.) -/
noncomputable def gaugeSchwartz (b m : V) (φ : 𝓢(V, ℂ))
    (hφ : HasCompactSupport (φ : V → ℂ)) : 𝓢(V, ℂ) :=
  (hφ.mul_left (f := gaugeFun b m)).toSchwartzMap
    ((contDiff_gaugeFun b m).mul (φ.smooth ⊤))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] lemma gaugeSchwartz_apply (b m : V) (φ : 𝓢(V, ℂ))
    (hφ : HasCompactSupport (φ : V → ℂ)) (x : V) :
    gaugeSchwartz b m φ hφ x = gaugeFun b m x * φ x := rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The gauge intertwines the mixed operator with the momentum operator**:
`(⟪·,b⟫ − i∂_m)(e^{iθ}φ) = e^{iθ}(−i∂_m φ)`. -/
lemma mixedLinearOp_gauge (b m : V) (hm : m ≠ 0) (φ : 𝓢(V, ℂ))
    (hφ : HasCompactSupport (φ : V → ℂ)) (x : V) :
    (mixedLinearOp b m (gaugeSchwartz b m φ hφ)) x
      = gaugeFun b m x * (momentumOp m φ x) := by
  have hφd : HasDerivAt (fun t : ℝ => φ (x + t • m)) (fderiv ℝ (φ : V → ℂ) x m) 0 :=
    (φ.differentiableAt).hasFDerivAt.hasLineDerivAt m
  have hνd := hasDerivAt_gaugeFun_line b m hm x
  have hprod : HasDerivAt (fun t : ℝ => gaugeFun b m (x + t • m) * φ (x + t • m))
      ((gaugeFun b m x * (Complex.I * ((-(inner ℝ x b : ℝ) : ℝ) : ℂ))) * φ x
        + gaugeFun b m x * fderiv ℝ (φ : V → ℂ) x m) 0 := by
    simpa using hνd.mul hφd
  have hgd : HasDerivAt (fun t : ℝ => (gaugeSchwartz b m φ hφ) (x + t • m))
      (fderiv ℝ ((gaugeSchwartz b m φ hφ) : V → ℂ) x m) 0 :=
    ((gaugeSchwartz b m φ hφ).differentiableAt).hasFDerivAt.hasLineDerivAt m
  have hval := hgd.unique hprod
  rw [mixedLinearOp_apply, hval, momentumOp_apply, gaugeSchwartz_apply]
  push_cast
  linear_combination ((inner ℝ x b : ℝ) : ℂ) * gaugeFun b m x * φ x * Complex.I_mul_I

/-! ## 5. Essential self-adjointness of the mixed operator -/

/-- **The mixed operator has trivial deficiency spaces** at every non-real point. -/
theorem mixedLinearOp_deficiencyTrivialAt (b m : V) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (schwartzDomain V) (opL2 (mixedLinearOp b m)) z := by
  rcases eq_or_ne m 0 with rfl | hm
  · have h0 : mixedLinearOp b (0 : V) = posOp b := by
      have h : momentumOp (0 : V) = 0 := by
        ext f x
        simp [momentumOp_apply]
      rw [mixedLinearOp, h, add_zero]
    rw [h0]
    exact posOp_deficiencyTrivialAt b hz
  intro u hu
  have hmem : MemLp (fun x => (starRingEnd ℂ) (gaugeFun b m x) * (u x)) 2
      (volume : Measure V) := by
    have hmeas : AEStronglyMeasurable (fun x => (starRingEnd ℂ) (gaugeFun b m x) * (u x))
        (volume : Measure V) :=
      (Complex.continuous_conj.comp ((contDiff_gaugeFun b m).continuous)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable u)
    refine (Lp.memLp u).of_le hmeas (Filter.Eventually.of_forall fun x => ?_)
    simp [norm_gaugeFun]
  set w : Lp ℂ 2 (volume : Measure V) := hmem.toLp _ with hwdef
  have hwcoe : ∀ᵐ x ∂(volume : Measure V),
      (w x : ℂ) = (starRingEnd ℂ) (gaugeFun b m x) * (u x) := hmem.coeFn_toLp
  have hw : ∀ φ : 𝓢(V, ℂ), HasCompactSupport (φ : V → ℂ) →
      ∫ x, (starRingEnd ℂ) ((momentumOp m φ) x) * (w x)
        = z * ∫ x, (starRingEnd ℂ) (φ x) * (w x) := by
    intro φ hφ
    have h1 := hu (schwartzEquiv V (gaugeSchwartz b m φ hφ))
    rw [opL2_apply, schwartzEquiv_coe, inner_toLp_left, inner_toLp_left] at h1
    have hL : ∫ x, (starRingEnd ℂ) ((momentumOp m φ) x) * (w x)
        = ∫ x, (starRingEnd ℂ) ((mixedLinearOp b m (gaugeSchwartz b m φ hφ)) x) * (u x) := by
      refine integral_congr_ae ?_
      filter_upwards [hwcoe] with x hx
      rw [hx, mixedLinearOp_gauge b m hm φ hφ x, map_mul]
      ring
    have hR : ∫ x, (starRingEnd ℂ) (φ x) * (w x)
        = ∫ x, (starRingEnd ℂ) ((gaugeSchwartz b m φ hφ) x) * (u x) := by
      refine integral_congr_ae ?_
      filter_upwards [hwcoe] with x hx
      rw [hx, gaugeSchwartz_apply, map_mul]
      ring
    rw [hL, hR, h1]
  have hw0 : w = 0 := momentumOp_eq_zero_of_compactSupport_test m hz w hw
  have hae : ∀ᵐ x ∂(volume : Measure V), (u x : ℂ) = 0 := by
    have h0 : ∀ᵐ x ∂(volume : Measure V), (w x : ℂ) = 0 := by
      rw [hw0]
      exact Lp.coeFn_zero ℂ 2 (volume : Measure V)
    filter_upwards [hwcoe, h0] with x hx hx0
    rw [hx] at hx0
    rcases mul_eq_zero.mp hx0 with h | h
    · have hn : ‖(starRingEnd ℂ) (gaugeFun b m x)‖ = 1 := by
        rw [RCLike.norm_conj]
        exact norm_gaugeFun b m x
      rw [h, norm_zero] at hn
      exact absurd hn (by norm_num)
    · exact h
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hae

/-- **The headline.**  For arbitrary `b, m ∈ V` the mixed first-order operator
`⟪x, b⟫ − i ∂_m` is essentially self-adjoint on the Schwartz core of `L²(V)`. -/
theorem mixedLinearOp_essentiallySelfAdjoint (b m : V) :
    EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (mixedLinearOp b m)) :=
  ⟨mixedLinearOp_deficiencyTrivialAt b m (by simp),
    mixedLinearOp_deficiencyTrivialAt b m (by simp)⟩

end BookProof.MixedLinearEsa
