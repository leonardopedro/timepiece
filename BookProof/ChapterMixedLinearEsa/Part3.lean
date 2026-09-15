import Mathlib
import BookProof.ChapterFourierMultiplierEsa
import BookProof.ChapterWaveUnboundedPotential
import BookProof.ChapterMixedLinearEsa.Part2

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
/-! ## 6. An arbitrary potential with a gauge along `m`

The gauge argument never uses that the potential is *linear*: it uses only that the phase
`θ` solves the transport equation `∂_m θ = −W` along the momentum direction.  Written that
way it is an instrument, and it covers unbounded polynomial potentials — for instance the
quartic `x⁴ − i d/dx` on `L²(ℝ)`, which is neither a Fourier multiplier nor an operator
with an `L²` eigenvector. -/

/-- The operator `W(x) − i ∂_m`: an arbitrary real potential of temperate growth plus a
momentum term. -/
noncomputable def potMomOp (W : V → ℝ) (m : V) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  potentialOp W + momentumOp m

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma potMomOp_apply {W : V → ℝ} (hW : Function.HasTemperateGrowth W) (m : V) (f : 𝓢(V, ℂ))
    (x : V) :
    (potMomOp W m f) x = ((W x : ℝ) : ℂ) * f x + (-Complex.I) * (fderiv ℝ f x m) := by
  simp [potMomOp, potentialOp_apply hW, momentumOp_apply]

/-- `W(x) − i ∂_m` is symmetric on the Schwartz core. -/
theorem potMomOp_symmetric (W : V → ℝ) (hW : Function.HasTemperateGrowth W) (m : V) :
    SymmetricOn (schwartzDomain V) (opL2 (potMomOp W m)) := by
  have hmom : SymmetricOn (schwartzDomain V) (opL2 (momentumOp m)) :=
    symmetricOn_of_real_symbol (momentumOp m) (fun x => 2 * Real.pi * (inner ℝ x m))
      (fun f x => by simpa using fourier_momentumOp_apply f m x)
  rw [potMomOp, opL2_add]
  intro x y
  simp only [LinearMap.add_apply, inner_add_left, inner_add_right,
    potentialOp_symmetric W hW x y, hmom x y]

/-- The unimodular gauge factor `e^{iθ}` of an arbitrary real phase. -/
noncomputable def phaseFun (θ : V → ℝ) (x : V) : ℂ :=
  Complex.exp (Complex.I * ((θ x : ℝ) : ℂ))

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
@[simp] lemma norm_phaseFun (θ : V → ℝ) (x : V) : ‖phaseFun θ x‖ = 1 := by
  rw [phaseFun, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma contDiff_phaseFun {θ : V → ℝ} (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (phaseFun θ) := by
  unfold phaseFun
  exact ((Complex.contDiff_exp (𝕜 := ℂ)).restrict_scalars ℝ).comp
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hθ))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- If `θ` has directional derivative `−W(x)` along `m`, the gauge factor has directional
derivative `−i W(x) e^{iθ}`. -/
lemma hasDerivAt_phaseFun_line {W θ : V → ℝ} {m : V}
    (hθd : ∀ x, HasDerivAt (fun t : ℝ => θ (x + t • m)) (-(W x)) 0) (x : V) :
    HasDerivAt (fun t : ℝ => phaseFun θ (x + t • m))
      (phaseFun θ x * (Complex.I * ((-(W x) : ℝ) : ℂ))) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => ((θ (x + t • m) : ℝ) : ℂ)) (((-(W x) : ℝ) : ℂ)) 0 :=
    (hθd x).ofReal_comp
  have h2 : HasDerivAt (fun t : ℝ => Complex.I * ((θ (x + t • m) : ℝ) : ℂ))
      (Complex.I * ((-(W x) : ℝ) : ℂ)) 0 := h1.const_mul _
  simpa [phaseFun] using h2.cexp

/-- The gauged test function `e^{iθ}φ`, still smooth and compactly supported. -/
noncomputable def phaseSchwartz {θ : V → ℝ} (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ)
    (φ : 𝓢(V, ℂ)) (hφ : HasCompactSupport (φ : V → ℂ)) : 𝓢(V, ℂ) :=
  (hφ.mul_left (f := phaseFun θ)).toSchwartzMap ((contDiff_phaseFun hθ).mul (φ.smooth ⊤))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] lemma phaseSchwartz_apply {θ : V → ℝ} (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ)
    (φ : 𝓢(V, ℂ)) (hφ : HasCompactSupport (φ : V → ℂ)) (x : V) :
    phaseSchwartz hθ φ hφ x = phaseFun θ x * φ x := rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The gauge intertwines `W(x) − i ∂_m` with the momentum operator** as soon as the phase
solves the transport equation `∂_m θ = −W`. -/
lemma potMomOp_gauge {W θ : V → ℝ} (hW : Function.HasTemperateGrowth W) {m : V}
    (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ)
    (hθd : ∀ x, HasDerivAt (fun t : ℝ => θ (x + t • m)) (-(W x)) 0)
    (φ : 𝓢(V, ℂ)) (hφ : HasCompactSupport (φ : V → ℂ)) (x : V) :
    (potMomOp W m (phaseSchwartz hθ φ hφ)) x = phaseFun θ x * (momentumOp m φ x) := by
  have hφd : HasDerivAt (fun t : ℝ => φ (x + t • m)) (fderiv ℝ (φ : V → ℂ) x m) 0 :=
    (φ.differentiableAt).hasFDerivAt.hasLineDerivAt m
  have hνd := hasDerivAt_phaseFun_line hθd x
  have hprod : HasDerivAt (fun t : ℝ => phaseFun θ (x + t • m) * φ (x + t • m))
      ((phaseFun θ x * (Complex.I * ((-(W x) : ℝ) : ℂ))) * φ x
        + phaseFun θ x * fderiv ℝ (φ : V → ℂ) x m) 0 := by
    simpa using hνd.mul hφd
  have hgd : HasDerivAt (fun t : ℝ => (phaseSchwartz hθ φ hφ) (x + t • m))
      (fderiv ℝ ((phaseSchwartz hθ φ hφ) : V → ℂ) x m) 0 :=
    ((phaseSchwartz hθ φ hφ).differentiableAt).hasFDerivAt.hasLineDerivAt m
  have hval := hgd.unique hprod
  rw [potMomOp_apply hW, hval, momentumOp_apply, phaseSchwartz_apply]
  push_cast
  linear_combination ((W x : ℝ) : ℂ) * phaseFun θ x * φ x * Complex.I_mul_I

/-- **Vanishing deficiency spaces for `W(x) − i ∂_m`** under the transport hypothesis. -/
theorem potMomOp_deficiencyTrivialAt {W θ : V → ℝ} (hW : Function.HasTemperateGrowth W)
    {m : V} (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ)
    (hθd : ∀ x, HasDerivAt (fun t : ℝ => θ (x + t • m)) (-(W x)) 0)
    {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (schwartzDomain V) (opL2 (potMomOp W m)) z := by
  intro u hu
  have hmem : MemLp (fun x => (starRingEnd ℂ) (phaseFun θ x) * (u x)) 2
      (volume : Measure V) := by
    have hmeas : AEStronglyMeasurable (fun x => (starRingEnd ℂ) (phaseFun θ x) * (u x))
        (volume : Measure V) :=
      (Complex.continuous_conj.comp ((contDiff_phaseFun hθ).continuous)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable u)
    refine (Lp.memLp u).of_le hmeas (Filter.Eventually.of_forall fun x => ?_)
    simp
  set w : Lp ℂ 2 (volume : Measure V) := hmem.toLp _ with hwdef
  have hwcoe : ∀ᵐ x ∂(volume : Measure V),
      (w x : ℂ) = (starRingEnd ℂ) (phaseFun θ x) * (u x) := hmem.coeFn_toLp
  have hw : ∀ φ : 𝓢(V, ℂ), HasCompactSupport (φ : V → ℂ) →
      ∫ x, (starRingEnd ℂ) ((momentumOp m φ) x) * (w x)
        = z * ∫ x, (starRingEnd ℂ) (φ x) * (w x) := by
    intro φ hφ
    have h1 := hu (schwartzEquiv V (phaseSchwartz hθ φ hφ))
    rw [opL2_apply, schwartzEquiv_coe, inner_toLp_left, inner_toLp_left] at h1
    have hL : ∫ x, (starRingEnd ℂ) ((momentumOp m φ) x) * (w x)
        = ∫ x, (starRingEnd ℂ) ((potMomOp W m (phaseSchwartz hθ φ hφ)) x) * (u x) := by
      refine integral_congr_ae ?_
      filter_upwards [hwcoe] with x hx
      rw [hx, potMomOp_gauge hW hθ hθd φ hφ x, map_mul]
      ring
    have hR : ∫ x, (starRingEnd ℂ) (φ x) * (w x)
        = ∫ x, (starRingEnd ℂ) ((phaseSchwartz hθ φ hφ) x) * (u x) := by
      refine integral_congr_ae ?_
      filter_upwards [hwcoe] with x hx
      rw [hx, phaseSchwartz_apply, map_mul]
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
    · have hn : ‖(starRingEnd ℂ) (phaseFun θ x)‖ = 1 := by
        rw [RCLike.norm_conj]
        exact norm_phaseFun θ x
      rw [h, norm_zero] at hn
      exact absurd hn (by norm_num)
    · exact h
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hae

/-- **The instrument.**  If the real potential `W` has temperate growth and admits a smooth
phase `θ` with `∂_m θ = −W` along the momentum direction, then `W(x) − i ∂_m` is essentially
self-adjoint on the Schwartz core of `L²(V)`. -/
theorem potMomOp_essentiallySelfAdjoint {W θ : V → ℝ} (hW : Function.HasTemperateGrowth W)
    {m : V} (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ)
    (hθd : ∀ x, HasDerivAt (fun t : ℝ => θ (x + t • m)) (-(W x)) 0) :
    EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (potMomOp W m)) :=
  ⟨potMomOp_deficiencyTrivialAt hW hθ hθd (by simp),
    potMomOp_deficiencyTrivialAt hW hθ hθd (by simp)⟩

/-! ## 7. Polynomial potentials along the momentum direction -/

/-- The polynomial potential `W(x) = ∑_{i<n} cᵢ ⟪x, m⟫ⁱ` in the momentum direction. -/
noncomputable def polyPotential (c : ℕ → ℝ) (n : ℕ) (m : V) (x : V) : ℝ :=
  ∑ i ∈ Finset.range n, c i * (inner ℝ x m : ℝ) ^ i

/-- Its transport phase `θ(x) = −∑_{i<n} cᵢ ⟪x,m⟫^{i+1}/((i+1)‖m‖²)`. -/
noncomputable def polyPhase (c : ℕ → ℝ) (n : ℕ) (m : V) (x : V) : ℝ :=
  ∑ i ∈ Finset.range n, -(c i * (inner ℝ x m : ℝ) ^ (i + 1) / ((i + 1) * ‖m‖ ^ 2))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma hasTemperateGrowth_polyPotential (c : ℕ → ℝ) (n : ℕ) (m : V) :
    Function.HasTemperateGrowth (polyPotential c n m) := by
  unfold polyPotential
  refine Function.HasTemperateGrowth.sum fun i _ => ?_
  simpa using (Function.HasTemperateGrowth.const (c i)).mul
    ((Function.hasTemperateGrowth_inner_left m).pow i)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma contDiff_polyPhase (c : ℕ → ℝ) (n : ℕ) (m : V) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (polyPhase c n m) := by
  unfold polyPhase
  refine ContDiff.sum fun i _ => ?_
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : V => (inner ℝ x m : ℝ)) :=
    ((innerSL ℝ).flip m).contDiff
  exact (((contDiff_const.mul (h.pow (i + 1))).div_const _)).neg

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The transport equation `∂_m θ = −W` for the polynomial potential. -/
lemma hasDerivAt_polyPhase_line (c : ℕ → ℝ) (n : ℕ) {m : V} (hm : m ≠ 0) (x : V) :
    HasDerivAt (fun t : ℝ => polyPhase c n m (x + t • m)) (-(polyPotential c n m x)) 0 := by
  have hD0 : (‖m‖ : ℝ) ^ 2 ≠ 0 := by positivity
  have hline : ∀ t : ℝ, (inner ℝ (x + t • m) m : ℝ) = (inner ℝ x m : ℝ) + t * ‖m‖ ^ 2 := by
    intro t
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hfun : (fun t : ℝ => polyPhase c n m (x + t • m))
      = fun t : ℝ => ∑ i ∈ Finset.range n,
          -(c i * ((inner ℝ x m : ℝ) + t * ‖m‖ ^ 2) ^ (i + 1) / ((i + 1) * ‖m‖ ^ 2)) := by
    funext t
    unfold polyPhase
    exact Finset.sum_congr rfl fun i _ => by rw [hline t]
  rw [hfun]
  have hbase : HasDerivAt (fun t : ℝ => (inner ℝ x m : ℝ) + t * ‖m‖ ^ 2) (‖m‖ ^ 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (‖m‖ ^ 2)).const_add (inner ℝ x m : ℝ)
  have hterm : ∀ i ∈ Finset.range n,
      HasDerivAt (fun t : ℝ => -(c i * ((inner ℝ x m : ℝ) + t * ‖m‖ ^ 2) ^ (i + 1)
        / ((i + 1) * ‖m‖ ^ 2))) (-(c i * (inner ℝ x m : ℝ) ^ i)) 0 := by
    intro i _
    have h1 : HasDerivAt (fun t : ℝ => ((inner ℝ x m : ℝ) + t * ‖m‖ ^ 2) ^ (i + 1))
        (((i : ℝ) + 1) * ((inner ℝ x m : ℝ)) ^ i * ‖m‖ ^ 2) 0 := by
      simpa using hbase.pow (i + 1)
    have h2 := ((h1.const_mul (c i)).div_const (((i : ℝ) + 1) * ‖m‖ ^ 2)).neg
    convert h2 using 1
    have hi0 : ((i : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  have hsum := HasDerivAt.sum hterm
  have hfe : (∑ i ∈ Finset.range n, fun t : ℝ =>
        -(c i * ((inner ℝ x m : ℝ) + t * ‖m‖ ^ 2) ^ (i + 1) / (((i : ℝ) + 1) * ‖m‖ ^ 2)))
      = fun t : ℝ => ∑ i ∈ Finset.range n,
        -(c i * ((inner ℝ x m : ℝ) + t * ‖m‖ ^ 2) ^ (i + 1) / (((i : ℝ) + 1) * ‖m‖ ^ 2)) :=
    funext fun t => by simp
  rw [hfe] at hsum
  convert hsum using 1
  simp [polyPotential]

/-- **A polynomial potential in the momentum direction plus the momentum operator.**  For
arbitrary real coefficients `c`, degree bound `n` and direction `m ≠ 0`, the operator
`∑_{i<n} cᵢ ⟪x, m⟫ⁱ − i ∂_m` is symmetric and essentially self-adjoint on the Schwartz core
of `L²(V)`.  With `V = ℝ`, `m = 1`, `c₄ = 1` this is the quartic operator
`x⁴ − i d/dx`: the potential is unbounded, has no `L²` eigenvector and is not a Fourier
multiplier. -/
theorem polyPotential_add_momentum_essentiallySelfAdjoint (c : ℕ → ℝ) (n : ℕ) {m : V}
    (hm : m ≠ 0) :
    EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (potMomOp (polyPotential c n m) m)) :=
  potMomOp_essentiallySelfAdjoint (hasTemperateGrowth_polyPotential c n m)
    (contDiff_polyPhase c n m) (hasDerivAt_polyPhase_line c n hm)

/-- The same operator is symmetric on the Schwartz core. -/
theorem polyPotential_add_momentum_symmetric (c : ℕ → ℝ) (n : ℕ) (m : V) :
    SymmetricOn (schwartzDomain V) (opL2 (potMomOp (polyPotential c n m) m)) :=
  potMomOp_symmetric _ (hasTemperateGrowth_polyPotential c n m) m

end BookProof.MixedLinearEsa
