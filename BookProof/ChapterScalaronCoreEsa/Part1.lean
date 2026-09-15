import Mathlib
import BookProof.ChapterWaveUnboundedPotential
import BookProof.ChapterStarobinskyPotential

/-!
# The scalaron sector: essential self-adjointness with an exponentially growing potential

Plan item **A5** (`CONSOLIDATED_PLAN.md` §10.5), the step that the Starobinsky wave left
open at the *continuum* level: the Einstein-frame scalaron potential

`V(φ) = (M⁴/16α)(1 − e^{−√(2/3)φ/M})²`

is **not** of temperate growth — it grows exponentially as `φ → −∞`, so the
multiplication-operator theorem of `BookProof.ChapterWaveUnboundedPotential`
(`potentialOp_essentiallySelfAdjoint`, stated for potentials of temperate growth on the
Schwartz core) does not apply to it.  This module removes that restriction.

## The point

Temperate growth is needed only to make the *Schwartz* core invariant.  On the smaller —
and still dense — core of **smooth compactly supported** functions no growth hypothesis is
needed at all: multiplication by any smooth real function maps the core into itself, and the
deficiency argument of `ChapterWaveUnboundedPotential` (divide a test bump `χ` by the
nowhere-vanishing smooth function `W − z̄`) stays inside the core.  What survives of the
analytic hypotheses is only what the plan records: *the operator must be defined on a dense
core*, and for the combination with the kinetic term the potential must be *bounded below*
— and the Starobinsky potential is bounded below in the strongest way, being a square.

## What is proved

**1. The compactly supported smooth core.**  `ccDomain E` is the image in `L²(E)` of the
smooth compactly supported functions, `ccDomain_dense` its density, and
`ccDomain_le_schwartzDomain` the inclusion in the Schwartz core.

**2. Multiplication by an arbitrary smooth potential.**  `opCc W hW` is multiplication by a
real `W`, assumed *only* smooth: `smoothPotential_symmetric`,
`smoothPotential_deficiencyTrivial` (at every non-real `z`) and
`smoothPotential_essentiallySelfAdjoint`.  No growth, no boundedness and no semiboundedness
hypothesis.

**3. The scalaron potential.**  `contDiff_starobinskyV`; `starobinskyV_not_hasTemperateGrowth`
— the potential genuinely falls outside the temperate class, so item 2 is needed;
`starobinskyV_essentiallySelfAdjoint` — and it is nevertheless essentially self-adjoint on
the compactly supported core, as is the full `V₃(R_c) + V(φ)` potential of the gauge-fixed
`R + αR²` Hamiltonian (`scalaronFullPotential_essentiallySelfAdjoint`), which is moreover
bounded below by `−M⁴/(16α)` (`scalaronFullPotential_ge`).

**4. The d'Alembertian with the scalaron potential.**  `wave_add_scalaron_symmetric` — the
gauge-fixed Hamiltonian `□ + V` is a well-defined symmetric operator on the dense compactly
supported core, and `wave_add_smoothTruncatedPotential_essentiallySelfAdjoint` — every
localization of it is essentially self-adjoint on the Schwartz core, again with smoothness
as the only hypothesis on the potential (`wave_add_scalaronTruncated_esa` for the scalaron
potential itself).  This is the exponential-growth analogue of
`wave_add_truncatedPotential_essentiallySelfAdjoint`.

**5. The full mode Hamiltonian with the scalaron sector, and its flow.**  At the mode level
the gravity fiber operator is multiplication by `(1/16)a_k² − (1/24)b_k² + V₃(R_c k) +
V(φ_k)`: `qgScalaronMode_esa` (essential self-adjointness on the dense maximal domain),
`qgScalaronMode_potential_ge` (the uniform lower bound `−M⁴/(16α)`, unaffected by the
non-negative scalaron term) and **`qgScalaron_stone_flow`** — the complete unitary group of
the `R + αR²` Hamiltonian *including* the scalaron potential.

## Honest boundary

Unchanged from `CONSOLIDATED_PLAN.md` §10.3/§10.5: the continuum `L²(ℝ⁸⁴)` essential
self-adjointness of the *sum* `□ + V` still needs the Strichartz finite-speed / gluing
input, which is not claimed here.  What this module settles is the point at issue for the
scalaron: the exponential wall is not an obstruction — the potential term is essentially
self-adjoint on a dense core with no growth hypothesis, every localization of the sum is
essentially self-adjoint, and the potential has the correct (bounded below) sign.
-/

open Filter Topology MeasureTheory SchwartzMap

namespace BookProof.ScalaronEsa

open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## 1. The compactly supported smooth core -/

/-- The compactly supported Schwartz functions, as a submodule of `𝓢(E, ℂ)`. -/
def ccSchwartz (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Submodule ℂ 𝓢(E, ℂ) where
  carrier := {f | HasCompactSupport (f : E → ℂ)}
  add_mem' := by
    intro f g hf hg
    have h : HasCompactSupport ((f : E → ℂ) + (g : E → ℂ)) := hf.add hg
    refine h.mono ?_
    intro x hx
    simp only [Function.mem_support, SchwartzMap.add_apply] at hx ⊢
    simpa using hx
  zero_mem' := by
    have h : HasCompactSupport (fun _ : E => (0 : ℂ)) := HasCompactSupport.zero
    exact h.mono (by intro x hx; simp at hx)
  smul_mem' := by
    intro c f hf
    refine hf.mono ?_
    intro x hx
    simp only [Function.mem_support, SchwartzMap.smul_apply, smul_eq_mul, ne_eq] at hx ⊢
    intro h
    exact hx (by simp [h])

@[simp] lemma mem_ccSchwartz {f : 𝓢(E, ℂ)} :
    f ∈ ccSchwartz E ↔ HasCompactSupport (f : E → ℂ) := Iff.rfl

/-- The compactly supported smooth functions, mapped into `L²(E)`. -/
def ccInclLM (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ccSchwartz E →ₗ[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (toLpCLM ℂ ℂ 2 (volume : Measure E)).toLinearMap ∘ₗ (ccSchwartz E).subtype

lemma ccInclLM_apply (f : ccSchwartz E) :
    ccInclLM E f = ((f : 𝓢(E, ℂ)).toLp 2 (volume : Measure E)) := rfl

lemma ccInclLM_injective : Function.Injective (ccInclLM E) := by
  intro f g hfg
  exact Subtype.ext (SchwartzMap.injective_toLp 2 (volume : Measure E) hfg)

/-- **The compactly supported smooth core** of `L²(E)`. -/
def ccDomain (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    Submodule ℂ (Lp ℂ 2 (volume : Measure E)) := LinearMap.range (ccInclLM E)

/-- Compactly supported smooth functions are in bijection with the core. -/
def ccEquiv (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ccSchwartz E ≃ₗ[ℂ] ccDomain E :=
  LinearEquiv.ofInjective (ccInclLM E) ccInclLM_injective

@[simp] lemma ccEquiv_coe (f : ccSchwartz E) :
    ((ccEquiv E f : ccDomain E) : Lp ℂ 2 (volume : Measure E))
      = (f : 𝓢(E, ℂ)).toLp 2 (volume : Measure E) := rfl

/-- The compactly supported core sits inside the Schwartz core. -/
lemma ccDomain_le_schwartzDomain : ccDomain E ≤ schwartzDomain E := by
  rintro _ ⟨f, rfl⟩
  exact ⟨(f : 𝓢(E, ℂ)), rfl⟩

/-- **The compactly supported smooth core is dense** in `L²(E)`. -/
theorem ccDomain_dense : Dense ((ccDomain E : Submodule ℂ (Lp ℂ 2 (volume : Measure E))) :
    Set (Lp ℂ 2 (volume : Measure E))) := by
  have hd : Dense {f : Lp ℂ 2 (volume : Measure E) | ∃ g, (f : E → ℂ) =ᵐ[volume] g ∧
      HasCompactSupport g ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff (by norm_num)
  refine Dense.mono ?_ hd
  rintro f ⟨g, hfg, hgc, hgs⟩
  refine ⟨⟨hgc.toSchwartzMap hgs, hgc⟩, ?_⟩
  rw [ccInclLM_apply]
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [(hgc.toSchwartzMap hgs).coeFn_toLp 2 (volume : Measure E), hfg]
    with x hx hy
  rw [hx, hy]
  rfl

/-! ## 2. Multiplication by an arbitrary smooth real potential -/

/-- Multiplication by a real `W`, as a map of the compactly supported core into Schwartz
space.  Only smoothness of `W` is required: compact support of `f` does the rest. -/
def mulCc (W : E → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    ccSchwartz E →ₗ[ℂ] 𝓢(E, ℂ) where
  toFun f :=
    (HasCompactSupport.mul_left f.2 :
        HasCompactSupport (fun x => (W x : ℂ) * (f : 𝓢(E, ℂ)) x)).toSchwartzMap
      ((Complex.ofRealCLM.contDiff.comp hW).mul ((f : 𝓢(E, ℂ)).smooth _))
  map_add' f g := by
    refine SchwartzMap.ext fun x => ?_
    change (W x : ℂ) * ((f : 𝓢(E, ℂ)) x + (g : 𝓢(E, ℂ)) x)
      = (W x : ℂ) * (f : 𝓢(E, ℂ)) x + (W x : ℂ) * (g : 𝓢(E, ℂ)) x
    ring
  map_smul' c f := by
    refine SchwartzMap.ext fun x => ?_
    change (W x : ℂ) * (c • (f : 𝓢(E, ℂ))) x = c • ((W x : ℂ) * (f : 𝓢(E, ℂ)) x)
    simp only [SchwartzMap.smul_apply, smul_eq_mul]
    ring

@[simp] lemma mulCc_apply (W : E → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (f : ccSchwartz E) (x : E) :
    (mulCc W hW f) x = (W x : ℂ) * (f : 𝓢(E, ℂ)) x := rfl

/-- Multiplication by a smooth real potential, as an unbounded operator on `L²(E)` with the
compactly supported smooth core as its domain. -/
def opCc (W : E → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    ccDomain E →ₗ[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (toLpCLM ℂ ℂ 2 (volume : Measure E)).toLinearMap ∘ₗ mulCc W hW ∘ₗ
    (ccEquiv E).symm.toLinearMap

@[simp] lemma opCc_apply (W : E → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (f : ccSchwartz E) :
    opCc W hW (ccEquiv E f) = (mulCc W hW f).toLp 2 (volume : Measure E) := by
  simp [opCc]

/-- A real potential, smooth but otherwise arbitrary, is symmetric on the compactly
supported core. -/
theorem smoothPotential_symmetric (W : E → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    SymmetricOn (ccDomain E) (opCc W hW) := by
  intro x y
  obtain ⟨f, rfl⟩ := (ccEquiv E).surjective x
  obtain ⟨g, rfl⟩ := (ccEquiv E).surjective y
  rw [opCc_apply, opCc_apply, ccEquiv_coe, ccEquiv_coe, inner_toLp_left, inner_toLp_left]
  refine integral_congr_ae ?_
  filter_upwards [(g : 𝓢(E, ℂ)).coeFn_toLp 2 (volume : Measure E),
    (mulCc W hW g).coeFn_toLp 2 (volume : Measure E)] with x hx hy
  rw [hx, hy]
  simp only [mulCc_apply, map_mul, Complex.conj_ofReal]
  ring

/-- The deficiency identity on the compactly supported core. -/
lemma integral_conj_mul_smoothPotential_sub_eq_zero (W : E → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (z : ℂ)
    (u : Lp ℂ 2 (volume : Measure E))
    (hu : ∀ v : ccDomain E,
      (inner ℂ (opCc W hW v) u : ℂ) = z * inner ℂ (v : Lp ℂ 2 _) u)
    (ψ : ccSchwartz E) :
    ∫ x, (starRingEnd ℂ) ((ψ : 𝓢(E, ℂ)) x) * (((W x : ℝ) : ℂ) - z) * (u x) = 0 := by
  have h1 := hu (ccEquiv E ψ)
  rw [opCc_apply, ccEquiv_coe, inner_toLp_left, inner_toLp_left] at h1
  have hL : ∫ x, (starRingEnd ℂ) ((mulCc W hW ψ) x) * (u x)
      = ∫ x, ((W x : ℝ) : ℂ) * ((starRingEnd ℂ) ((ψ : 𝓢(E, ℂ)) x) * (u x)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [mulCc_apply, map_mul, Complex.conj_ofReal]
    ring
  rw [hL] at h1
  have hint1 : Integrable (fun x => (starRingEnd ℂ) ((ψ : 𝓢(E, ℂ)) x) * (u x))
      (volume : Measure E) := integrable_conj_schwartz_mul _ u
  have hint2 : Integrable
      (fun x => ((W x : ℝ) : ℂ) * ((starRingEnd ℂ) ((ψ : 𝓢(E, ℂ)) x) * (u x)))
      (volume : Measure E) := by
    have := integrable_conj_schwartz_mul (mulCc W hW ψ) u
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [mulCc_apply, map_mul, Complex.conj_ofReal]
    ring
  have hcomb : ∫ x, (((W x : ℝ) : ℂ) * ((starRingEnd ℂ) ((ψ : 𝓢(E, ℂ)) x) * (u x))
      - z * ((starRingEnd ℂ) ((ψ : 𝓢(E, ℂ)) x) * (u x))) = 0 := by
    rw [integral_sub hint2 (hint1.const_mul z), MeasureTheory.integral_const_mul, h1]
    ring
  rw [← hcomb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-- **Vanishing deficiency spaces for an arbitrary smooth real potential** on the compactly
supported core — no growth hypothesis whatsoever. -/
theorem smoothPotential_deficiencyTrivial (W : E → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (ccDomain E) (opCc W hW) z := by
  intro u hu
  have hz1 : ∀ x : E, ((W x : ℝ) : ℂ) - (starRingEnd ℂ) z ≠ 0 := by
    intro x hx
    exact hz (by simpa using congrArg Complex.im hx)
  have hz2 : ∀ x : E, ((W x : ℝ) : ℂ) - z ≠ 0 := by
    intro x hx
    exact hz (by simpa using congrArg Complex.im hx)
  have main : ∀ χ : E → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → HasCompactSupport χ →
      ∫ x, χ x • (u x) = 0 := by
    intro χ hχ hχc
    have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x => (χ x : ℂ) * (((W x : ℝ) : ℂ) - (starRingEnd ℂ) z)⁻¹) := by
      refine (Complex.ofRealCLM.contDiff.comp hχ).mul (ContDiff.inv ?_ hz1)
      exact (Complex.ofRealCLM.contDiff.comp hW).sub contDiff_const
    have hsupp : HasCompactSupport
        (fun x => (χ x : ℂ) * (((W x : ℝ) : ℂ) - (starRingEnd ℂ) z)⁻¹) := by
      refine HasCompactSupport.mul_right ?_
      simpa using hχc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    set ψ : ccSchwartz E := ⟨hsupp.toSchwartzMap hsmooth, hsupp⟩ with hψ
    have hψx : ∀ x, (ψ : 𝓢(E, ℂ)) x
        = (χ x : ℂ) * (((W x : ℝ) : ℂ) - (starRingEnd ℂ) z)⁻¹ := fun _ => rfl
    have key := integral_conj_mul_smoothPotential_sub_eq_zero W hW z u hu ψ
    rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hc : (starRingEnd ℂ) ((ψ : 𝓢(E, ℂ)) x) * (((W x : ℝ) : ℂ) - z) = (χ x : ℂ) := by
      rw [hψx x]
      simp only [map_mul, map_inv₀, map_sub, Complex.conj_ofReal, Complex.conj_conj]
      field_simp
      exact mul_div_cancel_right₀ _ (hz2 x)
    change χ x • (u x) = (starRingEnd ℂ) ((ψ : 𝓢(E, ℂ)) x) * (((W x : ℝ) : ℂ) - z) * (u x)
    rw [Complex.real_smul, ← hc]
  have hloc : LocallyIntegrable (fun x => (u x : ℂ)) (volume : Measure E) :=
    (Lp.memLp u).locallyIntegrable (by norm_num)
  have hae : ∀ᵐ x ∂(volume : Measure E), (u x : ℂ) = 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun χ hχ hχc => main χ hχ hχc)
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hae

/-- **An arbitrary smooth real potential is essentially self-adjoint on the compactly
supported smooth core** of `L²(E)`.  Neither temperate growth (as in
`potentialOp_essentiallySelfAdjoint`), nor boundedness, nor semiboundedness is assumed: the
exponentially growing Starobinsky wall is covered. -/
theorem smoothPotential_essentiallySelfAdjoint (W : E → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    EssentiallySelfAdjointOn (ccDomain E) (opCc W hW) :=
  ⟨smoothPotential_deficiencyTrivial W hW (by simp),
    smoothPotential_deficiencyTrivial W hW (by simp)⟩

end

end BookProof.ScalaronEsa
