import Mathlib
import BookProof.ChapterWaveUnboundedPotential
import BookProof.ChapterStarobinskyPotential
import BookProof.ChapterScalaronCoreEsa.Part1

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
/-! ## 3. The Starobinsky scalaron potential -/

/-- The scalaron potential is smooth. -/
theorem contDiff_starobinskyV (M alpha : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun phi : ℝ => starobinskyV M alpha phi) := by
  unfold starobinskyV
  exact contDiff_const.mul
    ((contDiff_const.sub (Real.contDiff_exp.comp
      ((contDiff_const.mul contDiff_id).div_const M))).pow 2)

/-- **The scalaron potential is not of temperate growth**: it grows exponentially as
`φ → −∞`.  This is why `potentialOp_essentiallySelfAdjoint`, whose hypothesis is temperate
growth, cannot be applied to it — and why the compactly supported core of §2 is needed. -/
theorem starobinskyV_not_hasTemperateGrowth {M alpha : ℝ} (hM : 0 < M) (halpha : 0 < alpha) :
    ¬ Function.HasTemperateGrowth (fun phi : ℝ => starobinskyV M alpha phi) := by
  intro hgrow
  obtain ⟨k, C, hC⟩ := hgrow.2 0
  have hbound : ∀ x : ℝ, starobinskyV M alpha x ≤ |C| * (1 + |x|) ^ k := by
    intro x
    have h := hC x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    have h2 : starobinskyV M alpha x ≤ C * (1 + |x|) ^ k := by
      refine le_trans (le_abs_self _) ?_
      simpa [Real.norm_eq_abs] using h
    exact h2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  set a : ℝ := Real.sqrt (2 / 3) / M with ha_def
  have ha : 0 < a := div_pos (Real.sqrt_pos.mpr (by norm_num)) hM
  set c : ℝ := M ^ 4 / (16 * alpha) with hc_def
  have hc : 0 < c := div_pos (by positivity) (by linarith)
  have hval : ∀ t : ℝ, starobinskyV M alpha (-t) = c * (Real.exp (a * t) - 1) ^ 2 := by
    intro t
    have hexp : -(Real.sqrt (2 / 3)) * (-t) / M = a * t := by
      rw [ha_def]; field_simp
    rw [starobinskyV, hexp, ← hc_def]
    ring
  set B : ℝ := |C| * 2 ^ k with hB_def
  set K : ℝ := c * a ^ (k + 1) / (2 * (Nat.factorial (k + 1))) with hK_def
  have hK : 0 < K := by
    have : (0 : ℝ) < (Nat.factorial (k + 1) : ℝ) := by positivity
    rw [hK_def]; positivity
  set t : ℝ := max 1 (max (Real.log 2 / a) (B / K + 1)) with ht_def
  have ht1 : (1 : ℝ) ≤ t := le_max_left _ _
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have htlog : Real.log 2 / a ≤ t := le_trans (le_max_left _ _) (le_max_right _ _)
  have htB : B / K + 1 ≤ t := le_trans (le_max_right _ _) (le_max_right _ _)
  have hE2 : (2 : ℝ) ≤ Real.exp (a * t) := by
    have hlog : Real.log 2 ≤ a * t := by
      rw [div_le_iff₀ ha] at htlog; linarith [htlog]
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (a * t) := Real.exp_le_exp.mpr hlog
  have hfac : (a * t) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) ≤ Real.exp (a * t) :=
    Real.pow_div_factorial_le_exp (a * t) (by positivity) (k + 1)
  have hsq : Real.exp (a * t) / 2 ≤ (Real.exp (a * t) - 1) ^ 2 := by nlinarith [hE2]
  have hlow : K * t * t ^ k ≤ starobinskyV M alpha (-t) := by
    rw [hval t]
    have h2 : K * t * t ^ k = c * (((a * t) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) / 2) := by
      rw [hK_def]
      have hfpos : (0 : ℝ) < (Nat.factorial (k + 1) : ℝ) := by positivity
      field_simp
      ring
    rw [h2]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hc.le) (mul_le_mul_of_nonneg_left hsq hc.le)
    exact div_le_div_of_nonneg_right hfac (by norm_num)
  have hhigh : starobinskyV M alpha (-t) ≤ B * t ^ k := by
    have h1 := hbound (-t)
    have habs : |(-t)| = t := by rw [abs_neg, abs_of_pos ht0]
    rw [habs] at h1
    refine h1.trans ?_
    have h2 : (1 + t) ^ k ≤ (2 * t) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
    calc |C| * (1 + t) ^ k ≤ |C| * (2 * t) ^ k :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
      _ = B * t ^ k := by rw [hB_def, mul_pow]; ring
  have hmul : K * t ≤ B := le_of_mul_le_mul_right (by linarith) (pow_pos ht0 k)
  have hfinal : B + K ≤ K * t := by
    have h := mul_le_mul_of_nonneg_left htB hK.le
    rw [mul_add, mul_div_cancel₀ _ hK.ne'] at h
    linarith
  linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Smoothness of the scalaron potential read along a direction of a general
finite-dimensional space (the scalaron is one field among many). -/
theorem contDiff_scalaronAlong (M alpha : ℝ) (e : E) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : E => starobinskyV M alpha (inner ℝ x e)) :=
  (contDiff_starobinskyV M alpha).comp ((innerSL ℝ).flip e).contDiff

/-- **The scalaron potential is essentially self-adjoint** on the compactly supported smooth
core of `L²(ℝ)`, exponential wall notwithstanding. -/
theorem starobinskyV_essentiallySelfAdjoint (M alpha : ℝ) :
    EssentiallySelfAdjointOn (ccDomain ℝ)
      (opCc (fun phi : ℝ => starobinskyV M alpha phi) (contDiff_starobinskyV M alpha)) :=
  smoothPotential_essentiallySelfAdjoint _ _

/-- The full gauge-fixed `R + αR²` potential: the regularized conformal-mode parabola plus
the Einstein-frame scalaron potential, as a function of `(R_c, φ)` read off a pair of
directions of the field space. -/
def scalaronFullPotential (M alpha : ℝ) (eRc ephi : E) (x : E) : ℝ :=
  confV M alpha (inner ℝ x eRc) + starobinskyV M alpha (inner ℝ x ephi)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem contDiff_scalaronFullPotential (M alpha : ℝ) (eRc ephi : E) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scalaronFullPotential M alpha eRc ephi) := by
  unfold scalaronFullPotential confV
  refine ContDiff.add ?_ (contDiff_scalaronAlong M alpha ephi)
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : E => (inner ℝ x eRc : ℝ)) :=
    ((innerSL ℝ).flip eRc).contDiff
  exact (contDiff_const.mul h).add (contDiff_const.mul (h.pow 2))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The full potential is bounded below** by `−M⁴/(16α)`: the scalaron term is a square,
so it only helps, and the conformal-mode term is the completed parabola. -/
theorem scalaronFullPotential_ge {M alpha : ℝ} (halpha : 0 < alpha) (eRc ephi : E) (x : E) :
    -(M ^ 4 / (16 * alpha)) ≤ scalaronFullPotential M alpha eRc ephi x := by
  have h1 := confV_ge (M := M) halpha (inner ℝ x eRc)
  have h2 := starobinskyV_nonneg (M := M) halpha (inner ℝ x ephi)
  simp only [scalaronFullPotential]
  linarith

/-- **The full `R + αR²` potential — conformal mode plus scalaron — is essentially
self-adjoint** on the compactly supported smooth core. -/
theorem scalaronFullPotential_essentiallySelfAdjoint (M alpha : ℝ) (eRc ephi : E) :
    EssentiallySelfAdjointOn (ccDomain E)
      (opCc (scalaronFullPotential M alpha eRc ephi)
        (contDiff_scalaronFullPotential M alpha eRc ephi)) :=
  smoothPotential_essentiallySelfAdjoint _ _

/-! ## 4. The d'Alembertian with the scalaron potential -/

/-- The d'Alembertian, restricted to the compactly supported smooth core. -/
def waveCc (n : ℕ) : ccDomain (SpaceTime n) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (SpaceTime n)) :=
  opL2 (waveOp n 0) ∘ₗ Submodule.inclusion ccDomain_le_schwartzDomain

/-- **The gauge-fixed Hamiltonian `□ + W`** on the compactly supported smooth core, for an
arbitrary smooth real potential. -/
def waveAddSmoothPotential (n : ℕ) (W : SpaceTime n → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    ccDomain (SpaceTime n) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (SpaceTime n)) :=
  waveCc n + opCc W hW

/-- A symmetric operator stays symmetric on a smaller domain. -/
theorem symmetricOn_inclusion {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {D D' : Submodule ℂ F} (h : D ≤ D') (T : D' →ₗ[ℂ] F) (hT : SymmetricOn D' T) :
    SymmetricOn D (T ∘ₗ Submodule.inclusion h) := by
  intro x y
  simpa using hT (Submodule.inclusion h x) (Submodule.inclusion h y)

theorem waveCc_symmetric (n : ℕ) : SymmetricOn (ccDomain (SpaceTime n)) (waveCc n) :=
  symmetricOn_inclusion _ _ (wave_symmetric n 0)

/-- **`□ + V` with the scalaron potential is a well-defined symmetric operator on a dense
core.**  This is the hypothesis the plan's ESA route requires of the Hamiltonian; the
exponential growth of `V` plays no role, because the core consists of compactly supported
functions. -/
theorem wave_add_smoothPotential_symmetric (n : ℕ) (W : SpaceTime n → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    SymmetricOn (ccDomain (SpaceTime n)) (waveAddSmoothPotential n W hW) := by
  intro x y
  have h1 := waveCc_symmetric n x y
  have h2 := smoothPotential_symmetric W hW x y
  simp only [waveAddSmoothPotential, LinearMap.add_apply, inner_add_left, inner_add_right]
  linear_combination h1 + h2

/-- The scalaron Hamiltonian `□ + V(φ)` of the gauge-fixed `R + αR²` theory, with the
scalaron field read along a direction `e` of spacetime. -/
theorem wave_add_scalaron_symmetric (n : ℕ) (M alpha : ℝ) (e : SpaceTime n) :
    SymmetricOn (ccDomain (SpaceTime n))
      (waveAddSmoothPotential n (fun x => starobinskyV M alpha (inner ℝ x e))
        (contDiff_scalaronAlong M alpha e)) :=
  wave_add_smoothPotential_symmetric _ _ _

/-- **Localization with no growth hypothesis.**  For an arbitrary *smooth* real potential
`W` — the Starobinsky wall included — and every radius `R` there is a truncation `W_R`,
agreeing with `W` on the ball of radius `R` and vanishing outside the ball of radius
`R + 1`, for which `□ + W_R` is essentially self-adjoint on the Schwartz core.  This is
`wave_add_truncatedPotential_essentiallySelfAdjoint` with temperate growth removed. -/
theorem wave_add_smoothTruncatedPotential_essentiallySelfAdjoint (n : ℕ)
    (W : SpaceTime n → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (R : ℝ) :
    ∃ WR : SpaceTime n → ℝ, Function.HasTemperateGrowth WR ∧
      (∀ x, ‖x‖ ≤ R → WR x = W x) ∧ (∀ x, R + 1 ≤ ‖x‖ → WR x = 0) ∧
      EssentiallySelfAdjointOn (schwartzDomain (SpaceTime n))
        (opL2 (waveOp n 0 + potentialOp WR)) := by
  obtain ⟨χ, hχsmooth, hχc, hχone, -, hχzero, -⟩ := exists_smooth_cutoff (V := SpaceTime n) R
  have hcs : HasCompactSupport (fun x => W x * χ x) := hχc.mul_left
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => W x * χ x) := hW.mul hχsmooth
  refine ⟨fun x => W x * χ x, hcs.hasTemperateGrowth hsmooth, ?_, ?_, ?_⟩
  · intro x hx
    change W x * χ x = W x
    rw [hχone x hx, mul_one]
  · intro x hx
    change W x * χ x = 0
    rw [hχzero x hx, mul_zero]
  · exact wave_add_boundedPotentialOp_essentiallySelfAdjoint n _
      (hcs.hasTemperateGrowth hsmooth)
      (memLp_top_of_continuous_of_hasCompactSupport
        (hW.continuous.mul hχsmooth.continuous) hcs)

/-- Every localization of the scalaron Hamiltonian `□ + V(φ)` is essentially self-adjoint on
the Schwartz core. -/
theorem wave_add_scalaronTruncated_esa (n : ℕ) (M alpha : ℝ) (e : SpaceTime n) (R : ℝ) :
    ∃ WR : SpaceTime n → ℝ, Function.HasTemperateGrowth WR ∧
      (∀ x, ‖x‖ ≤ R → WR x = starobinskyV M alpha (inner ℝ x e)) ∧
      (∀ x, R + 1 ≤ ‖x‖ → WR x = 0) ∧
      EssentiallySelfAdjointOn (schwartzDomain (SpaceTime n))
        (opL2 (waveOp n 0 + potentialOp WR)) :=
  wave_add_smoothTruncatedPotential_essentiallySelfAdjoint n _
    (contDiff_scalaronAlong M alpha e) R

/-- **The scalaron Hamiltonian through the named Strichartz step.**  For `□ + W` on the
dense compactly supported smooth core the only missing analytic input is the
finite-speed / unique-continuation one — triviality of the adjoint deficiency at every
non-real point — exactly as recorded in
`BookProof.QuantumGravityDensitized.strichartz_esa_of_finiteSpeed`.  The growth of the
potential plays no role in the reduction: the operator is well defined and symmetric on the
core for every smooth `W`, the Starobinsky wall included.  The premise is a *hypothesis*,
never an axiom: nothing here asserts it for the continuum operator. -/
theorem wave_add_smoothPotential_esa_of_finiteSpeed (n : ℕ) (W : SpaceTime n → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (finiteSpeed : ∀ z : ℂ, z.im ≠ 0 →
      DeficiencyTrivialAt (ccDomain (SpaceTime n)) (waveAddSmoothPotential n W hW) z) :
    EssentiallySelfAdjointOn (ccDomain (SpaceTime n)) (waveAddSmoothPotential n W hW) :=
  strichartz_esa_of_finiteSpeed _ finiteSpeed

/-- The scalaron instance of the previous theorem. -/
theorem wave_add_scalaron_esa_of_finiteSpeed (n : ℕ) (M alpha : ℝ) (e : SpaceTime n)
    (finiteSpeed : ∀ z : ℂ, z.im ≠ 0 →
      DeficiencyTrivialAt (ccDomain (SpaceTime n))
        (waveAddSmoothPotential n (fun x => starobinskyV M alpha (inner ℝ x e))
          (contDiff_scalaronAlong M alpha e)) z) :
    EssentiallySelfAdjointOn (ccDomain (SpaceTime n))
      (waveAddSmoothPotential n (fun x => starobinskyV M alpha (inner ℝ x e))
        (contDiff_scalaronAlong M alpha e)) :=
  wave_add_smoothPotential_esa_of_finiteSpeed n _ _ finiteSpeed

/-! ## 5. The mode Hamiltonian with the scalaron sector, and its flow -/

variable (a b : ℕ → ℝ) (M alpha : ℝ) (Rc phi : ℕ → ℝ)

/-- The full `R + αR²` mode potential: the regularized conformal-mode parabola plus the
Einstein-frame scalaron potential. -/
def qgScalaronModePotential : ℕ → ℝ :=
  fun k => confV M alpha (Rc k) + starobinskyV M alpha (phi k)

/-- **The gauge-fixed `R + αR²` mode Hamiltonian including the scalaron sector**:
multiplication by `(1/16)a_k² − (1/24)b_k² + V₃(R_c k) + V(φ_k)`. -/
def qgScalaronModeHamiltonian :
    mulSymbolDomain (qgModeSymbol a b (qgScalaronModePotential M alpha Rc phi)) →ₗ[ℂ] L2Nat :=
  qgModeHamiltonian a b (qgScalaronModePotential M alpha Rc phi)

/-- The potential is bounded below by `−M⁴/(16α)`, uniformly in the mode: the scalaron term
is non-negative, so it does not spoil the conformal-mode bound. -/
theorem qgScalaronMode_potential_ge (halpha : 0 < alpha) (k : ℕ) :
    -(M ^ 4 / (16 * alpha)) ≤ qgScalaronModePotential M alpha Rc phi k := by
  have h1 := confV_ge (M := M) halpha (Rc k)
  have h2 := starobinskyV_nonneg (M := M) halpha (phi k)
  simp only [qgScalaronModePotential]
  linarith

theorem qgScalaronMode_symmetric :
    SymmetricOn (mulSymbolDomain (qgModeSymbol a b (qgScalaronModePotential M alpha Rc phi)))
      (qgScalaronModeHamiltonian a b M alpha Rc phi) :=
  mulSymbolOp_symmetric _ _ (fun _ => le_rfl)

/-- **Essential self-adjointness of the `R + αR²` mode Hamiltonian with the scalaron
potential** on its dense maximal domain. -/
theorem qgScalaronMode_esa :
    EssentiallySelfAdjointOn
      (mulSymbolDomain (qgModeSymbol a b (qgScalaronModePotential M alpha Rc phi)))
      (qgScalaronModeHamiltonian a b M alpha Rc phi) :=
  qgModeHamiltonian_essentiallySelfAdjoint a b (qgScalaronModePotential M alpha Rc phi)

theorem qgScalaronMode_deficiencyTrivialAt {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt
      (mulSymbolDomain (qgModeSymbol a b (qgScalaronModePotential M alpha Rc phi)))
      (qgScalaronModeHamiltonian a b M alpha Rc phi) z :=
  qgModeHamiltonian_deficiencyTrivialAt a b (qgScalaronModePotential M alpha Rc phi) hz

/-- **The continuous flow of the `R + αR²` Hamiltonian including the scalaron potential.**
Essential self-adjointness on the dense maximal domain selects one self-adjoint operator,
and Stone's theorem turns it into the unitary group `e^{−itH}` solving the Schrödinger
equation on the domain, globally in time. -/
theorem qgScalaron_stone_flow :
    ∃ (T : UnboundedSelfAdjoint L2Nat) (U : ℝ → (L2Nat →L[ℂ] L2Nat)),
      IsSelfAdjointExtension (qgScalaronModeHamiltonian a b M alpha Rc phi) T.op ∧
        IsStoneFlow T U :=
  exists_stone_flow_of_esa (qgScalaronModeHamiltonian a b M alpha Rc phi)
    (mulSymbolDomain_dense _) (qgScalaronMode_symmetric a b M alpha Rc phi)
    (qgScalaronMode_esa a b M alpha Rc phi)

end

end BookProof.ScalaronEsa
