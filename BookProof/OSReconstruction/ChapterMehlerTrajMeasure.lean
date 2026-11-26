import Mathlib
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import BookProof.OSReconstruction.ChapterTwoSlicePathMeasure

/-!
# Chapter MehlerTrajMeasure — H3's infinite Mehler path measure

`ChapterPathMeasureInduction` normalizes the finite `N`-slice path measures and
`ChapterPathMeasureMarginal` proves they are projective at the last slice.  This chapter goes
one step further and constructs an actual measure on infinite discrete-time paths `ℕ → ℝ`
whose one-step transition law is the Mehler kernel, using Mathlib's Ionescu–Tulcea theorem
(`ProbabilityTheory.Kernel.trajMeasure`).

The input is a Markov kernel `mehlerStep ρ hρ n` taking the history up to time `n` and
returning the density `mehlerKernel (ρ n) (last history) · volume` for the next position.  Its
Markov property is exactly `mehlerKernel_lintegral`.  `mehlerPathMeasure ρ hρ x` starts at the
Dirac mass `x` and iterates these kernels; it is a probability measure by the Ionescu–Tulcea
construction, and `mehlerPathMeasure_step` identifies the joint law of the history up to `n`
and the next position as the history law composed with the kernel.

This is the infinite-time measure with discrete steps only.  It does not identify its finite
marginals with the `Fin`-indexed `pathMeasure`, does not take the continuum limit
`ε = T/N → 0`, and does not add the interacting Strang weight.  H3's Feynman–Kac convergence to
continuous time remains open.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace BookProof.MehlerTrajMeasure

open MeasureTheory ProbabilityTheory Kernel Filter Topology Preorder Finset
open BookProof.MehlerTransitionDensity
open BookProof.TwoSlicePathMeasure

/-- The Mehler one-step Markov kernel: given the history up to time `n`, the next position has
    density `mehlerKernel (ρ n) (last coordinate)` against Lebesgue measure. -/
def mehlerStep (ρ : ℕ → ℝ) (hρ : ∀ n, (ρ n) ^ 2 < 1) (n : ℕ) :
    Kernel (Π i : Finset.Iic n, ℝ) ℝ :=
  (Kernel.const (Π i : Finset.Iic n, ℝ) volume).withDensity
    (fun hist y => ENNReal.ofReal (mehlerKernel (ρ n) (hist ⟨n, by simp⟩) y))

/-- Measurability of the uncurried Mehler step density. -/
lemma mehlerStep_meas (ρ : ℕ → ℝ) (hρ : ∀ n, (ρ n) ^ 2 < 1) (n : ℕ) :
    Measurable (Function.uncurry
      (fun hist : Π i : Finset.Iic n, ℝ => fun y : ℝ =>
        ENNReal.ofReal (mehlerKernel (ρ n) (hist ⟨n, by simp⟩) y))) := by
  have hc : Continuous (fun p : (Π i : Finset.Iic n, ℝ) × ℝ =>
      mehlerKernel (ρ n) (p.1 ⟨n, by simp⟩) p.2) := by
    unfold mehlerKernel
    have hden : 1 - (ρ n) ^ 2 ≠ 0 := by linarith [hρ n]
    fun_prop (disch := aesop)
  exact hc.measurable.ennreal_ofReal

/-- The Mehler step is a Markov kernel because the density integrates to one. -/
instance mehlerStep_isMarkov (ρ : ℕ → ℝ) (hρ : ∀ n, (ρ n) ^ 2 < 1) (n : ℕ) :
    IsMarkovKernel (mehlerStep ρ hρ n) := by
  classical
  constructor
  intro hist
  constructor
  dsimp [mehlerStep]
  rw [Kernel.withDensity_apply _ (mehlerStep_meas ρ hρ n)]
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  exact mehlerKernel_lintegral (hρ n) (hist ⟨n, by simp⟩)

/-- The infinite discrete-time path measure with Mehler transitions, started at `x`. -/
def mehlerPathMeasure (ρ : ℕ → ℝ) (hρ : ∀ n, (ρ n) ^ 2 < 1) (x : ℝ) : Measure (ℕ → ℝ) :=
  trajMeasure (X := fun _ : ℕ => ℝ) (Measure.dirac x) (mehlerStep ρ hρ)

/-- The path measure is a probability measure (Ionescu–Tulcea). -/
instance mehlerPathMeasure_isProbability (ρ : ℕ → ℝ) (hρ : ∀ n, (ρ n) ^ 2 < 1) (x : ℝ) :
    IsProbabilityMeasure (mehlerPathMeasure ρ hρ x) := by
  dsimp [mehlerPathMeasure]
  infer_instance

/-- The joint law of the history up to `n` and the next position is the history law composed
    with the Mehler step kernel.  This is the Markov property of the constructed measure. -/
theorem mehlerPathMeasure_step (ρ : ℕ → ℝ) (hρ : ∀ n, (ρ n) ^ 2 < 1) (x : ℝ) (n : ℕ) :
    (mehlerPathMeasure ρ hρ x).map (fun ω => (frestrictLe n ω, ω (n + 1))) =
      ((mehlerPathMeasure ρ hρ x).map (frestrictLe n)) ⊗ₘ (mehlerStep ρ hρ n) := by
  simpa only [mehlerPathMeasure] using
    (map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ : ℕ => ℝ) (μ₀ := Measure.dirac x) (κ := mehlerStep ρ hρ) (a := n)).symm

end BookProof.MehlerTrajMeasure
