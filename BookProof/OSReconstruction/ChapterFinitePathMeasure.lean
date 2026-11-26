import Mathlib
import BookProof.ReflectionPositivity.ChapterMehlerTransitionDensity

/-!
# Chapter FinitePathMeasure — H3's N-slice path measure (research)

The path space is `Fin (N+1) → ℝ`, with the start pinned at `z 0 = x`, transition kernel
`K_{ρⱼ}(zⱼ,zⱼ₊₁)`, and base measure `Measure.pi` of a Dirac at coordinate 0 and Lebesgue
elsewhere.  The path measure is that base weighted by the product of the transition densities.
Normalization is proved by induction, splitting `Fin (N+1)` at its last coordinate with
`measurePreserving_piFinSuccAbove` and applying Tonelli to the final kernel factor.

This is the measure assembly H3 needs.  The Strang weight and continuum transfer are open.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace BookProof.FinitePathMeasure

open MeasureTheory Filter Topology
open BookProof.MehlerTransitionDensity

/-- The base path measure: start pinned at `x`, remaining slices Lebesgue. -/
def pathBase (x : ℝ) (N : ℕ) : Measure (Fin (N + 1) → ℝ) :=
  Measure.pi (fun i : Fin (N + 1) => if i = 0 then Measure.dirac x else volume)

/-- The product of transition kernels along a path. -/
def pathDensity {N : ℕ} (ρ : Fin N → ℝ) (z : Fin (N + 1) → ℝ) : ENNReal :=
  ∏ j : Fin N, ENNReal.ofReal (mehlerKernel (ρ j) (z j.castSucc) (z j.succ))

/-- Measurability of the path density. -/
theorem pathDensity_measurable {N : ℕ} (ρ : Fin N → ℝ) (hρ : ∀ i, (ρ i) ^ 2 < 1) :
    Measurable (pathDensity ρ) := by
  classical
  apply Finset.measurable_prod
  intro j hj
  have hjρ : 1 - (ρ j) ^ 2 ≠ 0 := by linarith [hρ j]
  have hc : Continuous (fun z : Fin (N + 1) → ℝ =>
      mehlerKernel (ρ j) (z j.castSucc) (z j.succ)) := by
    unfold mehlerKernel
    fun_prop
  exact hc.measurable.ennreal_ofReal

/-- The finite-slice path measure. -/
def pathMeasure (x : ℝ) {N : ℕ} (ρ : Fin N → ℝ) : Measure (Fin (N + 1) → ℝ) :=
  (pathBase x N).withDensity (pathDensity ρ)

/-- Sigma-finiteness of the base path measure. -/
instance pathBase_sigmaFinite (x : ℝ) (N : ℕ) : SigmaFinite (pathBase x N) := by
  dsimp [pathBase]
  letI : ∀ i : Fin (N + 1), SigmaFinite (if i = 0 then Measure.dirac x else volume) := by
    intro i
    by_cases h : i = 0 <;> simp [h] <;> infer_instance
  infer_instance

/-- Zero-step normalization. -/
theorem pathMeasure_zero (x : ℝ) : pathMeasure x (fun i : Fin 0 => i.elim0) Set.univ = 1 := by
  dsimp [pathMeasure, pathBase, pathDensity]
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  simp [pathDensity]
  haveI : ∀ i : Fin 1, SigmaFinite (if i = 0 then Measure.dirac x else volume) := by
    intro i
    by_cases h : i = 0 <;> simp [h] <;> infer_instance
  rw [Measure.pi_univ]
  simp

/-- Density factorization at the last coordinate. -/
theorem pathDensity_last {N : ℕ} (ρ : Fin (N + 1) → ℝ) (z : Fin (N + 2) → ℝ) :
    pathDensity ρ z =
      pathDensity (fun j : Fin N => ρ j.castSucc)
        (fun j : Fin (N + 1) => z j.castSucc) *
        ENNReal.ofReal (mehlerKernel (ρ (Fin.last N)) (z (Fin.last N).castSucc)
          (z (Fin.last (N + 1)))) := by
  dsimp [pathDensity]
  rw [Fin.prod_univ_castSucc]
  simp

/-- Splitting the base measure at the last coordinate. -/
theorem pathBase_split (x : ℝ) (N : ℕ) :
    Measure.map (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 2) => ℝ) (Fin.last (N + 1)))
      (pathBase x (N + 1)) = volume.prod (pathBase x N) := by
  dsimp [pathBase]
  let μ : Fin (N + 2) → Measure ℝ := fun i => if i = 0 then Measure.dirac x else volume
  haveI : ∀ i : Fin (N + 2), SigmaFinite (μ i) := by
    intro i
    dsimp [μ]
    by_cases h : i = 0 <;> simp [h] <;> infer_instance
  have hmp := measurePreserving_piFinSuccAbove μ (Fin.last (N + 1))
  change Measure.map ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 2) => ℝ)
    (Fin.last (N + 1))) : (Fin (N + 2) → ℝ) → ℝ × (Fin (N + 1) → ℝ))
      (Measure.pi μ) =
        volume.prod (Measure.pi fun i : Fin (N + 1) =>
          if i = 0 then Measure.dirac x else volume)
  rw [hmp.map_eq]
  congr 1
  apply congrArg Measure.pi
  funext j
  by_cases hj : j = 0
  · simp [μ, hj, Fin.succAbove, Fin.last]
  · have hjv : j.val ≠ 0 := by
      intro h
      apply hj
      ext
      exact h
    have hs : (Fin.last (N + 1)).succAbove j ≠ 0 := by
      rw [Fin.succAbove_last]
      intro h
      apply hj
      apply Fin.ext
      have hv := congrArg (fun k : Fin (N + 2) => k.val) h
      simpa using hv
    dsimp [μ]
    rw [if_neg hj, if_neg hs]

end BookProof.FinitePathMeasure
