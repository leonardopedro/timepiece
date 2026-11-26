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

set_option maxHeartbeats 1000000

noncomputable section

namespace BookProof.MehlerTrajMeasure

open MeasureTheory ProbabilityTheory Kernel Filter Topology Preorder Finset Function
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

/-- A cylinder function of the first coordinate is unchanged by replacing the path before time
    `0` with the given initial history.  This is the `a = 0` case of `lintegral_traj`. -/
lemma traj_eval_zero_key (κ' : (n : ℕ) → Kernel (Π i : Finset.Iic n, ℝ) ℝ)
    [∀ n, IsMarkovKernel (κ' n)]
    (y : Π i : Finset.Iic 0, ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    (∫⁻ ω : ℕ → ℝ, s.indicator (fun _ : ℝ => (1 : ENNReal)) (ω 0) ∂traj κ' 0 y) =
      s.indicator (fun _ : ℝ => (1 : ENNReal)) (y ⟨0, by simp⟩) := by
  rw [lintegral_traj (X := fun _ : ℕ => ℝ) (κ := κ') y]
  · have hupd : (fun ω : ℕ → ℝ => s.indicator (fun _ : ℝ => (1 : ENNReal))
        ((updateFinset ω (Finset.Iic 0) y) 0)) =
        fun _ => s.indicator (fun _ : ℝ => (1 : ENNReal)) (y ⟨0, by simp⟩) := by
      funext ω
      simp [updateFinset]
    rw [hupd]
    simp
  · exact (measurable_const.indicator hs).comp (measurable_pi_apply 0)

/-- The initial coordinate of an Ionescu–Tulcea path measure has law `μ₀`.  This is the
    anchor of the finite-marginal identification with the `pathMeasure` family. -/
lemma trajMeasure_eval_zero {μ₀ : Measure ℝ} [IsProbabilityMeasure μ₀]
    (κ' : (n : ℕ) → Kernel (Π i : Finset.Iic n, ℝ) ℝ)
    [∀ n, IsMarkovKernel (κ' n)] :
    (trajMeasure (X := fun _ : ℕ => ℝ) μ₀ κ').map (fun ω => ω 0) = μ₀ := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs]
  rw [← lintegral_indicator_one hs]
  dsimp [trajMeasure]
  rw [Measure.bind_apply
    (f := traj (X := fun _ : ℕ => ℝ) κ' 0)
    (s := (fun ω : ℕ → ℝ => ω 0) ⁻¹' s)
    (hs.preimage (measurable_pi_apply 0)) (Kernel.aemeasurable _)]
  have hsetint (a : Π i : Finset.Iic 0, ℝ) :
      ((traj (X := fun _ : ℕ => ℝ) κ' 0) a) ((fun ω : ℕ → ℝ => ω 0) ⁻¹' s) =
        s.indicator (fun _ : ℝ => (1 : ENNReal)) (a ⟨0, by simp⟩) := by
    rw [← lintegral_indicator_one (hs.preimage (measurable_pi_apply 0))]
    calc
      (∫⁻ ω : ℕ → ℝ, ((fun ω : ℕ → ℝ => ω 0) ⁻¹' s).indicator
          (1 : (ℕ → ℝ) → ENNReal) ω ∂traj κ' 0 a) =
          ∫⁻ ω : ℕ → ℝ, s.indicator (fun _ : ℝ => (1 : ENNReal)) (ω 0) ∂traj κ' 0 a := by
        apply lintegral_congr_ae
        filter_upwards with ω
        by_cases hω : ω 0 ∈ s <;> simp [hω]
      _ = s.indicator (fun _ : ℝ => (1 : ENNReal)) (a ⟨0, by simp⟩) :=
        traj_eval_zero_key κ' a s hs
  simp_rw [hsetint]
  rw [MeasureTheory.lintegral_map]
  · apply lintegral_congr_ae
    filter_upwards with a
    rfl
  · exact (measurable_const.indicator hs).comp
      (measurable_pi_apply (⟨0, by simp⟩ : Finset.Iic 0))
  · exact (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => ℝ)).symm.measurable

/-- A cylinder function of the history up to time `0` is unchanged by `updateFinset`. -/
lemma traj_eval_zero_history_key (κ' : (n : ℕ) → Kernel (Π i : Finset.Iic n, ℝ) ℝ)
    [∀ n, IsMarkovKernel (κ' n)]
    (y : Π i : Finset.Iic 0, ℝ) (T : Set (Π i : Finset.Iic 0, ℝ))
    (hT : MeasurableSet T) :
    (∫⁻ ω : ℕ → ℝ, T.indicator (fun _ : (Π i : Finset.Iic 0, ℝ) => (1 : ENNReal))
      (frestrictLe 0 ω) ∂traj κ' 0 y) =
      T.indicator (fun _ : (Π i : Finset.Iic 0, ℝ) => (1 : ENNReal)) y := by
  rw [lintegral_traj (X := fun _ : ℕ => ℝ) (κ := κ') y]
  · have hupd : (fun ω : ℕ → ℝ => T.indicator
        (fun _ : (Π i : Finset.Iic 0, ℝ) => (1 : ENNReal))
        (frestrictLe 0 (updateFinset ω (Finset.Iic 0) y))) =
        fun _ => T.indicator (fun _ : (Π i : Finset.Iic 0, ℝ) => (1 : ENNReal)) y := by
      funext ω
      apply congrArg (fun h : (Π i : Finset.Iic 0, ℝ) =>
        T.indicator (fun _ => (1 : ENNReal)) h)
      funext i
      simp [frestrictLe, updateFinset]
    rw [hupd]
    simp
  · exact (measurable_const.indicator hT).comp (measurable_frestrictLe 0)

/-- The law of the history up to time `0` is the initial measure pushed through `piUnique`. -/
lemma trajMeasure_eval_zero_history {μ₀ : Measure ℝ} [IsProbabilityMeasure μ₀]
    (κ' : (n : ℕ) → Kernel (Π i : Finset.Iic n, ℝ) ℝ)
    [∀ n, IsMarkovKernel (κ' n)] :
    (trajMeasure (X := fun _ : ℕ => ℝ) μ₀ κ').map (frestrictLe 0) =
      μ₀.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => ℝ)).symm := by
  ext T hT
  rw [Measure.map_apply (measurable_frestrictLe 0) hT]
  rw [← lintegral_indicator_one hT]
  dsimp [trajMeasure]
  rw [Measure.bind_apply
    (f := traj (X := fun _ : ℕ => ℝ) κ' 0)
    (s := frestrictLe 0 ⁻¹' T)
    (hT.preimage (measurable_frestrictLe 0)) (Kernel.aemeasurable _)]
  have hsetint (a : Π i : Finset.Iic 0, ℝ) :
      ((traj (X := fun _ : ℕ => ℝ) κ' 0) a) (frestrictLe 0 ⁻¹' T) =
        T.indicator (fun _ : (Π i : Finset.Iic 0, ℝ) => (1 : ENNReal)) a := by
    rw [← lintegral_indicator_one (hT.preimage (measurable_frestrictLe 0))]
    calc
      (∫⁻ ω : ℕ → ℝ, (frestrictLe 0 ⁻¹' T).indicator
          (1 : (ℕ → ℝ) → ENNReal) ω ∂traj κ' 0 a) =
          ∫⁻ ω : ℕ → ℝ, T.indicator (fun _ : (Π i : Finset.Iic 0, ℝ) => (1 : ENNReal))
            (frestrictLe 0 ω) ∂traj κ' 0 a := by
        apply lintegral_congr_ae
        filter_upwards with ω
        by_cases hω : frestrictLe 0 ω ∈ T <;> simp [hω]
      _ = T.indicator (fun _ : (Π i : Finset.Iic 0, ℝ) => (1 : ENNReal)) a :=
        traj_eval_zero_history_key κ' a T hT
  simp_rw [hsetint]
  rw [lintegral_map']
  · rw [lintegral_map']
    · rfl
    · exact (measurable_const.indicator hT).aemeasurable
    · exact (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => ℝ)).symm.measurable.aemeasurable
  · exact (measurable_const.indicator hT).aemeasurable
  · exact (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => ℝ)).symm.measurable.aemeasurable

/-- The Mehler path measure is pinned at the starting point `x`. -/
theorem mehlerPathMeasure_eval_zero (ρ : ℕ → ℝ) (hρ : ∀ n, (ρ n) ^ 2 < 1) (x : ℝ) :
    (mehlerPathMeasure ρ hρ x).map (fun ω => ω 0) = Measure.dirac x := by
  dsimp [mehlerPathMeasure]
  exact trajMeasure_eval_zero (μ₀ := Measure.dirac x) (mehlerStep ρ hρ)

/-- The joint law of the history up to `n` and the next position is the history law composed
    with the Mehler step kernel.  This is the Markov property of the constructed measure. -/
theorem mehlerPathMeasure_step (ρ : ℕ → ℝ) (hρ : ∀ n, (ρ n) ^ 2 < 1) (x : ℝ) (n : ℕ) :
    (mehlerPathMeasure ρ hρ x).map (fun ω => (frestrictLe n ω, ω (n + 1))) =
      ((mehlerPathMeasure ρ hρ x).map (frestrictLe n)) ⊗ₘ (mehlerStep ρ hρ n) := by
  simpa only [mehlerPathMeasure] using
    (map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ : ℕ => ℝ) (μ₀ := Measure.dirac x) (κ := mehlerStep ρ hρ) (a := n)).symm

/-- The one-step law of the Mehler path measure is the first Mehler kernel: the position at
    time `1` has density `mehlerKernel (ρ 0) x` against Lebesgue measure. -/
lemma kernel_comp_dirac {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] (κ : Kernel α β) (a : α) : (κ ∘ₘ Measure.dirac a) = κ a := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable κ)]
  exact lintegral_dirac a _

theorem mehlerPathMeasure_eval_one (ρ : ℕ → ℝ) (hρ : ∀ n, (ρ n) ^ 2 < 1) (x : ℝ) :
    (mehlerPathMeasure ρ hρ x).map (fun ω => ω 1) =
      volume.withDensity (fun y : ℝ => ENNReal.ofReal (mehlerKernel (ρ 0) x y)) := by
  let P := mehlerPathMeasure ρ hρ x
  have hstep := mehlerPathMeasure_step ρ hρ x 0
  have hsnd := congrArg (fun μ : Measure ((Π i : Finset.Iic 0, ℝ) × ℝ) => μ.snd) hstep
  change (P.map (fun ω => (frestrictLe 0 ω, ω 1))).snd =
    ((P.map (frestrictLe 0)) ⊗ₘ (mehlerStep ρ hρ 0)).snd at hsnd
  have hsnd_rhs : (P.map (fun ω => (frestrictLe 0 ω, ω 1))).snd = P.map (fun ω => ω 1) := by
    change Measure.map Prod.snd (Measure.map (fun ω => (frestrictLe 0 ω, ω 1)) P) = _
    rw [Measure.map_map measurable_snd (by fun_prop)]
    rfl
  rw [hsnd_rhs] at hsnd
  rw [Measure.snd_compProd] at hsnd
  have hhist : P.map (frestrictLe 0) =
      (Measure.dirac x).map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => ℝ)).symm := by
    dsimp [P, mehlerPathMeasure]
    exact trajMeasure_eval_zero_history (μ₀ := Measure.dirac x) (mehlerStep ρ hρ)
  rw [hhist] at hsnd
  have hdirac : (Measure.dirac x).map
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => ℝ)).symm =
      Measure.dirac (fun _ : Finset.Iic 0 => x) := by
    rw [Measure.map_dirac (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => ℝ)).symm.measurable]
    congr
  rw [hdirac, kernel_comp_dirac] at hsnd
  have happly : (mehlerStep ρ hρ 0) (fun _ : Finset.Iic 0 => x) =
      volume.withDensity (fun y : ℝ => ENNReal.ofReal (mehlerKernel (ρ 0) x y)) := by
    dsimp [mehlerStep]
    rw [Kernel.withDensity_apply _ (mehlerStep_meas ρ hρ 0)]
    simp
  rw [happly] at hsnd
  simpa [P, mehlerPathMeasure] using hsnd

end BookProof.MehlerTrajMeasure
