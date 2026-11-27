import Mathlib
import BookProof.OSReconstruction.ChapterPathMeasureInduction
import BookProof.OSReconstruction.ChapterStrangPotentialWeight

/-!
# Chapter WeightedPathMeasure — H3's Strang-weighted path measure

Attaches the interacting potential weight of `ChapterStrangPotentialWeight` to the finite-slice
path measure of `ChapterPathMeasureInduction` and proves the elementary bounds H3 needs:

* for a potential bounded below by `m`, the weight is at most `exp(−(ε N m))`;
* hence the weighted path measure has total mass at most `exp(−(ε N m))` when `ε ≥ 0`;
* for a constant potential `c` the mass is exactly `exp(−(ε N c))`.

This is the measure-integrated form of the Strang bound.  The `N → ∞` transfer with the
potential and the interacting-sector reflection positivity remain open.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace BookProof.WeightedPathMeasure

open MeasureTheory Filter Topology
open BookProof.FinitePathMeasure
open BookProof.PathMeasureInduction
open BookProof.StrangPotentialWeight

/-- The Strang weight of a potential bounded below by `m` is at most `exp(−ε N m)`. -/
theorem strangWeight_le_of_floor {ε m : ℝ} (hε : 0 ≤ ε) (V : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    (hV : ∀ q, m ≤ V q) (z : ℕ → ℝ) :
    strangWeight ε V N z ≤ Real.exp (-(ε * N * m)) := by
  rw [strangWeight]
  apply Real.exp_le_exp.mpr
  have hmid : ∀ j ∈ Finset.Icc 1 (N - 1), m ≤ V (z j) := by
    intro j hj
    exact hV (z j)
  have hsum : (Finset.Icc 1 (N - 1)).sum (fun j => ε * V (z j)) ≥
      (Finset.Icc 1 (N - 1)).sum (fun _ => ε * m) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hV (z j)) hε
  have hcard : (Finset.Icc 1 (N - 1)).card = N - 1 := by
    rw [Nat.card_Icc]
    omega
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at hsum
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  rw [hcast] at hsum
  have hmiddle : ε / 2 * V (z 0) + (Finset.Icc 1 (N - 1)).sum (fun j => ε * V (z j)) +
      ε / 2 * V (z N) ≥ ε * N * m := by
    have h0 := hV (z 0)
    have hNv := hV (z N)
    nlinarith
  linarith

/-- A path on `Fin (N+1)` as a sequence indexed by `ℕ` (zero outside the path). -/
def pathToSeq {N : ℕ} (z : Fin (N + 1) → ℝ) : ℕ → ℝ :=
  fun k => if h : k < N + 1 then z ⟨k, h⟩ else 0

/-- The total mass of the weighted path measure is at most `exp(−ε N m)` when the potential is
    bounded below by `m`.  This is the measure-integrated Strang bound. -/
theorem weighted_pathMeasure_le {ε m : ℝ} (hε : 0 ≤ ε) (V : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    (hV : ∀ q, m ≤ V q) (ρ : Fin N → ℝ) (hρ : ∀ i, (ρ i) ^ 2 < 1) (x : ℝ) :
    (∫⁻ z : Fin (N + 1) → ℝ, ENNReal.ofReal (strangWeight ε V N (pathToSeq z))
      ∂pathMeasure x ρ) ≤ ENNReal.ofReal (Real.exp (-(ε * N * m))) := by
  calc
    (∫⁻ z : Fin (N + 1) → ℝ, ENNReal.ofReal (strangWeight ε V N (pathToSeq z))
        ∂pathMeasure x ρ) ≤
        ∫⁻ _z : Fin (N + 1) → ℝ, ENNReal.ofReal (Real.exp (-(ε * N * m)))
          ∂pathMeasure x ρ := by
      apply lintegral_mono
      intro z
      exact ENNReal.ofReal_le_ofReal (strangWeight_le_of_floor hε V hN hV (pathToSeq z))
    _ = ENNReal.ofReal (Real.exp (-(ε * N * m))) *
        (pathMeasure x ρ) Set.univ := by rw [lintegral_const]
    _ = ENNReal.ofReal (Real.exp (-(ε * N * m))) := by
      rw [pathMeasure_univ N ρ hρ x]
      simp

/-- A measured event on which the action is bounded gives an explicit lower
bound on the partition mass. Both inputs can depend on the regulator. -/
theorem partition_mass_of_action_event {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (S : α → ℝ) (K : ℝ) (E : Set α)
    (hE : MeasurableSet E) (hS : ∀ x ∈ E, S x ≤ K)
    (hw : Integrable (fun x => Real.exp (-S x)) μ) :
    μ.real E * Real.exp (-K) ≤ ∫ x, Real.exp (-S x) ∂μ := by
  have hi := (integrable_const (μ := μ) (Real.exp (-K))).indicator hE
  have h := integral_mono hi hw (fun x => show E.indicator (fun _ => Real.exp (-K)) x ≤ _ by
    by_cases hx : x ∈ E
    · simpa [hx] using Real.exp_le_exp.mpr (neg_le_neg (hS x hx))
    · simp [hx, Real.exp_nonneg])
  simpa only [integral_indicator_const _ hE, smul_eq_mul] using h

/-- If the unnormalized insertion and partition mass converge on the same regulator
filter, a strictly positive limiting mass gives the normalized insertion limit. -/
theorem normalized_insertion_limit {ι α : Type*} [MeasurableSpace α] {l : Filter ι}
    (μ : ι → Measure α) (w F : ι → α → ℝ) {a Z : ℝ}
    (hnum : Tendsto (fun i => ∫ x, w i x * F i x ∂μ i) l (𝓝 a))
    (hmass : Tendsto (fun i => ∫ x, w i x ∂μ i) l (𝓝 Z)) (hZ : 0 < Z) :
    Tendsto (fun i => (∫ x, w i x * F i x ∂μ i) / ∫ x, w i x ∂μ i) l (𝓝 (a / Z)) :=
  hnum.div hmass hZ.ne'

/-- A lower bound on the measured mass converts the unnormalized centered residual
into an error bar for a real insertion at this regulator. -/
theorem normalized_insertion_error {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (w F : α → ℝ) (target ε z : ℝ) (hz : 0 < z) (hmass : z ≤ ∫ x, w x ∂μ)
    (hw : Integrable w μ) (hF : Integrable (fun x => w x * F x) μ)
    (herr : |∫ x, w x * (F x - target) ∂μ| ≤ ε) :
    |(∫ x, w x * F x ∂μ) / (∫ x, w x ∂μ) - target| ≤ ε / z := by
  have hZ := lt_of_lt_of_le hz hmass
  simp_rw [mul_sub] at herr
  rw [integral_sub hF (hw.mul_const target), integral_mul_const] at herr
  rw [div_sub', abs_div, abs_of_pos hZ] <;> try exact hZ.ne'
  exact (div_le_div_of_nonneg_right herr hZ.le).trans
    (div_le_div_of_nonneg_left ((abs_nonneg _).trans herr) hz hmass)

private lemma abs_sub_sub_le (A B C : ℝ) : |A - B - C| ≤ |A| + |B| + |C| := by
  have heq : A - B - C = A + (-B) + (-C) := by ring
  rw [heq]
  calc |A + (-B) + (-C)| ≤ |A + (-B)| + |-C| := abs_add_le _ _
    _ ≤ (|A| + |-B|) + |-C| := by gcongr; exact abs_add_le _ _
    _ = |A| + |B| + |C| := by simp

/-- The centered two-point insertion of `cftproof.md`'s first nested comparison.  Apply
    `normalized_insertion_error` to the product and to both one-point insertions on the **same**
    weighted state, then center: the error of `⟨(F−cF)(G−cG)⟩_w` against `cFG − cF·cG` is
    `(εFG + |cF| εG + |cG| εF)/z`.  No spectral or positivity hypothesis is used, and the mass
    `∫w` cancels exactly in the centering. -/
theorem centered_insertion_error {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (w F G : α → ℝ) (cFG cF cG εFG εF εG z : ℝ) (hz : 0 < z)
    (hmass : z ≤ ∫ x, w x ∂μ) (hw : Integrable w μ)
    (hF : Integrable (fun x => w x * F x) μ)
    (hG : Integrable (fun x => w x * G x) μ)
    (hFG : Integrable (fun x => w x * (F x * G x)) μ)
    (herrFG : |∫ x, w x * (F x * G x - cFG) ∂μ| ≤ εFG)
    (herrF : |∫ x, w x * (F x - cF) ∂μ| ≤ εF)
    (herrG : |∫ x, w x * (G x - cG) ∂μ| ≤ εG) :
    |(∫ x, w x * ((F x - cF) * (G x - cG)) ∂μ) / (∫ x, w x ∂μ) -
        (cFG - cF * cG)| ≤ (εFG + |cF| * εG + |cG| * εF) / z := by
  have hZpos : 0 < ∫ x, w x ∂μ := lt_of_lt_of_le hz hmass
  have h1 := normalized_insertion_error μ w (fun x => F x * G x) cFG εFG z hz hmass hw hFG
    herrFG
  have h2 := normalized_insertion_error μ w F cF εF z hz hmass hw hF herrF
  have h3 := normalized_insertion_error μ w G cG εG z hz hmass hw hG herrG
  have hint : Integrable (fun x => w x * ((F x - cF) * (G x - cG))) μ := by
    have hmain : Integrable (fun x => w x * (F x * G x) - cG * (w x * F x) -
        cF * (w x * G x) + (cF * cG) * w x) μ :=
      ((hFG.sub (hF.const_mul cG)).sub (hG.const_mul cF)).add (hw.const_mul (cF * cG))
    convert hmain using 1
    ext x
    ring
  have hid : (∫ x, w x * ((F x - cF) * (G x - cG)) ∂μ) =
      (∫ x, w x * (F x * G x) ∂μ) - cG * (∫ x, w x * F x ∂μ) -
        cF * (∫ x, w x * G x ∂μ) + (cF * cG) * (∫ x, w x ∂μ) := by
    let A : α → ℝ := fun x => w x * (F x * G x) - cG * (w x * F x) - cF * (w x * G x)
    let B : α → ℝ := fun x => (cF * cG) * w x
    let C : α → ℝ := fun x => w x * (F x * G x) - cG * (w x * F x)
    let D : α → ℝ := fun x => cF * (w x * G x)
    have hC : Integrable C μ := hFG.sub (hF.const_mul cG)
    have hD : Integrable D μ := hG.const_mul cF
    have hAeq : A = fun x => C x - D x := by funext x; dsimp [A, C, D]
    have hfun : (fun x => w x * ((F x - cF) * (G x - cG))) = fun x => A x + B x := by
      funext x
      dsimp [A, B]
      ring
    rw [hfun, integral_add (hAeq ▸ hC.sub hD) (hw.const_mul (cF * cG))]
    rw [hAeq]
    rw [integral_sub hC hD]
    dsimp [C, D]
    rw [integral_sub hFG (hF.const_mul cG)]
    simp only [integral_const_mul]
  rw [hid]
  have hrewrite :
      ((∫ x, w x * (F x * G x) ∂μ) - cG * (∫ x, w x * F x ∂μ) -
          cF * (∫ x, w x * G x ∂μ) + (cF * cG) * (∫ x, w x ∂μ)) /
          (∫ x, w x ∂μ) - (cFG - cF * cG) =
        ((∫ x, w x * (F x * G x) ∂μ) / (∫ x, w x ∂μ) - cFG) -
          cG * ((∫ x, w x * F x ∂μ) / (∫ x, w x ∂μ) - cF) -
          cF * ((∫ x, w x * G x ∂μ) / (∫ x, w x ∂μ) - cG) := by
    field_simp [hZpos.ne']
    ring
  rw [hrewrite]
  calc
    |_ - _ - _| ≤ |(∫ x, w x * (F x * G x) ∂μ) / (∫ x, w x ∂μ) - cFG| +
        |cG * ((∫ x, w x * F x ∂μ) / (∫ x, w x ∂μ) - cF)| +
        |cF * ((∫ x, w x * G x ∂μ) / (∫ x, w x ∂μ) - cG)| := abs_sub_sub_le _ _ _
    _ ≤ εFG / z + |cG| * (εF / z) + |cF| * (εG / z) := by
      gcongr
      · simpa [abs_mul] using mul_le_mul_of_nonneg_left h2 (abs_nonneg cG)
      · simpa [abs_mul] using mul_le_mul_of_nonneg_left h3 (abs_nonneg cF)
    _ = (εFG + |cF| * εG + |cG| * εF) / z := by ring

end BookProof.WeightedPathMeasure
