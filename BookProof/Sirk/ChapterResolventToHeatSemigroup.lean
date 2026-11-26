import Mathlib
import BookProof.Sirk.ChapterHeatSemigroupBoundedTransfer

/-!
# Chapter ResolventToHeatSemigroup — H4's resolvent-to-semigroup bridge

`ChapterHeatSemigroupBoundedTransfer` proves that operator-norm convergence of bounded
generators implies operator-norm convergence of the heat semigroups `exp(−τA_n)`.  H4's input,
however, is formulated as convergence of resolvents `(A_n + γ)⁻¹`.  This chapter supplies the
missing algebraic step in the bounded case: inversion is continuous at a unit of a Banach
algebra (`NormedRing.inverse_continuousAt`), so norm convergence of the resolvents at one
resolvent point `γ` implies norm convergence of the generators themselves, and hence
convergence of the heat semigroups at every fixed time.

No unbounded operator, nonnegative self-adjointness or physical Hamiltonian is used.  The
result is conditional on each `A_n + γ` (and the limit) being a unit of `E →L[ℂ] E`; it does
not replace the unbounded strong-resolvent-to-heat theorem, which remains open.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace BookProof.ResolventToHeatSemigroup

open Filter Topology
open BookProof.HeatSemigroupBoundedTransfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local notation "R" => E →L[ℂ] E

/-- Norm convergence of the resolvents at one point implies norm convergence of the generators.
    The proof applies continuity of inversion twice: resolvents converge to the limit resolvent,
    which is a unit, so their inverses converge back to the original operators. -/
theorem tendsto_of_tendsto_resolvent {A : ℕ → R} {A₀ : R} {γ : ℂ}
    (hunit : ∀ n, IsUnit (A n + γ • (1 : R)))
    (hunit₀ : IsUnit (A₀ + γ • (1 : R)))
    (hres : Tendsto (fun n => Ring.inverse (A n + γ • (1 : R))) atTop
      (𝓝 (Ring.inverse (A₀ + γ • (1 : R))))) :
    Tendsto A atTop (𝓝 A₀) := by
  let u : ℕ → Rˣ := fun n => (hunit n).unit
  let u₀ : Rˣ := hunit₀.unit
  have hu : ∀ n, (u n : R) = A n + γ • (1 : R) := fun n => (hunit n).unit_spec
  have hu₀ : (u₀ : R) = A₀ + γ • (1 : R) := hunit₀.unit_spec
  have hinv_unit (v : Rˣ) : Ring.inverse (v : R) = (↑(v⁻¹) : R) := by simp
  have hres' : Tendsto (fun n => (↑((u n)⁻¹) : R)) atTop (𝓝 (↑(u₀⁻¹) : R)) := by
    convert hres using 1
    · funext n
      rw [← hu n, hinv_unit]
    · rw [← hu₀, hinv_unit]
  have hcont : ContinuousAt Ring.inverse (↑(u₀⁻¹) : R) :=
    NormedRing.inverse_continuousAt (u₀⁻¹)
  have hinv := hcont.tendsto.comp hres'
  have hu_tendsto : Tendsto (fun n => (u n : R)) atTop (𝓝 (u₀ : R)) := by
    simpa [Function.comp_def] using hinv
  have hsum : Tendsto (fun n => A n + γ • (1 : R)) atTop (𝓝 (A₀ + γ • (1 : R))) := by
    simpa [hu, hu₀] using hu_tendsto
  have hconst : Tendsto (fun _ : ℕ => γ • (1 : R)) atTop (𝓝 (γ • (1 : R))) :=
    tendsto_const_nhds
  simpa using hsum.sub hconst

omit [CompleteSpace E] in
/-- Quantitative form: the generator distance is controlled by the resolvent distance and the
    two norms `‖A + γ‖`, `‖A₀ + γ‖`.  It is the resolvent identity `A − A₀ =
    (A₀ + γ)((A₀ + γ)⁻¹ − (A + γ)⁻¹)(A + γ)` plus submultiplicativity of the operator norm. -/
theorem norm_sub_le_resolvent {A A₀ : R} {γ : ℂ}
    (hA : IsUnit (A + γ • (1 : R))) (hA₀ : IsUnit (A₀ + γ • (1 : R))) :
    ‖A - A₀‖ ≤ ‖A₀ + γ • (1 : R)‖ *
      ‖Ring.inverse (A₀ + γ • (1 : R)) - Ring.inverse (A + γ • (1 : R))‖ *
      ‖A + γ • (1 : R)‖ := by
  let u : Rˣ := hA.unit
  let u₀ : Rˣ := hA₀.unit
  have hu : (u : R) = A + γ • (1 : R) := hA.unit_spec
  have hu₀ : (u₀ : R) = A₀ + γ • (1 : R) := hA₀.unit_spec
  have hid : (u : R) - (u₀ : R) =
      (u₀ : R) * ((↑(u₀⁻¹) : R) - (↑(u⁻¹) : R)) * (u : R) := by
    rw [mul_sub, sub_mul]
    simp
  have hinv_unit (v : Rˣ) : Ring.inverse (v : R) = (↑(v⁻¹) : R) := by simp
  have hsub : A - A₀ = (A + γ • (1 : R)) - (A₀ + γ • (1 : R)) := by abel
  rw [hsub, ← hu, ← hu₀, hid]
  rw [hinv_unit u₀, hinv_unit u]
  have h1 : ‖(u₀ : R).comp ((↑(u₀⁻¹) : R) - (↑(u⁻¹) : R))‖ ≤
      ‖(u₀ : R)‖ * ‖(↑(u₀⁻¹) : R) - (↑(u⁻¹) : R)‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have h2 : ‖((u₀ : R).comp ((↑(u₀⁻¹) : R) - (↑(u⁻¹) : R))).comp (u : R)‖ ≤
      ‖(u₀ : R).comp ((↑(u₀⁻¹) : R) - (↑(u⁻¹) : R))‖ * ‖(u : R)‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have hu_nonneg : 0 ≤ ‖(u : R)‖ := norm_nonneg _
  have hmul := mul_le_mul_of_nonneg_right h1 hu_nonneg
  change ‖((u₀ : R).comp ((↑(u₀⁻¹) : R) - (↑(u⁻¹) : R))).comp (u : R)‖ ≤
    ‖(u₀ : R)‖ * ‖(↑(u₀⁻¹) : R) - (↑(u⁻¹) : R)‖ * ‖(u : R)‖
  linarith

/-- At every fixed Euclidean time, norm resolvent convergence implies norm convergence of the
    bounded heat semigroups.  This is the bounded counterpart of H4's requested transfer. -/
theorem heatSemigroup_tendsto_of_resolvent {A : ℕ → R} {A₀ : R} {γ : ℂ}
    (hunit : ∀ n, IsUnit (A n + γ • (1 : R)))
    (hunit₀ : IsUnit (A₀ + γ • (1 : R)))
    (hres : Tendsto (fun n => Ring.inverse (A n + γ • (1 : R))) atTop
      (𝓝 (Ring.inverse (A₀ + γ • (1 : R))))) (τ : ℝ) :
    Tendsto (fun n => heatSemigroup τ (A n)) atTop (𝓝 (heatSemigroup τ A₀)) :=
  heatSemigroup_tendsto (tendsto_of_tendsto_resolvent hunit hunit₀ hres) τ

end BookProof.ResolventToHeatSemigroup
