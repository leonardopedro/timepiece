import Mathlib
import BookProof.ReflectionPositivity.FeynmanKac
import BookProof.OSReconstruction.ChapterStrangPotentialWeight

/-!
# Chapter StrangWeightedSliceRP — lifting one-slice reflection positivity to the interacting
Strang-weighted `N`-slice measure (H3)

`cftproof.md` H3 asks for exactly one step here: lift the one-slice OS inequality
(`ReflectionPositivity.ChapterMehlerSliceReflectionPositivity`) to the interacting
Strang-symmetric `N`-slice path measure.  Two facts are needed, and this module supplies both.

## 1. The weighted Feynman–Kac measure

`ReflectionPositivity.FeynmanKac.fk_reflectionPositive` proves

  `0 ≤ ∫ θF · F d(ρ ⊗ ν ⊗ ν)`

for the free Feynman–Kac measure `fkMeasure ρ ν = ρ ⊗ ν ⊗ ν` on `boundary × (past × future)`.
`fkWeightedMeasure ρ ν g` reweights it by the **Dyson–Lieb–Simon density**

  `g z y₋ · g z y₊`,

one positive-time factor on each half (the lattice form of `e^{-V}` with `V = V₊ + θV₊`).
`fkWeighted_reflectionPositive` proves that the reweighted measure is again reflection
positive, by absorbing `g` into the observable: the OS form becomes
`∫ z, (∫ y, F z y g z y ∂ν)² ∂ρ`.

## 2. The Strang weight factorizes at the reflection slice

`strangWeight_even_split` proves, for **every** path `q` on `2M + 1` slices,

  `strangWeight ε V (2*M) q = strangWeight ε V M q · strangWeight ε V M (j ↦ q (M + j))`,

with no symmetry hypothesis: the boundary weight `ε/2 V(q M)` appears once in each factor and
the two interior sums are exactly the two halves.  `strangWeight_reverse` records the invariance
of the weight under reversing the path, and `strangWeight_reflection_factor` puts the two
together so that the second factor is the weight of the **reflected** half — the DLS form.

## Boundary

The free half-space law is `ν` on both halves, i.e. the reflection-invariant case; `g` is a
bounded measurable nonnegative half-weight, so a bounded `V` (or one bounded below).  The
Strang weight is the exact algebraic weight of `ChapterStrangPotentialWeight`; its
identification with a Gibbs measure after integrating out the kinetic factor is not redone here,
the `N → ∞` limit is untouched, and no slab Gram bound is proved.  Axioms are `propext`,
`Classical.choice`, `Quot.sound` only.
-/

noncomputable section

namespace BookProof.StrangWeightedSliceRP

open MeasureTheory
open BookProof.ReflectionPositivity
open BookProof.StrangPotentialWeight

open scoped NNReal ENNReal

/-! ## 1. Reweighting the Feynman–Kac measure by a factorized half-weight -/

section WeightedFK

variable {Z₀ Y : Type*} [MeasurableSpace Z₀] [MeasurableSpace Y]

/-- The interacting Strang-weighted `N`-slice measure: the Feynman–Kac measure
`ρ ⊗ ν ⊗ ν` weighted by one nonnegative factor `g` on each half. -/
def fkWeightedMeasure (ρ : Measure Z₀) (ν : Measure Y) (g : Z₀ → Y → ℝ≥0) :
    Measure (Z₀ × (Y × Y)) :=
  (fkMeasure ρ ν).withDensity fun p => ((g p.1 p.2.1 * g p.1 p.2.2 : ℝ≥0) : ℝ≥0∞)

/-- Measurability of the reflected half-weight. -/
theorem measurable_fkWeight {g : Z₀ → Y → ℝ≥0} (hg : Measurable (Function.uncurry g)) :
    Measurable fun p : Z₀ × (Y × Y) => (g p.1 p.2.1 * g p.1 p.2.2 : ℝ≥0) := by
  have h1 : Measurable fun p : Z₀ × (Y × Y) => g p.1 p.2.1 :=
    hg.comp (f := fun p : Z₀ × (Y × Y) => (p.1, p.2.1)) (by measurability)
  have h2 : Measurable fun p : Z₀ × (Y × Y) => g p.1 p.2.2 :=
    hg.comp (f := fun p : Z₀ × (Y × Y) => (p.1, p.2.2)) (by measurability)
  exact h1.mul h2

/-- **Interacting Strang-weighted reflection positivity.**  If the interaction weight
factorizes across the reflection slice as `g z y₋ · g z y₊`, then the reweighted
Feynman–Kac measure is reflection positive for every integrable half-space observable.
This is the Dyson–Lieb–Simon mechanism in the slice language: the two factors join the two
copies of the observable, and the free positivity of `fk_reflectionPositive` finishes it. -/
theorem fkWeighted_reflectionPositive (ρ : Measure Z₀) (ν : Measure Y) [SFinite ρ] [SFinite ν]
    (g : Z₀ → Y → ℝ≥0) (hg : Measurable (Function.uncurry g))
    (F : Z₀ → Y → ℝ)
    (hF : Integrable (Function.uncurry (fun z y => F z y * (g z y : ℝ))) (ρ.prod ν))
    (h2 : Integrable (fun p : Z₀ × (Y × Y) =>
      (F p.1 p.2.1 * (g p.1 p.2.1 : ℝ)) * (F p.1 p.2.2 * (g p.1 p.2.2 : ℝ)))
      (ρ.prod (ν.prod ν))) :
    0 ≤ ∫ p, fkOSForm F p ∂(fkWeightedMeasure ρ ν g) := by
  unfold fkWeightedMeasure fkMeasure
  rw [integral_withDensity_eq_integral_smul (measurable_fkWeight hg)]
  have hEq : (∫ p : Z₀ × (Y × Y),
        (g p.1 p.2.1 * g p.1 p.2.2 : ℝ≥0) • fkOSForm F p ∂(ρ.prod (ν.prod ν)))
      = ∫ p : Z₀ × (Y × Y), fkOSForm (fun z y => F z y * (g z y : ℝ)) p
          ∂(ρ.prod (ν.prod ν)) := by
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [fkOSForm, NNReal.smul_def, smul_eq_mul, NNReal.coe_mul]
    ring
  rw [hEq]
  exact fk_reflectionPositive ρ ν (fun z y => F z y * (g z y : ℝ)) hF h2

end WeightedFK

/-! ## 2. The Strang weight factors across the middle slice -/

/-- Reversing a path leaves its Strang weight unchanged: the endpoint weights are equal and
the interior sum is permuted by `j ↦ N - j`. -/
theorem strangWeight_reverse (ε : ℝ) (V : ℝ → ℝ) {N : ℕ} (q : ℕ → ℝ) :
    strangWeight ε V N (fun j => q (N - j)) = strangWeight ε V N q := by
  unfold strangWeight
  congr 1
  have hsum : (Finset.Icc 1 (N - 1)).sum (fun j => ε * V (q (N - j))) =
      (Finset.Icc 1 (N - 1)).sum (fun j => ε * V (q j)) := by
    refine Finset.sum_bij (fun a _ => N - a) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      omega
    · intro a1 ha1 a2 ha2 h
      simp only [Finset.mem_Icc] at ha1 ha2
      change N - a1 = N - a2 at h
      omega
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      refine ⟨N - b, ?_, ?_⟩
      · simp only [Finset.mem_Icc]; omega
      · show N - (N - b) = b; omega
    · intro a ha
      show ε * V (q a) = ε * V (q (M + a))
      rfl
  simp only [Nat.sub_zero, Nat.sub_self]
  linarith [hsum]

/-- **The Strang weight splits exactly at the middle slice.**  For a path on `2M + 1` slices,
the weight is the product of the weights of the two half-paths `q 0 … q M` and `q M … q 2M`:
the shared boundary slice carries `ε/2 V(q M)` in each factor.  No symmetry of `q` or of `V`
is assumed. -/
theorem strangWeight_even_split (ε : ℝ) (V : ℝ → ℝ) {M : ℕ} (hM : 1 ≤ M) (q : ℕ → ℝ) :
    strangWeight ε V (2 * M) q =
      strangWeight ε V M q * strangWeight ε V M (fun j => q (M + j)) := by
  unfold strangWeight
  rw [← Real.exp_add]
  congr 1
  have hM1 : (M - 1) + 1 = M := by omega
  have hkey : 2 * M - 1 = M + (M - 1) := by omega
  rw [hkey]
  have hsplit : Finset.Icc 1 (M + (M - 1)) =
      Finset.Icc 1 (M - 1) ∪ insert M (Finset.Icc (M + 1) (M + (M - 1))) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (M - 1))
      (insert M (Finset.Icc (M + 1) (M + (M - 1)))) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.mem_Icc, Finset.mem_insert] at hx hx2
    omega
  have hnotmem : M ∉ Finset.Icc (M + 1) (M + (M - 1)) := by
    simp only [Finset.mem_Icc]
    omega
  have hreindex : (Finset.Icc (M + 1) (M + (M - 1))).sum (fun j => ε * V (q j)) =
      (Finset.Icc 1 (M - 1)).sum (fun j => ε * V (q (M + j))) := by
    refine Finset.sum_bij (fun a _ => M + a) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      exact ⟨le_trans ha.1 (Nat.le_add_left a M), Nat.add_le_add_left ha.2 M⟩
    · intro a1 ha1 a2 ha2 h
      exact Nat.add_left_cancel h
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      have hMb : M ≤ b := by omega
      refine ⟨b - M, ?_, ?_⟩
      · simp only [Finset.mem_Icc]; omega
      · exact Nat.add_sub_of_le hMb
    · intro a ha
      show ε * V (q a) = ε * V (q (M + a))
      rfl
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_insert hnotmem, hreindex]
  rw [show 2 * M = M + M by ring]
  ring

/-- The Strang weight of the doubled path in Dyson–Lieb–Simon form: the second factor is the
weight of the **reflected** half-path `j ↦ q (M + (M - j))`, whose value at each slice of the
future half is the value of the past half at the mirrored slice.  This is exactly the shape the
weighted Feynman–Kac theorem `fkWeighted_reflectionPositive` consumes. -/
theorem strangWeight_reflection_factor (ε : ℝ) (V : ℝ → ℝ) {M : ℕ} (hM : 1 ≤ M) (q : ℕ → ℝ) :
    strangWeight ε V (2 * M) q =
      strangWeight ε V M q * strangWeight ε V M (fun j => q (M + (M - j))) := by
  rw [strangWeight_even_split ε V hM q, ← strangWeight_reverse ε V (fun j => q (M + j))]

end BookProof.StrangWeightedSliceRP
