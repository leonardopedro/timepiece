import Mathlib
import BookProof.OSReconstruction.HalfSpaceFreeState

/-!
# Reflection positivity of the infinite-volume free-field state

Plan: `cftproof.md`, **E3** — `HalfSpaceInfiniteVolumeGaussian` builds the infinite-volume
free-field state as a product of block laws.  This module proves the OS positivity statement *on
that state*: the reflection is the half swap inside every block, the observables are the finite
products over time slices of functions of the positive half of each slice, and the OS form is
nonnegative.

The proof is the infinite-volume form of the finite-volume Feynman–Kac identity
(`HalfSpaceFreeState.gibbsFun_osForm`): with the block law split as `μ ⊗ μ`, the positive and
negative halves of every slice are *independent*, so `ω(θF · F)` factorizes into a product of
squares `∏ (∫ fₙ)² ≥ 0`.  The infinite-volume step is `integral_restrict_infinitePi`: an integral of
a cylinder function against `Measure.infinitePi` is the corresponding finite product integral.

## Contents

* `halfGauss` — the Gaussian law of one time half of a block (independent Gaussians of variance
  `1/2`, the same mass term as `halfAction`);
* `splitBlockLaw`, `splitFreeField` — **the block law in half coordinates** and **the
  infinite-volume free-field state** on `ℕ → (HalfIdx → ℝ) × (HalfIdx → ℝ)`;
* `splitFreeField_isProbability`;
* `chainReflect` — the time reflection (swap the halves of every block), with
  `chainReflect_involutive` and `measurable_chainReflect`;
* `posCylinder` — a positive-time cylinder observable: a finite product over time slices of
  functions of the positive half of each slice;
* `posCylinder_reflect` — `θ` turns it into the same product of the negative halves;
* **`posCylinder_reflectionPositive`** — `0 ≤ ∫ θF · F`;
* `map_pi_prod_pi` — a finite product of pair laws separates into the product of the two
  half-marginals (via `Measure.pi_eq_generateFrom` on measurable rectangles);
* `posCyl`, `posCyl_reflect`, **`posCyl_reflectionPositive`** — the same positivity for the *whole*
  positive-time algebra of cylinder observables: an arbitrary measurable `G` of the positive halves,
  no product structure assumed.  Since the halves are independent copies of one law, the OS form is
  `(∫ G)²`, hence nonnegative.

## Boundary

* The observables are cylinders over a finite set of slices, arbitrary as functions but *not*
  antisymmetrized into the OS algebra: `posCyl_reflectionPositive` covers every measurable cylinder
  function of the positive half, and its proof is the independence of the two halves (for a product
  state the OS form degenerates to `(∫ G)²`).  Passing to the norm closure of `𝔄₊` in `L²` needs the
  OS form on the Lebesgue space, which is not built here.
* The state is written in *half coordinates* (`(HalfIdx → ℝ) × (HalfIdx → ℝ)` per block) rather
  than on `Config`.  `splitBlockLaw` is `freeFieldMeasure` read in those coordinates — both are
  `latticeDim` independent Gaussians of variance `1/2` — but that reindexing
  (`freeFieldMeasure.map configEquiv = splitBlockLaw`) is not proved here, nor is the corresponding
  chain-level identification with `freeFieldInfinite`.
* The state is the ultralocal free field: independent slices, identity covariance.  No interaction,
  no `(−Δ+m²)⁻¹` covariance, and hence no claim about the interacting Gibbs measure.
-/

namespace BookProof.OSReconstruction

open MeasureTheory
open BookProof.BalabanRG BookProof.ReflectionPositivity

noncomputable section

/-! ## The state in half coordinates -/

/-- The Gaussian law of one time half of a block: `halfCells · nComponents` independent
Gaussians of variance `1/2`, the mass term `exp(-x²)`. -/
def halfGauss : Measure (HalfIdx → ℝ) :=
  Measure.pi (fun _ : HalfIdx => ProbabilityTheory.gaussianReal 0 ⟨1 / 2, by norm_num⟩)

instance halfGauss_isProbability : IsProbabilityMeasure halfGauss := by
  unfold halfGauss
  infer_instance

/-- **The block law in half coordinates**: two independent halves. -/
def splitBlockLaw : Measure ((HalfIdx → ℝ) × (HalfIdx → ℝ)) :=
  halfGauss.prod halfGauss

instance splitBlockLaw_isProbability : IsProbabilityMeasure splitBlockLaw := by
  unfold splitBlockLaw
  infer_instance

/-- **The infinite-volume free-field state in half coordinates**: independent blocks over all of
`ℕ`, each split into its two time halves. -/
def splitFreeField : Measure (ℕ → (HalfIdx → ℝ) × (HalfIdx → ℝ)) :=
  Measure.infinitePi (fun _ : ℕ => splitBlockLaw)

/-- The state is a probability measure: its mass on the empty cylinder is one. -/
instance splitFreeField_isProbability : IsProbabilityMeasure splitFreeField := by
  constructor
  have h : (Measure.map (Finset.restrict (∅ : Finset ℕ))
        (Measure.infinitePi (fun _ : ℕ => splitBlockLaw))) Set.univ
      = (Measure.infinitePi (fun _ : ℕ => splitBlockLaw)) Set.univ := by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  rw [splitFreeField, ← h, Measure.infinitePi_map_restrict]
  simp

/-! ## The reflection -/

/-- **Time reflection** of the split chain: swap the two halves of every block. -/
def chainReflect (x : ℕ → (HalfIdx → ℝ) × (HalfIdx → ℝ)) : ℕ → (HalfIdx → ℝ) × (HalfIdx → ℝ) :=
  fun n => (x n).swap

/-- The reflection is an involution. -/
theorem chainReflect_involutive (x : ℕ → (HalfIdx → ℝ) × (HalfIdx → ℝ)) :
    chainReflect (chainReflect x) = x := by
  funext n
  simp [chainReflect]

theorem measurable_chainReflect : Measurable chainReflect := by
  refine measurable_pi_lambda _ fun n => ?_
  fun_prop

/-! ## Positive-time cylinder observables -/

/-- **A positive-time cylinder observable**: a finite product over time slices of functions of the
positive half of each slice. -/
def posCylinder (s : Finset ℕ) (f : (n : ↥s) → (HalfIdx → ℝ) → ℝ)
    (x : ℕ → (HalfIdx → ℝ) × (HalfIdx → ℝ)) : ℝ :=
  ∏ n, f n (x n).1

/-- **The reflection swaps the halves**: `θ` of a positive-time cylinder is the same product of
the negative halves. -/
theorem posCylinder_reflect (s : Finset ℕ) (f : (n : ↥s) → (HalfIdx → ℝ) → ℝ)
    (x : ℕ → (HalfIdx → ℝ) × (HalfIdx → ℝ)) :
    posCylinder s f (chainReflect x) = ∏ n, f n (x n).2 := by
  simp [posCylinder, chainReflect]

/-! ## Reflection positivity -/

/-- **Reflection positivity of the infinite-volume free-field state** on positive-time cylinder
observables. -/
theorem posCylinder_reflectionPositive (s : Finset ℕ)
    (f : (n : ↥s) → (HalfIdx → ℝ) → ℝ) (hf : ∀ n, Measurable (f n)) :
    0 ≤ ∫ x, posCylinder s f (chainReflect x) * posCylinder s f x ∂splitFreeField := by
  have hG : Measurable fun y : (n : ↥s) → (HalfIdx → ℝ) × (HalfIdx → ℝ) =>
      ∏ n, f n (y n).1 * f n (y n).2 := by
    refine Finset.measurable_prod _ fun n _ => ?_
    exact ((hf n).comp (measurable_pi_apply n).fst).mul
      ((hf n).comp (measurable_pi_apply n).snd)
  -- the two factors are products of the two halves of the same slices
  have hprod : ∀ x : ℕ → (HalfIdx → ℝ) × (HalfIdx → ℝ),
      posCylinder s f (chainReflect x) * posCylinder s f x
        = ∏ n, f n (x n).1 * f n (x n).2 := by
    intro x
    have h2 : (∏ n, f n (x n).2) * (∏ n, f n (x n).1)
        = ∏ n, f n (x n).1 * f n (x n).2 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun n _ => mul_comm _ _
    rw [posCylinder_reflect, posCylinder, h2]
  -- push the cylinder function to the finite product
  have h1 : (∫ x, posCylinder s f (chainReflect x) * posCylinder s f x ∂splitFreeField)
      = ∫ x, (fun y : (n : ↥s) → (HalfIdx → ℝ) × (HalfIdx → ℝ) =>
          ∏ n, f n (y n).1 * f n (y n).2) (s.restrict x) ∂splitFreeField := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    change posCylinder s f (chainReflect x) * posCylinder s f x
      = ∏ n, f n (x n).1 * f n (x n).2
    exact hprod x
  rw [h1, splitFreeField]
  rw [integral_restrict_infinitePi (μ := fun _ : ℕ => splitBlockLaw)
    (f := fun y : (n : ↥s) → (HalfIdx → ℝ) × (HalfIdx → ℝ) =>
      ∏ n, f n (y n).1 * f n (y n).2) hG.aestronglyMeasurable]
  rw [integral_fintype_prod_eq_prod (μ := fun _ : ↥s => splitBlockLaw)
    (f := fun (n : ↥s) (p : (HalfIdx → ℝ) × (HalfIdx → ℝ)) => f n p.1 * f n p.2)]
  refine Finset.prod_nonneg fun n _ => ?_
  simp only [splitBlockLaw]
  rw [integral_prod_mul]
  exact mul_self_nonneg _

end

/-! ## General positive-time cylinder observables

The multiplicative cone of the previous section is not the whole positive-time algebra: sums of
products are positive-time observables too, and `(θ(F + G))(F + G)` does not factorize slice by
slice.  For a *product* state the positivity survives arbitrary measurable observables, because the
two halves of the state are independent copies of the same law, so the OS form is the squared
integral of the observable.  This section proves that reduction.

The only non-elementary input is that a product of block laws separates into the product of the two
half-marginals (`map_pi_prod_pi`), which is proved from `Measure.pi_eq_generateFrom` on the
π-system of measurable rectangles. -/

section GeneralCylinders

/-- The π-system of measurable rectangles on a product space. -/
def rectPiSystem (α : Type*) [MeasurableSpace α] : Set (Set (α × α)) :=
  Set.image2 (fun x1 x2 => x1 ×ˢ x2) {s | MeasurableSet s} {t | MeasurableSet t}

theorem generateFrom_rectPiSystem (α : Type*) [MeasurableSpace α] :
    MeasurableSpace.generateFrom (rectPiSystem α) = Prod.instMeasurableSpace :=
  generateFrom_prod

theorem isPiSystem_rectPiSystem (α : Type*) [MeasurableSpace α] :
    IsPiSystem (rectPiSystem α) :=
  isPiSystem_prod

theorem mem_rectPiSystem {α : Type*} [MeasurableSpace α] {s : Set (α × α)} :
    s ∈ rectPiSystem α ↔ ∃ A B : Set α, MeasurableSet A ∧ MeasurableSet B ∧ s = A ×ˢ B := by
  simp only [rectPiSystem, Set.mem_image2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, hA, B, hB, rfl⟩
    exact ⟨A, B, hA, hB, rfl⟩
  · rintro ⟨A, B, hA, hB, rfl⟩
    exact ⟨A, hA, B, hB, rfl⟩

def finiteSpanningSetsIn_rectPiSystem (α : Type*) [MeasurableSpace α]
    (μ : Measure (α × α)) [IsFiniteMeasure μ] : μ.FiniteSpanningSetsIn (rectPiSystem α) :=
  ⟨fun _ => Set.univ,
    fun _ => mem_rectPiSystem.mpr ⟨Set.univ, Set.univ, MeasurableSet.univ, MeasurableSet.univ,
      Set.univ_prod_univ.symm⟩,
    fun _ => by simp,
    by rw [Set.iUnion_const]⟩

/-- The inverse of the separation map of a finite product of pairs. -/
def sepProdInv {ι : Type*} {α : Type*} (q : (ι → α) × (ι → α)) : ι → α × α :=
  fun i => (q.1 i, q.2 i)

theorem measurable_sepProdInv {ι : Type*} {α : Type*} [MeasurableSpace α] :
    Measurable (sepProdInv (ι := ι) (α := α)) := by
  refine measurable_pi_lambda _ fun i => ?_
  exact ((measurable_pi_apply i).comp measurable_fst).prod
    ((measurable_pi_apply i).comp measurable_snd)

/-- The separation map of a finite product of pairs. -/
def sepProd {ι : Type*} {α : Type*} (p : ι → α × α) : (ι → α) × (ι → α) :=
  ((fun i => (p i).1), (fun i => (p i).2))

theorem measurable_sepProd {ι : Type*} {α : Type*} [MeasurableSpace α] :
    Measurable (sepProd (ι := ι) (α := α)) := by
  refine Measurable.prod ?_ ?_
  · exact measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst
  · exact measurable_pi_lambda _ fun i => (measurable_pi_apply i).snd

theorem sepProd_comp_sepProdInv {ι : Type*} {α : Type*} :
    sepProd (ι := ι) (α := α) ∘ sepProdInv = id := by
  funext q
  rfl

/-- **A finite product of pair laws separates into the product of the two half-marginals.** -/
theorem map_pi_prod_pi {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (Measure.pi (fun _ : ι => μ.prod ν)).map (sepProd (ι := ι) (α := α))
      = (Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => ν)) := by
  classical
  have hmain : Measure.pi (fun _ : ι => μ.prod ν)
      = ((Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => ν))).map
          (sepProdInv (ι := ι) (α := α)) := by
    refine Measure.pi_eq_generateFrom (C := fun _ => rectPiSystem α)
      (fun i => generateFrom_rectPiSystem α) (fun i => isPiSystem_rectPiSystem α)
      (fun _ => finiteSpanningSetsIn_rectPiSystem α (μ.prod ν)) ?_
    intro s hs
    choose A B hA hB hAB using fun i => mem_rectPiSystem.mp (hs i)
    have hset : sepProdInv (ι := ι) (α := α) ⁻¹' (Set.univ.pi s)
        = (Set.univ.pi A) ×ˢ (Set.univ.pi B) := by
      ext q
      simp only [sepProdInv, Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_prod, hAB,
        forall_true_left]
      exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩,
        fun h i => ⟨h.1 i, h.2 i⟩⟩
    have hmeas : MeasurableSet (Set.univ.pi s) :=
      MeasurableSet.univ_pi fun i => by rw [hAB i]; exact (hA i).prod (hB i)
    rw [Measure.map_apply measurable_sepProdInv hmeas, hset, Measure.prod_prod,
      Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hAB i, Measure.prod_prod]
  rw [hmain, Measure.map_map measurable_sepProd measurable_sepProdInv,
    sepProd_comp_sepProdInv, Measure.map_id]

/-! ## Reflection positivity on the whole positive-time algebra -/

/-- **A positive-time cylinder observable**: an arbitrary measurable function of the positive halves
of a finite set of time slices (no product structure assumed). -/
def posCyl (s : Finset ℕ) (G : ((n : ↥s) → HalfIdx → ℝ) → ℝ)
    (x : ℕ → (HalfIdx → ℝ) × (HalfIdx → ℝ)) : ℝ :=
  G fun n => (x n).1

/-- The reflection acts on a general positive-time cylinder by reading the negative halves. -/
theorem posCyl_reflect (s : Finset ℕ) (G : ((n : ↥s) → HalfIdx → ℝ) → ℝ)
    (x : ℕ → (HalfIdx → ℝ) × (HalfIdx → ℝ)) :
    posCyl s G (chainReflect x) = G fun n => (x n).2 := by
  simp [posCyl, chainReflect]

/-- **Reflection positivity of the infinite-volume free-field state on general positive-time
cylinder observables.**  Since the two halves are independent copies of the same law, the OS form is
the square of the integral of the observable, hence nonnegative — no product structure on `G` is
needed. -/
theorem posCyl_reflectionPositive (s : Finset ℕ)
    (G : ((n : ↥s) → HalfIdx → ℝ) → ℝ) (hG : Measurable G) :
    0 ≤ ∫ x, posCyl s G (chainReflect x) * posCyl s G x ∂splitFreeField := by
  classical
  set P : Measure ((n : ↥s) → (HalfIdx → ℝ) × (HalfIdx → ℝ)) :=
    Measure.pi (fun _ : ↥s => splitBlockLaw) with hP
  set F : ((n : ↥s) → HalfIdx → ℝ) × ((n : ↥s) → HalfIdx → ℝ) → ℝ :=
    fun q => G q.1 * G q.2 with hF
  have hFmeas : Measurable F := (hG.comp measurable_fst).mul (hG.comp measurable_snd)
  have hhalf : Measurable fun y : (n : ↥s) → (HalfIdx → ℝ) × (HalfIdx → ℝ) =>
      G (fun n => (y n).1) * G (fun n => (y n).2) := by
    have h1 : Measurable fun y : (n : ↥s) → (HalfIdx → ℝ) × (HalfIdx → ℝ) =>
        G (fun n => (y n).1) :=
      hG.comp (measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst)
    have h2 : Measurable fun y : (n : ↥s) → (HalfIdx → ℝ) × (HalfIdx → ℝ) =>
        G (fun n => (y n).2) :=
      hG.comp (measurable_pi_lambda _ fun i => (measurable_pi_apply i).snd)
    exact h1.mul h2
  have hstep : (∫ x, posCyl s G (chainReflect x) * posCyl s G x ∂splitFreeField)
      = ∫ y, G (fun n => (y n).1) * G (fun n => (y n).2) ∂P := by
    have hcongr : ∀ x : ℕ → (HalfIdx → ℝ) × (HalfIdx → ℝ),
        posCyl s G (chainReflect x) * posCyl s G x
          = (fun y : (n : ↥s) → (HalfIdx → ℝ) × (HalfIdx → ℝ) =>
              G (fun n => (y n).1) * G (fun n => (y n).2)) (s.restrict x) := by
      intro x
      simp [posCyl, chainReflect, mul_comm]
    rw [splitFreeField]
    rw [integral_congr_ae (ae_of_all _ hcongr)]
    rw [integral_restrict_infinitePi (μ := fun _ : ℕ => splitBlockLaw)
      (f := fun y : (n : ↥s) → (HalfIdx → ℝ) × (HalfIdx → ℝ) =>
        G (fun n => (y n).1) * G (fun n => (y n).2)) hhalf.aestronglyMeasurable]
  rw [hstep, hP]
  rw [show (∫ y, G (fun n => (y n).1) * G (fun n => (y n).2)
        ∂Measure.pi (fun _ : ↥s => splitBlockLaw))
      = ∫ y, F (sepProd y) ∂Measure.pi (fun _ : ↥s => splitBlockLaw) from
    integral_congr_ae (ae_of_all _ fun y => by simp [F, sepProd])]
  rw [← integral_map (φ := sepProd (ι := ↥s) (α := HalfIdx → ℝ)) measurable_sepProd.aemeasurable
    hFmeas.aestronglyMeasurable]
  rw [show Measure.pi (fun _ : ↥s => splitBlockLaw)
      = Measure.pi (fun _ : ↥s => halfGauss.prod halfGauss) from rfl]
  rw [map_pi_prod_pi (μ := halfGauss) (ν := halfGauss), integral_prod_mul]
  exact mul_self_nonneg _

end GeneralCylinders

end BookProof.OSReconstruction
