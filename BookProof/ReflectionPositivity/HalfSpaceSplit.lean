import Mathlib
import BookProof.ReflectionPositivity.Proof
import BookProof.ReflectionPositivity.LatticeFreeField

/-!
# The half-space splitting of the lattice index set

Plan: `cftproof.md`, Phase 3.3, open item 3.  That item records the exact shape of the remaining
gap: `reflection_positivity_continuum` consumes functionals on `Observable = Config → ℝ` with
`Config = Fin latticeDim → ℝ`, whereas the two lattice reflection-positivity theorems
(`latticeGFF_reflectionPositive`, `wilson_reflectionPositive`) are stated on the *product*
configuration spaces `Z₀ × (Y × Y)` with the reflection `reflectConf γ = (γ.1, (γ.2.2, γ.2.1))`
swapping the two half-space factors.  What is missing is therefore a modelling choice, not
analysis: **split `Fin latticeDim` as `past-half × future-half` and transport the lattice theorems
along it.**

This file makes that choice and carries it out.

* `PosTime`, `NegTime` — the two time halves of the component index set (`isPosTime i` is
  `(coordOf i).2.val < halfCells`), and `negToPos`, the reflection as an equivalence between them
  (`isPosTime_reflectCoord` says exactly that `θ` exchanges the halves).
* **`configSplit`** — `Config ≃ (PosTime → ℝ) × (PosTime → ℝ)`, where *both* factors are indexed
  by the future half: the second reads the future coordinates directly and the first reads the
  past through `θ`.  Indexing both halves the same way is what turns the reflection into a plain
  swap instead of a swap composed with a reindexing.
* **`configSplit_fieldReflection`** — `configSplit (θx) = ((configSplit x).2, (configSplit x).1)`:
  in these coordinates the reflection *is* `reflectConf`.  This is the intertwining the plan asks
  for.
* **`osForm_liftHalf_eq`** — for an observable reading one half, the OS form `ω(θF·F)` is `ω`
  applied to the product-model integrand `fkOSForm`, and **`isReflectionPositive_of_fkOS`**
  transfers nonnegativity of that integrand to `osForm`.  Since
  `fkKernel_reflectionPositive` and `wilson_reflectionPositive` prove exactly
  `0 ≤ ∫ fkOSForm f dμ`, this is the lattice OS statement in the shape
  `reflection_positivity_continuum` consumes as `hRP`.
* **`splitMap`, `osForm_eq_integral_splitMap`** — the same identity after pushing `ω` to split
  coordinates: `ω(θF·F) = ∫ p, fkOSForm f ((), p) ∂(ω.map configSplit)`, which is the shape the
  lattice theorems state their conclusion in, so **`isReflectionPositive_of_splitIntegral`** feeds
  them into `reflection_positivity_continuum`'s `hRP`.

## Honest boundary

The boundary factor is trivial here: `cellsPerBlock = 16` is even, so `θ` has no fixed point and
every component sits in one of the two halves — hence `Config ≃ (PosTime → ℝ) × (PosTime → ℝ)`
rather than `Gz × (Gy × Gy)` with a non-trivial `Gz`, and `PUnit` carries the boundary role in the
`fkOSForm` statements.  The transport is done at the level of measures as well as functionals:
`splitMap ω = ω.map configSplit` pushes a measure on `Config` to the split coordinates, and
**`osForm_eq_integral_splitMap`** says the OS form of a future-half observable *is* the
product-model integral `∫ p, fkOSForm f ((), p) ∂(splitMap ω)`.  So the hypothesis
**`isReflectionPositive_of_splitIntegral`** consumes is literally the conclusion of
`fkKernel_reflectionPositive`/`wilson_reflectionPositive` — nonnegativity of the `ρ ⊗ ν_z ⊗ ν_z`
integral — and the continuum theorem's `hRP` follows from it.  What is *not* formalised is the
identification of `splitMap ω` with `fkKernelMeasure`/`wilsonMeasure`: that needs the index
arithmetic between `PosTime × PosTime` and `Z₀ × (Y × Y)` (and, for Wilson, the plaquette link
classification), and `fkKernel_integral_eq` is where it would land.  The half-space algebra
itself (`PositiveTimeAlgebra`, `thetaObs_dependsOn_negTime`) is untouched: this file supplies the
coordinate split underneath it.
-/

namespace BookProof.ReflectionPositivity

open BookProof.BalabanRG

noncomputable section

/-! ## 1. The two time halves of the component index set -/

/-- The positive-time (future) half of the component index set. -/
abbrev PosTime : Type := {i : Fin latticeDim // isPosTime i}

/-- The negative-time (past) half of the component index set. -/
abbrev NegTime : Type := {i : Fin latticeDim // ¬ isPosTime i}

/-- **The reflection exchanges the two halves**, as an equivalence: `θ` carries a past component to
a future one and is its own inverse.  This is `isPosTime_reflectCoord` read as a bijection, and it
is what makes the split below an equivalence rather than an injection. -/
def negToPos : NegTime ≃ PosTime where
  toFun i := ⟨reflectCoord i.1, (isPosTime_reflectCoord i.1).2 i.2⟩
  invFun j := ⟨reflectCoord j.1, fun h => (isPosTime_reflectCoord j.1).1 h j.2⟩
  left_inv i := Subtype.ext (reflectCoord_involutive i.1)
  right_inv j := Subtype.ext (reflectCoord_involutive j.1)

theorem negToPos_apply_val (i : NegTime) : (negToPos i).1 = reflectCoord i.1 := rfl

theorem negToPos_symm_apply_val (j : PosTime) : (negToPos.symm j).1 = reflectCoord j.1 := rfl

/-! ## 2. The split of a configuration -/

/-- The split of a configuration into its past and future halves, **both indexed by the future
half**: the first factor reads a coordinate through `θ`, the second directly.  Reading the past
through `θ` is what makes the reflection a swap of the two factors. -/
def configSplitFun (x : Config) : (PosTime → ℝ) × (PosTime → ℝ) :=
  (fun j => x (reflectCoord j.1), fun j => x j.1)

/-- The inverse split: read the future half directly and the past half through `θ`. -/
def configJoinFun (p : (PosTime → ℝ) × (PosTime → ℝ)) : Config :=
  fun i => if h : isPosTime i then p.2 ⟨i, h⟩
    else p.1 ⟨reflectCoord i, (isPosTime_reflectCoord i).2 h⟩

theorem configJoin_split (x : Config) : configJoinFun (configSplitFun x) = x := by
  funext i
  change (if h : isPosTime i then (configSplitFun x).2 ⟨i, h⟩
      else (configSplitFun x).1 ⟨reflectCoord i, (isPosTime_reflectCoord i).2 h⟩) = x i
  by_cases h : isPosTime i
  · simp only [dif_pos h, configSplitFun]
  · simp only [dif_neg h, configSplitFun, reflectCoord_involutive]

theorem configSplit_join (p : (PosTime → ℝ) × (PosTime → ℝ)) :
    configSplitFun (configJoinFun p) = p := by
  refine Prod.ext ?_ ?_
  · funext j
    have hneg : ¬ isPosTime (reflectCoord j.1) := fun hc => (isPosTime_reflectCoord j.1).1 hc j.2
    change (configJoinFun p) (reflectCoord j.1) = p.1 j
    change (if h : isPosTime (reflectCoord j.1) then p.2 ⟨reflectCoord j.1, h⟩
      else p.1 ⟨reflectCoord (reflectCoord j.1),
        (isPosTime_reflectCoord (reflectCoord j.1)).2 h⟩) = p.1 j
    rw [dif_neg hneg]
    have hsub : (⟨reflectCoord (reflectCoord j.1),
        (isPosTime_reflectCoord (reflectCoord j.1)).2 hneg⟩ : PosTime) = j :=
      Subtype.ext (reflectCoord_involutive j.1)
    rw [hsub]
  · funext j
    change (configJoinFun p) j.1 = p.2 j
    change (if h : isPosTime j.1 then p.2 ⟨j.1, h⟩
      else p.1 ⟨reflectCoord j.1, (isPosTime_reflectCoord j.1).2 h⟩) = p.2 j
    simp only [dif_pos j.2]

/-- **The half-space splitting of the lattice index set**: a configuration is a pair (past read
through `θ`, future), both indexed by the future half. -/
def configSplit : Config ≃ (PosTime → ℝ) × (PosTime → ℝ) where
  toFun := configSplitFun
  invFun := configJoinFun
  left_inv := configJoin_split
  right_inv := configSplit_join

theorem configSplit_apply (x : Config) :
    configSplit x = (fun j => x (reflectCoord j.1), fun j => x j.1) := rfl

/-! ## 3. The reflection is the swap in split coordinates -/

/-- `θ` acts pointwise by reading the reflected component. -/
theorem fieldReflection_apply (x : Config) (i : Fin latticeDim) :
    fieldReflection x i = x (reflectCoord i) := rfl

/-- **The intertwining**: in split coordinates the reflection is the swap of the two halves, i.e.
exactly `reflectConf` of the product model.  This is the statement `cftproof.md` item 3 asks for,
and it is what lets the product-model OS theorems be read on `Config`. -/
theorem configSplit_fieldReflection (x : Config) :
    configSplit (fieldReflection x) = ((configSplit x).2, (configSplit x).1) := by
  refine Prod.ext ?_ ?_
  · funext j
    change (fieldReflection x) (reflectCoord j.1) = x j.1
    rw [fieldReflection_apply, reflectCoord_involutive]
  · funext j
    change (fieldReflection x) j.1 = x (reflectCoord j.1)
    rw [fieldReflection_apply]

/-! ## 4. The OS form in split coordinates -/

/-- **`θF·F` for a split observable is the reflected product**: `θ` swaps the two halves of the
argument, so the OS form of a functional reads the product-model integrand. -/
theorem thetaObs_split (G : (PosTime → ℝ) × (PosTime → ℝ) → ℝ) (x : Config) :
    thetaObs (fun y => G (configSplit y)) x = G ((configSplit x).2, (configSplit x).1) := by
  simp only [thetaObs, configSplit_fieldReflection]

/-- The OS form of a split observable, in split coordinates. -/
theorem osForm_split (ω : Observable → ℝ) (G : (PosTime → ℝ) × (PosTime → ℝ) → ℝ) :
    osForm ω (fun y => G (configSplit y)) (fun y => G (configSplit y))
      = ω (fun x => G ((configSplit x).2, (configSplit x).1) * G (configSplit x)) := by
  have h : (thetaObs (fun y => G (configSplit y)) * fun y => G (configSplit y))
      = fun x => G ((configSplit x).2, (configSplit x).1) * G (configSplit x) := by
    funext x
    simp only [Pi.mul_apply, thetaObs, configSplit_fieldReflection]
  simp only [osForm, h]

/-- **The OS form of a half-space observable is the product-model integrand.**  Reading the future
half, `ω(θF·F)` is `ω` applied to `fkOSForm f` at the configuration split into
`((), (past, future))` — the exact integrand whose nonnegativity
`fkKernel_reflectionPositive`/`wilson_reflectionPositive` establish. -/
theorem osForm_liftHalf_eq (ω : Observable → ℝ) (f : PUnit → (PosTime → ℝ) → ℝ) :
    osForm ω (fun x => f () ((configSplit x).2)) (fun x => f () ((configSplit x).2))
      = ω (fun x => fkOSForm f ((), ((configSplit x).1, (configSplit x).2))) := by
  have h : (thetaObs (fun y => f () ((configSplit y).2)) * fun y => f () ((configSplit y).2))
      = fun x => fkOSForm f ((), ((configSplit x).1, (configSplit x).2)) := by
    funext x
    simp only [Pi.mul_apply, thetaObs, configSplit_fieldReflection, fkOSForm]
  simp only [osForm, h]

/-- **Feeding `reflection_positivity_continuum`.**  If a functional is nonnegative on the
product-model integrand of every half-space observable, it is reflection positive on every
observable reading the configuration through the future half.  With
`fkKernel_reflectionPositive` (or `wilson_reflectionPositive`) supplying exactly that hypothesis,
this is the lattice OS statement in the form the continuum limit consumes — the OS identity is no
longer an assumption for the observables the lattice theorems cover. -/
theorem isReflectionPositive_of_fkOS (ω : Observable → ℝ)
    (h : ∀ f : PUnit → (PosTime → ℝ) → ℝ,
      0 ≤ ω (fun x => fkOSForm f ((), ((configSplit x).1, (configSplit x).2))))
    (f : PUnit → (PosTime → ℝ) → ℝ) :
    0 ≤ osForm ω (fun y => f () ((configSplit y).2)) (fun y => f () ((configSplit y).2)) := by
  simpa only [osForm_liftHalf_eq] using h f

/-! ## 5. Transport of the measure along the split -/

/-- **The split is measurable**: both factors read coordinates of the configuration. -/
theorem measurable_configSplitFun :
    Measurable (configSplitFun : Config → (PosTime → ℝ) × (PosTime → ℝ)) := by
  refine Measurable.prod ?_ ?_
  · exact measurable_pi_iff.2 fun j => measurable_pi_apply _
  · exact measurable_pi_iff.2 fun j => measurable_pi_apply _

/-- The measure pushed forward to split coordinates. -/
def splitMap (ω : MeasureTheory.Measure Config) :
    MeasureTheory.Measure ((PosTime → ℝ) × (PosTime → ℝ)) :=
  ω.map configSplitFun

/-- **Integrating in split coordinates**: the change of variables along the split. -/
theorem integral_splitMap (ω : MeasureTheory.Measure Config)
    (G : (PosTime → ℝ) × (PosTime → ℝ) → ℝ)
    (hG : MeasureTheory.AEStronglyMeasurable G (splitMap ω)) :
    ∫ x, G (configSplitFun x) ∂ω = ∫ p, G p ∂(splitMap ω) := by
  rw [splitMap]
  exact (MeasureTheory.integral_map measurable_configSplitFun.aemeasurable hG).symm

/-- **The OS form of a half-space observable is the product-model integral in split
coordinates.**  This is `osForm_liftHalf_eq` followed by the change of measure, i.e. the shape in
which `fkKernel_reflectionPositive` and `wilson_reflectionPositive` state their conclusion. -/
theorem osForm_eq_integral_splitMap (ω : MeasureTheory.Measure Config)
    (f : PUnit → (PosTime → ℝ) → ℝ)
    (hf : MeasureTheory.AEStronglyMeasurable (fun p => fkOSForm f ((), p)) (splitMap ω)) :
    osForm (fun F => ∫ x, F x ∂ω) (fun x => f () ((configSplit x).2))
        (fun x => f () ((configSplit x).2))
      = ∫ p, fkOSForm f ((), p) ∂(splitMap ω) := by
  rw [osForm_liftHalf_eq]
  exact integral_splitMap ω (fun p => fkOSForm f ((), p)) hf

/-- **Feeding `reflection_positivity_continuum` from a split measure.**  A nonnegative
product-model integral in split coordinates — the conclusion of the lattice OS theorems — makes
the functional `F ↦ ∫ x, F x ∂ω` reflection positive on every observable reading the future half,
which is exactly the `hRP` hypothesis of `reflection_positivity_continuum`. -/
theorem isReflectionPositive_of_splitIntegral (ω : MeasureTheory.Measure Config)
    (h : ∀ f : PUnit → (PosTime → ℝ) → ℝ,
      0 ≤ ∫ p, fkOSForm f ((), p) ∂(splitMap ω))
    (f : PUnit → (PosTime → ℝ) → ℝ)
    (hf : MeasureTheory.AEStronglyMeasurable (fun p => fkOSForm f ((), p)) (splitMap ω)) :
    0 ≤ osForm (fun F => ∫ x, F x ∂ω) (fun y => f () ((configSplit y).2))
      (fun y => f () ((configSplit y).2)) := by
  rw [osForm_eq_integral_splitMap ω f hf]
  exact h f


end

end BookProof.ReflectionPositivity
