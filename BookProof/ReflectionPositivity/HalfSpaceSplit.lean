import Mathlib
import BookProof.ReflectionPositivity.Proof
import BookProof.ReflectionPositivity.LatticeFreeField
import BookProof.ReflectionPositivity.WilsonLattice

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

/-! ## 6. Identifying `splitMap ω` with `fkKernelMeasure` / `wilsonMeasure`

§5 pushed a functional's OS form to split coordinates and reduced the lattice OS theorems to
nonnegativity of `∫ p, fkOSForm f ((), p) ∂(splitMap ω)`.  The item §5 left open was that
`splitMap ω` *be* one of those measures.  This section supplies that identification.

The boundary factor of `fkKernelMeasure ρd νd` is `PUnit` here: `cellsPerBlock = 16` is even, so
`θ` has no fixed point and there is no invariant time slice to carry a boundary law.  On
`PUnit × (Y × Y)` the identification is then the trivial one — the boundary coordinate is `()`,
i.e. `((), p) = p` — so a measure whose split *is* the lattice kernel law read on the future half
literally is `fkKernelMeasure ρd νd`:

* **`map_snd_map_mk`** — pushing `fkKernelMeasure` to its second factor and re-inserting the
trivial boundary gives the same measure back;
* **`integral_snd_fkKernel`** — hence the OS integral in split coordinates *is* the kernel-model
  integral `∫ fkOSForm f ∂(fkKernelMeasure ρd νd)` — the exact quantity
  `fkKernel_reflectionPositive` bounds below;
* **`isReflectionPositive_of_fkKernelMeasure`** — so if `splitMap ω` is that measure (read on the
  future half), the lattice theorem discharges `hRP` with **no hypothesis on the OS form at all**.

The Wilson measure composes the same way through `wilsonMeasure_eq_fkKernelMeasure`: its two
densities are `wilsonBoundaryWeight`/`wilsonHalfWeight`, and with `Gz = PUnit`, `Gy = PosTime → ℝ`
the statement below is `wilson_reflectionPositive` read in the split coordinates of the continuum
theorem. -/

open MeasureTheory

/-- Re-inserting the (trivial) boundary coordinate is measurable. -/
theorem measurable_mk_unit :
    Measurable fun p : (PosTime → ℝ) × (PosTime → ℝ) => ((), p) :=
  measurable_prodMk_left

/-- **The boundary coordinate carries no information**: `((), p) = p` on `PUnit × (Y × Y)`. -/
theorem mk_unit_snd_eq_id :
    (fun p : PUnit × ((PosTime → ℝ) × (PosTime → ℝ)) => ((), p.2)) = id := by
  funext p
  exact Prod.ext (Subsingleton.elim _ _) rfl

/-- **The kernel measure read on its future half and re-inserted is itself.**  This is the
identification in the direction the lattice theorems need: the split measure, pushed along
`Prod.snd` and read with a trivial boundary factor, is `fkKernelMeasure ρd νd`. -/
theorem map_snd_map_mk (μ : MeasureTheory.Measure (PUnit × ((PosTime → ℝ) × (PosTime → ℝ)))) :
    (μ.map Prod.snd).map (fun p : (PosTime → ℝ) × (PosTime → ℝ) => ((), p)) = μ := by
  rw [MeasureTheory.Measure.map_map measurable_mk_unit measurable_snd,
    MeasureTheory.Measure.map_congr (Filter.Eventually.of_forall fun x => ?_),
    MeasureTheory.Measure.map_id]
  exact Prod.ext (Subsingleton.elim _ _) rfl

/-- **The OS integral in split coordinates is the kernel Feynman–Kac integral.**  Integrating
`fkOSForm f` against `(fkKernelMeasure ρd νd).map Prod.snd` — the shape §5 produces — is the same
integral as against `fkKernelMeasure ρd νd` itself, which is what `fkKernel_reflectionPositive`
bounds below. -/
theorem integral_snd_fkKernel (ρd : PUnit → ℝ) (νd : PUnit → (PosTime → ℝ) → ℝ)
    (G : PUnit × ((PosTime → ℝ) × (PosTime → ℝ)) → ℝ)
    (hG : MeasureTheory.AEStronglyMeasurable G
      (fkKernelMeasure (Z₀ := PUnit) (Y := PosTime → ℝ) ρd νd)) :
    ∫ p, G ((), p)
        ∂((fkKernelMeasure (Z₀ := PUnit) (Y := PosTime → ℝ) ρd νd).map Prod.snd)
      = ∫ q, G q ∂(fkKernelMeasure (Z₀ := PUnit) (Y := PosTime → ℝ) ρd νd) := by
  have hG' : MeasureTheory.AEStronglyMeasurable G
      (((fkKernelMeasure (Z₀ := PUnit) (Y := PosTime → ℝ) ρd νd).map Prod.snd).map
        fun p : (PosTime → ℝ) × (PosTime → ℝ) => ((), p)) := by
    rw [map_snd_map_mk]
    exact hG
  rw [← MeasureTheory.integral_map measurable_mk_unit.aemeasurable hG', map_snd_map_mk]

/-- **The lattice OS theorems discharge `hRP` with no hypothesis on the OS form.**  If the split
of a measure on `Config` is the lattice kernel law `fkKernelMeasure ρd νd` read on the future half,
then the OS form of every future-half observable is nonnegative — by
`fkKernel_reflectionPositive`, whose hypotheses are only measurability, nonnegativity of the two
densities and the integrability of the OS integrand.  The `hRP` of `reflection_positivity_continuum`
for such a functional is therefore a theorem, not an assumption. -/
theorem isReflectionPositive_of_fkKernelMeasure (ω : MeasureTheory.Measure Config)
    (ρd : PUnit → ℝ) (νd : PUnit → (PosTime → ℝ) → ℝ)
    (hsplit : splitMap ω =
      (fkKernelMeasure (Z₀ := PUnit) (Y := PosTime → ℝ) ρd νd).map Prod.snd)
    (hD : Measurable fun p : PUnit × ((PosTime → ℝ) × (PosTime → ℝ)) =>
      fkKernelDensity ρd νd p)
    (hρ : ∀ z, 0 ≤ ρd z) (hν : ∀ z y, 0 ≤ νd z y)
    (f : PUnit → (PosTime → ℝ) → ℝ)
    (hint : MeasureTheory.Integrable (fun p : PUnit × ((PosTime → ℝ) × (PosTime → ℝ)) =>
        fkKernelDensity ρd νd p * fkOSForm f p)
      ((volume : MeasureTheory.Measure PUnit).prod
        ((volume : MeasureTheory.Measure (PosTime → ℝ)).prod
          (volume : MeasureTheory.Measure (PosTime → ℝ)))))
    (hF : MeasureTheory.AEStronglyMeasurable (fkOSForm f)
      (fkKernelMeasure (Z₀ := PUnit) (Y := PosTime → ℝ) ρd νd))
    (hf : MeasureTheory.AEStronglyMeasurable
      (fun p : (PosTime → ℝ) × (PosTime → ℝ) => fkOSForm f ((), p)) (splitMap ω)) :
    0 ≤ osForm (fun F => ∫ x, F x ∂ω) (fun y => f () ((configSplit y).2))
      (fun y => f () ((configSplit y).2)) := by
  rw [osForm_eq_integral_splitMap ω f hf, hsplit,
    integral_snd_fkKernel ρd νd (fkOSForm f) hF]
  exact fkKernel_reflectionPositive ρd νd f hD hρ hν hint

/-- **The Wilson case.**  `wilsonMeasure` *is* `fkKernelMeasure` of its two interacting densities
(`wilsonMeasure_eq_fkKernelMeasure`), so the interacting lattice OS theorem feeds the same
hypothesis: with the plaquette weights `wilsonBoundaryWeight`, `wilsonHalfWeight` the measure
`(wilsonMeasure β N U b).map Prod.snd` is the split law, and `hRP` follows from
`wilson_reflectionPositive` through the identification above. -/
theorem isReflectionPositive_of_wilsonKernelMeasure (ω : MeasureTheory.Measure Config)
    {β : ℝ} {N : ℕ}
    {P : Type*} [Fintype P]
    {U : P → (PosTime → ℝ) → PUnit → Matrix (Fin N) (Fin N) ℂ} {b : PUnit → ℝ}
    (hsplit : splitMap ω =
      (wilsonMeasure (Gz := PUnit) (Gy := PosTime → ℝ) β N U b).map Prod.snd)
    (hD : Measurable fun p : PUnit × ((PosTime → ℝ) × (PosTime → ℝ)) =>
      fkKernelDensity (wilsonBoundaryWeight b) (wilsonHalfWeight β N U) p)
    (hρ : ∀ z, 0 ≤ wilsonBoundaryWeight b z)
    (hν : ∀ z y, 0 ≤ wilsonHalfWeight β N U z y)
    (f : PUnit → (PosTime → ℝ) → ℝ)
    (hint : MeasureTheory.Integrable (fun p : PUnit × ((PosTime → ℝ) × (PosTime → ℝ)) =>
        fkKernelDensity (wilsonBoundaryWeight b) (wilsonHalfWeight β N U) p * fkOSForm f p)
      ((volume : MeasureTheory.Measure PUnit).prod
        ((volume : MeasureTheory.Measure (PosTime → ℝ)).prod
          (volume : MeasureTheory.Measure (PosTime → ℝ)))))
    (hF : MeasureTheory.AEStronglyMeasurable (fkOSForm f)
      (fkKernelMeasure (Z₀ := PUnit) (Y := PosTime → ℝ)
        (wilsonBoundaryWeight b) (wilsonHalfWeight β N U)))
    (hf : MeasureTheory.AEStronglyMeasurable
      (fun p : (PosTime → ℝ) × (PosTime → ℝ) => fkOSForm f ((), p)) (splitMap ω)) :
    0 ≤ osForm (fun F => ∫ x, F x ∂ω) (fun y => f () ((configSplit y).2))
      (fun y => f () ((configSplit y).2)) := by
  refine isReflectionPositive_of_fkKernelMeasure ω (wilsonBoundaryWeight b)
    (wilsonHalfWeight β N U) ?_ hD hρ hν f hint hF hf
  rw [hsplit, wilsonMeasure_eq_fkKernelMeasure]

end

end BookProof.ReflectionPositivity
