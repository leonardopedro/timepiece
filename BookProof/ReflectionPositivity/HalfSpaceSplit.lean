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
* **`isReflectionPositive_of_fkKernelMeasure`** (§6) — that hypothesis is discharged from
  `fkKernel_reflectionPositive` as soon as `splitMap ω` *is* the lattice kernel law read on the
  future half (with `wilsonMeasure_eq_fkKernelMeasure` giving the Wilson case), and §7 constructs
  the first such `ω`: `gffConfigMeasure m`, the Gibbs measure of the mass action on `Config`.
* **`gffConfigMeasure_osForm_nonneg`, `gffConfigMeasure_isReflectionPositive`** (§8) — for that
  state the remaining bookkeeping is carried out: the split law is `ν ⊗ ν` with the same half-space
  density on both sides, so the Feynman–Kac square applies and the OS form is nonnegative for
  **every** future-half observable, with no hypothesis on the state and no integrability side
  condition.

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
integral — and the continuum theorem's `hRP` follows from it.  §6 formalises the identification of
`splitMap ω` with `fkKernelMeasure`/`wilsonMeasure` (conditionally on `ω`), and §8 carries it out
for the mass model `gffConfigMeasure m`, so `hRP` is a theorem for that state.  What stays a
modelling step is the *coupled* case: a nearest-neighbour action does not split as `ν ⊗ ν`, which
is why the free-field OS theorem is stated on the `2n+1`-slice model with a boundary slice
(`latticeGFFMeasure`, law `ρ ⊗ ν_z ⊗ ν_z`).  The half-space algebra itself
(`PositiveTimeAlgebra`, `thetaObs_dependsOn_negTime`) is untouched: this file supplies the
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

/-! ## 7. The finite-volume Gaussian measure on `Config` and its split law

§6 identified `splitMap ω` with the kernel measure *conditionally on* `ω`.  This section constructs
the measure: the Gibbs measure of the mass (ultralocal) Gaussian action
`S(x) = (m/2) Σ_i (x i)²` on `Config`, written as a density against Lebesgue measure
(`gffConfigMeasure`).

`S` is a sum of one term per component and `configSplit` only permutes components, so `S` is
separable across the halves with the *same* half action on both (`configAction_eq_split`) — the
reflection invariance of the density.  Pushing the measure along `configSplit` therefore gives
`ν ⊗ ν` with `ν = exp(−h)` (**`splitMap_gffConfigMeasure`**), which is the kernel law with a
trivial boundary factor: the `hsplit` hypothesis §6 consumes, up to the bookkeeping that rewrites
the product `ν ⊗ ν` as `(fkKernelMeasure (Z₀ := PUnit) _ _).map Prod.snd` (a `PUnit` base measure
against `Prod.snd`; not carried out here).  What is proved is the split law itself, i.e. the
measure-theoretic content of the identification.

Honest boundary: the ultralocal action has no gradient term, so it is the free field whose slices
decouple.  A nearest-neighbour action does *not* split this way — its cross-plane edge couples the
two halves — which is exactly why the free-field OS theorem is stated on the `2n+1`-slice model
with a boundary slice (`latticeGFFMeasure`, where the split law `ρ ⊗ ν_z ⊗ ν_z` is a mixture over
the boundary slice).  Transporting the *interacting* (nearest-neighbour) Gibbs measure on `Config`
to split coordinates is therefore a different and still open modelling step; what is settled below
is the `Config`-side construction and its split law. -/

/-! ### The two halves as one index set -/

/-- The component index set as the disjoint union of the two halves: the past is read through `θ`,
the future directly.  This is the index arithmetic `PosTime ⊕ PosTime ≃ Fin latticeDim` that §6
left implicit. -/
def halvesEquiv : PosTime ⊕ PosTime ≃ Fin latticeDim where
  toFun s := match s with
    | Sum.inl j => reflectCoord j.1
    | Sum.inr j => j.1
  invFun i := if h : isPosTime i then Sum.inr ⟨i, h⟩
    else Sum.inl ⟨reflectCoord i, (isPosTime_reflectCoord i).2 h⟩
  left_inv := by
    rintro (j | j)
    · have hneg : ¬ isPosTime (reflectCoord j.1) := fun hc =>
        (isPosTime_reflectCoord j.1).1 hc j.2
      simp only [dif_neg hneg, reflectCoord_involutive]
    · simp only [dif_pos j.2]
  right_inv := by
    intro i
    by_cases h : isPosTime i
    · simp only [dif_pos h]
    · simp only [dif_neg h, reflectCoord_involutive]

theorem halvesEquiv_inl (j : PosTime) : halvesEquiv (Sum.inl j) = reflectCoord j.1 := rfl

theorem halvesEquiv_inr (j : PosTime) : halvesEquiv (Sum.inr j) = j.1 := rfl

/-- **The mass action splits over the two halves**: the sum over all components is the sum over the
past (read through `θ`) plus the sum over the future. -/
theorem sum_sq_split (x : Config) :
    ∑ i, (x i) ^ 2
      = (∑ j : PosTime, (x (reflectCoord j.1)) ^ 2) + ∑ j : PosTime, (x j.1) ^ 2 := by
  have h1 : (∑ s : PosTime ⊕ PosTime, (match s with
          | Sum.inl j => x (reflectCoord j.1)
          | Sum.inr j => x j.1) ^ 2) = ∑ i : Fin latticeDim, (x i) ^ 2 :=
    Fintype.sum_equiv halvesEquiv
      (fun s : PosTime ⊕ PosTime => (match s with
        | Sum.inl j => x (reflectCoord j.1)
        | Sum.inr j => x j.1) ^ 2)
      (fun i : Fin latticeDim => (x i) ^ 2)
      (fun s => by cases s <;> rfl)
  rw [← h1, Fintype.sum_sum_type]
/-! ### The action, the Gibbs density and the measure -/

open scoped ENNReal

/-- The half-space mass action on one half: `(m/2) Σ_j (y j)²`. -/
def halfMassAction (m : ℝ) (y : PosTime → ℝ) : ℝ := (m / 2) * ∑ j, (y j) ^ 2

/-- **The mass (ultralocal) Gaussian action on the finite volume**: `(m/2) Σ_i (x i)²`. -/
def configAction (m : ℝ) (x : Config) : ℝ := (m / 2) * ∑ i, (x i) ^ 2

/-- **The action splits over the halves**: `S(x) = h(y₋) + h(y₊)` with the *same* half action on
both sides.  This is reflection invariance at the level of the density. -/
theorem configAction_eq_split (m : ℝ) (x : Config) :
    configAction m x
      = halfMassAction m (configSplitFun x).1 + halfMassAction m (configSplitFun x).2 := by
  unfold configAction halfMassAction configSplitFun
  rw [sum_sq_split x, mul_add]

theorem measurable_configAction (m : ℝ) : Measurable fun x : Config => configAction m x := by
  unfold configAction
  refine Measurable.mul measurable_const ?_
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2

/-- The Gibbs density `exp(−S)` of the mass Gaussian measure. -/
def configGibbsDensity (m : ℝ) (x : Config) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(configAction m x)))

theorem measurable_configGibbsDensity (m : ℝ) : Measurable (configGibbsDensity m) :=
  ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp (measurable_configAction m).neg)

/-- **The finite-volume Gaussian measure on `Config`**: the (unnormalised) Gibbs measure of the
mass action, as a density `exp(−S)` against Lebesgue measure on `Config`. -/
def gffConfigMeasure (m : ℝ) : MeasureTheory.Measure Config :=
  (volume : MeasureTheory.Measure Config).withDensity (configGibbsDensity m)

/-! ### The split as a measurable equivalence, and volume preservation

`configSplit` permutes the components and curries, so Lebesgue measure on `Config` is preserved.
The proof goes through the index equivalence `halvesEquiv`: `piCongrLeft` along it is measure
preserving (`pi_map_piCongrLeft`), and `sumPiEquivProdPi` is measure preserving
(`volume_measurePreserving_sumPiEquivProdPi`). -/

/-- `configSplit` as a measurable equivalence. -/
def configSplitEquiv : Config ≃ᵐ (PosTime → ℝ) × (PosTime → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin latticeDim => ℝ) halvesEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : PosTime ⊕ PosTime => ℝ))

theorem configSplitEquiv_apply (x : Config) : configSplitEquiv x = configSplitFun x := by
  refine Prod.ext ?_ ?_
  · funext j
    simp [configSplitEquiv, configSplitFun, MeasurableEquiv.sumPiEquivProdPi,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, halvesEquiv]
  · funext j
    simp [configSplitEquiv, configSplitFun, MeasurableEquiv.sumPiEquivProdPi,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, halvesEquiv]

/-- **The split is measurable** (restated from §5 via the measurable equivalence). -/
theorem measurable_configSplitEquiv :
    Measurable (configSplitFun : Config → (PosTime → ℝ) × (PosTime → ℝ)) := by
  rw [show configSplitFun
      = (configSplitEquiv : Config → (PosTime → ℝ) × (PosTime → ℝ))
      from funext configSplitEquiv_apply]
  exact configSplitEquiv.measurable

theorem measurable_configJoinFun :
    Measurable (configJoinFun : (PosTime → ℝ) × (PosTime → ℝ) → Config) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : isPosTime i
  · simpa only [configJoinFun, dif_pos h] using
      (measurable_pi_apply (⟨i, h⟩ : PosTime)).comp measurable_snd
  · simpa only [configJoinFun, dif_neg h] using
      (measurable_pi_apply
        (⟨reflectCoord i, (isPosTime_reflectCoord i).2 h⟩ : PosTime)).comp measurable_fst

/-- **The split preserves Lebesgue measure.** -/
theorem measurePreserving_configSplitEquiv :
    MeasureTheory.MeasurePreserving configSplitEquiv volume volume := by
  have h1 : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : PosTime ⊕ PosTime => ℝ)) volume volume :=
    MeasureTheory.volume_measurePreserving_sumPiEquivProdPi _
  have h2 : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin latticeDim => ℝ) halvesEquiv).symm volume volume :=
    (MeasureTheory.measurePreserving_piCongrLeft
      (fun _ : Fin latticeDim => (volume : MeasureTheory.Measure ℝ)) halvesEquiv).symm
  exact h1.comp h2

theorem volume_map_configSplitFun :
    (volume : MeasureTheory.Measure Config).map configSplitFun = volume := by
  rw [show configSplitFun
      = (configSplitEquiv : Config → (PosTime → ℝ) × (PosTime → ℝ))
      from funext configSplitEquiv_apply]
  exact measurePreserving_configSplitEquiv.map_eq

/-! ### Transporting a density along the split -/

/-- Pushing a measure with a density along a measurable equivalence pushes the density back along
the inverse. -/
theorem map_withDensity_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : MeasureTheory.Measure α) (f : α → ℝ≥0∞)
    (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext t ht
  rw [MeasureTheory.Measure.map_apply e.measurable ht,
    MeasureTheory.withDensity_apply _ (e.measurable ht),
    MeasureTheory.withDensity_apply _ ht,
    MeasureTheory.Measure.restrict_map e.measurable ht]
  change ∫⁻ a in e ⁻¹' t, f a ∂μ
    = ∫⁻ a, (f ∘ e.symm) a ∂(MeasureTheory.Measure.map e (μ.restrict (e ⁻¹' t)))
  rw [MeasureTheory.lintegral_map (hf.comp e.symm.measurable) e.measurable]
  simp

/-! ### The split law of the Gaussian measure -/

/-- **The split law of the finite-volume Gaussian measure on `Config`**: pushing `gffConfigMeasure`
along `configSplit` gives the product of the *same* half-space Gibbs density on the two halves —
the density is separable, which is the whole content of reflection invariance here. -/
theorem splitMap_gffConfigMeasure (m : ℝ) :
    splitMap (gffConfigMeasure m)
      = ((volume : MeasureTheory.Measure (PosTime → ℝ)).prod
          (volume : MeasureTheory.Measure (PosTime → ℝ))).withDensity
          (fun p => ENNReal.ofReal (Real.exp (-(halfMassAction m p.1))
            * Real.exp (-(halfMassAction m p.2)))) := by
  rw [splitMap, gffConfigMeasure,
    show configSplitFun
      = (configSplitEquiv : Config → (PosTime → ℝ) × (PosTime → ℝ))
      from funext configSplitEquiv_apply,
    map_withDensity_measurableEquiv configSplitEquiv volume (configGibbsDensity m)
      (measurable_configGibbsDensity m),
    measurePreserving_configSplitEquiv.map_eq]
  congr 1
  funext p
  have hsplit : configSplitFun (configSplitEquiv.symm p) = p := by
    rw [← configSplitEquiv_apply, MeasurableEquiv.apply_symm_apply]
  rw [configGibbsDensity, configAction_eq_split, hsplit, ← Real.exp_add]
  congr 1
  congr 1
  ring

/-! ## 8. The mass model's OS form is nonnegative, with no hypothesis on the state

§7 constructed `gffConfigMeasure m` and computed its split law, leaving one bookkeeping step to
§6's `hsplit`: rewrite the product `ν ⊗ ν` as `(fkKernelMeasure (Z₀ := PUnit) ρd νd).map Prod.snd`.
This section takes the same step in the form the lattice theorem actually needs — the OS
*integral* rather than the measure — and is shorter for it: the Mathlib lemma
`integral_withDensity_eq_integral_toReal_smul` (unconditional in the integrand) turns the split
integral into the two-density integral, and `fkKernel_inner` evaluates it at the single boundary
point `()`.

* **`gffHalfDensity`** — `exp(−h)`, the half of `configGibbsDensity` on one half-space;
* **`integral_splitMap_gffConfigMeasure`** — `∫ G d(splitMap (gffConfigMeasure m))` is the
  integral of `a y₋ · a y₊ · G` against Lebesgue on `(Y × Y)`, with `a = gffHalfDensity m`;
* **`gffConfigMeasure_osForm_nonneg`** — hence `0 ≤ ∫ fkOSForm f ((), ·) d(splitMap ω)` for
  **every** future-half observable, with no hypothesis on the OS form and no integrability
  condition: this is item 3's remaining bookkeeping carried out, in the shape
  `isReflectionPositive_of_splitIntegral` consumes;
* **`gffConfigMeasure_isReflectionPositive`** — and therefore the `hRP` of
  `reflection_positivity_continuum` holds for the functional of the mass model.

Honest boundary, unchanged from §7: the state is the *mass* (ultralocal) Gibbs measure on `Config`,
not a nearest-neighbour one, and it is unnormalised — positivity of the OS form is invariant under
rescaling by a positive constant, which is all that is used.  What is *not* assumed anywhere below
is reflection positivity itself. -/

/-- The half-space Boltzmann density `exp(−h)`, one half of `configGibbsDensity m`. -/
def gffHalfDensity (m : ℝ) (y : PosTime → ℝ) : ℝ := Real.exp (-(halfMassAction m y))

theorem gffHalfDensity_pos (m : ℝ) (y : PosTime → ℝ) : 0 < gffHalfDensity m y :=
  Real.exp_pos _

theorem measurable_halfMassAction (m : ℝ) :
    Measurable fun y : PosTime → ℝ => halfMassAction m y := by
  unfold halfMassAction
  exact measurable_const.mul
    (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).pow_const 2)

theorem measurable_gffHalfDensity (m : ℝ) : Measurable (gffHalfDensity m) :=
  Real.measurable_exp.comp (measurable_halfMassAction m).neg

/-- **The split mass measure integrates its density.**  Pushing `gffConfigMeasure m` to split
coordinates gives the product of the two half-space densities, so the integral of any `G` against
it is the integral of `a y₋ · a y₊ · G` against Lebesgue measure on the product. -/
theorem integral_splitMap_gffConfigMeasure (m : ℝ)
    (G : (PosTime → ℝ) × (PosTime → ℝ) → ℝ) :
    ∫ p, G p ∂(splitMap (gffConfigMeasure m))
      = ∫ p, (gffHalfDensity m p.1 * gffHalfDensity m p.2) * G p
          ∂((volume : MeasureTheory.Measure (PosTime → ℝ)).prod
            (volume : MeasureTheory.Measure (PosTime → ℝ))) := by
  have hmeas : Measurable fun p : (PosTime → ℝ) × (PosTime → ℝ) =>
      ENNReal.ofReal (Real.exp (-(halfMassAction m p.1)) * Real.exp (-(halfMassAction m p.2))) := by
    refine ENNReal.measurable_ofReal.comp
      (((measurable_halfMassAction m).comp measurable_fst).neg.exp.mul
        (((measurable_halfMassAction m).comp measurable_snd).neg.exp))
  rw [splitMap_gffConfigMeasure m,
    integral_withDensity_eq_integral_toReal_smul (f_meas := hmeas)
      (hf_lt_top := Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [Pi.smul_apply, gffHalfDensity, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]

/-- **Reflection positivity of the finite-volume mass model on `Config`, unconditionally.**  For
every future-half observable `f` the OS integrand `fkOSForm f` is nonnegative-in-integral against
the split law of `gffConfigMeasure m` — because the split law is `ν ⊗ ν` with the *same* `ν` on
both halves, which is the one input of the Feynman–Kac square.  No hypothesis on `f` (beyond
measurability of the integrand, which is not even needed here) and none on the state. -/
theorem gffConfigMeasure_osForm_nonneg (m : ℝ) (f : PUnit → (PosTime → ℝ) → ℝ) :
    0 ≤ ∫ p, fkOSForm f ((), p) ∂(splitMap (gffConfigMeasure m)) := by
  rw [integral_splitMap_gffConfigMeasure m (fun p => fkOSForm f ((), p))]
  have hfk : ∀ p : (PosTime → ℝ) × (PosTime → ℝ),
      (gffHalfDensity m p.1 * gffHalfDensity m p.2) * fkOSForm f ((), p)
        = fkKernelDensity (fun _ => (1 : ℝ)) (fun _ => gffHalfDensity m) ((), p)
            * fkOSForm f ((), p) := by
    intro p
    simp only [fkKernelDensity, one_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hfk),
    fkKernel_inner (ρd := fun _ => (1 : ℝ)) (νd := fun _ => gffHalfDensity m) (F := f) ()]
  exact mul_nonneg (sq_nonneg _) zero_le_one

/-- **`hRP` for the mass model, with no hypothesis on the OS form.**  The functional
`F ↦ ∫ F d(gffConfigMeasure m)` satisfies the reflection-positivity hypothesis that
`reflection_positivity_continuum` consumes, on the future-half observables of the split — by
`gffConfigMeasure_osForm_nonneg` through `isReflectionPositive_of_splitIntegral`. -/
theorem gffConfigMeasure_isReflectionPositive (m : ℝ) (f : PUnit → (PosTime → ℝ) → ℝ)
    (hf : MeasureTheory.AEStronglyMeasurable
      (fun p : (PosTime → ℝ) × (PosTime → ℝ) => fkOSForm f ((), p))
        (splitMap (gffConfigMeasure m))) :
    0 ≤ osForm (fun F => ∫ x, F x ∂(gffConfigMeasure m))
      (fun y => f () ((configSplit y).2)) (fun y => f () ((configSplit y).2)) :=
  isReflectionPositive_of_splitIntegral (gffConfigMeasure m)
    (fun g => gffConfigMeasure_osForm_nonneg m g) f hf

end

end BookProof.ReflectionPositivity
