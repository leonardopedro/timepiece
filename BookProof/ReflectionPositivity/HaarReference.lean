import Mathlib
import BookProof.ReflectionPositivity.WilsonPastClass

/-!
# The Haar reference measure on the half-space configuration space

`BookProof.ReflectionPositivity.WilsonPastClass` makes the half-space configuration space explicit
— `PastConf L M N` below the reflection slice, `BoundConf L M N` in it — and proves that the
past-class Wilson sum is a measurable function of that data (`measurable_pastSideObservable`).  Its
`Honest boundary` records the one thing it did not supply: **the reference measure** against which
the Wilson density is integrated.  `WilsonLattice` had used `volume` on the abstract configuration
space, and `WilsonPastClass` left the `MeasureSpace`/`SFinite` hypotheses of
`wilson_reflectionPositive` to the caller.

This chapter instantiates that measure as **Haar measure**, in the only place it can come from: the
gauge group.

## 1. Normalised Haar measure on a compact group

`haarProb G` is Haar measure against the whole group, `haarMeasure ⊤`; on a compact group that is a
*probability* measure (`haarProb_univ`, from `haarMeasure_self` at `K₀ = ⊤`).  Being a probability
measure it is finite and sigma-finite, so the `SFinite` hypotheses that were previously obligations
of the caller are now instances (`haarProb_isProbability` and its `SFinite` companion).

## 2. Haar on a link, and on the half-space configuration space

A link variable is the image of a group element under a measurable matrix representation
`ρ : G → Fin N → Fin N → ℂ`; the reference measure on one link is the pushforward of Haar,
`haarLinkMeasure ρ`.  It is again a probability measure, and — the form in which the support is
used downstream — every property that holds on the image of `ρ` holds almost everywhere
(`haarLinkMeasure_ae`), so a statement about unitary link variables never needs a measurability
argument for the group itself.

The half-space and boundary configuration spaces are products over their (finitely many) links, and
the reference measure there is `Measure.pi` of the one-link measure: `pastHaarMeasure ρ` and
`boundHaarMeasure ρ` are probability measures (`isProbabilityMeasure_pastHaarMeasure`,
`isProbabilityMeasure_boundHaarMeasure`) with `SFinite` instances.  This is the instantiation: the
reference measure of the half-space theory is a product of Haar measures over the links of the
half-space, not an unspecified `volume`.

## 3. Feynman–Kac against arbitrary reference measures

`fkKernelMeasure` of `LatticeFreeField` is tied to `volume` through the `MeasureSpace` instance of
its state spaces, which is exactly what a Haar reference cannot use (the Lebesgue measure of a
matrix space is not the Haar measure of the gauge group).  `fkRefMeasure` is the same construction
with the two reference measures passed explicitly, and it inherits the structure: the density
factorises (`fkKernelDensity`), the OS form is a single square
(**`fkRef_integral_eq`**: `∫ θF·F = ∫ z, (∫ y, F ν_z)² ρ`), and it is nonnegative
(**`fkRef_reflectionPositive`**).  Nothing about the reference measure is used except that it is
sigma-finite, so the Haar product measures of §2 are admissible where `volume` was.

## 4. The Wilson measure against the Haar reference

With `b` the boundary action (the invariant plaquettes) and `A = pastSideObservable` the
past-class action of §2 of `WilsonPastClass`, the Haar-referenced Gibbs measure is
`haarGibbsMeasure β M N b ρ`: the product of the boundary and the two half-space Haar measures,
weighted by `exp(-(A(y₋,z) + A(y₊,z) + b z))`.  **`fkKernelDensity_haar`** identifies that weight
with the Feynman–Kac kernel density, so `haarGibbsMeasure` *is* `fkRefMeasure` of the Wilson
densities (`haarGibbsMeasure_eq_fkRef`) — the lattice gauge measure is `ρ ⊗ ν_z ⊗ ν_z` against
Haar, with the interacting kernel `ν_z = exp(-A)`.

## 5. Reflection positivity

**`haarWilson_reflectionPositive`** is the OS inequality for that measure,
`0 ≤ ∫ θF · F d(haarGibbsMeasure β M N b ρ)`, for every half-space observable whose OS integrand is
integrable against the Haar product.  The only hypotheses are measurability of the boundary action
and that integrability: the `MeasureSpace`/`SFinite` obligations that `WilsonPastClass` had left
open are discharged by §1–2.

## Honest boundary

* The instantiation is **parametric in the compact group**.  Mathlib has no compact-group structure
  on the whole unitary group `Matrix.unitaryGroup (Fin N) ℂ` (it is a submonoid, and no
  `CompactSpace` instance is available), so the gauge group is carried as a compact group `G`
  together with a measurable matrix representation `ρ` — a genuine instantiation for every choice of
  `(G, ρ)`, the `U(1)^N` link variables of the diagonal torus `G = (Fin N → Circle)` included.
* Gauge invariance of the observables is not used or claimed, and the normalising constant of the
  interacting measure is not evaluated: it cancels in the OS inequality, as in the free case.
* Integrability of the OS integrand is kept as a hypothesis.  It is *not* automatic for
  `F = pastSideObservable` on the whole matrix space — the past-class weight is only bounded on
  unitary configurations — and this chapter does not prove the almost-everywhere unitarity of a
  Haar-distributed configuration.
-/

namespace BookProof.ReflectionPositivity

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ENNReal
open TopologicalSpace

noncomputable section

variable {L : ℕ}

/-! ## 1. Normalised Haar measure on a compact group -/

/-- **The whole group as a positive compact set**, for a compact group: its carrier is `univ`,
which is compact and has nonempty interior.  This is the `K₀` at which Haar measure is normalised
to a probability measure. -/
def topPositiveCompacts (G : Type*) [Group G] [TopologicalSpace G] [CompactSpace G] :
    PositiveCompacts G where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by simpa using (Set.univ_nonempty (α := G))

/-- **The normalised Haar measure of a compact group**: Haar measure against the whole group, so
that `haarProb G univ = 1`.  For a compact group this is the unique Haar probability measure. -/
def haarProb (G : Type*) [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [CompactSpace G] [LocallyCompactSpace G] [IsTopologicalGroup G] : Measure G :=
  haarMeasure (topPositiveCompacts G)

/-- **Haar measure of a compact group is a probability measure**: `haarMeasure_self` at the whole
group. -/
theorem haarProb_univ (G : Type*) [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [CompactSpace G] [LocallyCompactSpace G] [IsTopologicalGroup G] :
    haarProb G Set.univ = 1 := by
  simpa [haarProb, topPositiveCompacts] using (haarMeasure_self (K₀ := topPositiveCompacts G))

instance haarProb_isProbability (G : Type*) [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [CompactSpace G] [LocallyCompactSpace G] [IsTopologicalGroup G] :
    IsProbabilityMeasure (haarProb G) where
  measure_univ := haarProb_univ G

/-! ## 2. Haar on a link and on the half-space configuration space -/

/-- **The reference measure on one link variable**: the pushforward of the normalised Haar
measure under the matrix representation `ρ` of the gauge group. -/
def haarLinkMeasure (G : Type*) [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [CompactSpace G] [LocallyCompactSpace G] [IsTopologicalGroup G]
    {N : ℕ} (ρ : G → Fin N → Fin N → ℂ) : Measure (Fin N → Fin N → ℂ) :=
  (haarProb G).map ρ

/-- The one-link Haar measure is a probability measure. -/
theorem haarLinkMeasure_isProbability (G : Type*) [Group G] [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] [CompactSpace G] [LocallyCompactSpace G]
    [IsTopologicalGroup G] {N : ℕ} (ρ : G → Fin N → Fin N → ℂ) (hρ : Measurable ρ) :
    IsProbabilityMeasure (haarLinkMeasure G ρ) :=
  Measure.isProbabilityMeasure_map hρ.aemeasurable

/-- **Everything true on the image of the representation holds Haar-almost everywhere.**  This is
the support statement in the form used below: a property of link variables that holds for every
group element (unitarity, for instance) holds for Haar-almost every link variable, with no
measurability argument about the group needed. -/
theorem haarLinkMeasure_ae (G : Type*) [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [CompactSpace G] [LocallyCompactSpace G] [IsTopologicalGroup G]
    {N : ℕ} (ρ : G → Fin N → Fin N → ℂ) (hρ : Measurable ρ)
    {p : (Fin N → Fin N → ℂ) → Prop} (hpm : MeasurableSet {v | p v}) (hp : ∀ g, p (ρ g)) :
    ∀ᵐ v ∂(haarLinkMeasure G ρ), p v := by
  rw [haarLinkMeasure, MeasureTheory.ae_map_iff hρ.aemeasurable hpm]
  exact Filter.Eventually.of_forall hp

/-! ### The links of the box are finitely many -/

/-- A link is determined by its base, direction and target, so the links of the box are a finite
type.  (The step condition is a proposition, hence disregarded by injectivity.) -/
instance linkFinite {L : ℕ} : Finite (Link L) :=
  Finite.of_injective (fun l : Link L => (l.base, l.dir, l.target)) (by
    rintro ⟨b, d, t, h⟩ ⟨b', d', t', h'⟩ he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    rw [Subsingleton.elim h h'])

instance linkFintype {L : ℕ} : Fintype (Link L) := Fintype.ofFinite _

instance pastLinkFintype {L : ℕ} (M : ℕ) : Fintype (PastLink L M) := Fintype.ofFinite _

instance boundaryLinkFintype {L : ℕ} (M : ℕ) : Fintype (BoundaryLink L M) := Fintype.ofFinite _

/-- **The reference measure on the past half-space configuration space**: the product of the
one-link Haar measures over the links based at time at most `M`. -/
abbrev pastHaarMeasure (G : Type*) [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [CompactSpace G] [LocallyCompactSpace G] [IsTopologicalGroup G]
    {M N : ℕ} (ρ : G → Fin N → Fin N → ℂ) : Measure (PastConf L M N) :=
  Measure.pi fun _ : PastLink L M => haarLinkMeasure G ρ

/-- **The reference measure on the reflection slice**: the product of the one-link Haar measures
over the links based in the slice `t = M`. -/
abbrev boundHaarMeasure (G : Type*) [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [CompactSpace G] [LocallyCompactSpace G] [IsTopologicalGroup G]
    {M N : ℕ} (ρ : G → Fin N → Fin N → ℂ) : Measure (BoundConf L M N) :=
  Measure.pi fun _ : BoundaryLink L M => haarLinkMeasure G ρ

/-- **The half-space reference measure is a probability measure.** -/
instance isProbabilityMeasure_pastHaarMeasure (G : Type*) [Group G] [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] [CompactSpace G] [LocallyCompactSpace G]
    [IsTopologicalGroup G] (M : ℕ) {N : ℕ} (ρ : G → Fin N → Fin N → ℂ) (hρ : Measurable ρ) :
    IsProbabilityMeasure (pastHaarMeasure (L := L) (M := M) (N := N) G ρ) := by
  haveI : ∀ _ : PastLink L M, IsProbabilityMeasure (haarLinkMeasure G ρ) :=
    fun _ => haarLinkMeasure_isProbability G ρ hρ
  infer_instance

/-- **The boundary reference measure is a probability measure.** -/
instance isProbabilityMeasure_boundHaarMeasure (G : Type*) [Group G] [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] [CompactSpace G] [LocallyCompactSpace G]
    [IsTopologicalGroup G] (M : ℕ) {N : ℕ} (ρ : G → Fin N → Fin N → ℂ) (hρ : Measurable ρ) :
    IsProbabilityMeasure (boundHaarMeasure (L := L) (M := M) (N := N) G ρ) := by
  haveI : ∀ _ : BoundaryLink L M, IsProbabilityMeasure (haarLinkMeasure G ρ) :=
    fun _ => haarLinkMeasure_isProbability G ρ hρ
  infer_instance

/-- The Lebesgue measure `volume` on the past half-space configuration space is sigma-finite: it is
the finite product of the (sigma-finite) Lebesgue measures on the links. -/
instance sigmaFinite_volume_pastConf {L M N : ℕ} [Fintype (PastLink L M)] :
    SigmaFinite (volume : Measure (PastConf L M N)) :=
  Measure.pi.sigmaFinite _

/-- The Lebesgue measure on the boundary configuration space is sigma-finite. -/
instance sigmaFinite_volume_boundConf {L M N : ℕ} [Fintype (BoundaryLink L M)] :
    SigmaFinite (volume : Measure (BoundConf L M N)) :=
  Measure.pi.sigmaFinite _

/-- The `SFinite` hypothesis that the Feynman–Kac theory needs, discharged for the half-space Haar
measure. -/
instance sFinite_pastHaarMeasure (G : Type*) [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [CompactSpace G] [LocallyCompactSpace G] [IsTopologicalGroup G]
    (M : ℕ) {N : ℕ} (ρ : G → Fin N → Fin N → ℂ) (hρ : Measurable ρ) :
    SFinite (pastHaarMeasure (L := L) (M := M) (N := N) G ρ) := by
  haveI : IsProbabilityMeasure (pastHaarMeasure (L := L) (M := M) (N := N) G ρ) :=
    isProbabilityMeasure_pastHaarMeasure (L := L) G M ρ hρ
  infer_instance

/-- The `SFinite` hypothesis discharged for the boundary Haar measure. -/
instance sFinite_boundHaarMeasure (G : Type*) [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [CompactSpace G] [LocallyCompactSpace G] [IsTopologicalGroup G]
    (M : ℕ) {N : ℕ} (ρ : G → Fin N → Fin N → ℂ) (hρ : Measurable ρ) :
    SFinite (boundHaarMeasure (L := L) (M := M) (N := N) G ρ) := by
  haveI : IsProbabilityMeasure (boundHaarMeasure (L := L) (M := M) (N := N) G ρ) :=
    isProbabilityMeasure_boundHaarMeasure (L := L) G M ρ hρ
  infer_instance

/-! ## 3. The Feynman–Kac kernel measure against explicit reference measures -/

variable {Z₀ Y : Type*} [MeasureSpace Z₀] [MeasureSpace Y]

/-- **The Feynman–Kac kernel measure `ρ ⊗ ν_z ⊗ ν_z` against explicit reference measures**: the
boundary slice is drawn from `ρM` and, given it, the past and the future independently from the
same `νM`, weighted by the kernel density `ρd z · νd z y₋ · νd z y₊`.  This is `fkKernelMeasure`
with the reference measures made parameters, which is what a Haar reference requires. -/
def fkRefMeasure (ρM : Measure Z₀) (νM : Measure Y) (ρd : Z₀ → ℝ) (νd : Z₀ → Y → ℝ) :
    Measure (Z₀ × (Y × Y)) :=
  (ρM.prod (νM.prod νM)).withDensity (fun p => ENNReal.ofReal (fkKernelDensity ρd νd p))

/-- The definition, unfolded. -/
theorem fkRefMeasure_eq (ρM : Measure Z₀) (νM : Measure Y) (ρd : Z₀ → ℝ)
    (νd : Z₀ → Y → ℝ) :
    fkRefMeasure ρM νM ρd νd
      = (ρM.prod (νM.prod νM)).withDensity
          (fun p => ENNReal.ofReal (fkKernelDensity ρd νd p)) := rfl

/-- **The inner Fubini step against an explicit half-space reference measure**: at a fixed boundary
slice, the OS integrand weighted by the kernel integrates to a single square times the boundary
weight.  Same proof as `fkKernel_inner`, with `νM` in place of `volume`. -/
theorem fkRef_inner (νM : Measure Y) [SFinite νM] (ρd : Z₀ → ℝ) (νd : Z₀ → Y → ℝ)
    (F : Z₀ → Y → ℝ) (z : Z₀) :
    ∫ w : Y × Y, fkKernelDensity ρd νd (z, w) * fkOSForm F (z, w) ∂(νM.prod νM)
      = (∫ y, F z y * νd z y ∂νM) ^ 2 * ρd z := by
  have hstep : ∫ w : Y × Y, fkKernelDensity ρd νd (z, w) * fkOSForm F (z, w) ∂(νM.prod νM)
      = ρd z * ∫ w : Y × Y, (F z w.1 * νd z w.1) * (F z w.2 * νd z w.2)
          ∂(νM.prod νM) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [fkOSForm, fkKernelDensity]
    ring
  rw [hstep, integral_prod_mul (f := fun y => F z y * νd z y) (g := fun y => F z y * νd z y)]
  ring

/-- **The kernel Feynman–Kac identity against explicit reference measures.**  For a half-space
observable `F`, the OS form against `ρM ⊗ νM ⊗ νM` weighted by the kernel density is a *single*
square, integrated over the boundary slice: `∫ θF·F = ∫ z, (∫ y, F ν_z)² ρ`. -/
theorem fkRef_integral_eq (ρM : Measure Z₀) (νM : Measure Y) [SFinite ρM] [SFinite νM]
    [SFinite (volume : Measure Z₀)] [SFinite (volume : Measure Y)]
    (ρd : Z₀ → ℝ) (νd : Z₀ → Y → ℝ) (F : Z₀ → Y → ℝ)
    (hD : Measurable fun p : Z₀ × (Y × Y) => fkKernelDensity ρd νd p)
    (hρ : ∀ z, 0 ≤ ρd z) (hν : ∀ z y, 0 ≤ νd z y)
    (hint : Integrable (fun p : Z₀ × (Y × Y) => fkKernelDensity ρd νd p * fkOSForm F p)
      (ρM.prod (νM.prod νM))) :
    ∫ p, fkOSForm F p ∂(fkRefMeasure ρM νM ρd νd)
      = ∫ z, (∫ y, F z y * νd z y ∂νM) ^ 2 * ρd z ∂ρM := by
  rw [fkRefMeasure_eq,
    integral_withDensity_eq_integral_toReal_smul (f_meas := Measurable.ennreal_ofReal hD)
      (hf_lt_top := Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have htc : ∀ p : Z₀ × (Y × Y),
      (ENNReal.ofReal (fkKernelDensity ρd νd p)).toReal = fkKernelDensity ρd νd p :=
    fun p => ENNReal.toReal_ofReal (fkKernelDensity_nonneg hρ hν p)
  simp only [htc, smul_eq_mul]
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact fkRef_inner νM ρd νd F z

/-- **Reflection positivity against explicit reference measures**: for every half-space observable
whose OS integrand is integrable against `ρM ⊗ νM ⊗ νM`, the OS form is nonnegative.  Nothing about
the reference measures is used except sigma-finiteness, so this is where Haar measures enter. -/
theorem fkRef_reflectionPositive (ρM : Measure Z₀) (νM : Measure Y) [SFinite ρM] [SFinite νM]
    [SFinite (volume : Measure Z₀)] [SFinite (volume : Measure Y)]
    (ρd : Z₀ → ℝ) (νd : Z₀ → Y → ℝ) (F : Z₀ → Y → ℝ)
    (hD : Measurable fun p : Z₀ × (Y × Y) => fkKernelDensity ρd νd p)
    (hρ : ∀ z, 0 ≤ ρd z) (hν : ∀ z y, 0 ≤ νd z y)
    (hint : Integrable (fun p : Z₀ × (Y × Y) => fkKernelDensity ρd νd p * fkOSForm F p)
      (ρM.prod (νM.prod νM))) :
    0 ≤ ∫ p, fkOSForm F p ∂(fkRefMeasure ρM νM ρd νd) := by
  rw [fkRef_integral_eq ρM νM ρd νd F hD hρ hν hint]
  exact integral_nonneg fun z => mul_nonneg (sq_nonneg _) (hρ z)

/-! ## 4. The Wilson measure against the Haar reference -/

variable {M N : ℕ}

/-- **The boundary weight** `ρ = exp(-b)`, from the reflection-invariant plaquettes. -/
def haarBoundWeight (b : BoundConf L M N → ℝ) (z : BoundConf L M N) : ℝ := Real.exp (-(b z))

/-- **The interacting half-space kernel** `ν_z(y) = exp(-A(z, y))`, with `A = pastSideObservable`
the past-class Wilson sum of `WilsonPastClass`. -/
def haarHalfKernel (β : ℝ) (z : BoundConf L M N) (y : PastConf L M N) : ℝ :=
  Real.exp (-(pastSideObservable β N M y z))

/-- **The Wilson action of the split configuration**: past half, future half, boundary.  The two
halves are the *same* function `pastSideObservable`, read on the two halves — the reflection
identity `pastSideWeight_reflectConfig` of `WilsonPastClass`. -/
def haarWilsonAction (β : ℝ) (b : BoundConf L M N → ℝ)
    (p : BoundConf L M N × (PastConf L M N × PastConf L M N)) : ℝ :=
  pastSideObservable β N M p.2.1 p.1 + pastSideObservable β N M p.2.2 p.1 + b p.1

/-- **The density factorises at the reflection slice**: `exp(-S)` is the Feynman–Kac kernel
density of the boundary weight and the interacting half-space kernel. -/
theorem fkKernelDensity_haar (β : ℝ) (b : BoundConf L M N → ℝ)
    (p : BoundConf L M N × (PastConf L M N × PastConf L M N)) :
    fkKernelDensity (haarBoundWeight b) (haarHalfKernel (L := L) (M := M) (N := N) β) p
      = Real.exp (-(haarWilsonAction (L := L) (M := M) (N := N) β b p)) := by
  simp only [fkKernelDensity, haarBoundWeight, haarHalfKernel, haarWilsonAction, ← Real.exp_add]
  congr 1
  ring

/-- **The Haar-referenced lattice gauge measure**: the product measure of the boundary and the two
half-space Haar measures of §2, weighted by the Wilson density `exp(-S)`.  This is the reference
measure instantiated, with `WilsonLattice`'s `volume` replaced by Haar measure on the links. -/
def haarGibbsMeasure (G : Type*) [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [CompactSpace G] [LocallyCompactSpace G] [IsTopologicalGroup G]
    (ρ : G → Fin N → Fin N → ℂ) (β : ℝ) (b : BoundConf L M N → ℝ) :
    Measure (BoundConf L M N × (PastConf L M N × PastConf L M N)) :=
  fkRefMeasure (boundHaarMeasure (L := L) G ρ) (pastHaarMeasure (L := L) G ρ)
    (haarBoundWeight b) (haarHalfKernel (L := L) (M := M) (N := N) β)

/-- **The Haar-referenced measure is the Wilson measure**: the product measure weighted by the
Feynman–Kac kernel density, i.e. `ρ ⊗ ν_z ⊗ ν_z` against Haar with the interacting kernel
`ν_z = exp(-A)`. -/
theorem haarGibbsMeasure_eq (G : Type*) [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [CompactSpace G] [LocallyCompactSpace G] [IsTopologicalGroup G]
    (ρv : G → Fin N → Fin N → ℂ) (β : ℝ) (b : BoundConf L M N → ℝ) :
    haarGibbsMeasure (L := L) (M := M) (N := N) G ρv β b
      = ((boundHaarMeasure (L := L) G ρv).prod
          ((pastHaarMeasure (L := L) G ρv).prod (pastHaarMeasure (L := L) G ρv))).withDensity
        (fun p => ENNReal.ofReal (Real.exp (-(haarWilsonAction (L := L) (M := M) (N := N)
          β b p)))) := by
  rw [haarGibbsMeasure, fkRefMeasure_eq]
  congr 1
  funext p
  rw [fkKernelDensity_haar]

/-- **Measurability of the Haar-referenced Wilson action**: a sum of the two half-space
observables (measurable by `measurable_pastSideObservable`) and the boundary action. -/
theorem measurable_haarWilsonAction (β : ℝ) {b : BoundConf L M N → ℝ} (hb : Measurable b) :
    Measurable fun p : BoundConf L M N × (PastConf L M N × PastConf L M N) =>
      haarWilsonAction (L := L) (M := M) (N := N) β b p := by
  have h1 : Measurable fun p : BoundConf L M N × (PastConf L M N × PastConf L M N) =>
      (p.2.1, p.1) := by fun_prop
  have h2 : Measurable fun p : BoundConf L M N × (PastConf L M N × PastConf L M N) =>
      (p.2.2, p.1) := by fun_prop
  have hb1 : Measurable fun p : BoundConf L M N × (PastConf L M N × PastConf L M N) => b p.1 :=
    hb.comp measurable_fst
  have hsum : Measurable fun p : BoundConf L M N × (PastConf L M N × PastConf L M N) =>
      pastSideObservable β N M p.2.1 p.1 + pastSideObservable β N M p.2.2 p.1 + b p.1 :=
    (((measurable_pastSideObservable (L := L) (M := M) (N := N) β).comp h1).add
      ((measurable_pastSideObservable (L := L) (M := M) (N := N) β).comp h2)).add hb1
  simpa only [haarWilsonAction, Function.comp_def] using hsum

/-! ## 5. Reflection positivity of the Haar-referenced Wilson measure -/

/-- The kernel density of the Haar-referenced Wilson measure, as a function of the split
configuration: `exp(-S)`. -/
theorem density_haar (β : ℝ) (b : BoundConf L M N → ℝ) :
    (fun p : BoundConf L M N × (PastConf L M N × PastConf L M N) =>
        fkKernelDensity (haarBoundWeight b) (haarHalfKernel (L := L) (M := M) (N := N) β) p)
      = fun p => Real.exp (-(haarWilsonAction (L := L) (M := M) (N := N) β b p)) := by
  funext p
  exact fkKernelDensity_haar β b p

/-- The OS integrand `exp(-S)·θF·F` of the Haar-referenced Wilson measure, as a function of the
split configuration. -/
theorem osIntegrand_haar (β : ℝ) (b : BoundConf L M N → ℝ)
    (F : BoundConf L M N → PastConf L M N → ℝ) :
    (fun p : BoundConf L M N × (PastConf L M N × PastConf L M N) =>
        fkKernelDensity (haarBoundWeight b) (haarHalfKernel (L := L) (M := M) (N := N) β) p
          * fkOSForm F p)
      = fun p => Real.exp (-(haarWilsonAction (L := L) (M := M) (N := N) β b p)) * fkOSForm F p := by
  funext p
  rw [fkKernelDensity_haar]

set_option maxHeartbeats 8000000 in
/-- **Reflection positivity with the Haar reference measure instantiated.**  For the lattice gauge
measure built from Haar measure on the links — boundary slice, past half, future half, weighted by
the Wilson plaquette density — the OS form is nonnegative:
`0 ≤ ∫ θF · F d(haarGibbsMeasure β b ρ)`.

The reference measure is a *construction* here, not a hypothesis: both product measures are
probability measures (`isProbabilityMeasure_boundHaarMeasure`,
`isProbabilityMeasure_pastHaarMeasure`), so sigma-finiteness and finiteness are discharged.  What
remains a hypothesis is only what is not automatic for an arbitrary observable: measurability of
the boundary action `b` and integrability of the OS integrand `exp(-S)·θF·F` against the Haar
product. -/
theorem haarWilson_reflectionPositive (G : Type*) [Group G] [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] [CompactSpace G] [LocallyCompactSpace G]
    [IsTopologicalGroup G] (ρv : G → Fin N → Fin N → ℂ) (hρv : Measurable ρv) (β : ℝ)
    (b : BoundConf L M N → ℝ)
    (hb : Measurable b) (F : BoundConf L M N → PastConf L M N → ℝ)
    (hint : Integrable (fun p : BoundConf L M N × (PastConf L M N × PastConf L M N) =>
        Real.exp (-(haarWilsonAction (L := L) (M := M) (N := N) β b p)) * fkOSForm F p)
      ((boundHaarMeasure (L := L) G ρv).prod
        ((pastHaarMeasure (L := L) G ρv).prod (pastHaarMeasure (L := L) G ρv)))) :
    0 ≤ ∫ p, fkOSForm F p ∂(haarGibbsMeasure (L := L) (M := M) (N := N) G ρv β b) := by
  haveI := isProbabilityMeasure_boundHaarMeasure (L := L) G M ρv hρv
  haveI := isProbabilityMeasure_pastHaarMeasure (L := L) G M ρv hρv
  rw [← osIntegrand_haar] at hint
  refine fkRef_reflectionPositive (boundHaarMeasure (L := L) G ρv)
    (pastHaarMeasure (L := L) G ρv) (haarBoundWeight b)
    (haarHalfKernel (L := L) (M := M) (N := N) β) F ?_ ?_ ?_ hint
  · rw [density_haar]
    exact (measurable_haarWilsonAction (L := L) (M := M) (N := N) (β := β) hb).neg.exp
  · exact fun _ => (Real.exp_pos _).le
  · exact fun _ _ => (Real.exp_pos _).le
end

end BookProof.ReflectionPositivity
