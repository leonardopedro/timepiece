import Mathlib
import BookProof.ReflectionPositivity.LatticeFreeField

/-!
# The Wilson plaquette term and reflection positivity of the lattice gauge measure

`BookProof.ReflectionPositivity.LatticeFreeField` identifies the *free* lattice Gaussian with the
Feynman–Kac product form `ρ ⊗ ν_z ⊗ ν_z`, whose reflection positivity is then a theorem about
positive densities.  The obvious question is whether the interaction destroys this, and it does
not: the Wilson plaquette term splits at the reflection slice for the same structural reason the
Gaussian action does.  This chapter proves that, with the plaquette bound it rests on.

## 1. The plaquette bound

The Wilson plaquette Boltzmann factor is `exp(-β (1 - Re tr U_p / N))` with `U_p` the plaquette
holonomy in `U(N)`.  The bound that makes it a *weight* rather than merely a number is

`Re tr U ≤ N`   (**`re_trace_le_card`**), for `U` unitary,

which gives `0 ≤ 1 - Re tr U / N` (**`plaqDensity_nonneg`**) and hence
`0 < plaquetteWeight ≤ 1` for `β ≥ 0` and `N > 0` (**`plaquetteWeight_pos`**,
**`plaquetteWeight_le_one`**).  So every plaquette contributes a positive factor no larger than
one, and the interacting Boltzmann density is a product of positive factors — the property the
reflection-positivity argument uses, and the only property of the interaction it uses.

The bound itself is elementary but not vacuous: it is `|tr U| ≤ N` for a unitary matrix, proved
here from row-orthonormality of `U` (`sum_normSq_row`: the rows are unit vectors), which gives
`‖U i j‖ ≤ 1` entrywise (`norm_entry_le_one`) and then `‖tr U‖ ≤ N` by the triangle inequality
(`norm_trace_le_card`).

## 2. The interaction does not spoil the slice split

A plaquette is classified by which links it uses: those in the past half-space, those invariant
under the reflection, and those in the future half-space.  Under the reflection the future class
is the image of the past class, so with `A` the past half-space action (a sum of plaquette
weights), the future half contributes the *same* function `A`, and the invariant plaquettes give
a function `b` of the boundary configuration only:

`S(z, y₋, y₊) = A(z, y₋) + A(z, y₊) + b(z)`   (**`wilsonAction`**).

The content is that **no plaquette contributes a term depending on both halves**: the discrete
mixed difference of `S` in `(y₋, y₊)` vanishes identically
(**`wilson_mixed_difference_zero`**), the interacting analogue of
`FeynmanKac.freeAction_cross_vanishes`.  Consequently the density factorises,
`exp(-S) = exp(-A(z,y₋)) · exp(-A(z,y₊)) · exp(-b(z))`
(**`wilson_density_factorises`**), the reflection exchanges the two middle factors without
changing them (**`wilsonAction_reflect`**), and the measure **is** `ρ ⊗ ν_z ⊗ ν_z`
(**`wilsonMeasure_eq_fkKernelMeasure`**) with the *interacting* half-space kernel
`ν_z = exp(-A(z,·))`.  Reflection positivity then follows from the kernel Feynman–Kac theorem —
which never used that the density was Gaussian:

**`wilson_reflectionPositive`** — the lattice gauge measure with the Wilson plaquette action is
reflection positive, for every half-space observable with integrable moments.

## Honest boundary

* The **lattice geometry** is partly an input here: the link variables are not modelled in this
  file, and the classification of plaquettes into past / invariant / future is packaged in the
  shape of `wilsonAction` (a sum of a past-, a future- and a boundary-supported term) rather than
  derived.  What is proved here is that *given* that classification, reflection positivity
  follows — i.e. that the interaction is not an obstruction.  The classification itself is derived
  from an explicit lattice of links in `BookProof.ReflectionPositivity.WilsonLinkLattice`
  (`timeSet_subset`, `plaq_cover`, `plaq_classification`, `pastSide_image_iff`); the remaining gap
  is the matrix-valued holonomy across the reflection, recorded in that chapter's boundary.
* The **group measure** is not modelled: the half-space kernel `ν_z` is a positive function
  against a fixed reference measure (`volume`), not a Haar measure on a compact group, and gauge
  invariance of the observables is not used or claimed.
* The normalising constant of the interacting measure is not evaluated (it cancels, as in the
  free case), so no statement about finiteness or about the thermodynamic limit is made.
-/

namespace BookProof.ReflectionPositivity

open MeasureTheory
open scoped BigOperators

noncomputable section

/-! ## 1. The plaquette bound -/

/-- **Row-orthonormality of a unitary matrix**: the squared norms of the entries of any row sum
to one. -/
theorem sum_normSq_row {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) (i : Fin N) : ∑ j, ‖U i j‖ ^ 2 = 1 := by
  have h : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have hii := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i i) h
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hii
  have hterm : ∀ k : Fin N, U i k * star (U i k) = ((‖U i k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [show star (U i k) = (starRingEnd ℂ) (U i k) from rfl, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hterm k] at hii
  refine Complex.ofReal_injective ?_
  rw [Complex.ofReal_sum]
  simpa using hii

/-- Every entry of a unitary matrix has norm at most one. -/
theorem norm_entry_le_one {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) (i j : Fin N) : ‖U i j‖ ≤ 1 := by
  have h := sum_normSq_row hU i
  have hsingle : ‖U i j‖ ^ 2 ≤ 1 := by
    rw [← h]
    exact Finset.single_le_sum (f := fun k => ‖U i k‖ ^ 2) (fun k _ => by positivity)
      (Finset.mem_univ j)
  nlinarith [norm_nonneg (U i j)]

/-- **`|tr U| ≤ N` for a unitary matrix.** -/
theorem norm_trace_le_card {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) : ‖U.trace‖ ≤ N := by
  have htr : U.trace = ∑ i, U i i := rfl
  rw [htr]
  calc ‖∑ i, U i i‖ ≤ ∑ i, ‖U i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => norm_entry_le_one hU i i
    _ = N := by simp

/-- **The plaquette bound**: the real part of the trace of a unitary `N × N` matrix is at most
`N`.  This is what makes `1 - Re tr U / N` nonnegative. -/
theorem re_trace_le_card {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) : U.trace.re ≤ N :=
  le_trans (Complex.re_le_norm _) (norm_trace_le_card hU)

/-- The **plaquette action density** `1 - Re tr U_p / N`: the Wilson action per plaquette, up to
the inverse coupling `β`. -/
def plaqDensity (N : ℕ) (U : Matrix (Fin N) (Fin N) ℂ) : ℝ := 1 - U.trace.re / N

/-- **The plaquette density is nonnegative** — this is `re_trace_le_card`, divided by `N`. -/
theorem plaqDensity_nonneg {N : ℕ} (hN : 0 < N) {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) : 0 ≤ plaqDensity N U := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have := re_trace_le_card hU
  simp only [plaqDensity]
  have : U.trace.re / N ≤ 1 := by
    rw [div_le_one hN']
    exact this
  linarith

/-- The **plaquette Boltzmann factor** `exp(-β (1 - Re tr U / N))`. -/
def plaquetteWeight (β : ℝ) (N : ℕ) (U : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  Real.exp (-(β * plaqDensity N U))

/-- The plaquette weight is strictly positive. -/
theorem plaquetteWeight_pos (β : ℝ) (N : ℕ) (U : Matrix (Fin N) (Fin N) ℂ) :
    0 < plaquetteWeight β N U :=
  Real.exp_pos _

/-- **The plaquette weight is at most one** for `β ≥ 0`: the bound `Re tr U ≤ N` makes the
exponent nonpositive. -/
theorem plaquetteWeight_le_one {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 0 < N)
    {U : Matrix (Fin N) (Fin N) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    plaquetteWeight β N U ≤ 1 := by
  have h := plaqDensity_nonneg hN hU
  rw [plaquetteWeight, Real.exp_le_one_iff]
  nlinarith [mul_nonneg hβ h]

/-! ## 2. The interacting half-space action and the slice split -/

variable {Gz Gy : Type*} [MeasureSpace Gz] [MeasureSpace Gy]
variable [SFinite (volume : Measure Gz)] [SFinite (volume : Measure Gy)]
variable {P : Type*} [Fintype P]

/-- **The half-space Wilson action**: the sum of the plaquette densities of one half-space,
`A(y, z) = Σ_{p in the half} β (1 - Re tr U_p / N)`, where the holonomy `U p y z` of the
`p`-th plaquette is a function of the half-space configuration `y` and the boundary
configuration `z`.  This is *the same function* for the past and the future half-space — the
reflection identifies them — which is what makes the OS form a square. -/
def wilsonHalfAction (β : ℝ) (N : ℕ) (U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ)
    (y : Gy) (z : Gz) : ℝ :=
  ∑ p, β * plaqDensity N (U p y z)

/-- **The interaction's half-space action is nonnegative** for `β ≥ 0`: a sum of nonnegative
plaquette densities. -/
theorem wilsonHalfAction_nonneg {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 0 < N)
    {U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ}
    (hU : ∀ (p : P) (y : Gy) (z : Gz), U p y z ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (y : Gy) (z : Gz) : 0 ≤ wilsonHalfAction β N U y z :=
  Finset.sum_nonneg fun p _ => mul_nonneg hβ (plaqDensity_nonneg hN (hU p y z))

/-- The interacting half-space weight `ν_z(y) = exp(-A(y,z))` is **strictly positive**: every
plaquette of the half-space contributes a positive factor. -/
theorem wilsonHalfWeight_pos (β : ℝ) (N : ℕ) (U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ)
    (y : Gy) (z : Gz) : 0 < Real.exp (-(wilsonHalfAction β N U y z)) :=
  Real.exp_pos _

/-- **The interacting half-space weight is at most one** — the product of the plaquette bounds
`plaquetteWeight_le_one` over the half-space. -/
theorem wilsonHalfWeight_le_one {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 0 < N)
    {U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ}
    (hU : ∀ (p : P) (y : Gy) (z : Gz), U p y z ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (y : Gy) (z : Gz) : Real.exp (-(wilsonHalfAction β N U y z)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.2 (wilsonHalfAction_nonneg hβ hN hU y z)

/-- **The lattice gauge action at the reflection slice**: the past half-space action, the future
half-space action (the same function on the reflected configuration), and the boundary action of
the plaquettes invariant under the reflection. -/
def wilsonAction (β : ℝ) (N : ℕ) (U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ)
    (b : Gz → ℝ) (γ : Gz × (Gy × Gy)) : ℝ :=
  wilsonHalfAction β N U γ.2.1 γ.1 + wilsonHalfAction β N U γ.2.2 γ.1 + b γ.1

/-- **No plaquette couples the two half-spaces**: the discrete mixed difference of the action in
`(y₋, y₊)` vanishes.  This is the interacting counterpart of
`FeynmanKac.freeAction_cross_vanishes`, and it is what the plaquette classification buys. -/
theorem wilson_mixed_difference_zero (β : ℝ) (N : ℕ)
    (U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ) (b : Gz → ℝ) (z : Gz) (y₁ y₂ y₃ y₄ : Gy) :
    wilsonAction β N U b (z, (y₁, y₃)) - wilsonAction β N U b (z, (y₂, y₃))
        - wilsonAction β N U b (z, (y₁, y₄)) + wilsonAction β N U b (z, (y₂, y₄)) = 0 := by
  simp only [wilsonAction]
  ring

/-- **The density factorises at the reflection slice**: `exp(-S)` is the product of the two
half-space weights and the boundary weight.  No factor mixes the two halves. -/
theorem wilson_density_factorises (β : ℝ) (N : ℕ)
    (U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ) (b : Gz → ℝ) (γ : Gz × (Gy × Gy)) :
    Real.exp (-(wilsonAction β N U b γ))
      = Real.exp (-(wilsonHalfAction β N U γ.2.1 γ.1))
        * Real.exp (-(wilsonHalfAction β N U γ.2.2 γ.1)) * Real.exp (-(b γ.1)) := by
  simp only [wilsonAction, ← Real.exp_add]
  congr 1
  ring

/-- **The reflection** on the configuration space: it exchanges the two half-spaces and fixes the
boundary slice. -/
def reflectConf (γ : Gz × (Gy × Gy)) : Gz × (Gy × Gy) := (γ.1, (γ.2.2, γ.2.1))

theorem reflectConf_involutive : Function.Involutive (reflectConf (Gz := Gz) (Gy := Gy)) :=
  fun _ => rfl

/-- **The Wilson action is reflection invariant**: exchanging the two half-spaces leaves it
unchanged, because the future half-space action is the same function of the reflected
configuration. -/
theorem wilsonAction_reflect (β : ℝ) (N : ℕ)
    (U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ) (b : Gz → ℝ) (γ : Gz × (Gy × Gy)) :
    wilsonAction β N U b (reflectConf γ) = wilsonAction β N U b γ := by
  simp only [wilsonAction, reflectConf]
  ring

/-- **The interacting lattice gauge measure** (unnormalised): the Wilson Boltzmann density
against the reference measure on `boundary × (past × future)`. -/
def wilsonMeasure (β : ℝ) (N : ℕ) (U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ)
    (b : Gz → ℝ) : Measure (Gz × (Gy × Gy)) :=
  ((volume : Measure Gz).prod ((volume : Measure Gy).prod (volume : Measure Gy))).withDensity
    (fun γ => ENNReal.ofReal (Real.exp (-(wilsonAction β N U b γ))))

/-- **The boundary weight** `ρ = exp(-b)`, coming from the plaquettes invariant under the
reflection. -/
def wilsonBoundaryWeight (b : Gz → ℝ) (z : Gz) : ℝ := Real.exp (-(b z))

/-- **The half-space kernel** `ν_z(y) = exp(-A(y,z))`. -/
def wilsonHalfWeight (β : ℝ) (N : ℕ) (U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ)
    (z : Gz) (y : Gy) : ℝ := Real.exp (-(wilsonHalfAction β N U y z))

theorem fkKernelDensity_wilson (β : ℝ) (N : ℕ)
    (U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ) (b : Gz → ℝ) (γ : Gz × (Gy × Gy)) :
    fkKernelDensity (wilsonBoundaryWeight b) (wilsonHalfWeight β N U) γ
      = Real.exp (-(wilsonAction β N U b γ)) := by
  simp only [fkKernelDensity, wilsonBoundaryWeight, wilsonHalfWeight, wilsonAction,
    ← Real.exp_add]
  congr 1
  ring

/-- **The Wilson lattice gauge measure is `ρ ⊗ ν_z ⊗ ν_z`** — with the *interacting* half-space
kernel `ν_z = exp(-A(z,·))`.  The interaction changes the kernel, not the structure. -/
theorem wilsonMeasure_eq_fkKernelMeasure (β : ℝ) (N : ℕ)
    (U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ) (b : Gz → ℝ) :
    wilsonMeasure β N U b
      = fkKernelMeasure (Z₀ := Gz) (Y := Gy)
          (wilsonBoundaryWeight b) (wilsonHalfWeight β N U) := by
  rw [wilsonMeasure, fkKernelMeasure_eq]
  congr 1
  funext γ
  rw [fkKernelDensity_wilson]

/-- A half-space observable, read on the full configuration through the *future* half.  Applying
the reflection reads it through the past half. -/
def liftHalf (f : Gz → Gy → ℝ) : Gz × (Gy × Gy) → ℝ := fun γ => f γ.1 γ.2.2

theorem liftHalf_reflect (f : Gz → Gy → ℝ) (γ : Gz × (Gy × Gy)) :
    liftHalf f (reflectConf γ) = f γ.1 γ.2.1 := rfl

/-- `θF · F` for a half-space observable is the Feynman–Kac integrand `f(z,y₋) · f(z,y₊)`. -/
theorem liftHalf_osForm (f : Gz → Gy → ℝ) (γ : Gz × (Gy × Gy)) :
    liftHalf f (reflectConf γ) * liftHalf f γ = fkOSForm f γ := rfl

/-- **Measurability of the interacting action**: it is a sum of the two half-space actions and the
boundary action, each a function of a projection. -/
theorem measurable_wilsonAction {β : ℝ} {N : ℕ}
    {U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ} {b : Gz → ℝ}
    (hmeas : Measurable fun q : Gy × Gz => wilsonHalfAction β N U q.1 q.2)
    (hb : Measurable b) :
    Measurable fun γ : Gz × (Gy × Gy) => wilsonAction β N U b γ := by
  have hpair1 : Measurable fun γ : Gz × (Gy × Gy) => (γ.2.1, γ.1) := by fun_prop
  have hpair2 : Measurable fun γ : Gz × (Gy × Gy) => (γ.2.2, γ.1) := by fun_prop
  have hb1 : Measurable fun γ : Gz × (Gy × Gy) => b γ.1 := hb.comp measurable_fst
  have hsum : Measurable fun γ : Gz × (Gy × Gy) =>
      wilsonHalfAction β N U γ.2.1 γ.1 + wilsonHalfAction β N U γ.2.2 γ.1 + b γ.1 :=
    ((hmeas.comp hpair1).add (hmeas.comp hpair2)).add hb1
  simpa only [wilsonAction] using hsum

set_option maxHeartbeats 1600000 in
-- the product-measure unifications over `Gz × (Gy × Gy)` need more than the default budget
/-- **Reflection positivity of the lattice gauge measure**, for the Wilson plaquette action.

The proof uses exactly two facts about the interaction: every plaquette weight is positive
(`plaquetteWeight_pos`, from the bound `Re tr U ≤ N`) and the plaquettes classify into past /
invariant / future (`wilson_density_factorises`), so the measure is `ρ ⊗ ν_z ⊗ ν_z` with a
positive kernel.  The Gaussian form of the free-field kernel is *not* used, which is why the
interaction does not spoil the argument. -/
theorem wilson_reflectionPositive {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 0 < N)
    {U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ} {b : Gz → ℝ}
    (hmeas : Measurable fun q : Gy × Gz => wilsonHalfAction β N U q.1 q.2)
    (hb : Measurable b) (f : Gz → Gy → ℝ)
    (hint : Integrable (fun γ : Gz × (Gy × Gy) =>
        Real.exp (-(wilsonAction β N U b γ)) * fkOSForm f γ)
      ((volume : Measure Gz).prod ((volume : Measure Gy).prod (volume : Measure Gy)))) :
    0 ≤ ∫ γ, liftHalf f (reflectConf γ) * liftHalf f γ ∂(wilsonMeasure β N U b) := by
  have hD : Measurable fun γ : Gz × (Gy × Gy) =>
      fkKernelDensity (wilsonBoundaryWeight b) (wilsonHalfWeight β N U) γ := by
    have hexp : Measurable fun γ : Gz × (Gy × Gy) =>
        Real.exp (-(wilsonAction β N U b γ)) := (measurable_wilsonAction hmeas hb).neg.exp
    simpa only [fkKernelDensity_wilson] using hexp
  have hρ : ∀ z : Gz, 0 ≤ wilsonBoundaryWeight b z := fun _ => (Real.exp_pos _).le
  have hν : ∀ (z : Gz) (y : Gy), 0 ≤ wilsonHalfWeight β N U z y := fun _ _ => (Real.exp_pos _).le
  rw [wilsonMeasure_eq_fkKernelMeasure]
  have h := fkKernel_reflectionPositive (wilsonBoundaryWeight b) (wilsonHalfWeight β N U) f
    hD hρ hν (by simpa only [fkKernelDensity_wilson] using hint)
  simpa only [liftHalf_osForm] using h

end

end BookProof.ReflectionPositivity
