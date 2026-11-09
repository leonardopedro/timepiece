import Mathlib
import BookProof.OSReconstruction.HalfSpaceState
import BookProof.ReflectionPositivity.HalfSpaceAlgebra

/-!
# A concrete half-space state: the finite-volume free-field Gibbs state

Plan: `cftproof.md`, **E3** — `HalfSpaceState` is the abstract input of the reconstruction (a
`θ`-invariant linear functional, reflection positive on `𝔄₊`, normalized).  This module supplies a
*concrete* instance, built from the product structure the corpus's Feynman–Kac free-field measure
has: `BookProof.ReflectionPositivity.FeynmanKac.fkMeasure ρ ν = ρ ⊗ ν ⊗ ν`, with
`fk_reflectionPositive` the statement that the OS form is a single square integrated over the
reflection slice.

## Why the instance is finitely supported

`Observable` is `Config → ℝ` with no boundedness, measurability or integrability built in, and
`LinearFunctional`'s `map_add` quantifies over *all* observables.  A Bochner integral
`F ↦ ∫ F dμ` is therefore not additive on that carrier: `integral_add` needs both summands
integrable, which arbitrary `F` are not.  So the concrete state here is the **finite-volume**
Gibbs state — a finite sum over a finite grid of half-configurations with Gibbs weights — for
which additivity holds for every `F`.  It is the discrete shadow of the lattice free field: the
product structure `ρ ⊗ ν ⊗ ν` becomes a product of two identical finitely supported laws, and the
Feynman–Kac identity survives verbatim as `gibbsFun_osForm`.

## Contents

* `HalfIdx`, `halfCellEquiv`, `coordSumEquiv`, `configEquiv` — the splitting of the block lattice
  into its positive-time and negative-time halves, `Config ≃ (HalfIdx → ℝ) × (HalfIdx → ℝ)`;
  `coordSumEquiv_reflectCoord` and `configEquiv_symm_fieldReflection` say that the reflection
  *swaps the two halves*, and `dependsOn_posTimeCoords_iff` says that `𝔄₊` is exactly the
  observables that do not see the second half;
* `halfAction`, `GibbsVolume`, `gibbsWeight` — the free-field mass action on a half, a nonempty
  finite grid of half-configurations, and the normalized Gibbs weights on it;
* `gibbsFun`, `gibbsHalfSpaceState` — **the concrete `HalfSpaceState`**: the product Gibbs state
  `ω F = Σ_{x,y} w x w y F(x, y)`, with `ω 1 = 1` and reflection positivity on `𝔄₊`;
* `gibbsFun_osForm` — **the Feynman–Kac identity in finite volume**:
  `⟨F,F⟩ = (Σ_x w x · F(x, 0))² ≥ 0`;
* `gibbsMeasure`, `integral_gibbsMeasure` — **the same state as a genuine measure on `Config`**:
  the finitely supported law `Σ_{x,y} w x · w y · δ_{(x,y)}`, a probability measure
  (`gibbsMeasure_univ`, `gibbsMeasure_isProbability`) whose integral is the Gibbs functional on the
  integrable observables; `freeFieldMeasure` is the block-lattice product Gaussian reference law.

## Boundary

* The grid is arbitrary (any nonempty finite `support`); no continuum limit, and no identification
  with `fkKernelMeasure` is claimed — that identification would need the integral state above,
  which is not a `LinearFunctional`.
* The weights are the Gibbs weights of the *mass* term `Σ xᵢ²` of one half-slice; the
  nearest-neighbour term across slices is not weighted, because the halves are drawn
  independently, exactly as in the `fkMeasure` model.
* `𝔄₊` is dependence on the positive-time coordinates, and the block lattice has no reflection
  slice: `cellsPerBlock = 16` splits as `8 + 8`, so the "boundary" of the kernel form is absent.
  The free-field kernel `ν_z` therefore degenerates to a fixed `ν` here — the `fkMeasure` case,
  not the `fkKernelMeasure` case.
* `gibbsMeasure` is *supported on the declared grid*, so it is not `freeFieldMeasure`: the weights
  are the grid samples of the Gaussian density, and no identification, weak convergence or
  continuum limit between a grid law and the product Gaussian is claimed.
-/

namespace BookProof.OSReconstruction

open MeasureTheory
open BookProof.BalabanRG BookProof.ReflectionPositivity

noncomputable section

/-! ## Splitting the block lattice into the two time halves -/

/-- The indices of one time half: `nComponents` field components on `halfCells` cells. -/
abbrev HalfIdx : Type := Fin nComponents × Fin halfCells

theorem cellsPerBlock_eq : cellsPerBlock = 16 := by decide

theorem halfCells_eq : halfCells = 8 := by decide

/-- The cell split: the first `halfCells` cells go to the positive half. -/
def halfCellFun (c : Fin cellsPerBlock) : Fin halfCells ⊕ Fin halfCells :=
  if h : c.val < halfCells then Sum.inl ⟨c.val, h⟩
  else Sum.inr ⟨c.val - halfCells, by
    have h16 : cellsPerBlock = 16 := cellsPerBlock_eq
    have h8 : halfCells = 8 := halfCells_eq
    omega⟩

/-- The inverse cell split. -/
def halfCellInv (s : Fin halfCells ⊕ Fin halfCells) : Fin cellsPerBlock :=
  s.elim (fun i => ⟨i.val, by
      have h16 : cellsPerBlock = 16 := cellsPerBlock_eq
      have h8 : halfCells = 8 := halfCells_eq
      omega⟩) (fun i => ⟨i.val + halfCells, by
      have h16 : cellsPerBlock = 16 := cellsPerBlock_eq
      have h8 : halfCells = 8 := halfCells_eq
      omega⟩)

/-- **The cell split**, an equivalence.  Checked cell by cell: there are sixteen. -/
def halfCellEquiv : Fin cellsPerBlock ≃ Fin halfCells ⊕ Fin halfCells where
  toFun := halfCellFun
  invFun := halfCellInv
  left_inv := by intro c; fin_cases c <;> decide
  right_inv := by intro s; rcases s with i | i <;> fin_cases i <;> decide

/-- **The reflection swaps the halves** at the level of a cell. -/
theorem halfCellFun_flipCell (c : Fin cellsPerBlock) :
    halfCellFun (flipCell c) = (halfCellFun c).swap := by
  fin_cases c <;> decide

/-- **The component split** `Fin latticeDim ≃ HalfIdx ⊕ HalfIdx`, positive half first. -/
def coordSumEquiv : Fin latticeDim ≃ HalfIdx ⊕ HalfIdx :=
  coordEquiv.symm.trans
    ((Equiv.prodCongr (Equiv.refl (Fin nComponents)) halfCellEquiv).trans
      (Equiv.prodSumDistrib (Fin nComponents) (Fin halfCells) (Fin halfCells)))

/-- The value of the component split. -/
theorem coordSumEquiv_apply (i : Fin latticeDim) :
    coordSumEquiv i =
      Equiv.prodSumDistrib (Fin nComponents) (Fin halfCells) (Fin halfCells)
        ((coordEquiv.symm i).1, halfCellFun (coordEquiv.symm i).2) := rfl

/-- The inverse of the component split on the positive half. -/
theorem coordSumEquiv_symm_inl (p : HalfIdx) :
    coordSumEquiv.symm (Sum.inl p) = coordIdx (p.1, halfCellInv (Sum.inl p.2)) := by
  obtain ⟨μ, i⟩ := p
  fin_cases μ <;> fin_cases i <;> decide

/-- The positive half has a positive-time index. -/
theorem isPosTime_coordSumEquiv_symm_inl (p : HalfIdx) :
    isPosTime (coordSumEquiv.symm (Sum.inl p)) := by
  obtain ⟨μ, i⟩ := p
  fin_cases μ <;> fin_cases i <;> decide

/-- A positive-time index lies in the positive half. -/
theorem coordSumEquiv_eq_inl_of_isPosTime {i : Fin latticeDim} (h : isPosTime i) :
    ∃ p : HalfIdx, coordSumEquiv i = Sum.inl p := by
  refine ⟨((coordEquiv.symm i).1, ⟨(coordEquiv.symm i).2.val, h⟩), ?_⟩
  rw [show coordSumEquiv i = Equiv.prodSumDistrib (Fin nComponents) (Fin halfCells) (Fin halfCells)
      ((coordEquiv.symm i).1, halfCellFun (coordEquiv.symm i).2) from rfl]
  rw [show halfCellFun (coordEquiv.symm i).2
      = Sum.inl ⟨(coordEquiv.symm i).2.val, h⟩ from dif_pos h]
  rfl

/-- **The reflection swaps the two halves** on the component split. -/
theorem coordSumEquiv_reflectCoord (i : Fin latticeDim) :
    coordSumEquiv (reflectCoord i) = (coordSumEquiv i).swap := by
  fin_cases i <;> decide

/-- **The configuration split** `Config ≃ (HalfIdx → ℝ) × (HalfIdx → ℝ)`: the positive half and
the negative half of the block lattice. -/
def configEquiv : Config ≃ ((HalfIdx → ℝ) × (HalfIdx → ℝ)) :=
  (Equiv.arrowCongr coordSumEquiv (Equiv.refl ℝ)).trans
    (Equiv.sumArrowEquivProdArrow HalfIdx HalfIdx ℝ)

/-- Evaluation of the inverse split. -/
theorem configEquiv_symm_apply (a b : HalfIdx → ℝ) (i : Fin latticeDim) :
    configEquiv.symm (a, b) i = Sum.elim a b (coordSumEquiv i) := rfl

/-- The positive half of a split configuration. -/
theorem configEquiv_fst (z : Config) (p : HalfIdx) :
    (configEquiv z).1 p = z (coordSumEquiv.symm (Sum.inl p)) := rfl

/-- **The reflection swaps the halves** of a configuration. -/
theorem configEquiv_symm_fieldReflection (a b : HalfIdx → ℝ) :
    fieldReflection (configEquiv.symm (a, b)) = configEquiv.symm (b, a) := by
  funext i
  change (configEquiv.symm (a, b)) (reflectCoord i) = configEquiv.symm (b, a) i
  rw [configEquiv_symm_apply, configEquiv_symm_apply, coordSumEquiv_reflectCoord]
  cases h : coordSumEquiv i <;> simp

/-- **`𝔄₊` is exactly the observables that do not see the negative half.** -/
theorem dependsOn_posTimeCoords_iff (F : Observable) :
    F ∈ PositiveTimeAlgebra ↔
      ∀ (a b b' : HalfIdx → ℝ), F (configEquiv.symm (a, b)) = F (configEquiv.symm (a, b')) := by
  constructor
  · intro hF a b b'
    refine hF _ _ fun i hi => ?_
    obtain ⟨p, hp⟩ := coordSumEquiv_eq_inl_of_isPosTime (mem_posTimeCoords.1 hi)
    rw [configEquiv_symm_apply, configEquiv_symm_apply, hp]
    simp
  · intro h x y hxy
    have ha : (configEquiv x).1 = (configEquiv y).1 := by
      funext p
      rw [configEquiv_fst, configEquiv_fst]
      exact hxy _ (mem_posTimeCoords.2 (isPosTime_coordSumEquiv_symm_inl p))
    have h1 : F x = F (configEquiv.symm ((configEquiv y).1, (configEquiv x).2)) := by
      conv_lhs => rw [show x = configEquiv.symm ((configEquiv x).1, (configEquiv x).2) from
        (configEquiv.symm_apply_apply x).symm]
      rw [ha]
    have h2 : F (configEquiv.symm ((configEquiv y).1, (configEquiv x).2))
        = F (configEquiv.symm ((configEquiv y).1, (configEquiv y).2)) :=
      h _ _ _
    have h3 : F (configEquiv.symm ((configEquiv y).1, (configEquiv y).2)) = F y := by
      rw [show configEquiv.symm ((configEquiv y).1, (configEquiv y).2) = y from
        configEquiv.symm_apply_apply y]
    exact h1.trans (h2.trans h3)

/-! ## Gibbs weights on a finite grid of half-configurations -/

/-- The free-field mass action of one half-configuration. -/
def halfAction (x : HalfIdx → ℝ) : ℝ := ∑ i, (x i) ^ 2

/-- A finite grid of half-configurations: the finite-volume support of the Gibbs state. -/
structure GibbsVolume where
  /-- The grid. -/
  support : Finset (HalfIdx → ℝ)
  /-- The grid is nonempty, so the partition function is positive. -/
  support_nonempty : support.Nonempty

/-- The finite-volume partition function of the mass term. -/
def gibbsPartition (V : GibbsVolume) : ℝ :=
  ∑ x ∈ V.support, Real.exp (-(halfAction x))

theorem gibbsPartition_pos (V : GibbsVolume) : 0 < gibbsPartition V := by
  obtain ⟨x, hx⟩ := V.support_nonempty
  refine Finset.sum_pos' (fun y _ => (Real.exp_pos _).le) ⟨x, hx, Real.exp_pos _⟩

/-- **The normalized Gibbs weight** of a half-configuration. -/
def gibbsWeight (V : GibbsVolume) (x : HalfIdx → ℝ) : ℝ :=
  Real.exp (-(halfAction x)) / gibbsPartition V

theorem gibbsWeight_nonneg (V : GibbsVolume) (x : HalfIdx → ℝ) : 0 ≤ gibbsWeight V x :=
  div_nonneg (Real.exp_pos _).le (gibbsPartition_pos V).le

theorem gibbsWeight_sum (V : GibbsVolume) : ∑ x ∈ V.support, gibbsWeight V x = 1 := by
  simp only [gibbsWeight, ← Finset.sum_div]
  exact div_self (ne_of_gt (gibbsPartition_pos V))

/-! ## The concrete state -/

/-- **The product Gibbs functional** `ω F = Σ_{x,y} w x w y F(x, y)`: the finite-volume
`ρ ⊗ ν ⊗ ν` of the Feynman–Kac model, with both half-space laws the same `w`. -/
def gibbsFun (V : GibbsVolume) (F : Observable) : ℝ :=
  ∑ x ∈ V.support, ∑ y ∈ V.support,
    gibbsWeight V x * gibbsWeight V y * F (configEquiv.symm (x, y))

theorem gibbsFun_add (V : GibbsVolume) (F G : Observable) :
    gibbsFun V (F + G) = gibbsFun V F + gibbsFun V G := by
  simp only [gibbsFun, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem gibbsFun_smul (V : GibbsVolume) (c : ℝ) (F : Observable) :
    gibbsFun V (c • F) = c * gibbsFun V F := by
  simp only [gibbsFun, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

theorem gibbsFun_theta (V : GibbsVolume) (F : Observable) :
    gibbsFun V (thetaObs F) = gibbsFun V F := by
  simp only [gibbsFun, thetaObs_apply, configEquiv_symm_fieldReflection]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem gibbsFun_one (V : GibbsVolume) : gibbsFun V (1 : Observable) = 1 := by
  simp only [gibbsFun, Pi.one_apply, mul_one]
  rw [← Finset.sum_mul_sum, gibbsWeight_sum]
  exact mul_one 1

/-- **The finite-volume Feynman–Kac identity**: the OS form on `𝔄₊` is a single square. -/
theorem gibbsFun_osForm (V : GibbsVolume) (F : PositiveTimeAlgebra) :
    gibbsFun V (thetaObs (F : Observable) * (F : Observable))
      = (∑ x ∈ V.support, gibbsWeight V x * (F : Observable) (configEquiv.symm (x, 0))) ^ 2 := by
  have hdep := (dependsOn_posTimeCoords_iff (F : Observable)).1 F.2
  have hterm : ∀ x y : HalfIdx → ℝ,
      gibbsWeight V x * gibbsWeight V y *
        ((thetaObs (F : Observable) * (F : Observable)) (configEquiv.symm (x, y)))
      = (gibbsWeight V x * (F : Observable) (configEquiv.symm (x, 0)))
          * (gibbsWeight V y * (F : Observable) (configEquiv.symm (y, 0))) := by
    intro x y
    simp only [Pi.mul_apply, thetaObs_apply, configEquiv_symm_fieldReflection,
      hdep x y 0, hdep y x 0]
    ring
  calc gibbsFun V (thetaObs (F : Observable) * (F : Observable))
      = ∑ x ∈ V.support, ∑ y ∈ V.support,
          (gibbsWeight V x * (F : Observable) (configEquiv.symm (x, 0)))
            * (gibbsWeight V y * (F : Observable) (configEquiv.symm (y, 0))) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hterm x y
    _ = (∑ x ∈ V.support, gibbsWeight V x * (F : Observable) (configEquiv.symm (x, 0)))
          * (∑ x ∈ V.support, gibbsWeight V x * (F : Observable) (configEquiv.symm (x, 0))) := by
        rw [Finset.sum_mul_sum]
    _ = _ := by ring

/-- **Reflection positivity of the finite-volume Gibbs state on `𝔄₊`**, from the
Feynman–Kac identity alone. -/
theorem gibbs_reflectionPositive (V : GibbsVolume) :
    IsReflectionPositiveOn (PositiveTimeAlgebra : Set Observable) (gibbsFun V) := by
  intro F hF
  have h : osForm (gibbsFun V) F F = gibbsFun V (thetaObs F * F) := rfl
  rw [h, gibbsFun_osForm V ⟨F, hF⟩]
  exact sq_nonneg _

/-- **A concrete half-space state**: the finite-volume free-field Gibbs state. -/
def gibbsHalfSpaceState (V : GibbsVolume) : HalfSpaceState where
  ω :=
    { toFun := gibbsFun V
      map_add := gibbsFun_add V
      map_smul := gibbsFun_smul V
      map_theta := gibbsFun_theta V }
  pos := gibbs_reflectionPositive V
  norm_one := gibbsFun_one V

/-- Its reconstructed vacuum is a unit vector — `hsVacuum_norm`, instantiated. -/
theorem gibbsVacuum_norm (V : GibbsVolume) :
    ‖hsVacuum (gibbsHalfSpaceState V)‖ = 1 :=
  hsVacuum_norm _

/-! ## The Gibbs measure on `Config`

`gibbsFun` is a finite sum over a grid, and above it is only a `LinearFunctional` because an
unbounded Bochner integral is not additive on `Observable = Config → ℝ`.  It *is* however the
integral against a genuine measure on the block lattice: the finitely supported measure that puts
the mass `w x · w y` on the configuration `configEquiv.symm (x, y)`.  On the integrable observables
the two agree (`integral_gibbsMeasure`), so `gibbsHalfSpaceState` is the integral state of
`gibbsMeasure`.

The block-lattice free-field reference law is the product Gaussian `freeFieldMeasure`; the grid
weights are its normalized densities `exp (-Σ xᵢ²)`, i.e. the mass term of the free-field action
with the Gaussian variance `1/2`.  The two objects are *not* identified: `gibbsMeasure` is
supported on the declared grid, and no continuum or infinite-volume limit is claimed. -/

/-- The atom of the finite Gibbs measure: mass `w x · w y` at `configEquiv.symm (x, y)`. -/
noncomputable def gibbsAtom (V : GibbsVolume) (x y : HalfIdx → ℝ) : Measure Config :=
  ENNReal.ofReal (gibbsWeight V x * gibbsWeight V y) •
    Measure.dirac (configEquiv.symm (x, y))

/-- **The finite-volume Gibbs measure on the block lattice.** -/
noncomputable def gibbsMeasure (V : GibbsVolume) : Measure Config :=
  ∑ x ∈ V.support, ∑ y ∈ V.support, gibbsAtom V x y

theorem gibbsAtom_apply (V : GibbsVolume) (x y : HalfIdx → ℝ) (s : Set Config) :
    gibbsAtom V x y s = ENNReal.ofReal (gibbsWeight V x * gibbsWeight V y) *
      (Measure.dirac (configEquiv.symm (x, y))) s := by
  rw [gibbsAtom, Measure.smul_apply, smul_eq_mul]

theorem gibbsAtom_univ (V : GibbsVolume) (x y : HalfIdx → ℝ) :
    gibbsAtom V x y Set.univ = ENNReal.ofReal (gibbsWeight V x * gibbsWeight V y) := by
  rw [gibbsAtom, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
    mul_one]

/-- One atom is dominated by the row of atoms over the same first half. -/
theorem gibbsAtom_le_row (V : GibbsVolume) {x y : HalfIdx → ℝ} (hy : y ∈ V.support) :
    gibbsAtom V x y ≤ ∑ y' ∈ V.support, gibbsAtom V x y' := by
  rw [Measure.le_iff']
  intro s
  simp only [Measure.finset_sum_apply]
  exact Finset.single_le_sum (f := fun y' => gibbsAtom V x y' s) (fun i _ => zero_le _) hy

/-- A row of atoms is dominated by the full Gibbs measure. -/
theorem gibbsRow_le (V : GibbsVolume) {x : HalfIdx → ℝ} (hx : x ∈ V.support) :
    (∑ y ∈ V.support, gibbsAtom V x y) ≤ gibbsMeasure V := by
  rw [Measure.le_iff']
  intro s
  simp only [gibbsMeasure, Measure.finset_sum_apply]
  exact Finset.single_le_sum (f := fun x' => ∑ y' ∈ V.support, gibbsAtom V x' y' s)
    (fun i _ => zero_le _) hx

/-- An atom is dominated by the full Gibbs measure. -/
theorem gibbsAtom_le (V : GibbsVolume) {x y : HalfIdx → ℝ} (hx : x ∈ V.support)
    (hy : y ∈ V.support) : gibbsAtom V x y ≤ gibbsMeasure V :=
  le_trans (gibbsAtom_le_row V hy) (gibbsRow_le V hx)

/-- The Gibbs measure is a probability measure. -/
theorem gibbsMeasure_univ (V : GibbsVolume) : gibbsMeasure V Set.univ = 1 := by
  have hmul : ∀ x y : HalfIdx → ℝ, ENNReal.ofReal (gibbsWeight V x * gibbsWeight V y)
      = ENNReal.ofReal (gibbsWeight V x) * ENNReal.ofReal (gibbsWeight V y) := by
    intro x y
    rw [ENNReal.ofReal_mul (gibbsWeight_nonneg V x)]
  have hw : ∑ x ∈ V.support, ENNReal.ofReal (gibbsWeight V x) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => gibbsWeight_nonneg V i), gibbsWeight_sum V]
    simp
  simp only [gibbsMeasure, Measure.finset_sum_apply, gibbsAtom_univ, hmul]
  rw [← Finset.sum_mul_sum, hw, one_mul]

instance gibbsMeasure_isProbability (V : GibbsVolume) : IsProbabilityMeasure (gibbsMeasure V) :=
  ⟨gibbsMeasure_univ V⟩

/-- **The integral of an observable against one atom** is its Gibbs-weighted value. -/
theorem integral_gibbsAtom (V : GibbsVolume) (x y : HalfIdx → ℝ) (F : Config → ℝ) :
    ∫ z, F z ∂(gibbsAtom V x y)
      = gibbsWeight V x * gibbsWeight V y * F (configEquiv.symm (x, y)) := by
  rw [gibbsAtom, integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (mul_nonneg (gibbsWeight_nonneg V x) (gibbsWeight_nonneg V y)),
    smul_eq_mul]

/-- **The Gibbs functional is an integral against the Gibbs measure** on the integrable
observables. -/
theorem integral_gibbsMeasure (V : GibbsVolume) {F : Config → ℝ}
    (hF : Integrable F (gibbsMeasure V)) :
    ∫ z, F z ∂(gibbsMeasure V) = gibbsFun V F := by
  have hInt : ∀ x ∈ V.support, Integrable F (∑ y ∈ V.support, gibbsAtom V x y) :=
    fun x hx => hF.mono_measure (gibbsRow_le V hx)
  have hatom : ∀ x ∈ V.support, ∀ y ∈ V.support, Integrable F (gibbsAtom V x y) :=
    fun x hx y hy => (hInt x hx).mono_measure (gibbsAtom_le_row V hy)
  calc ∫ z, F z ∂(gibbsMeasure V)
      = ∑ x ∈ V.support, ∫ z, F z ∂(∑ y ∈ V.support, gibbsAtom V x y) := by
        rw [gibbsMeasure, integral_finset_sum_measure hInt]
    _ = ∑ x ∈ V.support, ∑ y ∈ V.support, ∫ z, F z ∂(gibbsAtom V x y) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        exact integral_finset_sum_measure (fun y hy => hatom x hx y hy)
    _ = ∑ x ∈ V.support, ∑ y ∈ V.support,
          gibbsWeight V x * gibbsWeight V y * F (configEquiv.symm (x, y)) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        exact integral_gibbsAtom V x y F
    _ = gibbsFun V F := rfl

/-! ## The block-lattice free-field reference law -/

/-- **The product Gaussian free-field law** on the block lattice: `∏ᵢ N(0, 1/2)`, whose density is
`exp (-Σ xᵢ²)` up to the normalizing constant — the mass term of the free-field action.  It is the
reference measure `gibbsMeasure` discretizes; no identity between the two is claimed. -/
noncomputable def freeFieldMeasure : Measure Config :=
  Measure.pi (fun _ : Fin latticeDim => ProbabilityTheory.gaussianReal 0 ⟨1 / 2, by norm_num⟩)

instance freeFieldMeasure_isProbability : IsProbabilityMeasure freeFieldMeasure := by
  constructor
  rw [freeFieldMeasure, Measure.pi_univ]
  simp

end

end BookProof.OSReconstruction
