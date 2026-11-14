import BookProof.ReflectionPositivity.HalfSpaceAlgebra
import BookProof.OSReconstruction.HalfSpaceHilbert

/-!
# The concrete lattice translation, and why `PreservesPositiveTime` fails for it

`PreservesPositiveTime` (`HalfSpaceHilbert`) has so far been an abstract hypothesis: the corpus
contains no instance of `TimeTranslation` at all, so the E3 chain never instantiates `hsEvol`.
This module builds the translation the lattice actually supplies and reports what it gives.

## The construction

A configuration is a function `Config = Fin latticeDim → ℝ` on cells `c : Fin cellsPerBlock`,
split into a component `μ : Fin nComponents` and a cell (`coordOf`).  A time step is the cyclic
cell rotation `cellRotate = finRotate cellsPerBlock`, lifted to sites by acting on the cell and
leaving `μ` alone (`siteShift`).  The induced action on observables is precomposition,
`obsShift k F x = F (x ∘ siteShift ^ k)`; it is linear, multiplicative, unital, and invertible
with inverse `obsShift (-k)`, i.e. an automorphism of the observable algebra for every `k : ℤ`.

## What this gives, and what it cannot

* The lattice group acting here is `ℤ` (in fact `ℤ/16`, on the cells of one block).  A
  `TimeTranslation` requires an `ℝ`-parameter group, and `ℝ → ℤ/16` has no nontrivial
  homomorphism, so **no `TimeTranslation` can be the lattice shift**; the shift is only
  `ℤ`-indexed.  `obsShift_add`/`obsShift_zero` are the group law at that level.
* `PreservesPositiveTime` asks that `T τ F` be positive-time for **every real** `τ`, including
  `τ < 0`.  For the lattice shift it already fails at `τ = 1`: the last positive-time cell
  (`halfCells - 1`) is shifted onto the first negative-time cell (`halfCells`), so the image of
  a positive-time observable depends on a past coordinate.  `not_preservesPositiveTime_of_shift`
  proves this for any `TimeTranslation` whose time-one map is the shift.

The failure is not an accident of this choice of shift: the "positive half" of a single block is
a finite cyclic half, so a step that moves the last positive cell necessarily lands in the
negative half.  A half-space with a one-sided translation direction would need an infinite
lattice (or a half-infinite block), which this carrier does not have.  The honest conclusions are
therefore the two recorded here: the shift is a genuine `ℤ`-automorphism of the observable
algebra, and the `ℝ`-parameter positive-time-preservation hypothesis is *false* for it rather than
merely unproved.
-/

namespace BookProof.OSReconstruction

open BookProof.BalabanRG BookProof.ReflectionPositivity

noncomputable section

/-! ## The lattice step as a permutation of sites -/

/-- One lattice step in the time direction: the cyclic rotation of the cells of a block. -/
def cellRotate : Equiv.Perm (Fin cellsPerBlock) := finRotate cellsPerBlock

/-- **The lattice step on sites**: rotate the cell and keep the field component `μ`. -/
def siteShift : Equiv.Perm (Fin latticeDim) :=
  (coordEquiv.symm.trans
    (Equiv.prodCongr (Equiv.refl (Fin nComponents)) cellRotate)).trans coordEquiv

/-- The step acts on the `(μ, cell)` decomposition by rotating the cell. -/
theorem coordOf_siteShift (i : Fin latticeDim) :
    coordOf (siteShift i) = ((coordOf i).1, cellRotate (coordOf i).2) := by
  simp [siteShift, cellRotate, coordOf, Prod.map]

/-- The cell rotation moves the last positive-time cell onto the first negative-time cell. -/
theorem cellRotate_lastPos :
    cellRotate (⟨7, by decide⟩ : Fin cellsPerBlock) = ⟨8, by decide⟩ :=
  finRotate_of_lt (n := 15) (k := 7) (by decide)

/-! ## The action on observables -/

/-- **Time `k` on observables**: `(T_k F)(x) = F(x ∘ siteShift ^ k)`. -/
def obsShift (k : ℤ) (F : Observable) : Observable :=
  fun x => F fun i => x ((siteShift ^ k) i)

/-- The same action as a linear map. -/
def obsShiftₗ (k : ℤ) : Observable →ₗ[ℝ] Observable where
  toFun F := obsShift k F
  map_add' F G := by
    funext x
    simp [obsShift, Pi.add_apply]
  map_smul' c F := by
    funext x
    simp [obsShift, Pi.smul_apply]

@[simp]
theorem obsShiftₗ_apply (k : ℤ) (F : Observable) : obsShiftₗ k F = obsShift k F := rfl

/-- The identity at time zero. -/
theorem obsShift_zero (F : Observable) : obsShift 0 F = F := by
  funext x
  simp [obsShift]

/-- **The group law of the lattice translation**: `T_{m+n} = T_m ∘ T_n`. -/
theorem obsShift_add (m n : ℤ) (F : Observable) :
    obsShift (m + n) F = obsShift m (obsShift n F) := by
  funext x
  simp [obsShift, zpow_add, Equiv.Perm.mul_apply]

/-- The translation is multiplicative: it is an endomorphism of the observable algebra. -/
theorem obsShift_mul (k : ℤ) (F G : Observable) :
    obsShift k (F * G) = obsShift k F * obsShift k G := by
  funext x
  simp [obsShift, Pi.mul_apply]

/-- The translation is unital. -/
theorem obsShift_one (k : ℤ) : obsShift k (1 : Observable) = 1 := by
  funext x
  simp [obsShift]

/-- The translation is invertible, with inverse the step in the opposite direction. -/
theorem obsShift_comp_neg (k : ℤ) (F : Observable) :
    obsShift k (obsShift (-k) F) = F := by
  rw [← obsShift_add, add_neg_cancel, obsShift_zero]

/-! ## Failure of positive-time preservation -/

/-- The last positive-time site: cell `halfCells - 1` of the first component. -/
def lastPosSite : Fin latticeDim := coordIdx (⟨0, by decide⟩, ⟨7, by decide⟩)

theorem coordOf_lastPosSite :
    coordOf lastPosSite = (⟨0, by decide⟩, ⟨7, by decide⟩) :=
  coordOf_coordIdx _

/-- `lastPosSite` is a positive-time site. -/
theorem isPosTime_lastPosSite : isPosTime lastPosSite := by
  rw [isPosTime, coordOf_lastPosSite]
  decide

/-- Its translate is a negative-time site. -/
theorem not_isPosTime_siteShift_lastPosSite : ¬ isPosTime (siteShift lastPosSite) := by
  rw [isPosTime, coordOf_siteShift, coordOf_lastPosSite, cellRotate_lastPos]
  decide

/-- The coordinate functional at the last positive-time site belongs to `𝔄₊`. -/
theorem coordFun_mem_positiveTime :
    ((fun x : Config => x lastPosSite) : Observable) ∈ PositiveTimeAlgebra :=
  fun _ _ hxy => hxy lastPosSite (mem_posTimeCoords.2 isPosTime_lastPosSite)

/-- **The lattice step does not preserve the positive-time algebra.**  The coordinate functional
at the last positive-time site is positive-time, but its translate reads the first negative-time
coordinate, so it is not. -/
theorem obsShift_one_not_mem_positiveTime :
    obsShift 1 ((fun x : Config => x lastPosSite) : Observable) ∉ PositiveTimeAlgebra := by
  intro hmem
  have hdep : dependsOn (obsShift 1 fun x : Config => x lastPosSite) posTimeCoords := hmem
  set y : Config := Pi.single (M := fun _ => ℝ) (siteShift lastPosSite) 1 with hy
  have hxy : ∀ i ∈ posTimeCoords, (0 : Config) i = y i := by
    intro i hi
    have hne : i ≠ siteShift lastPosSite := by
      intro h
      exact not_isPosTime_siteShift_lastPosSite (h ▸ mem_posTimeCoords.1 hi)
    rw [Pi.zero_apply, hy, Pi.single_eq_of_ne hne]
  have h0 := hdep 0 y hxy
  have hy1 : y (siteShift lastPosSite) = 1 := by
    rw [hy, Pi.single_eq_same]
  simp only [obsShift, Pi.zero_apply] at h0
  rw [zpow_one] at h0
  rw [hy1] at h0
  exact zero_ne_one h0

/-- **No `TimeTranslation` whose time-one map is the lattice step preserves positive time.**
This is why `PreservesPositiveTime` cannot be discharged for the concrete lattice translation: the
hypothesis is false, not merely unproved. -/
theorem not_preservesPositiveTime_of_shift {T : TimeTranslation}
    (hone : T 1 = obsShiftₗ 1) : ¬ PreservesPositiveTime T := by
  intro hT
  have hmem : T 1 ((fun x : Config => x lastPosSite) : Observable) ∈ PositiveTimeAlgebra :=
    hT 1 ⟨_, coordFun_mem_positiveTime⟩
  rw [hone] at hmem
  simpa only [obsShiftₗ_apply] using obsShift_one_not_mem_positiveTime hmem

end

end BookProof.OSReconstruction
