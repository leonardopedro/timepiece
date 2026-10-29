import Mathlib
import BookProof.ReflectionPositivity.Involution

/-!
# The positive-time observable algebra `𝔄₊`

Plan: `cftproof.md`, Phase 3.2 — "Define the positive-time algebra `𝔄₊ = {F : CylindricalObservables
| supp F ⊆ {x₀ > 0}}` … Show that `𝔄₊` is dense" (density in Phase 3.2 is a $C^*$-claim about
the full observable algebra, see the boundary note).

## Model

Observables are real functions on field configurations, `Observable = (Fin latticeDim → ℝ) → ℝ`,
with the pointwise algebra structure.  "Support in the positive-time half" is read as
*dependence* on the positive-time components: a cylindrical observable is constant along changes
of the components it does not see, so dependence is the correct (and, unlike support, pointwise)
notion.  It makes the set of functions depending only on `{x₀ > 0}` a **unital** subalgebra,
which is what OS positivity needs (`1` is allowed).

## Contents

* `posTimeFinset`, `posTimeCoords`, `negTimeCoords`, `dependsOn`;
* `PositiveTimeAlgebra` — the subalgebra of observables supported in `{x₀ > 0}`;
* `IsCylindrical`, `CylindricalObservables` — the finitely-supported observables, and
  `positiveTimeAlgebra_cylindrical`: `𝔄₊ ⊆ CylindricalObservables` (plan Phase 3.2);
* `thetaObs` — the action `θF(x) = F(θx)` of the reflection on observables;
* `thetaObs_mul`, `thetaObs_one` — `θ` is an algebra endomorphism (in the commutative
  observable algebra it is an algebra *homomorphism*, and `θ² = 1` gives an automorphism);
* `isPosTime_reflectCoord`, `thetaObs_dependsOn_negTime` — **`θ` maps `𝔄₊` into `𝔄₋`**,
  the structural fact OS positivity is stated with.

## Boundary

The plan's `𝔄₊` is the algebra of *bounded* cylindrical functions and Phase 3.2 asks for
density in the $C^*$-algebra of the lattice gauge theory.  No $C^*$/von Neumann algebra of
gauge fields exists in Mathlib, so density is not claimed: what is claimed is that
`𝔄₊` is a unital subalgebra of the observables, that it lies in the cylindrical observables,
and that `θ` maps it into the past algebra.  This is exactly the structure the later OS
statements use.
-/

namespace BookProof.ReflectionPositivity

open BookProof.BalabanRG

noncomputable section

/-- The positive-time components. -/
def posTimeFinset : Finset (Fin latticeDim) := Finset.univ.filter (fun i => isPosTime i)

/-- The positive-time components, as a set. -/
def posTimeCoords : Set (Fin latticeDim) := ↑posTimeFinset

/-- The negative-time components, as a set. -/
def negTimeCoords : Set (Fin latticeDim) := {i | ¬ isPosTime i}

theorem mem_posTimeCoords {i : Fin latticeDim} : i ∈ posTimeCoords ↔ isPosTime i := by
  simp [posTimeCoords, posTimeFinset]

theorem mem_negTimeCoords {i : Fin latticeDim} : i ∈ negTimeCoords ↔ ¬ isPosTime i := Iff.rfl

/-- Observables: real functions on the field configurations of one sector. -/
abbrev Observable : Type := Config → ℝ

/-- `f` depends only on the coordinates in `S`. -/
def dependsOn (f : Observable) (S : Set (Fin latticeDim)) : Prop :=
  ∀ x y : Config, (∀ i ∈ S, x i = y i) → f x = f y

/-- **The positive-time algebra** `𝔄₊`: observables depending only on `{x₀ > 0}`. -/
def PositiveTimeAlgebra : Subalgebra ℝ Observable where
  carrier := {f | dependsOn f posTimeCoords}
  mul_mem' := by
    intro f g hf hg x y hxy
    simp [hf x y hxy, hg x y hxy]
  one_mem' := by
    intro x y _
    rfl
  add_mem' := by
    intro f g hf hg x y hxy
    simp [hf x y hxy, hg x y hxy]
  zero_mem' := by
    intro x y _
    rfl
  algebraMap_mem' := by
    intro c x y _
    rfl

theorem mem_positiveTimeAlgebra_iff {f : Observable} :
    f ∈ PositiveTimeAlgebra ↔ dependsOn f posTimeCoords := Iff.rfl

/-- An observable is cylindrical when it depends on finitely many components. -/
def IsCylindrical (f : Observable) : Prop :=
  ∃ S : Finset (Fin latticeDim), dependsOn f ↑S

/-- **The cylindrical observables.** -/
def CylindricalObservables : Set Observable := {f | IsCylindrical f}

/-- **`𝔄₊ ⊆ CylindricalObservables`** (plan Phase 3.2): the positive-time algebra is
cylindrical, because there are only finitely many components. -/
theorem positiveTimeAlgebra_cylindrical {f : Observable} (hf : f ∈ PositiveTimeAlgebra) :
    f ∈ CylindricalObservables :=
  ⟨posTimeFinset, hf⟩

/-! ## The reflection acting on observables -/

/-- **`θ` acting on observables**: `(θF)(x) = F(θx)`. -/
def thetaObs (F : Observable) : Observable := fun x => F (fieldReflection x)

@[simp]
theorem thetaObs_apply (F : Observable) (x : Config) : thetaObs F x = F (fieldReflection x) := rfl

/-- `θ` is a ring homomorphism on observables (the algebra is commutative). -/
theorem thetaObs_mul (F G : Observable) : thetaObs (F * G) = thetaObs F * thetaObs G := by
  funext x
  simp [thetaObs, Pi.mul_apply]

theorem thetaObs_one : thetaObs (1 : Observable) = 1 := by
  funext x
  simp [thetaObs]

theorem thetaObs_add (F G : Observable) : thetaObs (F + G) = thetaObs F + thetaObs G := by
  funext x
  simp [thetaObs, Pi.add_apply]

/-- `θ` applied twice is the identity on observables. -/
theorem thetaObs_involutive (F : Observable) : thetaObs (thetaObs F) = F := by
  funext x
  simp [thetaObs, fieldReflection_involutive]

/-- The reflected component of a positive-time component is a negative-time component. -/
theorem isPosTime_reflectCoord (i : Fin latticeDim) :
    isPosTime (reflectCoord i) ↔ ¬ isPosTime i := by
  have h1 : coordOf (reflectCoord i) = ((coordOf i).1, flipCell (coordOf i).2) := by
    unfold reflectCoord
    exact coordOf_coordIdx _
  constructor
  · intro h
    rw [isPosTime, h1] at h
    have h' : halfCells ≤ (coordOf i).2.val := (flipCell_pos_iff (coordOf i).2).1 h
    exact not_lt.2 h'
  · intro h
    rw [isPosTime, h1]
    exact (flipCell_pos_iff (coordOf i).2).2 (not_lt.1 h)

/-- **`θ` maps the positive-time algebra into the past algebra** (plan Phase 3.2). -/
theorem thetaObs_dependsOn_negTime {F : Observable} (hF : F ∈ PositiveTimeAlgebra) :
    dependsOn (thetaObs F) negTimeCoords := by
  intro x y hxy
  apply hF
  intro i hi
  have hpos : isPosTime i := mem_posTimeCoords.1 hi
  have hneg : ¬ isPosTime (reflectCoord i) := fun h => (isPosTime_reflectCoord i).1 h hpos
  exact hxy (reflectCoord i) (mem_negTimeCoords.2 hneg)

end

end BookProof.ReflectionPositivity
