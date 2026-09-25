import Mathlib

/-!
# Chapter "Free field parametrization in Classical Statistical Field Theory and
Navier-Stokes equations" — §"Local operators and the momentum constraint"

Source: `book.tex`, chapter *"Free field parametrization in Classical Statistical
Field Theory and Navier-Stokes equations"*, section *"Local operators and the
momentum constraint"* (line ~4011).

The book argues that, once the momentum constraint is imposed, **all operators
must be invariant under a translation in space**, so that *"in rigor we can't"*
define local operators.  What one *can* do is use translation-invariant
combinations of local operators, e.g. the space integral `∫ d\vec{x}\ l(\vec{x})`
of a local operator `l(\vec{x})`, which "behaves effectively as a local operator
when the wave-function is concentrated around one point".

This file formalizes the two self-contained mathematical claims underlying that
passage, for an operator-valued field on `d`-dimensional position space
`ℝ^d = Fin d → ℝ` with values in an arbitrary real Banach space `E` (the algebra
of operators):

* `localIntegral_translation_invariant` — the space integral `∫ l(x) dx` **is**
  translation invariant: shifting the local field `l` by any spatial vector `y`
  leaves the integral unchanged (`∫ l(x + y) dx = ∫ l(x) dx`).  This is the sense
  in which the translation-invariant operator `∫ d\vec{x}\ l(\vec{x})` is an
  admissible operator.
* `not_translationInvariant_of_pointSupported` — conversely, a genuinely *local*
  operator field (nonzero at a single point `x₀` and vanishing elsewhere) is
  **not** translation invariant (in dimension `d ≥ 1`); this is the precise sense
  in which local operators cannot be defined as admissible (translation-invariant)
  operators "in rigor".

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.LocalOperators

open MeasureTheory

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A *local operator field* on `d`-dimensional space is a map assigning to each
point `x ∈ ℝ^d` an operator `l x ∈ E`. -/
abbrev LocalField (d : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (Fin d → ℝ) → E

/-- The translation-invariant operator `∫ d\vec{x}\ l(\vec{x})` obtained by
integrating a local operator field over all of space. -/
noncomputable def localIntegral (l : LocalField d E) : E := ∫ x, l x

/-- `x` is *translation invariant* if shifting its argument by any spatial vector
leaves it unchanged.  Under the momentum constraint, only such operator fields are
admissible. -/
def TranslationInvariant (l : LocalField d E) : Prop :=
  ∀ y, (fun x => l (x + y)) = l

/-- **The space integral of a local operator is translation invariant.**  For any
local operator field `l` and any spatial shift `y`, integrating the shifted field
`x ↦ l(x + y)` gives the same operator as integrating `l` itself.  This is the
book's point that `∫ d\vec{x}\ l(\vec{x})` "is translation invariant". -/
theorem localIntegral_translation_invariant (l : LocalField d E) (y : Fin d → ℝ) :
    (∫ x, l (x + y)) = ∫ x, l x :=
  integral_add_right_eq_self l y

/-- Restated in terms of `localIntegral`: the space integral of the shifted field
equals the space integral of the original field. -/
theorem localIntegral_shift (l : LocalField d E) (y : Fin d → ℝ) :
    localIntegral (fun x => l (x + y)) = localIntegral l :=
  localIntegral_translation_invariant l y

/-- **A genuinely local operator is not translation invariant.**  If a local
operator field `l` is nonzero at a single point `x₀` and vanishes at every other
point, then (in dimension `d ≥ 1`) it fails to be translation invariant: this is
the precise sense in which, under the momentum constraint, local operators cannot
be defined as admissible (translation-invariant) operators "in rigor". -/
theorem not_translationInvariant_of_pointSupported
    (hd : 0 < d) (l : LocalField d E) (x₀ : Fin d → ℝ)
    (hne : l x₀ ≠ 0) (hsupp : ∀ z, z ≠ x₀ → l z = 0) :
    ¬ TranslationInvariant l := by
  intro h
  set i : Fin d := ⟨0, hd⟩
  set y : Fin d → ℝ := fun j => if j = i then 1 else 0 with hy
  have hy0 : y ≠ 0 := by
    intro hcon
    have := congrFun hcon i
    simp [hy] at this
  have hx : x₀ + y ≠ x₀ := by
    intro hcon
    apply hy0
    have : y = (x₀ + y) - x₀ := by ring
    rw [this, hcon]; ring
  have h2 : l (x₀ + y) = l x₀ := congrFun (h y) x₀
  rw [hsupp _ hx] at h2
  exact hne h2.symm

end BookProof.LocalOperators
