import Mathlib
import BookProof.YangMillsFormClosure
import BookProof.YangMillsFormClosureNonDiagonal
import BookProof.YangMillsEffectiveBarrier

/-!
# Chapter AbsoluteFormBound — U4's absolute one-particle floor in the diagonal model

U4 needs a *strictly positive absolute* lower bound on the entire one-particle space,
so that `dΓ(h) ≥ m N_out ≥ m(I − P_Ω)` rather than only a gap above an identified ground.
This module proves that floor for the **diagonal one-particle model of the form of record**:
the Yang–Mills symbol `N + N² + rootCount·zeroPoint` of
`BookProof.YangMillsFormClosureND`, whose closed form is `yangMillsForm` on the core and
whose operator is `diagUnb` of that symbol.

With at least one root direction (`T.card < d`) and `g > 0`, the vacuum value
`m = rootCount T · zeroPoint g 0 = rootCount T · g/(2√2)` is strictly positive, and every
other symbol value is at least `m + 2`.  Hence `m‖x‖² ≤ ⟪x, diagUnb … x⟫` on the operator
domain and the corresponding core/closed-form bounds hold.

**Boundary.** The object bounded here is the diagonal symbol's operator, not the full
gauge-fixed `h_g` with all magnetic cross terms, ordering constants and physical
restriction (U0).  The `dΓ` lift `ym_fock_mass_gap_of_one_particle_form_gap` takes the
one-particle form gap as a *hypothesis*, and no such hypothesis is discharged here for
`ymHamiltonian`.  Therefore no outer-vacuum mass gap of the physical nested-Fock theory,
no continuum claim and no regulator removal is asserted.  Axioms: `propext`,
`Classical.choice`, `Quot.sound` only.
-/

noncomputable section

namespace BookProof.AbsoluteFormBound

open BookProof.YangMillsFormClosure
open BookProof.YangMillsFormClosureND
open BookProof.YangMillsEffectiveBarrier
open BookProof.ReferenceGap

/-- The absolute vacuum barrier of the diagonal Yang–Mills symbol. -/
def absoluteFloor (T : Finset (Fin d)) (g : ℝ) : ℝ := rootCount T * zeroPoint g 0

/-- With a root direction and positive coupling the floor is strictly positive, and it is
    a lower bound for every symbol value (non-vacuum values are higher by at least `2`). -/
theorem absoluteFloor_pos_and_le {T : Finset (Fin d)} (hT : T.card < d) {g : ℝ} (hg : 0 < g) :
    0 < absoluteFloor T g ∧ ∀ n : Idx d, absoluteFloor T g ≤ yangMillsSymbol T g n := by
  have hrc : 0 < rootCount T := rootCount_pos hT
  have hzp : 0 < zeroPoint g 0 := by
    rw [zeroPoint, transFreq]
    positivity
  refine ⟨mul_pos hrc hzp, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    rw [absoluteFloor, yangMillsSymbol_vacuum]
  · have hge := yangMillsSymbol_ge (T := T) (le_of_lt hg) hn
    dsimp [absoluteFloor] at hge ⊢
    linarith

/-- The one-particle core form dominates the floor times the norm: U4's absolute input,
    for the diagonal model. -/
theorem yangMillsForm_absolute {T : Finset (Fin d)} (hT : T.card < d) {g : ℝ} (hg : 0 < g)
    (c : CoreCoeff d) :
    absoluteFloor T g * coreNormSq c ≤ yangMillsForm T g c := by
  have hle := (absoluteFloor_pos_and_le hT hg).2
  rw [Barrier.yangMillsForm_eq_diagonalForm]
  exact diagonalForm_ge_of_le_symbol hle c

/-- The closed form inherits the same absolute floor on `L²`. -/
theorem closedForm_absolute {T : Finset (Fin d)} (hT : T.card < d) {g : ℝ} (hg : 0 < g)
    (x : L2 d) :
    ENNReal.ofReal (absoluteFloor T g) * closedNormSq x ≤
      closedForm (yangMillsSymbol T g) x := by
  exact closedForm_ge_of_le_symbol (absoluteFloor_pos_and_le hT hg).2 x

/-- The floor is the vacuum edge of the diagonal operator: no point of its spectrum lies
    in `(0, absoluteFloor T g)`, so the absolute bound is sharp at the vacuum. -/
theorem spectrum_above_floor {T : Finset (Fin d)} (hT : T.card < d) {g : ℝ} (hg : 0 < g) :
    closure (Set.range (yangMillsSymbol T g)) ⊆ Set.Ici (absoluteFloor T g) := by
  have hle := (absoluteFloor_pos_and_le hT hg).2
  exact closure_minimal (by rintro s ⟨n, rfl⟩; exact hle n) isClosed_Ici

end BookProof.AbsoluteFormBound
