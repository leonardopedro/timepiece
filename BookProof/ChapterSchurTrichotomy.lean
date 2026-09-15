import Mathlib
import BookProof.ChapterA2
import BookProof.ChapterA2b
import BookProof.ChapterA2c
import BookProof.ChapterSchurIrreducible

/-!
# The ℝ / ℂ / ℍ trichotomy without the Schur hypothesis

Source: `book.tex`, chapter *"Real representations, CPT theorem and the relativistic
position operator"*, §A.2: **Lemma 14** (uniqueness of the antiisometry up to a phase) and
**Props 17–19** (the commutant of an R-real / R-complex / R-pseudoreal Schur system is
`ℝ` / `ℂ` / `ℍ`).

`ChapterA2`, `ChapterA2b` and `ChapterA2c` prove these statements from the named hypotheses
`IsSchurUnitary` / `IsSchurFull` — Schur's lemma for the system, which was `EXTERNAL` in
infinite dimension.  `BookProof.ChapterSchurIrreducible` now proves Schur's lemma for every
topologically irreducible **normal** system on a complex Hilbert space, so this file
restates the four results with the Schur hypothesis replaced by the book's own hypotheses
on the system: *normal* (Def 24, closed under the adjoint) and *irreducible* (Def 7).

Everything is `sorry`-free and `axiom`-free.
-/

open scoped ComplexConjugate InnerProductSpace

namespace BookProof.ChapterSchurTrichotomy

open BookProof.ChapterA BookProof.ChapterA.System BookProof.ChapterSchurIrreducible

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- **Lemma 14 without the Schur hypothesis.**  In an irreducible normal system on a
nonzero complex Hilbert space, any two commuting anti-unitaries differ by a unit phase. -/
theorem antiisometry_unique_up_to_phase' [Nontrivial V] (M : System ℂ V) (hM : M.IsNormal)
    (hirr : M.IsIrreducible) {θ₁ θ₂ : AntiUnitary V} (h₁ : CommutesAntiUnitary M θ₁)
    (h₂ : CommutesAntiUnitary M θ₂) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, θ₂ x = c • θ₁ x :=
  antiisometry_unique_up_to_phase M (isSchurUnitary_of_irreducible M hM hirr) h₁ h₂

/-- **Prop 17 without the Schur hypothesis.**  For an irreducible normal system with a
C-conjugation `θ`, the operators commuting with the system *and* with `θ` are exactly the
**real** scalars. -/
theorem Rreal_commutant_eq_real_scalars' (M : System ℂ V) (hM : M.IsNormal)
    (hirr : M.IsIrreducible) {θ : AntiUnitary V} (hθ : IsConjugation M θ) (S : V →L[ℂ] V) :
    (M.Commutes S ∧ CommutesConj θ S) ↔ ∃ r : ℝ, S = ((r : ℂ)) • (1 : V →L[ℂ] V) :=
  Rreal_commutant_eq_real_scalars M (isSchurFull_of_irreducible M hM hirr) hθ S

/-- **Prop 18 without the Schur hypothesis.**  For an irreducible normal system with no
nonzero commuting antilinear operator, the real commutant is exactly `ℂ`. -/
theorem Rcomplex_realCommutant_eq_complex' (M : System ℂ V) (hM : M.IsNormal)
    (hirr : M.IsIrreducible) (hNo : NoAntilinearCommutant M) (S : V →L[ℝ] V) :
    RealCommutes M S ↔ ∃ c : ℂ, S = cembed c :=
  Rcomplex_realCommutant_eq_complex M (isSchurFull_of_irreducible M hM hirr) hNo S

/-- **Prop 19 without the Schur hypothesis.**  For an irreducible normal system with a
commuting anti-unitary `θ` with `θ² = -1`, the real commutant is exactly the quaternions. -/
theorem Rpseudoreal_realCommutant_eq_quaternion' (M : System ℂ V) (hM : M.IsNormal)
    (hirr : M.IsIrreducible) {θ : AntiUnitary V} (hθ : ∀ x, θ (θ x) = -x)
    (hθc : CommutesAntiUnitary M θ) (S : V →L[ℝ] V) :
    RealCommutes M S ↔ ∃ q : Quaternion ℝ, S = qembed θ hθ q :=
  Rpseudoreal_realCommutant_eq_quaternion M (isSchurFull_of_irreducible M hM hirr) hθ hθc S

end BookProof.ChapterSchurTrichotomy
