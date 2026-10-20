import Mathlib
import BookProof.Realification.ChapterA
import BookProof.Realification.ChapterA1
import BookProof.Realification.Complexification
import BookProof.Realification.ChapterA1b
import BookProof.Realification.ChapterA1c
import BookProof.Realification.ChapterA1d
import BookProof.Realification.ChapterA1e

/-!
# Chapter A, §A.1 — realification of a C-real system reduces (work-package N1)

This file continues work-package **N1** of `FORMALIZATION_ROADMAP.md` (§A.1,
Props 11/12).  Building on the realification correspondence of
`BookProof/Realification/ChapterA1d.lean` (the canonical R-imaginary operator `Jmap : u ↦ i·u`,
the criterion `complex_irreducible_iff_no_Jinvariant_subsystem`) and the
`V ⊕ V̄` dichotomy of `BookProof/Realification/ChapterA1e.lean` (`realification_splits`), we
formalize the concrete direction of Prop 12 that requires no external input:

> **`realification_reducible_of_conjugation`.**  If a complex system `(M, V)`
> admits a **C-conjugation** `θ` (an anti-unitary involution commuting with `M`,
> i.e. `M` is *C-real*), then its realification `(M, V^r)` is **reducible**: the
> real fixed space `conjFixed θ = {v : θ v = v}` is a proper non-trivial real
> subsystem (the real form `V = W ⊕ i·W` picture of Def 10 / Prop 11).

This is exactly the R-real half of the Def 10 dichotomy from the realification
side: a complex irreducible system is C-real precisely when its realification
splits along a real form.  The converse direction (a reducible realification of a
complex-irreducible system produces a C-conjugation — the R-pseudoreal/R-complex
sorting) is recorded as the remaining N1 obstruction in `BookProof/STATUS.md`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace BookProof.ChapterA

attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- **The real fixed space `conjFixed θ = {v : θ v = v}`** of an anti-unitary
operator `θ`, as a real subspace of the realification `V^r`.  When `θ` is a
C-conjugation this is the real form `W` with `V = W ⊕ i·W`. -/
noncomputable def conjFixed (θ : AntiUnitary V) : Submodule ℝ V where
  carrier := {v | θ v = v}
  add_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq] at *; rw [map_add, ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro r v hv; simp only [Set.mem_setOf_eq] at *
    have : (r : ℝ) • v = ((r : ℝ) : ℂ) • v := by simp [Complex.coe_smul]
    rw [this, θ.map_smulₛₗ, hv]; simp

omit [CompleteSpace V] in
@[simp] lemma mem_conjFixed {θ : AntiUnitary V} {v : V} : v ∈ conjFixed θ ↔ θ v = v := Iff.rfl

omit [CompleteSpace V] in
/-- `conjFixed θ` is closed (an equalizer of continuous maps). -/
lemma conjFixed_isClosed (θ : AntiUnitary V) :
    IsClosed ((conjFixed θ : Submodule ℝ V) : Set V) := by
  have h : ((conjFixed θ : Submodule ℝ V) : Set V) = {v | θ v = v} := rfl
  rw [h]; exact isClosed_eq θ.continuous continuous_id

/-- The fixed space of a C-conjugation is invariant under every realified
operator of `M` (because `θ` commutes with `M`). -/
lemma conjFixed_invariant (M : System ℂ V) (θ : AntiUnitary V) (hθ : IsConjugation M θ) :
    ∀ m ∈ (rxSystem M).ops, ∀ w ∈ conjFixed θ, m w ∈ conjFixed θ := by
  rintro _ ⟨m, hm, rfl⟩ w hw
  rw [mem_conjFixed] at *
  change θ (m w) = m w
  rw [hθ.2 m hm w, hw]

/-- The fixed space of a C-conjugation is a subsystem of the realification. -/
lemma conjFixed_isSubsystem (M : System ℂ V) (θ : AntiUnitary V) (hθ : IsConjugation M θ) :
    (rxSystem M).IsSubsystem (conjFixed θ) :=
  ⟨conjFixed_isClosed θ, conjFixed_invariant M θ hθ⟩

omit [CompleteSpace V] in
/-- On a non-trivial space the fixed space of a C-conjugation is non-trivial
(`≠ ⊥`): otherwise `θ = -1`, which is impossible for an anti-linear involution. -/
lemma conjFixed_ne_bot [Nontrivial V] (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = x) :
    conjFixed θ ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  by_contra h
  push_neg at h
  have hneg : ∀ x : V, θ x = -x := by
    intro x
    have hfix : ((2⁻¹ : ℂ) • (x + θ x)) ∈ conjFixed θ := by
      rw [mem_conjFixed]; exact conjugation_avg_fixed θ hθ x
    have hzero := h _ hfix
    have hx : x + θ x = 0 := by
      have h2 : ((2 : ℂ)) • ((2⁻¹ : ℂ) • (x + θ x)) = 0 := by rw [hzero]; simp
      rw [smul_smul] at h2; norm_num at h2; exact h2
    linear_combination (norm := module) hx
  obtain ⟨x, hx0⟩ := exists_ne (0 : V)
  have e1 : θ ((Complex.I) • x) = (Complex.I) • x := by rw [θ.map_smulₛₗ]; simp [hneg]
  have e2 : θ ((Complex.I) • x) = -((Complex.I) • x) := hneg _
  rw [e1] at e2
  have hz : Complex.I • x = 0 := by
    rw [eq_neg_iff_add_eq_zero] at e2
    have h2 : (2 : ℂ) • (Complex.I • x) = 0 := by rw [two_smul]; exact e2
    rcases smul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact h
  rcases smul_eq_zero.mp hz with h | h
  · simp [Complex.I_ne_zero] at h
  · exact hx0 h

omit [CompleteSpace V] in
/-- On a non-trivial space the fixed space of a C-conjugation is proper
(`≠ ⊤`): otherwise `θ = 1`, impossible for an anti-linear map. -/
lemma conjFixed_ne_top [Nontrivial V] (θ : AntiUnitary V) : conjFixed θ ≠ ⊤ := by
  intro h
  obtain ⟨x, hx0⟩ := exists_ne (0 : V)
  have hxI : (Complex.I • x) ∈ conjFixed θ := by rw [h]; trivial
  have hx : x ∈ conjFixed θ := by rw [h]; trivial
  rw [mem_conjFixed] at hxI hx
  rw [θ.map_smulₛₗ, hx] at hxI
  -- hxI : conj I • x = I • x, i.e. -I • x = I • x
  have hI : (starRingEnd ℂ) Complex.I = -Complex.I := by simp
  rw [hI] at hxI
  have hz : Complex.I • x = 0 := by
    have e2 : Complex.I • x = -(Complex.I • x) := by
      rw [neg_smul] at hxI; linear_combination (norm := module) hxI.symm
    rw [eq_neg_iff_add_eq_zero] at e2
    have h2 : (2 : ℂ) • (Complex.I • x) = 0 := by rw [two_smul]; exact e2
    rcases smul_eq_zero.mp h2 with hh | hh
    · norm_num at hh
    · exact hh
  rcases smul_eq_zero.mp hz with hh | hh
  · simp [Complex.I_ne_zero] at hh
  · exact hx0 hh

/-! ## Headline: a C-real realification is reducible -/

/-- **`realification_reducible_of_conjugation` (§A.1, R-real realification side).**
If a complex system `(M, V)` on a non-trivial space admits a C-conjugation `θ`
(so `M` is C-real), its realification `(M, V^r)` is **reducible**: the real fixed
space `conjFixed θ` is a proper non-trivial subsystem. -/
theorem realification_reducible_of_conjugation [Nontrivial V] (M : System ℂ V)
    (θ : AntiUnitary V) (hθ : IsConjugation M θ) : ¬ (rxSystem M).IsIrreducible := by
  intro hirr
  rcases hirr (conjFixed θ) (conjFixed_isSubsystem M θ hθ) with h | h
  · exact conjFixed_ne_bot θ hθ.1 h
  · exact conjFixed_ne_top θ h

/-- **Corollary (Def 10, R-real side).**  The realification of a C-real complex
system on a non-trivial space is reducible. -/
theorem isCReal_realification_reducible [Nontrivial V] (M : System ℂ V)
    (h : IsCReal M) : ¬ (rxSystem M).IsIrreducible := by
  obtain ⟨θ, hθ⟩ := h
  exact realification_reducible_of_conjugation M θ hθ

/-- **Contrapositive.**  If the realification of a complex system on a
non-trivial space is irreducible, the system is **not** C-real (it is
C-pseudoreal or C-complex).  This is the "only if" half of the Def 10
realification dichotomy; the full "iff" (the converse `not C-real ⇒ realification
irreducible`) is the remaining N1 residue recorded in `BookProof/STATUS.md`. -/
theorem not_isCReal_of_realification_irreducible [Nontrivial V] (M : System ℂ V)
    (h : (rxSystem M).IsIrreducible) : ¬ IsCReal M :=
  fun hc => isCReal_realification_reducible M hc h

end BookProof.ChapterA
