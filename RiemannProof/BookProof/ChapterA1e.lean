import Mathlib
import BookProof.ChapterA
import BookProof.ChapterA1
import BookProof.Complexification
import BookProof.ChapterA1b
import BookProof.ChapterA1c
import BookProof.ChapterA1d

/-!
# Chapter A, §A.1 — the `V ⊕ V̄` splitting of a realified irreducible system (work-package N1)

This file continues work-package **N1** of `FORMALIZATION_ROADMAP.md` (§A.1,
Props 11/12).  Building on the realification correspondence of
`BookProof/ChapterA1d.lean` (the canonical R-imaginary operator `Jmap : u ↦ i·u`
and the criterion `complex_irreducible_iff_no_Jinvariant_subsystem`), we
establish the *structural dichotomy* underlying the R-pseudoreal / R-complex
cases of Prop 11/12:

> **`realification_splits`.**  If a complex system `(M, V)` is irreducible and
> `Y` is a real subsystem of its realification `(M, V^r)`, then either `Y` is
> trivial (`⊥` or `⊤`), or `V` splits as the (closure of the) internal direct
> sum `Y ⊕ J Y` — i.e. `Y ⊓ J Y = ⊥` and `(Y ⊔ J Y)‾ = ⊤`.

Here `J Y := Jmap '' Y` is the image of `Y` under the R-imaginary operator.
Both `Y ⊓ J Y` and the topological closure `(Y ⊔ J Y)‾` are `J`-invariant
subsystems, hence trivial by complex irreducibility (via
`complex_irreducible_iff_no_Jinvariant_subsystem`); the three cases of the
dichotomy are the resulting possibilities.  This is exactly the `V ⊕ V̄`
conjugate-space decomposition of a reducible realification that the roadmap
flags as the remaining ingredient of the R-pseudoreal / R-complex classification.

Everything here is intended to be `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace BookProof.ChapterA

attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- **The image `J Y := Jmap '' Y`** of a real subspace under the R-imaginary
operator `Jmap : u ↦ i·u`. -/
noncomputable def JY (Y : Submodule ℝ V) : Submodule ℝ V :=
  Y.map (Jmap.toLinearIsometry.toLinearMap)

lemma mem_JY {Y : Submodule ℝ V} {x : V} : x ∈ JY Y ↔ ∃ y ∈ Y, Jmap y = x := by
  simp [JY, Submodule.mem_map]

/-- If `y ∈ Y` then `Jmap y ∈ J Y`. -/
lemma Jmap_mem_JY {Y : Submodule ℝ V} {y : V} (hy : y ∈ Y) : Jmap y ∈ JY Y :=
  mem_JY.2 ⟨y, hy, rfl⟩

/-- If `x ∈ J Y` then `Jmap x ∈ Y` (because `J² = -1` and `Y` is a submodule). -/
lemma Jmap_mem_of_mem_JY {Y : Submodule ℝ V} {x : V} (hx : x ∈ JY Y) : Jmap x ∈ Y := by
  obtain ⟨y, hy, rfl⟩ := mem_JY.1 hx
  rw [Jmap_sq]
  exact Y.neg_mem hy

/-
`J (J Y) = Y`: applying `Jmap` twice returns the original subspace.
-/
lemma JY_JY (Y : Submodule ℝ V) : JY (JY Y) = Y := by
  refine' le_antisymm _ _ <;> intro x hx <;> simp_all +decide [ mem_JY ];
  · obtain ⟨ a, ha, rfl ⟩ := hx;
    simp +decide [ ← smul_assoc, ha ];
  · refine' ⟨ -x, Y.neg_mem hx, _ ⟩ ; simp +decide [ ← smul_assoc ]

/-
`J Y` is closed when `Y` is (image of a closed set under an isometric
equivalence).
-/
lemma JY_isClosed {Y : Submodule ℝ V} (hY : IsClosed (Y : Set V)) :
    IsClosed ((JY Y : Submodule ℝ V) : Set V) := by
  -- Since `Jmap` is a linear isometry equivalence, it is a homeomorphism.
  have h_homeo : IsHomeomorph (Jmap : V → V) := by
    convert Homeomorph.isHomeomorph ( Jmap.toHomeomorph ) using 1;
  convert h_homeo.isClosedMap Y hY using 1

/-
**`J Y` is a subsystem** of the realification whenever `Y` is: `Jmap`
commutes with every realified (`ℂ`-linear) operator.
-/
lemma JY_isSubsystem (M : System ℂ V) {Y : Submodule ℝ V}
    (hY : (rxSystem M).IsSubsystem Y) : (rxSystem M).IsSubsystem (JY Y) := by
  refine' ⟨ JY_isClosed hY.1, _ ⟩;
  intro m hm w hw;
  obtain ⟨ y, hy, rfl ⟩ := hw;
  convert Jmap_mem_JY ( hY.2 _ hm _ hy ) using 1;
  obtain ⟨ m', hm', rfl ⟩ := hm;
  simp +decide [ rxMap, Jmap ]

/-! ## The `J`-invariant subsystems `Y ⊓ J Y` and `(Y ⊔ J Y)‾` -/

/-
`Y ⊓ J Y` is `J`-invariant.
-/
lemma inf_JY_Jinvariant (Y : Submodule ℝ V) :
    ∀ x ∈ Y ⊓ JY Y, Jmap x ∈ Y ⊓ JY Y := by
  simp +zetaDelta at *;
  exact fun x hx₁ hx₂ => ⟨ Jmap_mem_of_mem_JY hx₂, Jmap_mem_JY hx₁ ⟩

/-
`Y ⊓ J Y` is a subsystem of the realification whenever `Y` is.
-/
lemma inf_JY_isSubsystem (M : System ℂ V) {Y : Submodule ℝ V}
    (hY : (rxSystem M).IsSubsystem Y) : (rxSystem M).IsSubsystem (Y ⊓ JY Y) := by
  refine' ⟨ _, _ ⟩;
  · exact IsClosed.inter hY.1 ( JY_isClosed hY.1 );
  · exact fun m hm w hw => ⟨ hY.2 m hm w hw.1, JY_isSubsystem M hY |>.2 m hm w hw.2 ⟩

/-
`Y ⊔ J Y` is `J`-invariant (`J` permutes the two summands up to sign).
-/
lemma sup_JY_Jinvariant (Y : Submodule ℝ V) :
    ∀ x ∈ Y ⊔ JY Y, Jmap x ∈ Y ⊔ JY Y := by
  intro x hx; rw [ Submodule.mem_sup ] at hx; obtain ⟨ a, ha, b, hb, rfl ⟩ := hx; simp_all +decide [ Submodule.mem_sup ] ;
  refine' ⟨ Complex.I • b, _, Complex.I • a, _, _ ⟩ <;> simp_all +decide [ JY ];
  · obtain ⟨ y, hy, rfl ⟩ := hb; simp +decide [ ← smul_assoc, hy ] ;
  · exact add_comm _ _

/-
The topological closure `(Y ⊔ J Y)‾` is `J`-invariant.
-/
lemma sup_JY_closure_Jinvariant (Y : Submodule ℝ V) :
    ∀ x ∈ (Y ⊔ JY Y).topologicalClosure, Jmap x ∈ (Y ⊔ JY Y).topologicalClosure := by
  intro x hx;
  -- Since $Jmap$ is continuous and $Y ⊔ JY Y$ is $J$-invariant, we have $Jmap x ∈ (Y ⊔ JY Y).topologicalClosure$.
  have hJmap_cont : Continuous (Jmap : V → V) := by
    exact Jmap.toContinuousLinearEquiv.continuous;
  have hJmap_invariant : ∀ x ∈ Y ⊔ JY Y, Jmap x ∈ Y ⊔ JY Y := sup_JY_Jinvariant Y
  exact mem_closure_image hJmap_cont.continuousAt hx |> fun h => closure_mono ( Set.image_subset_iff.mpr hJmap_invariant ) h

/-
The topological closure `(Y ⊔ J Y)‾` is a subsystem of the realification
whenever `Y` is (a closed `M`-invariant subspace containing the `M`-invariant
algebraic sum `Y ⊔ J Y`).
-/
lemma sup_JY_closure_isSubsystem (M : System ℂ V) {Y : Submodule ℝ V}
    (hY : (rxSystem M).IsSubsystem Y) :
    (rxSystem M).IsSubsystem (Y ⊔ JY Y).topologicalClosure := by
  refine' ⟨ isClosed_closure, _ ⟩;
  intro m hm w hw
  have h_maps_to : ∀ w ∈ Y ⊔ JY Y, m w ∈ Y ⊔ JY Y := by
    intro w hw
    have h_maps_to : ∀ y ∈ Y, m y ∈ Y := by
      exact hY.2 m hm
    have h_maps_to_JY : ∀ y ∈ JY Y, m y ∈ JY Y := by
      have := JY_isSubsystem M hY;
      exact this.2 m hm;
    rw [ Submodule.mem_sup ] at hw ⊢;
    rcases hw with ⟨ y, hy, z, hz, rfl ⟩ ; exact ⟨ m y, h_maps_to y hy, m z, h_maps_to_JY z hz, by simp +decide [ map_add ] ⟩ ;
  exact mem_closure_of_tendsto ( m.continuous.continuousAt.tendsto.comp ( show Filter.Tendsto ( fun n : ℕ => Classical.choose ( mem_closure_iff_seq_limit.mp hw ) n ) Filter.atTop ( nhds w ) from Classical.choose_spec ( mem_closure_iff_seq_limit.mp hw ) |>.2 ) ) ( Filter.Eventually.of_forall fun n => h_maps_to _ ( Classical.choose_spec ( mem_closure_iff_seq_limit.mp hw ) |>.1 n ) )

/-! ## Headline: the `V ⊕ V̄` dichotomy -/

/-
**`realification_splits` (§A.1, the `V ⊕ V̄` decomposition).**  If a complex
system `(M, V)` is irreducible and `Y` is a real subsystem of its realification
`(M, V^r)`, then either `Y` is trivial, or `V` is the closure of the internal
direct sum `Y ⊕ J Y`: `Y ⊓ J Y = ⊥` and `(Y ⊔ J Y)‾ = ⊤`.

The two `J`-invariant subsystems `Y ⊓ J Y` and `(Y ⊔ J Y)‾` are each `⊥` or `⊤`
by `complex_irreducible_iff_no_Jinvariant_subsystem`; the possible combinations
give exactly the three cases (the `Y ⊓ J Y = ⊤` case forces `Y = ⊤`, the
`(Y ⊔ J Y)‾ = ⊥` case forces `Y = ⊥`, and the remaining case is the direct-sum
splitting).
-/
theorem realification_splits (M : System ℂ V) (h : M.IsIrreducible)
    (Y : Submodule ℝ V) (hY : (rxSystem M).IsSubsystem Y) :
    Y = ⊥ ∨ Y = ⊤ ∨ (Y ⊓ JY Y = ⊥ ∧ (Y ⊔ JY Y).topologicalClosure = ⊤) := by
  have hcrit := (complex_irreducible_iff_no_Jinvariant_subsystem M).1 h
  obtain hsup | hsup :=
    hcrit (Y ⊔ JY Y).topologicalClosure (sup_JY_closure_isSubsystem M hY)
      (sup_JY_closure_Jinvariant Y)
  · refine Or.inl (le_bot_iff.mp ?_)
    exact le_trans le_sup_left (le_trans (Submodule.le_topologicalClosure _) hsup.le)
  · obtain hinf | hinf :=
      hcrit (Y ⊓ JY Y) (inf_JY_isSubsystem M hY) (inf_JY_Jinvariant Y)
    · exact Or.inr (Or.inr ⟨hinf, hsup⟩)
    · exact Or.inr (Or.inl (top_le_iff.mp (le_trans hinf.ge inf_le_left)))

/-- **Corollary of `realification_splits`.**  A *proper non-trivial* real
subsystem `Y` of the realification of a complex-irreducible system always
realizes the direct-sum splitting `V = (Y ⊕ J Y)‾`: `Y ⊓ J Y = ⊥` and
`(Y ⊔ J Y)‾ = ⊤`.  In particular, a reducible realification is always the
(closure of the) internal sum `Y ⊕ J Y` of a proper subsystem and its
`J`-image — the `V ⊕ V̄` picture. -/
theorem proper_realification_subsystem_splits (M : System ℂ V) (h : M.IsIrreducible)
    {Y : Submodule ℝ V} (hY : (rxSystem M).IsSubsystem Y) (hbot : Y ≠ ⊥) (htop : Y ≠ ⊤) :
    Y ⊓ JY Y = ⊥ ∧ (Y ⊔ JY Y).topologicalClosure = ⊤ := by
  rcases realification_splits M h Y hY with h₁ | h₁ | h₁
  · exact absurd h₁ hbot
  · exact absurd h₁ htop
  · exact h₁

end BookProof.ChapterA
