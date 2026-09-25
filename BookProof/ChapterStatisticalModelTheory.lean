import Mathlib.ModelTheory.Satisfiability
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Algebra.Order.Archimedean.Real.Hom

/-!
# Statistical Model Theory — the Upward Löwenheim–Skolem boundary

`book.tex`, chapter *Statistical Model Theory and Bayesian priors where the Riemann
Hypothesis is true*, opens with the model-theoretic obstruction that motivates the
whole chapter:

> **The Theorem:** If a First-Order theory has an infinite model … **The Consequence:**
> No matter how many axioms you add (as long as they are First-Order), if the model
> allows for an infinite set of numbers, a "monster" uncountable model that satisfies
> those exact same axioms automatically exists.  You cannot filter out the uncountable
> models using First-Order axioms.

This chapter formalizes exactly that boundary, and nothing beyond it.  The
Bayesian-prior/Riemann-hypothesis material of the same chapter is deliberately out of
scope here.

* `upward_lowenheim_skolem` — the theorem itself: a first-order theory with an infinite
  model has a model of **every** cardinality `κ` that is at least `ℵ₀` and at least the
  cardinality of the language.
* `exists_uncountable_model` — the "monster": any such theory has an uncountable model.
* `monster_model_continuum` / `exists_uncountable_model_of_countable_language` — the
  same two statements for a countable language, with the monster produced at the
  cardinality of the continuum.
* `countability_not_first_order_axiomatizable` — the consequence as the book states it:
  *no* first-order theory with an infinite model has only countable models, so no set of
  first-order axioms filters the uncountable models out.
* `exists_nonisomorphic_models` — consequently a first-order theory with an infinite
  model never determines its model up to isomorphism: it has two models that are not
  even in bijection.
* `exists_countable_model`, `exists_model_not_bijective_of_uncountable` and
  `secondOrder_categoricity_real` — the book's contrast "there are non-standard models of
  the real numbers in first-order-logic (which is complete), while in second-order-logic
  the real numbers are the unique solution to a set of axioms": first-order axioms over a
  countable language always admit a countable model beside any uncountable one, while the
  second-order completeness axiom is categorical — every conditionally complete linear
  ordered field is order-ring-isomorphic to `ℝ`, by a unique isomorphism.

The upward theorem itself is Mathlib's `FirstOrder.Language.Theory.exists_model_card_eq`;
the statements below are the book's readings of it.
-/

universe u v w

open Cardinal FirstOrder FirstOrder.Language FirstOrder.Language.Theory

namespace BookProof.ChapterStatisticalModelTheory

variable {L : Language.{u, v}} {T : L.Theory}

/-- **Upward Löwenheim–Skolem theorem.**  If the first-order theory `T` has an infinite
model, then for every cardinal `κ` that is infinite and at least as large as the
cardinality of the language, `T` has a model of cardinality exactly `κ`. -/
theorem upward_lowenheim_skolem
    (h : ∃ M : ModelType.{u, v, max u v} T, Infinite M) (κ : Cardinal.{w})
    (h1 : ℵ₀ ≤ κ) (h2 : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ N : ModelType.{u, v, w} T, #N = κ :=
  Theory.exists_model_card_eq h κ h1 h2

/-- The **"monster" model**: a first-order theory with an infinite model has an
uncountable model, at any prescribed uncountable cardinality the language permits. -/
theorem exists_uncountable_model
    (h : ∃ M : ModelType.{u, v, max u v} T, Infinite M) (κ : Cardinal.{w})
    (h1 : ℵ₀ < κ) (h2 : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ N : ModelType.{u, v, w} T, ¬ Countable N := by
  obtain ⟨N, hN⟩ := upward_lowenheim_skolem h κ h1.le h2
  refine ⟨N, fun hc => ?_⟩
  rw [← Cardinal.mk_le_aleph0_iff, hN] at hc
  exact absurd hc (not_le.2 h1)

section CountableLanguage

variable {L : Language.{0, 0}} {T : L.Theory}

/-- For a countable first-order language, a theory with an infinite model has a model of
the cardinality of the continuum. -/
theorem monster_model_continuum (hL : L.card ≤ ℵ₀)
    (h : ∃ M : ModelType.{0, 0, 0} T, Infinite M) :
    ∃ N : ModelType.{0, 0, 0} T, #N = 𝔠 := by
  refine Theory.exists_model_card_eq h _ Cardinal.aleph0_le_continuum ?_
  simpa using hL.trans Cardinal.aleph0_le_continuum

/-- For a countable first-order language, a theory with an infinite model has an
uncountable model. -/
theorem exists_uncountable_model_of_countable_language (hL : L.card ≤ ℵ₀)
    (h : ∃ M : ModelType.{0, 0, 0} T, Infinite M) :
    ∃ N : ModelType.{0, 0, 0} T, ¬ Countable N := by
  obtain ⟨N, hN⟩ := monster_model_continuum hL h
  refine ⟨N, fun hc => ?_⟩
  rw [← Cardinal.mk_le_aleph0_iff, hN] at hc
  exact absurd hc (not_le.2 Cardinal.aleph0_lt_continuum)

/-- **"You cannot filter out the uncountable models using First-Order axioms."**  No
matter which further first-order axioms are added, as long as the resulting theory still
has an infinite model it is *false* that all its models are countable. -/
theorem countability_not_first_order_axiomatizable (hL : L.card ≤ ℵ₀)
    (h : ∃ M : ModelType.{0, 0, 0} T, Infinite M) :
    ¬ ∀ N : ModelType.{0, 0, 0} T, Countable N := by
  obtain ⟨N, hN⟩ := exists_uncountable_model_of_countable_language hL h
  exact fun hall => hN (hall N)

/-- A first-order theory with an infinite model never pins its model down up to
isomorphism: it has a countable model and a model of size continuum, and these are not
even in bijection. -/
theorem exists_nonisomorphic_models (hL : L.card ≤ ℵ₀)
    (h : ∃ M : ModelType.{0, 0, 0} T, Infinite M) :
    ∃ N₁ N₂ : ModelType.{0, 0, 0} T, ¬ Nonempty (N₁ ≃ N₂) := by
  obtain ⟨N₁, h₁⟩ := Theory.exists_model_card_eq h ℵ₀ le_rfl (by simpa using hL)
  obtain ⟨N₂, h₂⟩ := monster_model_continuum hL h
  refine ⟨N₁, N₂, fun ⟨e⟩ => ?_⟩
  have : (ℵ₀ : Cardinal.{0}) = 𝔠 := by rw [← h₁, ← h₂]; exact Cardinal.mk_congr e
  exact absurd this (ne_of_lt Cardinal.aleph0_lt_continuum)

/-- **Non-standard models.**  `book.tex` notes that "despite being decidable, Presburger
arithmetic has non-standard models".  This is the general statement: if a theory over a
countable language has a countable infinite model `M`, it also has a model that is not
even in bijection with `M` — a non-standard one. -/
theorem exists_nonstandard_model (hL : L.card ≤ ℵ₀) (M : ModelType.{0, 0, 0} T)
    [Infinite M] [Countable M] :
    ∃ N : ModelType.{0, 0, 0} T, ¬ Nonempty ((M : Type) ≃ (N : Type)) := by
  obtain ⟨N, hN⟩ := monster_model_continuum hL ⟨M, inferInstance⟩
  refine ⟨N, fun ⟨e⟩ => ?_⟩
  have hM : #(M : Type) ≤ ℵ₀ := Cardinal.mk_le_aleph0_iff.mpr inferInstance
  rw [Cardinal.mk_congr e, hN] at hM
  exact absurd hM (not_le.2 Cardinal.aleph0_lt_continuum)

/-- **Downward Löwenheim–Skolem.**  Over a countable language, a first-order theory with an
infinite model has a countable model. -/
theorem exists_countable_model (hL : L.card ≤ ℵ₀)
    (h : ∃ M : ModelType.{0, 0, 0} T, Infinite M) :
    ∃ N : ModelType.{0, 0, 0} T, #N = ℵ₀ :=
  Theory.exists_model_card_eq h ℵ₀ le_rfl (by simpa using hL)

/-- **First-order axioms cannot characterize an uncountable structure.**  If a first-order
theory over a countable language has an uncountable model `M`, it also has a model that is
not in bijection with `M`.  Applied to any first-order axiomatization of the real numbers,
this is the book's "there are non-standard models of the real numbers in
first-order-logic". -/
theorem exists_model_not_bijective_of_uncountable (hL : L.card ≤ ℵ₀)
    (M : ModelType.{0, 0, 0} T) (hM : ¬ Countable M) :
    ∃ N : ModelType.{0, 0, 0} T, ¬ Nonempty ((M : Type) ≃ (N : Type)) := by
  have hinf : Infinite M := by
    rw [← not_finite_iff_infinite]
    exact fun _ => hM Finite.to_countable
  obtain ⟨N, hN⟩ := exists_countable_model hL ⟨M, hinf⟩
  refine ⟨N, fun ⟨e⟩ => hM ?_⟩
  rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_congr e, hN]

end CountableLanguage

/-- **The second-order axioms are categorical.**  "In second-order-logic the real numbers
are the unique solution to a set of axioms": every conditionally complete linear ordered
field — the completeness axiom being the second-order one — is order-ring-isomorphic to
`ℝ`, and the isomorphism is unique. -/
theorem secondOrder_categoricity_real (β : Type*)
    [Field β] [ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β] :
    ∃ e : β ≃+*o ℝ, ∀ f : β ≃+*o ℝ, f = e := by
  have : Unique (β ≃+*o ℝ) :=
    ConditionallyCompleteLinearOrderedField.uniqueOrderRingIso β ℝ
  exact ⟨default, fun f => Unique.eq_default f⟩

end BookProof.ChapterStatisticalModelTheory
