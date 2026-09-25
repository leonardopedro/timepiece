import Mathlib
import BookProof.ChapterComputableScarcity

/-!
# Chapter D — Aligned deep learning as a random sampling method

This file formalizes one crisp mathematical statement of Chapter D of
`book.tex` (see `FORMALIZATION_ROADMAP.md` §D.1): *almost all functions are
uncomputable*, in the precise form **computable ⇒ countable ⇒ null**.
-/

open MeasureTheory

namespace BookProof.ChapterD

open BookProof.ComputableScarcity

/-
**Chapter D.1 (countability).** The set of computable functions `ℕ → ℕ`
is countable.
-/
theorem computable_countable : {f : ℕ → ℕ | Computable f}.Countable :=
  countable_computable

/-
**Chapter D.1 (countability, Boolean form).** The set of computable
predicates `ℕ → Bool` is countable.
-/
theorem computable_bool_countable : {f : ℕ → Bool | Computable f}.Countable := by
  refine Set.Countable.mono ?_
    (computable_countable.image (fun g : ℕ → ℕ => fun n => g n == 1))
  rintro f hf
  refine ⟨fun n => bif f n then 1 else 0, ?_, ?_⟩
  · exact Computable.cond hf (Computable.const 1) (Computable.const 0)
  · funext n
    cases h : f n <;> simp [h]

/-
**Chapter D.1 (negligibility).** Under any atomless (`NoAtoms`) measure on the
space of functions `ℕ → ℕ`, the set of computable functions is null: almost every
function is uncomputable.
-/
theorem computable_null (μ : Measure (ℕ → ℕ)) [NullSingletonClass μ] :
    μ {f : ℕ → ℕ | Computable f} = 0 := by
  exact computable_countable.measure_zero μ

/-
**Chapter D.1 (negligibility, Boolean form).** Under any atomless measure on
`ℕ → Bool`, the set of computable predicates is null.
-/
theorem computable_bool_null (μ : Measure (ℕ → Bool)) [NullSingletonClass μ] :
    μ {f : ℕ → Bool | Computable f} = 0 :=
  computable_bool_countable.measure_zero μ

end BookProof.ChapterD
