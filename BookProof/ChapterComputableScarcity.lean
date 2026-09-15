import Mathlib

/-!
# Chapter "Aligned deep learning as a random sampling method", §4 — almost all
functions are not computable, not even approximately

Source: `book.tex`, chapter *"Aligned deep learning as a random sampling
method"*, §*"4. Why deep neural networks do not overfit"* (line ~9999):

> *"Under reasonable assumptions, almost all functions are not computable not
> even approximately.  Thus, Machine Learning works because the functions we are
> approximating are in fact probability distributions …"*

The self-contained mathematical content of that sentence is a counting /
diagonalization statement about the functions `ℕ → ℕ`:

* there are only **countably many** computable functions, because every
  computable function is described by one of the countably many programs;
* there are **uncountably many** functions, so "almost all" of them (all but a
  countable set) are not computable;
* and this is not repaired by allowing approximations: there is a single
  function that differs from **every** computable function at infinitely many
  arguments, hence no computable function eventually agrees with it.

## Deliverables

* `evalTotal` — the total function computed by a program (a `Nat.Partrec.Code`),
  undefined values being read as `0`;
* `exists_code_of_computable` — every computable `f : ℕ → ℕ` is `evalTotal c` for
  some program `c`;
* `countable_computable` — **countably many computable functions**;
* `exists_infinitely_often_ne` — **diagonalization**: for every sequence `e` of
  functions there is a function differing from each `e k` at infinitely many
  arguments;
* `uncountable_natFun` — there are uncountably many functions `ℕ → ℕ`;
* `exists_differs_infinitely_often_from_all_computable` — **the book's claim**:
  some function differs from *every* computable function at infinitely many
  arguments;
* `exists_not_eventually_eq_computable` — the "not even approximately" form: no
  computable function eventually agrees with that function;
* `exists_not_computable` — in particular non-computable functions exist.
-/

namespace BookProof.ComputableScarcity

open Nat.Partrec

open Classical in
/-- The total function computed by the program `c`: the value of `c` on `n` when
`c` halts on `n`, and `0` otherwise.  Reading the partial function this way loses
no generality here, because a program computing a *total* function halts
everywhere. -/
noncomputable def evalTotal (c : Code) (n : ℕ) : ℕ :=
  if h : (c.eval n).Dom then (c.eval n).get h else 0

/-- Every computable function is the total evaluation of some program. -/
theorem exists_code_of_computable {f : ℕ → ℕ} (hf : Computable f) :
    ∃ c : Code, evalTotal c = f := by
  have h1 : Nat.Partrec (fun n => Part.some (f n)) := Partrec.nat_iff.mp hf.partrec
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp h1
  refine ⟨c, ?_⟩
  funext n
  simp [evalTotal, hc]

/-- **There are only countably many computable functions `ℕ → ℕ`**, because each
of them is named by one of the countably many programs. -/
theorem countable_computable : {f : ℕ → ℕ | Computable f}.Countable := by
  have hsub : {f : ℕ → ℕ | Computable f} ⊆ Set.range evalTotal := by
    intro f hf
    obtain ⟨c, hc⟩ := exists_code_of_computable hf
    exact ⟨c, hc⟩
  exact Set.Countable.mono hsub (Set.countable_range _)

/-- **Diagonalization.**  For any sequence `e` of functions `ℕ → ℕ` there is a
function that differs from every `e k` at infinitely many arguments. -/
theorem exists_infinitely_often_ne (e : ℕ → (ℕ → ℕ)) :
    ∃ f : ℕ → ℕ, ∀ k, {n | f n ≠ e k n}.Infinite := by
  refine ⟨fun n => e n.unpair.1 n + 1, fun k => ?_⟩
  apply Set.Infinite.mono (s := Set.range (fun m => Nat.pair k m))
  · rintro n ⟨m, rfl⟩
    simp [Set.mem_setOf_eq, Nat.unpair_pair]
  · apply Set.infinite_range_of_injective
    intro a b hab
    simpa using hab

/-- **There are uncountably many functions `ℕ → ℕ`.** -/
theorem uncountable_natFun : ¬ Countable (ℕ → ℕ) := by
  intro hc
  obtain ⟨g, hg⟩ := hc.exists_injective_nat
  obtain ⟨f, hf⟩ := exists_infinitely_often_ne (Function.invFun g)
  have hfe : Function.invFun g (g f) = f := Function.leftInverse_invFun hg f
  have := hf (g f)
  rw [hfe] at this
  simp at this

/-- **The book's claim.**  There is a function `f : ℕ → ℕ` which differs from
*every* computable function at infinitely many arguments.  Since the computable
functions are only countably many, such an `f` is produced by diagonalizing
against an enumeration of them. -/
theorem exists_differs_infinitely_often_from_all_computable :
    ∃ f : ℕ → ℕ, ∀ g : ℕ → ℕ, Computable g → {n | f n ≠ g n}.Infinite := by
  obtain ⟨f, hf⟩ :=
    exists_infinitely_often_ne (fun k => evalTotal ((Encodable.decode k).getD Code.zero))
  refine ⟨f, fun g hg => ?_⟩
  obtain ⟨c, hc⟩ := exists_code_of_computable hg
  have := hf (Encodable.encode c)
  simpa [hc] using this

/-- **"Not even approximately".**  For the function of the previous theorem, no
computable function eventually agrees with it. -/
theorem exists_not_eventually_eq_computable :
    ∃ f : ℕ → ℕ, ∀ g : ℕ → ℕ, Computable g → ¬ (∀ᶠ n in Filter.atTop, f n = g n) := by
  obtain ⟨f, hf⟩ := exists_differs_infinitely_often_from_all_computable
  refine ⟨f, fun g hg hev => ?_⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine (hf g hg) (Set.Finite.subset (Set.finite_Iio N) ?_)
  intro n hn
  by_contra hlt
  exact hn (hN n (by simpa [Set.mem_Iio] using not_lt.mp hlt))

/-- In particular, non-computable functions exist. -/
theorem exists_not_computable : ∃ f : ℕ → ℕ, ¬ Computable f := by
  obtain ⟨f, hf⟩ := exists_differs_infinitely_often_from_all_computable
  refine ⟨f, fun hcomp => ?_⟩
  have := hf f hcomp
  simp at this

end BookProof.ComputableScarcity
