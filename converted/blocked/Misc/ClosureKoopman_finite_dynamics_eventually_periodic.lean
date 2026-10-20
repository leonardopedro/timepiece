/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 1b73bd05-64d6-4c05-b193-e3a19f295f6f
* original name       : `ClosureKoopman.finite_dynamics_eventually_periodic`
* title               : Every function on a finite type is eventually periodic.
* statement author    : raver1975
* solution author     : raver1975 (submission 27400952-3deb-4ab9-ab10-06f6f6c07ef3,
                        accepted 2026-09-16T21:16:48.228669+00:00)
* source              : https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ClosureKoopmanReconstruction.lean#L273
* platform Mathlib rev: c5ea00351c28e24afc9f0f84379aa41082b1188f
* original file       : Downloads/misc/ClosureKoopman.finite_dynamics_eventually_periodic.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/ClosureKoopman_finite_dynamics_eventually_periodic.diff`.
-/
-- Sol generated from Bridges/ClosureKoopmanReconstruction.lean
import Mathlib
import Definitions.Def_Bridges_ClosureKoopmanReconstruction

/-
# Algebraic–EML Phase-Space Reconstruction via Closure Bialgebras and Koopman Spectra

This file formalizes a bridge between algebraic closure semantics, finite Koopman
spectral theory, character-based phase-space reconstruction, and certified
quantitative bounds with applications to quantum, cryptographic, and ML semantics.

## Central Reconstruction Principle
> Closure-fixed observable algebra + Koopman intertwining + observable separation
> ⇒ reconstructible recurrent phase portrait with explicit stabilization bounds.

Bridge: algebraic closure theory ↔ dynamical systems ↔ quantum semantics ↔
cryptographic stabilization ↔ certified ML robustness.
-/


open Finset Function

open ClosureKoopman

/-! ## Section 1: Closure Orbit Primitives -/












/-! ## Section 2: Closure Observable Structure -/





/-! ## Section 3: Koopman Map and Endomorphism -/










/-! ## Section 4: Evaluation Characters -/




/-! ## Section 5: Observable Separation and Phase-Space Reconstruction -/







/-! ## Section 6: Finite Dynamics and Recurrence -/


open Classical








/-! ## Section 7: Quantitative Bounds -/















open ClosureKoopman in
theorem _root_.Prove2me.Solution.ClosureKoopman_finite_dynamics_eventually_periodic    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : σ → σ) (s : σ) :
    ∃ m n : ℕ, m < n ∧ (f^[m]) s = (f^[n]) s := by
  by_contra h
  push_neg at h
  have hinj : Function.Injective
      (fun i : Fin (Fintype.card σ + 1) => (f^[i.val]) s) := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [Fin.mk.injEq]
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd hab (h a b hlt)
    · exact absurd hab.symm (h b a hgt)
  have hle := Fintype.card_le_of_injective _ hinj
  simp at hle

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open Finset Function
open ClosureKoopman

theorem ClosureKoopman.finite_dynamics_eventually_periodic    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : σ → σ) (s : σ) :
    ∃ m n : ℕ, m < n ∧ (f^[m]) s = (f^[n]) s :=
  _root_.Prove2me.Solution.ClosureKoopman_finite_dynamics_eventually_periodic f s



end Prove2meStatement
