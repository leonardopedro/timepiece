/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 2e692a39-3915-46b4-9c29-78863a7b1396
* original name       : `ShamirSecretSharing.perfect_privacy_extension`
* title               : The unique low-degree extension of prescribed observations and a prescribed
* statement author    : raver1975
* solution author     : raver1975 (submission 730f0b84-55d5-49be-ad58-03cdaa1cea6f,
                        accepted 2026-09-12T07:04:32.407191+00:00)
* source              : https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/ShamirSecretSharing.lean#L28
* platform Mathlib rev: c5ea00351c28e24afc9f0f84379aa41082b1188f
* original file       : Downloads/arctic-crypto/ShamirSecretSharing.perfect_privacy_extension.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/ShamirSecretSharing_perfect_privacy_extension.diff`.
-/
-- Sol generated from Cryptography/ShamirSecretSharing.lean
import Mathlib
import Definitions.Def_Cryptography_ShamirSecretSharing

/-!
# Shamir secret sharing

This file formalizes the algebraic and information-theoretic core of Shamir's
scheme over an arbitrary field.  A sharing polynomial has its secret as its
value at zero.  Privacy is expressed without choosing a probability API: after
fixing any values at `t - 1` nonzero locations, every possible secret has
exactly one degree-`< t` polynomial extension.  Consequently a uniformly
random sharing polynomial induces exactly the same observation distribution
for every secret.
-/

open ShamirSecretSharing

open Polynomial

variable {F : Type*} [Field F]









open ShamirSecretSharing in
theorem _root_.Prove2me.Solution.ShamirSecretSharing_perfect_privacy_extension[DecidableEq F]
    (observed : Finset F) (hzero : 0 ∉ observed) (t : ℕ)
    (hcard : observed.card + 1 = t) (values : F → F) (secret : F) :
    ∃! p : F[X],
      p.degree < (t : WithBot ℕ) ∧ p.eval 0 = secret ∧
        ∀ x ∈ observed, p.eval x = values x := by
  -- Let s = observed ∪ {0} be the set of all interpolation points
  let s : Finset F := observed ∪ {0}
  have hs_card : s.card = t := by
    simp [s, hzero, hcard]
  -- Define the values function on s
  let f : F → F := fun x => if x = 0 then secret else values x
  -- Use Lagrange interpolation
  use Lagrange.interpolate s id f
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- degree < t
    have hinj : Set.InjOn (id : F → F) s := Set.injOn_id _
    have : (Lagrange.interpolate s id f).degree < s.card := Lagrange.degree_interpolate_lt f hinj
    simp [hs_card] at this
    exact this
  · -- eval 0 = secret
    have h0in : 0 ∈ s := by simp [s]
    simp only [Lagrange.interpolate_apply]
    rw [eval_finset_sum]
    rw [Finset.sum_eq_single_of_mem 0 h0in]
    · simp [f]
      have hinj : Set.InjOn (id : F → F) (s : Set F) := Set.injOn_id _
      have heval := Lagrange.eval_basis_self hinj h0in
      simp at heval
      rw [heval]
      ring
    · intro b hb hne
      have heval := @Lagrange.eval_basis_of_ne F _ _ _ s id b 0 hne h0in
      simp at heval
      simp [heval]
  · -- eval x = values x
    intro x hx
    have hx0 : x ≠ 0 := fun h => hzero (h ▸ hx)
    simp only [Lagrange.interpolate_apply, eval_finset_sum]
    rw [Finset.sum_eq_single_of_mem x (by simp [s, hx] : x ∈ s)]
    · simp [f, hx0]
      have hinj : Set.InjOn (id : F → F) (s : Set F) := Set.injOn_id _
      have heval := @Lagrange.eval_basis_self F _ _ _ s id x hinj (by simp [s, hx] : x ∈ s)
      simp at heval
      rw [heval]
      ring
    · intro b hb hne
      have heval := @Lagrange.eval_basis_of_ne F _ _ _ s id b x hne (by simp [s, hx] : x ∈ s)
      simp at heval
      simp [heval]
  · -- uniqueness
    intro y ⟨hy_deg, hy_zero, hy_obs⟩
    have hinj : Set.InjOn (id : F → F) (s : Set F) := Set.injOn_id _
    have hs_card' : s.card = t := hs_card
    -- y agrees with the interpolating polynomial at all points in s
    have hy_eval : ∀ x ∈ s, y.eval x = f x := by
      intro x hx
      simp [s] at hx
      rcases hx with (hx | hx)
      · rw [hx, hy_zero]; simp [f]
      · have hx0 : x ≠ 0 := fun h => hzero (h ▸ hx)
        simp [f, hx0, hy_obs x hx]
    -- The interpolating polynomial also agrees with f at all points in s
    -- By uniqueness of interpolation, y = Lagrange.interpolate s id f
    refine (Lagrange.eq_interpolate_iff f hinj).mp ?_
    refine ⟨?_, ?_⟩
    · simp [hs_card]; exact hy_deg
    · intro i hi
      exact hy_eval i hi

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open ShamirSecretSharing
open Polynomial
variable {F : Type*} [Field F]

theorem ShamirSecretSharing.perfect_privacy_extension[DecidableEq F]
    (observed : Finset F) (hzero : 0 ∉ observed) (t : ℕ)
    (hcard : observed.card + 1 = t) (values : F → F) (secret : F) :
    ∃! p : F[X],
      p.degree < (t : WithBot ℕ) ∧ p.eval 0 = secret ∧
        ∀ x ∈ observed, p.eval x = values x := by
  first
  | exact _root_.Prove2me.Solution.ShamirSecretSharing_perfect_privacy_extension observed hzero t hcard values secret
  | (apply _root_.Prove2me.Solution.ShamirSecretSharing_perfect_privacy_extension <;> assumption)


end Prove2meStatement
