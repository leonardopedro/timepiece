/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 0b94566a-0f29-4401-a5ae-7bab57838b2b
* original name       : `ShorWiki.discreteLog_hiddenSubgroup`
* title               : Discrete logarithm as a hidden subgroup problem: $f(a,b) = g^a x^{-b}$ is a homomorphism with kernel the multiples of $(r,1)$
* statement author    : Lucas
* solution author     : fizzyinc3 (submission 65702d5d-26d2-4eeb-94a1-54e259c4d309,
                        accepted 2026-10-17T03:40:11.476716+00:00)
* source              : Wikipedia, "Shor's algorithm", revision oldid=1378862216, https://en.wikipedia.org/w/index.php?title=Shor%27s_algorithm&oldid=1378862216, section "Shor's algorithm for discrete logarithms" (PDF p. 7)
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/arctic-crypto/ShorWiki.discreteLog_hiddenSubgroup.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/ShorWiki_discreteLog_hiddenSubgroup.diff`.
-/
import Mathlib
import Definitions.Def_ShorWiki_Defs

open ShorWiki

namespace ShorDLog

lemma f_eq {G : Type*} [Group G] (g : G) (r : ℕ) (x y : ℕ) :
    g ^ x * ((g ^ r) ^ y)⁻¹ = g ^ ((x : ℤ) - r * y) := by
  rw [zpow_sub, zpow_natCast, ← pow_mul,
    show (r : ℤ) * y = ((r * y : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

end ShorDLog

open ShorDLog in
theorem _root_.Prove2me.Solution.ShorWiki_discreteLog_hiddenSubgroup {G : Type*} [Group G] [Fintype G] (g : G)
    (hg : ∀ h : G, h ∈ Subgroup.zpowers g) (r : ℕ) :
    (∀ a b a' b' : ZMod (Fintype.card G),
        g ^ (a + a').val * ((g ^ r) ^ (b + b').val)⁻¹
          = (g ^ a.val * ((g ^ r) ^ b.val)⁻¹) * (g ^ a'.val * ((g ^ r) ^ b'.val)⁻¹)) ∧
    ∀ a b : ZMod (Fintype.card G),
      g ^ a.val * ((g ^ r) ^ b.val)⁻¹ = 1 ↔
        ∃ t : ZMod (Fintype.card G), a = t * (r : ZMod (Fintype.card G)) ∧ b = t := by
  set n := Fintype.card G with hn
  have hord : orderOf g = n := by
    rw [hn, ← Nat.card_eq_fintype_card]; exact orderOf_eq_card_of_forall_mem_zpowers hg
  -- g ^ k = g ^ k' iff k ≡ k' in ZMod n
  have key : ∀ k k' : ℤ, ((k : ZMod n) = k') → g ^ k = g ^ k' := by
    intro k k' h
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
    have : g ^ (k' - k) = 1 := by rw [← orderOf_dvd_iff_zpow_eq_one, hord]; exact_mod_cast h
    rw [zpow_sub, mul_inv_eq_one] at this
    exact this.symm
  have hval : ∀ x : ZMod n, (((x.val : ℕ) : ℤ) : ZMod n) = x := by
    intro x; push_cast; exact ZMod.natCast_zmod_val x
  refine ⟨fun a b a' b' => ?_, fun a b => ?_⟩
  · simp only [f_eq]
    rw [← zpow_add]
    apply key
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  · rw [f_eq, ← orderOf_dvd_iff_zpow_eq_one, hord, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    constructor
    · intro h; exact ⟨by linear_combination h, rfl⟩
    · intro h; linear_combination h.1

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open Matrix Kronecker

namespace ShorWiki

theorem discreteLog_hiddenSubgroup {G : Type*} [Group G] [Fintype G] (g : G)
    (hg : ∀ h : G, h ∈ Subgroup.zpowers g) (r : ℕ) :
    (∀ a b a' b' : ZMod (Fintype.card G),
        g ^ (a + a').val * ((g ^ r) ^ (b + b').val)⁻¹
          = (g ^ a.val * ((g ^ r) ^ b.val)⁻¹) * (g ^ a'.val * ((g ^ r) ^ b'.val)⁻¹)) ∧
    ∀ a b : ZMod (Fintype.card G),
      g ^ a.val * ((g ^ r) ^ b.val)⁻¹ = 1 ↔
        ∃ t : ZMod (Fintype.card G), a = t * (r : ZMod (Fintype.card G)) ∧ b = t :=
  _root_.Prove2me.Solution.ShorWiki_discreteLog_hiddenSubgroup g hg r

end ShorWiki

end Prove2meStatement
