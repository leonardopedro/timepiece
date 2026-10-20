/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 74df8fe8-8e73-419f-959e-a0dac68caf49
* original name       : `special_soundness`
* title               : Special soundness.
* statement author    : raver1975
* solution author     : raver1975 (submission 70d00077-a44c-42bc-ac49-8526c54fecc5,
                        accepted 2026-09-12T07:58:39.315526+00:00)
* source              : https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/SchnorrIdentification.lean#L96
* platform Mathlib rev: c5ea00351c28e24afc9f0f84379aa41082b1188f
* original file       : Downloads/arctic-crypto/special_soundness.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/special_soundness.diff`.
-/
-- Sol generated from Cryptography/SchnorrIdentification.lean
import Mathlib
import Definitions.Def_Cryptography_SchnorrIdentification

/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The Schnorr identification Σ-protocol

An additive model of the Schnorr identification scheme over a prime field.  The
"group" is `ZMod p` with a fixed nonzero generator `g`; "scalar times group
element" is field multiplication, and the public key of the secret `x` is
`pk x = x * g`.

A transcript is a triple `(t, c, s)` (commitment, challenge, response) and the
verifier accepts iff `s * g = t + c * Y`.

## Main results

* `completeness` — the honest prover is always accepted;
* `special_soundness` — two accepting transcripts with a common commitment and
  distinct challenges determine the secret;
* `sim_accepts` — the witness-free simulator produces accepting transcripts;
* `honestSimEquiv`, `hvzk_bijection` — honest and simulated transcripts are
  matched by an explicit bijection of the randomness, which is perfect
  honest-verifier zero knowledge in its combinatorial form.
-/


attribute [instance] SchnorrParams.hp

open SchnorrParams



variable (P : SchnorrParams)











theorem _root_.Prove2me.Solution.special_soundness(x t c₁ s₁ c₂ s₂ : ZMod P.p)
    (h₁ : accepts P (P.pk x) (t, c₁, s₁))
    (h₂ : accepts P (P.pk x) (t, c₂, s₂))
    (hc : c₁ ≠ c₂) :
    x = (c₁ - c₂)⁻¹ * (s₁ - s₂) := by
  haveI := P.hp
  simp only [accepts, SchnorrParams.pk] at h₁ h₂
  have hcne : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hc
  have hdiff : (s₁ - s₂) * P.g = (c₁ - c₂) * (x * P.g) := by
    rw [sub_mul, h₁, h₂]; ring
  have hx : (s₁ - s₂) = (c₁ - c₂) * x := by
    have := mul_right_cancel₀ P.hg (by rw [hdiff]; ring :
      (s₁ - s₂) * P.g = ((c₁ - c₂) * x) * P.g)
    exact this
  rw [hx, ← mul_assoc, inv_mul_cancel₀ hcne, one_mul]

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open SchnorrParams

theorem special_soundness(x t c₁ s₁ c₂ s₂ : ZMod P.p)
    (h₁ : accepts P (P.pk x) (t, c₁, s₁))
    (h₂ : accepts P (P.pk x) (t, c₂, s₂))
    (hc : c₁ ≠ c₂) :
    x = (c₁ - c₂)⁻¹ * (s₁ - s₂) :=
  _root_.Prove2me.Solution.special_soundness



end Prove2meStatement
