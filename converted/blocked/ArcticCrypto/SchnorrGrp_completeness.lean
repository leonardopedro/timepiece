/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : b078fc52-f86e-4de1-8628-d6194b4a0657
* original name       : `SchnorrGrp.completeness`
* title               : Completeness.
* statement author    : raver1975
* solution author     : raver1975 (submission 512513a6-dd37-4e4e-ba3d-ecda7ca5569b,
                        accepted 2026-09-12T07:01:05.280988+00:00)
* source              : https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/ZeroKnowledge/SchnorrGroupProtocol.lean#L136
* platform Mathlib rev: c5ea00351c28e24afc9f0f84379aa41082b1188f
* original file       : Downloads/arctic-crypto/SchnorrGrp.completeness.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/SchnorrGrp_completeness.diff`.
-/
-- Sol generated from Cryptography/ZeroKnowledge/SchnorrGroupProtocol.lean
import Mathlib
import Definitions.Def_Cryptography_ZeroKnowledge_SchnorrGroupProtocol

/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The Schnorr identification Σ-protocol in a genuine cyclic group

The catalog already contains an *additive* model of Schnorr (`Cryptography.SchnorrIdentification`
and the files in `Cryptography/ZeroKnowledge/`), where the "group" is the field `ZMod p`,
"scalar multiplication" is field multiplication and the public key of `x` is `x * g`.  That
model is algebraically convenient but it hides the actual group-theoretic content of the
protocol: in the real scheme the prover works in a cyclic group `G` of prime order `q`, the
commitment is `g ^ r`, the public key is `g ^ x`, and verification reads `g ^ z = a * pub ^ c`
with the exponents living in `ZMod q` while the group operation lives in `G`.

This file develops that faithful multiplicative model:

* `gexp h e = h ^ e.val` is exponentiation of a group element by a `ZMod q` scalar; it is
  well defined as a homomorphism precisely on the `q`-torsion (`h ^ q = 1`), which is the
  standing hypothesis throughout.
* `SchnorrGrp.Accepts g pub T` is the verification equation `g ^ z = a * pub ^ c`.

## Main results

* `gexp_add`, `gexp_mul`, `gexp_sub`, `gexp_injective` — the exponentiation API.
* `completeness` — the honest prover `(g ^ r, c, r + c * x)` is always accepted.
* `special_soundness_witness` — two accepting transcripts sharing a commitment with distinct
  challenges yield a genuine discrete logarithm of an *arbitrary* public key `pub`
  (only `pub ^ q = 1` is needed), i.e. knowledge soundness with extractor
  `(z₁ - z₂) * (c₁ - c₂)⁻¹`.
* `special_soundness_eq_witness` — specialised to `pub = g ^ x`, the extractor returns `x`.
* `simulate_accepts`, `honest_eq_simulate`, `hvzk_equiv`, `hvzk_pmf` — perfect
  honest-verifier zero knowledge: the simulator's output is accepting, matches the honest
  transcript under an explicit bijection of the randomness, and induces *literally the same
  distribution* as the honest prover (equality of `PMF`s).
* `accepting_challenges_card_le_one`, `soundness_error_le` — the quantitative soundness
  error: a commitment/response pair fixed in advance is accepted for at most one challenge,
  so a cheating prover succeeds with probability at most `1 / q`.
-/

open SchnorrGrp

variable {G : Type*} [CommGroup G] {q : ℕ}

/-! ### Exponentiation by a `ZMod q` scalar -/


/-- On a `q`-torsion element, `h ^ ·` only depends on the exponent modulo `q`. -/
theorem pow_congr_of_modEq {h : G} (hh : h ^ q = 1) {m n : ℕ} (hmn : m ≡ n [MOD q]) :
    h ^ m = h ^ n :=
  pow_eq_pow_iff_modEq.mpr (hmn.of_dvd (orderOf_dvd_iff_pow_eq_one.mpr hh))



theorem gexp_add [NeZero q] {h : G} (hh : h ^ q = 1) (e₁ e₂ : ZMod q) :
    gexp h (e₁ + e₂) = gexp h e₁ * gexp h e₂ := by
  rw [gexp, gexp, gexp, ← pow_add]
  exact pow_congr_of_modEq hh (by rw [ZMod.val_add]; exact Nat.mod_modEq _ q)


theorem gexp_mul [NeZero q] {h : G} (hh : h ^ q = 1) (e₁ e₂ : ZMod q) :
    gexp h (e₁ * e₂) = gexp (gexp h e₁) e₂ := by
  rw [gexp, gexp, gexp, ← pow_mul]
  exact pow_congr_of_modEq hh (by rw [ZMod.val_mul]; exact Nat.mod_modEq _ q)







/-! ### The protocol -/










/-! ### Honest-verifier zero knowledge -/







/-! ### Quantitative soundness error -/




open SchnorrGrp in
theorem _root_.Prove2me.Solution.SchnorrGrp_completeness[NeZero q] {g : G} (hg : g ^ q = 1) (x r c : ZMod q) :
    Accepts g (gexp g x) (honest g x r c) := by
  show gexp g (r + c * x) = gexp g r * gexp (gexp g x) c
  rw [gexp_add hg, mul_comm c x, gexp_mul hg]

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open SchnorrGrp

theorem SchnorrGrp.completeness[NeZero q] {g : G} (hg : g ^ q = 1) (x r c : ZMod q) :
    Accepts g (gexp g x) (honest g x r c) :=
  _root_.Prove2me.Solution.SchnorrGrp_completeness



end Prove2meStatement
