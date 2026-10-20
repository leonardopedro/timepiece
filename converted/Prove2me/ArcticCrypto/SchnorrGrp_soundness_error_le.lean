/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : fe8bab6d-f8d7-4516-ac03-fd21b7a0468b
* original name       : `SchnorrGrp.soundness_error_le`
* title               : Soundness error `≤ 1/q`.
* statement author    : raver1975
* solution author     : raver1975 (submission 546e3b70-c605-442f-9cf6-5bcbdf398610,
                        accepted 2026-09-12T07:04:40.257252+00:00)
* source              : https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/ZeroKnowledge/SchnorrGroupProtocol.lean#L248
* platform Mathlib rev: c5ea00351c28e24afc9f0f84379aa41082b1188f
* original file       : Downloads/arctic-crypto/SchnorrGrp.soundness_error_le.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/SchnorrGrp_soundness_error_le.diff`.
-/
-- Sol generated from Cryptography/ZeroKnowledge/SchnorrGroupProtocol.lean
import Mathlib
import Definitions.Def_Cryptography_ZeroKnowledge_SchnorrGroupProtocol
import Prove2me.ArcticCrypto.SchnorrGrp_accepting_challenges_card_le_one  -- was `Theorems.Thm_SchnorrGrp_accepting_challenges_card_le_one`

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














/-! ### The protocol -/










/-! ### Honest-verifier zero knowledge -/







/-! ### Quantitative soundness error -/




open SchnorrGrp in
open scoped Classical in
theorem _root_.Prove2me.Solution.SchnorrGrp_soundness_error_le[Fact q.Prime] {g pub : G} (hpub : pub ^ q = 1) (hpub1 : pub ≠ 1)
    (a : G) (z : ZMod q) :
    ((Finset.univ.filter (fun c : ZMod q => Accepts g pub ⟨a, c, z⟩)).card : ℚ)
        / (Finset.univ : Finset (ZMod q)).card ≤ 1 / q := by
  have hcard : (Finset.univ : Finset (ZMod q)).card = q := by
    simp
  rw [hcard]
  have hq : (0 : ℚ) < q := by
    exact_mod_cast (Fact.out : q.Prime).pos
  have hle : ((Finset.univ.filter (fun c : ZMod q => Accepts g pub ⟨a, c, z⟩)).card : ℚ) ≤ 1 := by
    exact_mod_cast accepting_challenges_card_le_one hpub hpub1 a z
  exact div_le_div_of_nonneg_right hle hq.le

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open SchnorrGrp
variable {G : Type*} [CommGroup G] {q : ℕ}
open scoped Classical in

theorem SchnorrGrp.soundness_error_le[Fact q.Prime] {g pub : G} (hpub : pub ^ q = 1) (hpub1 : pub ≠ 1)
    (a : G) (z : ZMod q) :
    ((Finset.univ.filter (fun c : ZMod q => Accepts g pub ⟨a, c, z⟩)).card : ℚ)
        / (Finset.univ : Finset (ZMod q)).card ≤ 1 / q := by
  first
  | exact _root_.Prove2me.Solution.SchnorrGrp_soundness_error_le hpub hpub1 a z
  | (apply _root_.Prove2me.Solution.SchnorrGrp_soundness_error_le <;> assumption)


end Prove2meStatement
