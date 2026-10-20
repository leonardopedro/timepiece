/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 8dd3adef-cfbd-47f1-a3fb-5b4cc8c20559
* original name       : `SchnorrGrp.hvzk_pmf`
* title               : Perfect HVZK, distributional form.
* statement author    : raver1975
* solution author     : raver1975 (submission fbf8172f-957e-45a9-9007-0daf3635158e,
                        accepted 2026-09-12T07:04:24.910541+00:00)
* source              : https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/ZeroKnowledge/SchnorrGroupProtocol.lean#L221
* platform Mathlib rev: c5ea00351c28e24afc9f0f84379aa41082b1188f
* original file       : Downloads/arctic-crypto/SchnorrGrp.hvzk_pmf.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/SchnorrGrp_hvzk_pmf.diff`.
-/
-- Sol generated from Cryptography/ZeroKnowledge/SchnorrGroupProtocol.lean
import Mathlib
import Definitions.Def_Cryptography_ZeroKnowledge_SchnorrGroupProtocol
import Prove2me.ArcticCrypto.SchnorrGrp_honest_eq_simulate  -- was `Theorems.Thm_SchnorrGrp_honest_eq_simulate`
import Prove2me.ArcticCrypto.SchnorrGrp_map_uniformOfFintype_equiv  -- was `Theorems.Thm_SchnorrGrp_map_uniformOfFintype_equiv`

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




/-- **Perfect HVZK, bijection form.** Honest and simulated transcripts are matched by the
explicit bijection `hvzkEquiv` of the randomness. -/
theorem hvzk_equiv [NeZero q] {g : G} (hg : g ^ q = 1) (x c r : ZMod q) :
    honest g x r c = simulate g (gexp g x) c (hvzkEquiv x c r) :=
  honest_eq_simulate hg x r c



/-! ### Quantitative soundness error -/




open SchnorrGrp in
theorem _root_.Prove2me.Solution.SchnorrGrp_hvzk_pmf[NeZero q] {g : G} (hg : g ^ q = 1) (x c : ZMod q) :
    (PMF.uniformOfFintype (ZMod q)).map (fun r => honest g x r c)
      = (PMF.uniformOfFintype (ZMod q)).map (fun z => simulate g (gexp g x) c z) := by
  have h : (fun r => honest g x r c)
      = (fun z => simulate g (gexp g x) c z) ∘ (hvzkEquiv x c) := by
    funext r; exact hvzk_equiv hg x c r
  rw [h, ← PMF.map_comp, map_uniformOfFintype_equiv]

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open SchnorrGrp
variable {G : Type*} [CommGroup G] {q : ℕ}

theorem SchnorrGrp.hvzk_pmf[NeZero q] {g : G} (hg : g ^ q = 1) (x c : ZMod q) :
    (PMF.uniformOfFintype (ZMod q)).map (fun r => honest g x r c)
      = (PMF.uniformOfFintype (ZMod q)).map (fun z => simulate g (gexp g x) c z) := by
  first
  | exact _root_.Prove2me.Solution.SchnorrGrp_hvzk_pmf hg x c
  | (apply _root_.Prove2me.Solution.SchnorrGrp_hvzk_pmf <;> assumption)


end Prove2meStatement
