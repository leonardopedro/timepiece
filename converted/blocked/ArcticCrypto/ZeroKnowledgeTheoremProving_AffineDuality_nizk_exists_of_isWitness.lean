/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 870e6067-51a0-467c-a616-8deb8b8747dd
* original name       : `ZeroKnowledgeTheoremProving.AffineDuality.nizk_exists_of_isWitness`
* title               : Unconditional Fiat–Shamir failure on true statements.
* statement author    : raver1975
* solution author     : raver1975 (submission c84bf6b6-9d2e-436a-b2dd-5166a8e867fd,
                        accepted 2026-09-11T07:19:35.458648+00:00)
* source              : https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/ZeroKnowledgeTheoremProving/FiatShamir.lean#L109
* platform Mathlib rev: c5ea00351c28e24afc9f0f84379aa41082b1188f
* original file       : Downloads/arctic-crypto/ZeroKnowledgeTheoremProving.AffineDuality.nizk_exists_of_isWitness.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/ZeroKnowledgeTheoremProving_AffineDuality_nizk_exists_of_isWitness.diff`.
-/
-- Sol generated from Applications/ZeroKnowledgeTheoremProving/FiatShamir.lean
import Mathlib
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_AffineDuality
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_EntropyAndBoundaries
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_FiatShamir
import Theorems.Thm_ZeroKnowledgeTheoremProving_AffineDuality_nizk_exists_iff

/-!
# The Fiat–Shamir Inversion: Non-Interactive Soundness Holds Exactly for False Statements

Cycle 2 of the research loop. Having proved (in `ProvabilityAmplification`) that
the *interactive* affine Σ-protocol has soundness error `(1/2)^n`, the obvious
next conjecture is that removing interaction — replacing the verifier's coin by
a public hash of the commitment, the Fiat–Shamir transform — preserves
soundness. It does not, and the failure is *unconditional*: it has nothing to do
with the quality of the hash.

Fix a public hash `Hash : H → Bool`. A non-interactive proof is a pair `(a, z)`
accepted when `Accepts s ⟨a, Hash a, z⟩` (`NIZKAccepts`). Call the hash
*forgery-free* for the statement when no such pair exists at all.

The main results are:

* `nizk_exists_iff` — accepted non-interactive proofs correspond exactly to
  solutions of the fixed-point equation `Hash (f z - c · target) = c`;
* `forgeryFree_iff` — forgery-freeness is the conjunction of two rigid colouring
  conditions: `Hash` must be constantly `true` on the image of the public
  homomorphism and constantly `false` on the image translated by `-target`;
* `nizk_exists_of_isWitness` — **if the statement is true, every hash whatsoever
  admits an accepted non-interactive proof**;
* `exists_forgeryFree_iff_no_witness` — **a forgery-free hash exists if and only
  if the statement is false**.

So in the information-theoretic model, a Fiat–Shamir proof of a *true* statement
is never evidence of knowledge: an accepted pair exists unconditionally, for
every hash function. Non-interactive conviction therefore cannot be
information-theoretic; it must rest on the computational hardness of *finding*
the pair. This is the exact boundary of the "prove a theorem without revealing
why" programme: interaction (or computational hardness) is not a convenience but
a necessity, and `zk_convinces_provable` genuinely needs *two* transcripts.

`constantHash_forgeable` records the extreme case: with a constant hash, an
accepted non-interactive proof exists for *every* statement, true or false.
-/

open ZeroKnowledgeTheoremProving.AffineDuality

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]













open ZeroKnowledgeTheoremProving.AffineDuality in
theorem _root_.Prove2me.Solution.ZeroKnowledgeTheoremProving_AffineDuality_nizk_exists_of_isWitness(s : Statement (G := G) (H := H)) {w : G}
    (hw : IsWitness s w) (Hash : H → Bool) :
    ∃ a z, NIZKAccepts s Hash a z := by
  have hw' : s.hom w = s.target := hw
  rw [nizk_exists_iff]
  cases hb : Hash (0 : H) with
  | false =>
      refine ⟨0, false, ?_⟩
      simpa [challengeTerm] using hb
  | true =>
      refine ⟨w, true, ?_⟩
      have : s.hom w - challengeTerm true s.target = 0 := by
        simp [challengeTerm, hw']
      rw [this, hb]

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open ZeroKnowledgeTheoremProving.AffineDuality

theorem ZeroKnowledgeTheoremProving.AffineDuality.nizk_exists_of_isWitness(s : Statement (G := G) (H := H)) {w : G}
    (hw : IsWitness s w) (Hash : H → Bool) :
    ∃ a z, NIZKAccepts s Hash a z :=
  _root_.Prove2me.Solution.ZeroKnowledgeTheoremProving_AffineDuality_nizk_exists_of_isWitness



end Prove2meStatement
