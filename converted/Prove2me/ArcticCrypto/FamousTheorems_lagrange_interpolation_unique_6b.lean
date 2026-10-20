/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 17ef5fbe-f4b5-4fd8-abfa-9a76a3822084
* original name       : `FamousTheorems.lagrange_interpolation_unique_6b`
* title               : Uniqueness of the Lagrange interpolation polynomial
* statement author    : cm_beta
* solution author     : cm_beta (submission 23830fcb-35e1-4c47-b8d0-d151ff74542a,
                        accepted 2026-09-24T11:15:13.204697+00:00)
* source              : Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Lagrange.eq_interpolate_of_eval_eq`. Proof here reduces to that Mathlib result.
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/arctic-crypto/FamousTheorems.lagrange_interpolation_unique_6b.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/FamousTheorems_lagrange_interpolation_unique_6b.diff`.
-/
import Mathlib

theorem _root_.Prove2me.Solution.FamousTheorems_lagrange_interpolation_unique_6b {F ι : Type*} [Field F] [DecidableEq ι] {s : Finset ι} {v : ι → F} (r : ι → F) {f : Polynomial F}
    (hvs : Set.InjOn v s) (hf : f.degree < s.card) (heval : ∀ i ∈ s, f.eval (v i) = r i) :
    f = Lagrange.interpolate s v r :=
  Lagrange.eq_interpolate_of_eval_eq r hvs hf heval

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

namespace FamousTheorems

theorem lagrange_interpolation_unique_6b {F ι : Type*} [Field F] [DecidableEq ι] {s : Finset ι} {v : ι → F} (r : ι → F) {f : Polynomial F}
    (hvs : Set.InjOn v s) (hf : f.degree < s.card) (heval : ∀ i ∈ s, f.eval (v i) = r i) :
    f = Lagrange.interpolate s v r :=
  _root_.Prove2me.Solution.FamousTheorems_lagrange_interpolation_unique_6b r hvs hf heval

end FamousTheorems

end Prove2meStatement
