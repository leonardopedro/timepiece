/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 8b516c74-3789-4f50-8624-54a63fc831fc
* original name       : `FamousTheorems.spectrum_nonempty_banach_algebra_7a`
* title               : The spectrum of an element of a complex Banach algebra is nonempty
* statement author    : cm_beta
* solution author     : cm_beta (submission 01a89a99-d654-47b2-8f1b-1ce626201071,
                        accepted 2026-09-24T12:36:35.681829+00:00)
* source              : Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `spectrum.nonempty`. Proof here reduces to that Mathlib result.
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/cstar-gelfand/FamousTheorems.spectrum_nonempty_banach_algebra_7a.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/FamousTheorems_spectrum_nonempty_banach_algebra_7a.diff`.
-/
import Mathlib

theorem _root_.Prove2me.Solution.FamousTheorems_spectrum_nonempty_banach_algebra_7a {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (a : A) :
    (spectrum ℂ a).Nonempty :=
  spectrum.nonempty a

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

namespace FamousTheorems

theorem spectrum_nonempty_banach_algebra_7a {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (a : A) :
    (spectrum ℂ a).Nonempty :=
  _root_.Prove2me.Solution.FamousTheorems_spectrum_nonempty_banach_algebra_7a a

end FamousTheorems

end Prove2meStatement
