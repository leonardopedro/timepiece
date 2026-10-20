/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 54a23a63-e422-4c64-8a16-69f44a420836
* original name       : `FamousTheorems.gelfand_transform_bijective`
* title               : Gelfand duality: the Gelfand transform is bijective
* statement author    : cm_beta
* solution author     : cm_beta (submission 6f335b21-b770-42c2-a03f-55f6c33d57d5,
                        accepted 2026-09-24T07:52:11.75618+00:00)
* source              : Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `gelfandTransform_bijective`. Proof here reduces to that Mathlib result.
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/cstar-gelfand/FamousTheorems.gelfand_transform_bijective.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/FamousTheorems_gelfand_transform_bijective.diff`.
-/
import Mathlib

theorem _root_.Prove2me.Solution.FamousTheorems_gelfand_transform_bijective (A : Type*) [CommCStarAlgebra A] :
    Function.Bijective (WeakDual.gelfandTransform ℂ A) :=
  gelfandTransform_bijective A

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

namespace FamousTheorems

theorem gelfand_transform_bijective (A : Type*) [CommCStarAlgebra A] :
    Function.Bijective (WeakDual.gelfandTransform ℂ A) :=
  _root_.Prove2me.Solution.FamousTheorems_gelfand_transform_bijective A

end FamousTheorems

end Prove2meStatement
