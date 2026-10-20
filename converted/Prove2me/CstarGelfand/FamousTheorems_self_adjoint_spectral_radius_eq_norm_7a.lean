/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 2b4228ef-e81c-445a-8a11-d2e54997bb44
* original name       : `FamousTheorems.self_adjoint_spectral_radius_eq_norm_7a`
* title               : Spectral radius of a self-adjoint element of a C*-algebra equals its norm
* statement author    : cm_beta
* solution author     : cm_beta (submission 9a4655d7-7bed-4186-a8bd-e76a592c2c85,
                        accepted 2026-09-24T12:38:01.370191+00:00)
* source              : Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsSelfAdjoint.spectralRadius_eq_nnnorm`. Proof here reduces to that Mathlib result.
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/cstar-gelfand/FamousTheorems.self_adjoint_spectral_radius_eq_norm_7a.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/FamousTheorems_self_adjoint_spectral_radius_eq_norm_7a.diff`.
-/
import Mathlib

theorem _root_.Prove2me.Solution.FamousTheorems_self_adjoint_spectral_radius_eq_norm_7a {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) : spectralRadius ℂ a = (‖a‖₊ : ENNReal) :=
  ha.spectralRadius_eq_nnnorm

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

namespace FamousTheorems

theorem self_adjoint_spectral_radius_eq_norm_7a {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) : spectralRadius ℂ a = (‖a‖₊ : ENNReal) :=
  _root_.Prove2me.Solution.FamousTheorems_self_adjoint_spectral_radius_eq_norm_7a ha

end FamousTheorems

end Prove2meStatement
