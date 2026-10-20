/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : bbb0e2a4-8f4f-45a7-a247-6ae5fb7c19dd
* original name       : `DiracEquation.slash_sq`
* title               : $p\!\!\!/\,p\!\!\!/ = (\eta^{\mu\nu}p_\mu p_\nu)\,I_4$
* statement author    : Lucas
* solution author     : cm_beta (submission a491c063-f40f-452f-8cfe-caf37e61b8ce,
                        accepted 2026-09-23T09:18:24.711609+00:00)
* source              : "Dirac equation", Wikipedia, https://en.wikipedia.org/wiki/Dirac_equation, sections "Formulation - Covariant formulation" (Dirac equation, Clifford relation {gamma^mu, gamma^nu} = 2 eta^{mu nu} I_4, Dirac representation of the gamma matrices, Hamiltonian form with alpha and beta) and "Properties - Plane wave solutions" (Klein-Gordon reduction, plane waves, momentum-space Dirac equation). Section "Plane wave solutions": the Klein-Gordon reduction (i d-slash + m)(i d-slash - m) psi = (d_mu d^mu + m^2) psi, of which this is the momentum-space form.
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/qft-wick/DiracEquation.slash_sq.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/DiracEquation_slash_sq.diff`.
-/
import Definitions.Def_DiracEquation_fields

open DiracEquation

namespace Ag1Aux_DiracSlash

theorem slash_sq_core (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hg : IsGammaFamily g)
    (p : Fin 4 → ℂ) :
    slash g p * slash g p = (∑ mu, eta mu mu * p mu * p mu) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have hg' : ∀ mu nu, g mu * g nu + g nu * g mu = (2 * eta mu nu) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := hg
  set S := ∑ mu, ∑ nu, (p mu * p nu) • (g mu * g nu) with hS
  have e1 : slash g p * slash g p = S := by
    simp only [hS, slash, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
    exact Finset.sum_comm
  have e2 : S = ∑ mu, ∑ nu, (p mu * p nu) • (g nu * g mu) := by
    rw [hS, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun mu _ => Finset.sum_congr rfl (fun nu _ => ?_))
    rw [mul_comm]
  have key : S + S = (2 : ℂ) • ((∑ mu, eta mu mu * p mu * p mu) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
    nth_rewrite 2 [e2]
    rw [hS, ← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, ← smul_add, hg']
    simp only [Fin.sum_univ_four, eta]
    simp only [smul_smul, Finset.smul_sum, Finset.sum_smul]
    simp
    module
  have h2 : (2 : ℂ) • S = (2 : ℂ) • ((∑ mu, eta mu mu * p mu * p mu) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
    rw [two_smul]; exact key
  rw [e1]
  exact smul_right_injective _ (two_ne_zero) h2

end Ag1Aux_DiracSlash

open Ag1Aux_DiracSlash

theorem _root_.Prove2me.Solution.DiracEquation_slash_sq (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hg : IsGammaFamily g) (p : Fin 4 → ℂ) :
    slash g p * slash g p = (∑ mu, eta mu mu * p mu * p mu) • (1 : Matrix (Fin 4) (Fin 4) ℂ) :=
  slash_sq_core g hg p

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

namespace DiracEquation

theorem slash_sq (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hg : IsGammaFamily g) (p : Fin 4 → ℂ) :
    slash g p * slash g p = (∑ mu, eta mu mu * p mu * p mu) • (1 : Matrix (Fin 4) (Fin 4) ℂ) :=
  _root_.Prove2me.Solution.DiracEquation_slash_sq g hg p

end DiracEquation

end Prove2meStatement
