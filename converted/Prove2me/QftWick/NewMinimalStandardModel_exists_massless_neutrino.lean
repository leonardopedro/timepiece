/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : f6832cf0-8fc0-4276-a1b9-dabbfb911d64
* original name       : `NewMinimalStandardModel.exists_massless_neutrino`
* title               : New Minimal Standard Model: one neutrino is exactly massless
* statement author    : Lucas
* solution author     : Nickrobbins95 (submission a7cb8aed-3e83-4666-a06c-91b95be17a16,
                        accepted 2026-10-05T16:36:00.473241+00:00)
* source              : H. Davoudiasl, R. Kitano, T. Li, H. Murayama, The new Minimal Standard Model, Phys. Lett. B 609 (2005) 117-123, https://doi.org/10.1016/j.physletb.2005.01.026, p. 119 (Eq. (4) and the following discussion) and p. 122 ("one of the neutrino masses exactly vanishes")
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/qft-wick/NewMinimalStandardModel.exists_massless_neutrino.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/NewMinimalStandardModel_exists_massless_neutrino.diff`.
-/
import Mathlib
import Definitions.Def_NewMinimalStandardModel_Defs

set_option autoImplicit false

open Matrix in
theorem f6832cf0_ker (B : Matrix (Fin 2) (Fin 3) ℂ) : ∃ u : Fin 3 → ℂ, u ≠ 0 ∧ B *ᵥ u = 0 := by
  have h : LinearMap.ker (Matrix.mulVecLin B) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨u, hu, hne⟩ := (Submodule.ne_bot_iff _).mp h
  exact ⟨u, hne, by simpa using hu⟩

open Matrix in
theorem f6832cf0_det (v : ℝ) (hν : Matrix (Fin 2) (Fin 3) ℂ) (M : Fin 2 → ℝ) :
    (NewMinimalStandardModel.neutralLeptonMassMatrix v hν M).det = 0 := by
  obtain ⟨u, hu, hBu⟩ := f6832cf0_ker (NewMinimalStandardModel.diracMass v hν)
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨Sum.elim u 0, ?_, ?_⟩
  · intro h
    apply hu
    funext i
    have := congrFun h (Sum.inl i)
    simpa using this
  · unfold NewMinimalStandardModel.neutralLeptonMassMatrix
    rw [Matrix.fromBlocks_mulVec]
    simp [hBu]

open Matrix in
theorem f6832cf0_det2 {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (h : A.det = 0) :
    ∃ i, NewMinimalStandardModel.majoranaMasses A i = 0 := by
  have hH := Matrix.isHermitian_conjTranspose_mul_self A
  have hd : (Aᴴ * A).det = 0 := by rw [Matrix.det_mul, h, mul_zero]
  rw [hH.det_eq_prod_eigenvalues, Finset.prod_eq_zero_iff] at hd
  obtain ⟨i, -, hi⟩ := hd
  refine ⟨i, ?_⟩
  unfold NewMinimalStandardModel.majoranaMasses
  have : hH.eigenvalues i = 0 := by simpa using hi
  rw [this, Real.sqrt_zero]

open NewMinimalStandardModel in
theorem _root_.Prove2me.Solution.NewMinimalStandardModel_exists_massless_neutrino (v : ℝ) (hν : Matrix (Fin 2) (Fin 3) ℂ) (M : Fin 2 → ℝ)
    (hM : ∀ α, 0 < M α) :
    ∃ i, majoranaMasses (neutralLeptonMassMatrix v hν M) i = 0 := by
  exact f6832cf0_det2 _ (f6832cf0_det v hν M)

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

namespace NewMinimalStandardModel

theorem exists_massless_neutrino (v : ℝ) (hν : Matrix (Fin 2) (Fin 3) ℂ) (M : Fin 2 → ℝ)
    (hM : ∀ α, 0 < M α) :
    ∃ i, majoranaMasses (neutralLeptonMassMatrix v hν M) i = 0 := by
  first
  | exact _root_.Prove2me.Solution.NewMinimalStandardModel_exists_massless_neutrino v hν M hM
  | (apply _root_.Prove2me.Solution.NewMinimalStandardModel_exists_massless_neutrino <;> assumption)

end NewMinimalStandardModel


end Prove2meStatement
