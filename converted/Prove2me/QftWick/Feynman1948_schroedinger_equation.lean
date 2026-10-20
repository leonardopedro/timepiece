/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : b211e250-3bac-4805-b773-d00c7f6299c0
* original name       : `Feynman1948.schroedinger_equation`
* title               : Eq. (30): the path-integral wave function satisfies Schrödinger's equation
* statement author    : Lucas
* solution author     : Mazecto (submission b61bbf2f-629d-4540-bed5-3beb0e6231b1,
                        accepted 2026-10-02T22:25:15.422436+00:00)
* source              : R. P. Feynman, Space-Time Approach to Non-Relativistic Quantum Mechanics, Rev. Mod. Phys. 20, 367 (1948), https://doi.org/10.1103/RevModPhys.20.367, pp. 374-376, Section 6, Eqs. (18), (22), (23), (28)-(30)
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/qft-wick/Feynman1948.schroedinger_equation.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/Feynman1948_schroedinger_equation.diff`.
-/
import Definitions.Def_Feynman1948_WaveEquation
import Prove2me.QftWick.Feynman1948_free_step_first_order  -- was `Theorems.Thm_Feynman1948_free_step_first_order`
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

open Complex Filter Topology SchwartzMap MeasureTheory Feynman1948

theorem _root_.Prove2me.Solution.Feynman1948_schroedinger_equation (ħ m : ℝ) (hħ : 0 < ħ) (hm : 0 < m) (V : ℝ → ℝ)
    (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Tendsto (fun ε : ℝ => (stepEvolution ħ m V ε ψ x - ψ x) / ε) (𝓝[>] 0)
      (𝓝 (-(I / ħ) * hamiltonian ħ m V ψ x)) := by
  let c : ℂ := -I * (V x : ℂ) / ħ
  let phase : ℝ → ℂ := fun ε => Complex.exp (c * ε)
  have hphase_deriv : HasDerivAt phase c 0 := by
    simpa [phase] using (((hasDerivAt_id (0 : ℂ)).const_mul c).cexp.comp_ofReal)
  have hphase : Tendsto phase (𝓝[>] 0) (𝓝 1) := by
    simpa [phase] using hphase_deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hphase_slope : Tendsto (fun ε : ℝ => (phase ε - 1) / (ε : ℂ))
      (𝓝[>] 0) (𝓝 c) := by
    simpa [phase, RCLike.real_smul_eq_coe_mul, RCLike.ofReal_eq_complex_ofReal,
      div_eq_mul_inv, mul_comm] using
      hphase_deriv.tendsto_slope_zero_right
  have hstep (ε : ℝ) : stepEvolution ħ m V ε ψ x =
      phase ε * stepEvolution ħ m (fun _ => 0) ε ψ x := by
    have haction (y : ℝ) : shortTimeAction m V ε x y =
        shortTimeAction m (fun _ => 0) ε x y - ε * V x := by
      simp [shortTimeAction]
    have hint (y : ℝ) : Complex.exp (I * (shortTimeAction m V ε x y : ℂ) / ħ) * ψ y =
        phase ε * (Complex.exp (I * (shortTimeAction m (fun _ => 0) ε x y : ℂ) / ħ) * ψ y) := by
      have hexp : I * (shortTimeAction m V ε x y : ℂ) / ħ =
          c * ε + I * (shortTimeAction m (fun _ => 0) ε x y : ℂ) / ħ := by
        rw [haction]
        push_cast
        dsimp [c]
        ring
      rw [hexp, Complex.exp_add]
      simp only [phase, mul_assoc]
    unfold stepEvolution
    simp_rw [hint]
    rw [integral_const_mul]
    ring
  have hfree := free_step_first_order ħ m hħ hm ψ x
  have ht := (hphase.mul hfree).add (hphase_slope.mul_const (ψ x))
  have hlimit : 1 * (I * ħ / (2 * m) * deriv (deriv ψ) x) + c * ψ x =
      -(I / ħ) * hamiltonian ħ m V ψ x := by
    dsimp [c, hamiltonian]
    have hħ0 : (ħ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hħ
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hm
    field_simp [hħ0, hm0]
    ring
  rw [hlimit] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [hstep]
  have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hε
  field_simp [hε0]
  ring

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open Complex Filter Topology SchwartzMap

namespace Feynman1948

theorem schroedinger_equation (ħ m : ℝ) (hħ : 0 < ħ) (hm : 0 < m) (V : ℝ → ℝ)
    (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Tendsto (fun ε : ℝ => (stepEvolution ħ m V ε ψ x - ψ x) / ε) (𝓝[>] 0)
      (𝓝 (-(I / ħ) * hamiltonian ħ m V ψ x)) := by
  first
  | exact _root_.Prove2me.Solution.Feynman1948_schroedinger_equation ħ m hħ hm V ψ x
  | (apply _root_.Prove2me.Solution.Feynman1948_schroedinger_equation <;> assumption)

end Feynman1948


end Prove2meStatement
