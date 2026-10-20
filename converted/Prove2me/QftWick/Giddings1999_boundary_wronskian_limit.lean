/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 6d5f3a6b-fa38-4b88-a78f-734ed228d46b
* original name       : `Giddings1999.boundary_wronskian_limit`
* title               : Eqs. (19)–(20): $\lim_{r\to\pi/2}(\tan r)^{d-1}[(\cos r)^{2h_-}\overleftrightarrow{\partial_r}(\cos r)^{2h_+}]=-2\nu$
* statement author    : Lucas
* solution author     : fizzyinc3 (submission eae4e3c7-3228-49b0-af00-53c488c9e218,
                        accepted 2026-10-17T09:41:04.261347+00:00)
* source              : S. B. Giddings, Boundary S matrix and the anti-de Sitter space to conformal field theory dictionary, Phys. Rev. Lett. 83, 2707 (1999), https://doi.org/10.1103/PhysRevLett.83.2707, eqs. (19), (20), p. 2708
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/qft-wick/Giddings1999.boundary_wronskian_limit.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/Giddings1999_boundary_wronskian_limit.diff`.
-/
import Mathlib
import Definitions.Def_Giddings1999_AdSModes

open Real Filter Topology
open Giddings1999

theorem _root_.Prove2me.Solution.Giddings1999_boundary_wronskian_limit (d : ℕ) (hd : 1 ≤ d) (m R : ℝ) :
    Tendsto (fun r => tan r ^ (d - 1) *
        (cos r ^ twoHMinus d m R * deriv (fun s => cos s ^ twoHPlus d m R) r
          - cos r ^ twoHPlus d m R * deriv (fun s => cos s ^ twoHMinus d m R) r))
      (𝓝[<] (π / 2)) (𝓝 (-2 * nu d m R)) := by
  set a := twoHMinus d m R
  set b := twoHPlus d m R
  have hab : a + b = d := by simp only [a, b, twoHMinus, twoHPlus]; ring
  have hba : b - a = 2 * nu d m R := by simp only [a, b, twoHMinus, twoHPlus]; ring
  have key : ∀ r ∈ Set.Ioo 0 (π / 2), tan r ^ (d - 1) *
        (cos r ^ a * deriv (fun s => cos s ^ b) r - cos r ^ b * deriv (fun s => cos s ^ a) r)
        = -2 * nu d m R * sin r ^ d := by
    intro r hr
    have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hr.2⟩
    have hD : ∀ e : ℝ, deriv (fun s => cos s ^ e) r = e * cos r ^ (e - 1) * (-sin r) := by
      intro e
      rw [((hasDerivAt_cos r).rpow_const (Or.inl hc.ne')).deriv]; ring
    rw [hD, hD]
    have e1 : cos r ^ a * cos r ^ (b - 1) = cos r ^ ((d:ℝ) - 1) := by
      rw [← rpow_add hc]; congr 1; linarith
    have e2 : cos r ^ b * cos r ^ (a - 1) = cos r ^ ((d:ℝ) - 1) := by
      rw [← rpow_add hc]; congr 1; linarith
    have e3 : cos r ^ ((d:ℝ) - 1) = cos r ^ (d - 1) := by
      rw [← rpow_natCast]; congr 1; push_cast [hd]; ring
    have e4 : tan r ^ (d - 1) * cos r ^ (d - 1) = sin r ^ (d - 1) := by
      rw [tan_eq_sin_div_cos, div_pow, div_mul_cancel₀]; exact pow_ne_zero _ hc.ne'
    have e5 : sin r ^ d = sin r ^ (d - 1) * sin r := by
      rw [← pow_succ]; congr 1; omega
    calc tan r ^ (d - 1) * (cos r ^ a * (b * cos r ^ (b - 1) * -sin r) -
          cos r ^ b * (a * cos r ^ (a - 1) * -sin r))
        = -(b - a) * (tan r ^ (d - 1) * cos r ^ ((d:ℝ) - 1)) * sin r := by
          linear_combination (tan r ^ (d - 1) * (-sin r) * b) * e1 - (tan r ^ (d - 1) * (-sin r) * a) * e2
      _ = -2 * nu d m R * sin r ^ d := by rw [e3, e4, e5, hba]; ring
  have hlim : Tendsto (fun r => -2 * nu d m R * sin r ^ d) (𝓝[<] (π / 2)) (𝓝 (-2 * nu d m R)) := by
    have hcont : Continuous (fun r : ℝ => -2 * nu d m R * sin r ^ d) := by fun_prop
    have := (hcont.tendsto (π / 2)).mono_left
      (nhdsWithin_le_nhds (s := Set.Iio (π/2)))
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < π / 2 by positivity)] with r hr
  exact (key r hr).symm

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open Real Filter Topology

namespace Giddings1999

/-- **Milestone, eqs. (19)–(20)**: the boundary limit
`lim_{r→π/2} (tan r)^{d−1} [(cos r)^{2h₋} ∂⃡_r (cos r)^{2h₊}] = −2ν`, where `A ∂⃡ B = A ∂B − (∂A) B`. -/
theorem boundary_wronskian_limit (d : ℕ) (hd : 1 ≤ d) (m R : ℝ) :
    Tendsto (fun r => tan r ^ (d - 1) *
        (cos r ^ twoHMinus d m R * deriv (fun s => cos s ^ twoHPlus d m R) r
          - cos r ^ twoHPlus d m R * deriv (fun s => cos s ^ twoHMinus d m R) r))
      (𝓝[<] (π / 2)) (𝓝 (-2 * nu d m R)) := by
  first
  | exact _root_.Prove2me.Solution.Giddings1999_boundary_wronskian_limit d hd m R
  | (apply _root_.Prove2me.Solution.Giddings1999_boundary_wronskian_limit <;> assumption)

end Giddings1999


end Prove2meStatement
