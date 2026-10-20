/-
prove2.me platform library module `Theorems.Thm_SWPort_ZetaSum_aux2`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_SWPort_ZetaSum_aux2.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Batteries.Tactic.Lemma

section

namespace SWPort

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta

theorem _root_.SWPort.ZetaSum_aux2 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  sorry

open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt

end SWPort
end
