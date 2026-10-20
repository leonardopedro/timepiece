/-
prove2.me platform library module `Definitions.Def_RPB108_ThreeGram`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_RPB108_ThreeGram.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

open scoped BigOperators
namespace WeilDefect.RPB108

noncomputable def offWeights (u : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![0,u 0,u 1], ![u 0,0,u 2], ![u 1,u 2,0]]
noncomputable def rowMargins (d u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![d 0-u 0-u 1, d 1-u 0-u 2, d 2-u 1-u 2]
noncomputable def realGram (A : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j*x i*x j
noncomputable def complexGram (A : Fin 3 → Fin 3 → ℝ) (z : Fin 3 → ℂ) : ℝ :=
  ∑ i, ∑ j, A i j*(star (z i)*z j).re











end WeilDefect.RPB108
