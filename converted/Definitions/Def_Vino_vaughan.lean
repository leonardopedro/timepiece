/-
prove2.me platform library module `Definitions.Def_Vino_vaughan`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_Vino_vaughan.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_Vino_primes
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Log

open Finset ArithmeticFunction

namespace Vaughan

/-- Truncation of an arithmetic function to the range `n ≤ V`. -/
noncomputable def trunc (f : ArithmeticFunction ℝ) (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ V then f n else 0, by simp⟩

@[simp] theorem trunc_apply (f : ArithmeticFunction ℝ) (V n : ℕ) :
    trunc f V n = if n ≤ V then f n else 0 := rfl

/-- `μ_V`: the Möbius function truncated to `d ≤ V`. -/
noncomputable def muT (V : ℕ) : ArithmeticFunction ℝ := trunc (moebius : ArithmeticFunction ℝ) V

/-- `Λ_U`: the von Mangoldt function truncated to `r ≤ U`. -/
noncomputable def lamT (U : ℕ) : ArithmeticFunction ℝ := trunc vonMangoldt U

/-- The bilinear exponential sum `∑_{m·k < N} f(m) g(k) e(α m k)`. -/
noncomputable def bilin (f g : ArithmeticFunction ℝ) (α : ℝ) (N : ℕ) : ℂ :=
  ∑ m ∈ range N, ∑ k ∈ range N,
    if m * k < N then ((f m * g k : ℝ) : ℂ) * CircleMethod.e (α * ((m * k : ℕ) : ℝ)) else 0

/-- The dyadic restriction of `g` to `[2^j, 2^(j+1)) ∩ [1, T]`. -/
noncomputable def dyad (g : ℕ → ℝ) (T j k : ℕ) : ℝ :=
  if 2 ^ j ≤ k ∧ k < 2 ^ (j + 1) ∧ k ≤ T then g k else 0

/-- A safe form of `min (X, 1/(2‖θ‖))`: it equals `X` whenever `2‖θ‖X ≤ 1` (in particular when
`‖θ‖ = 0`) and `1/(2‖θ‖)` otherwise. -/
noncomputable def capMin (X θ : ℝ) : ℝ :=
  if 2 * CircleMethod.nrm θ * X ≤ 1 then X else 1 / (2 * CircleMethod.nrm θ)

/-- Dyadic block `j` (scale `U 2^j`, i.e. `m` with `⌊log₂ ((m-1)/U)⌋ = j`) of `f`,
truncated to `m ≤ T`. -/
noncomputable def blockT (f : ArithmeticFunction ℝ) (U T j : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun m => if m ≤ T ∧ Nat.log 2 ((m - 1) / U) = j then f m else 0, by simp⟩

@[simp] theorem blockT_apply (f : ArithmeticFunction ℝ) (U T j m : ℕ) :
    blockT f U T j m = if m ≤ T ∧ Nat.log 2 ((m - 1) / U) = j then f m else 0 := rfl

end Vaughan
