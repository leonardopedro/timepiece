/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 109255f0-95e6-4aad-8947-1c99a5b80fcb
* original name       : `Davenport.three_primes`
* title               : Vinogradov's three primes theorem (unconditional)
* statement author    : alya
* solution author     : alya (submission 5d22d5f9-b6a4-4ef0-83eb-37f2307dc525,
                        accepted 2026-09-04T03:49:45.658675+00:00)
* source              : I. M. Vinogradov, Representation of an odd number as a sum of three primes, Dokl. Akad. Nauk SSSR 15 (1937), 291–294; H. Davenport, Multiplicative Number Theory, 3rd ed. (revised by H. L. Montgomery), GTM 74, Springer, 2000, https://doi.org/10.1007/978-1-4757-5927-3, §26 (The three primes theorem); platform theorem ThreePrimes.three_primes (conditional on ThreePrimes.SiegelWalfisz)
* platform Mathlib rev: c5ea00351c28e24afc9f0f84379aa41082b1188f
* original file       : Downloads/analytic-nt/Davenport.three_primes.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/Davenport_three_primes.diff`.
-/
import Theorems.Thm_Davenport_siegel_walfisz_char
import Theorems.Thm_ThreePrimes_three_primes

theorem _root_.Prove2me.Solution.Davenport_three_primes :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Odd n →
      ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = n :=
  ThreePrimes.three_primes Davenport.siegel_walfisz_char

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open Finset DirichletCharacter Vino

namespace Davenport

theorem three_primes :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Odd n →
      ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = n :=
  _root_.Prove2me.Solution.Davenport_three_primes

end Davenport

end Prove2meStatement
