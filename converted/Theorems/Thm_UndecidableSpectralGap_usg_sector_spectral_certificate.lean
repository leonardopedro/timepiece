/-
prove2.me platform library module `Theorems.Thm_UndecidableSpectralGap_usg_sector_spectral_certificate`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_UndecidableSpectralGap_usg_sector_spectral_certificate.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_usg_spectral_notions

set_option autoImplicit false
open scoped ComplexOrder

namespace UndecidableSpectralGap

theorem usg_sector_spectral_certificate (u : Nat.Partrec.Code) (ε : ℝ) (hε : 0 < ε) :
    ∃ (d : ℕ) (A A' B C D D' : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
      (Pi : Matrix (Fin d) (Fin d) ℂ) (β : ℚ) (α : ℕ → ℝ),
      -- `β` is a rational number, as small as desired
      0 < β ∧ (β : ℝ) < ε ∧
      -- (i) `A` is diagonal with integer entries
      (∀ i j, i ≠ j → A i j = 0) ∧ (∀ i, ∃ a : ℤ, A i i = (a : ℂ)) ∧
      -- (ii) `A'` is Hermitian with entries in `ℤ + (1/√2) ℤ`
      A'.IsHermitian ∧
        (∀ i j, ∃ a b : ℤ, A' i j = (a : ℂ) + (b : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) ∧
      -- (iii) `B`, `C` have integer entries
      (∀ i j, ∃ a : ℤ, B i j = (a : ℂ)) ∧ (∀ i j, ∃ a : ℤ, C i j = (a : ℂ)) ∧
      -- (iv) `D` is diagonal with integer entries
      (∀ i j, i ≠ j → D i j = 0) ∧ (∀ i, ∃ a : ℤ, D i i = (a : ℂ)) ∧
      -- (v) `D'` is Hermitian with integer entries
      D'.IsHermitian ∧ (∀ i j, ∃ a : ℤ, D' i j = (a : ℂ)) ∧
      -- `Π` is a diagonal projector
      Pi.IsHermitian ∧ (∀ i j, i ≠ j → Pi i j = 0) ∧ Pi * Pi = Pi ∧
      -- `α(n)` is an algebraic number bounded by `2β`
      (∀ n, IsAlgebraic ℚ (α n) ∧ α n ≤ 2 * (β : ℝ)) ∧
      ∀ n : ℕ, ∀ (h1 : Matrix (Fin d) (Fin d) ℂ)
        (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
        h1 = ((α n : ℝ) : ℂ) • Pi →
        hcol = D + ((β : ℝ) : ℂ) • D' →
        hrow = A + ((β : ℝ) : ℂ) •
          (A' + Complex.exp (Complex.I * (Real.pi : ℂ) * ((phi n : ℚ) : ℂ)) • B
            + Complex.exp (-(Complex.I * (Real.pi : ℂ) * ((phi n : ℚ) : ℂ))) • B.conjTranspose
            + Complex.exp (Complex.I * (Real.pi : ℂ) * (2 : ℂ) ^ (-(phiLen n : ℤ))) • C
            + Complex.exp (-(Complex.I * (Real.pi : ℂ) * (2 : ℂ) ^ (-(phiLen n : ℤ)))) • C.conjTranspose) →
        -- (i) the local interaction strength is bounded by 1
        localInteractionStrength h1 hrow hcol ≤ 1 ∧
        ∃ (E : ℕ → ℝ) (S : ℕ → Set ℝ) (L0 : ℕ),
          (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ L > N,
            ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ s ∈ S L, |x - s| ≤ δ) ∧
          (∀ L > L0,
            (0 ∈ specReal (latticeHam L d h1 hrow hcol) ∧
             E L ∈ specReal (latticeHam L d h1 hrow hcol) ∧
             ∀ μ ∈ specReal (latticeHam L d h1 hrow hcol), min 0 (E L) ≤ μ) ∧
            (∀ s ∈ S L, E L + s ∈ specReal (latticeHam L d h1 hrow hcol)) ∧
            (1 ≤ E L → eigMultiplicity (latticeHam L d h1 hrow hcol) 0 = 1 ∧
              ∀ μ ∈ specReal (latticeHam L d h1 hrow hcol), μ ≠ 0 → 1 ≤ μ)) ∧
          ((u.eval n).Dom → ∀ L > L0, 1 ≤ E L) ∧
          (¬ (u.eval n).Dom → ∀ L > L0, E L ≤ 0) := by sorry

end UndecidableSpectralGap
