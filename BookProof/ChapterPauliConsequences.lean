import Mathlib
import BookProof.ChapterA3c
import BookProof.ChapterPauliFundamental

/-!
# Prop 46 without external input — the Pin(3,1) → O(1,3) covering

Source: `book.tex`, chapter *"Real representations, CPT theorem and the relativistic
position operator"*, §A.3, **Proposition 46**: the map `S ↦ Λ(S)` from `Pin(3,1)` to the
Lorentz group `O(1,3)` is *surjective* and *two-to-one* (`S' = ± S`).

`BookProof.ChapterA3c` proves both halves from the real Pauli theorem, i.e. from the named
hypothesis `PauliFundamental` (Note 36).  `BookProof.ChapterPauliFundamental` now **proves**
that hypothesis, so this file records the two statements with no external input at all.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.ChapterPauliConsequences

open Matrix BookProof.ChapterA3 BookProof.ChapterPauliFundamental

/-- **Prop 46 (surjectivity), unconditional.**  Every Lorentz transformation is the image
of some element of `Pin(3,1)`. -/
theorem lambda_surjective' (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hΛ : Λ ∈ LorentzO) :
    ∃ S : Matrix (Fin 4) (Fin 4) ℝ, IsPin S ∧ LambdaOf S = Λ :=
  lambda_surjective pauliFundamental Λ hΛ

/-- **Prop 46 (two-to-one), unconditional.**  Two `Pin(3,1)` elements with the same Lorentz
image differ by a sign. -/
theorem lambda_two_to_one' {S S' : Matrix (Fin 4) (Fin 4) ℝ} (hS : IsPin S) (hS' : IsPin S')
    (h : LambdaOf S = LambdaOf S') : S' = S ∨ S' = -S :=
  lambda_two_to_one pauliFundamental hS hS' h

end BookProof.ChapterPauliConsequences
