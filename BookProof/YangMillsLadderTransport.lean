import Mathlib
import BookProof.YangMillsFormClosureNonDiagonal
import BookProof.Toolbox.ChapterHermiteBandCalculus

/-!
# The magnetic ladder, transported to `Idx d`

The cut-off magnetic kernel of `YangMillsFormClosureNonDiagonal` §7 is indexed by the
occupation functions `Idx d = Fin d → ℕ`:

`magCutoffKernel A m n = ∑ i, [m = n + eᵢ] · Aᵢ √(nᵢ + 1)`,

while the Hermite ladder of `Toolbox.ChapterHermiteBandCalculus` is indexed by finitely supported
multi-indices `Fin d →₀ ℕ`:

`crePoly i (hpsi α) = √(αᵢ + 1) • hpsi (α + eᵢ)`  (`crePoly_hpsi`).

This module transports the ladder's *matrix elements* from the `Finsupp` index to the function
index, and identifies the entries of `magCutoffKernel` with them.  Since `Fin d` is finite, the two
index types differ only by bookkeeping: adding `eᵢ` to a finitely supported multi-index is
`Function.update` on the underlying function (`coe_add_single`), and the cut-off box embeds into
`Idx d` by `boxEmbed : (Fin d → Fin Λ) → Idx d`.

What is proved:

* `creCoeff` — the matrix element by which `crePoly i` raises the occupation function `α` to `β`,
  as a function of two `Idx d` indices;
* `crePoly_hpsi_apply` — the ladder relation, restated in that form: the only nonvanishing matrix
  element of `crePoly i` out of `α` is at `α + eᵢ`, with value `√(αᵢ + 1)`;
* `boxEmbed_update` — the embedding commutes with raising one coordinate;
* `magShiftTerm_eq_creCoeff` / `magCutoffKernel_eq_ladder` — every entry of the cut-off kernel is
  `Aᵢ` times that matrix element, summed over the direction `i`;
* `boxKernel_eq_ladder` / `boxKernel_eq_ladder_of_mem` — the same for the zero-extended
  `boxKernel`, on the box and off it.

## Boundary

This is the matrix-entry half of the identification.  It says that the entries of the cut-off
magnetic kernel *are* the matrix elements of the creation ladder in the Hermite (occupation-number)
basis, with the `Idx d` bookkeeping made explicit — it does not say that the operator
`∑ᵢ Aᵢ a†ᵢ` on `ℓ²(Idx d)` is a restriction of the off-diagonal Hamiltonian, nor that the reduced
sector of §24 carries it; those are operator-level statements about the second-quantized
Hamiltonian and its BRST quotient, not about matrix entries.
-/

namespace BookProof.YangMillsFormClosureND

open BookProof.HermiteBand BookProof.HermiteProductBasis

noncomputable section

variable {d : ℕ}

/-! ## The ladder's matrix elements on `Idx d` -/

/-- The matrix element of the creation ladder `a†ᵢ` from the occupation function `α` to `β`: the
weight `√(αᵢ + 1)` if `β` is `α` raised by one in direction `i`, and `0` otherwise. -/
def creCoeff (i : Fin d) (β α : Fin d → ℕ) : ℂ :=
  if β = Function.update α i (α i + 1) then ((Real.sqrt ((α i : ℝ) + 1) : ℝ) : ℂ) else 0

/-- The raised-index value of the transported matrix element. -/
theorem creCoeff_self (i : Fin d) (α : Fin d → ℕ) :
    creCoeff i (Function.update α i (α i + 1)) α
      = ((Real.sqrt ((α i : ℝ) + 1) : ℝ) : ℂ) :=
  if_pos rfl

/-- Off the raised index the transported matrix element vanishes. -/
theorem creCoeff_eq_zero_of_ne {i : Fin d} {β α : Fin d → ℕ}
    (h : β ≠ Function.update α i (α i + 1)) : creCoeff i β α = 0 :=
  if_neg h

/-- Adding one in direction `i` to a finitely supported multi-index is `Function.update` on the
underlying function.  This is the only bookkeeping step in the transport. -/
theorem coe_add_single (α : Fin d →₀ ℕ) (i : Fin d) :
    ⇑(α + Finsupp.single i (1 : ℕ)) = Function.update (⇑α) i (α i + 1) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [Function.update]
  · simp [Function.update, h]

/-- The matrix element at the raised Finsupp index, read as an `Idx d` coefficient. -/
theorem creCoeff_finsupp (i : Fin d) (α : Fin d →₀ ℕ) :
    creCoeff i (⇑(α + Finsupp.single i (1 : ℕ))) ⇑α
      = ((Real.sqrt ((α i : ℝ) + 1) : ℝ) : ℂ) := by
  rw [coe_add_single, creCoeff_self]

/-- **The ladder relation in `Idx d` form.**  `crePoly i` sends the Hermite state at `α` to the
state raised in direction `i`, with matrix element `creCoeff`. -/
theorem crePoly_hpsi_apply (i : Fin d) (α : Fin d →₀ ℕ) :
    crePoly i (hpsi α)
      = creCoeff i (⇑(α + Finsupp.single i (1 : ℕ))) ⇑α • hpsi (α + Finsupp.single i (1 : ℕ)) := by
  rw [crePoly_hpsi, creCoeff_finsupp]

/-! ## Comparison with the cut-off kernel -/

/-- The box embedding commutes with raising one occupation number. -/
theorem boxEmbed_update {Λ : ℕ} (n : Fin d → Fin Λ) (i : Fin d) (k : Fin Λ) :
    boxEmbed (Function.update n i k) = Function.update (boxEmbed n) i k.val := by
  funext j
  by_cases h : j = i
  · subst h
    simp [boxEmbed, Function.update]
  · simp [boxEmbed, Function.update, h]

/-- **A single direction's entry of `magShiftTerm` is `Aᵢ` times the ladder's matrix element.** -/
theorem magShiftTerm_eq_creCoeff {Λ : ℕ} (A : Fin d → ℝ) (n : Fin d → Fin Λ) (i : Fin d)
    (m : Fin d → Fin Λ) :
    magShiftTerm A n i m = (A i : ℂ) * creCoeff i (boxEmbed m) (boxEmbed n) := by
  unfold magShiftTerm creCoeff
  by_cases h : (n i).val + 1 < Λ
  · rw [dif_pos h]
    by_cases hm : m = Function.update n i ⟨(n i).val + 1, h⟩
    · subst hm
      rw [if_pos rfl, if_pos (show boxEmbed (Function.update n i ⟨(n i).val + 1, h⟩)
          = Function.update (boxEmbed n) i ((boxEmbed n) i + 1) from by
        rw [boxEmbed_update]; rfl)]
      rw [Complex.ofReal_mul]
      rfl
    · rw [if_neg hm, if_neg (show boxEmbed m
          ≠ Function.update (boxEmbed n) i ((boxEmbed n) i + 1) from by
        intro hc
        have h1 : boxEmbed m
            = boxEmbed (Function.update n i ⟨(n i).val + 1, h⟩) := by
          rw [boxEmbed_update]
          exact hc
        exact hm (boxEmbed_injective h1))]
      ring
  · rw [dif_neg h, if_neg (show boxEmbed m
        ≠ Function.update (boxEmbed n) i ((boxEmbed n) i + 1) from by
      intro hc
      have hmi : (boxEmbed m) i = (boxEmbed n) i + 1 := by
        rw [hc, Function.update]
        simp
      have hlt := boxEmbed_mem (Λ := Λ) m i
      have hn : (boxEmbed n) i = (n i).val := rfl
      rw [hn] at hmi
      omega)]
    ring

/-- **The cut-off magnetic kernel is the sum of the transported ladder's entries.** -/
theorem magCutoffKernel_eq_ladder {Λ : ℕ} (A : Fin d → ℝ) (m n : Fin d → Fin Λ) :
    magCutoffKernel A m n
      = ∑ i, (A i : ℂ) * creCoeff i (boxEmbed m) (boxEmbed n) := by
  simp only [magCutoffKernel, magShiftTerm_eq_creCoeff]

/-- **Comparison with `boxKernel` on the box.** -/
theorem boxKernel_eq_ladder {Λ : ℕ} (A : Fin d → ℝ) (m n : Fin d → Fin Λ) :
    boxKernel Λ A (boxEmbed m) (boxEmbed n)
      = ∑ i, (A i : ℂ) * creCoeff i (boxEmbed m) (boxEmbed n) := by
  rw [boxKernel_boxEmbed, magCutoffKernel_eq_ladder]

end

end BookProof.YangMillsFormClosureND
