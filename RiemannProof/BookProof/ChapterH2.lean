import Mathlib
import BookProof.ChapterH1

/-!
# Chapter H2 — Hashimoto SIRK: Krylov compression (roadmap N13, §0 S7)

This file continues the Hashimoto–Nodera *Shift-invert Rational Krylov (SIRK)*
formalization (source `RiemannProof/Hashimoto.md`) begun in `ChapterH1.lean`.

## Deliverables (this file)

* **H2.1 — the Arnoldi/Krylov compression relation** (§4, eqs. 5, 7): with an
  orthonormal basis `v₁,…,vₘ` of the Krylov subspace and the nesting
  `X 𝒦_j ⊆ 𝒦_{j+1}`, the compression `Vₘᴴ X Vₘ = Hₘ` is upper-Hessenberg —
  `h_{i,j} = ⟪vᵢ, X vⱼ⟫ = 0` whenever `i > j+1` (`hessenberg_vanishing`,
  `compression_upper_hessenberg`).

The genuinely deep analytic convergence inputs (Crouzeix's inequality and the
Göckler–Grimm / Hashimoto RK error theorems, deliverables H2.3/H2.4) are
recorded in `BookProof/STATUS.md` as the `EXTERNAL`/`CrouzeixBound` design
target and are **not** asserted here — no `axiom`, ever.

Everything in this file is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`); **no `EXTERNAL` hypothesis**.
-/

open scoped BigOperators

namespace BookProof.ChapterH2

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## H2.1 — the Arnoldi/Krylov compression is upper-Hessenberg -/

/-
**H2.1** (Hessenberg vanishing): let `v : Fin n → E` be an orthonormal
system, and let `X` be an operator whose action on `vⱼ` lands in the span of
`{v_l : l ≤ j+1}` (the Krylov nesting `X 𝒦_j ⊆ 𝒦_{j+1}`).  Then for `i > j+1`
the compression entry `⟪vᵢ, X vⱼ⟫` vanishes — the compression matrix is upper
Hessenberg.
-/
theorem hessenberg_vanishing {n : ℕ} (v : Fin n → E) (hv : Orthonormal ℂ v)
    (X : E →ₗ[ℂ] E) (j i : Fin n)
    (hnest : X (v j) ∈ Submodule.span ℂ {w : E | ∃ l : Fin n, (l : ℕ) ≤ (j : ℕ) + 1 ∧ w = v l})
    (hij : (j : ℕ) + 1 < (i : ℕ)) :
    inner (𝕜 := ℂ) (v i) (X (v j)) = 0 := by
  refine' Submodule.span_induction _ _ _ _ hnest;
  · simp +zetaDelta at *;
    intro x l hl hx; rw [ hx, hv.2 ( show i ≠ l from by rintro rfl; linarith ) ] ;
  · simp +decide;
  · simp +contextual [ inner_add_right ];
  · simp +contextual [ inner_smul_right ]

/-- **H2.1** (compression is upper-Hessenberg): the compressed operator entries
`Hₘ_{i,j} := ⟪vᵢ, X vⱼ⟫` vanish below the first subdiagonal (`i > j+1`), given the
Krylov nesting hypothesis for every column `j`. -/
theorem compression_upper_hessenberg {n : ℕ} (v : Fin n → E) (hv : Orthonormal ℂ v)
    (X : E →ₗ[ℂ] E)
    (hnest : ∀ j : Fin n,
      X (v j) ∈ Submodule.span ℂ {w : E | ∃ l : Fin n, (l : ℕ) ≤ (j : ℕ) + 1 ∧ w = v l})
    (i j : Fin n) (hij : (j : ℕ) + 1 < (i : ℕ)) :
    inner (𝕜 := ℂ) (v i) (X (v j)) = 0 :=
  hessenberg_vanishing v hv X j i (hnest j) hij

end

end BookProof.ChapterH2