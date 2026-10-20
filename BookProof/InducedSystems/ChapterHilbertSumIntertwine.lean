import Mathlib

/-!
# Operators that act fibrewise on a Hilbert sum

If a Hilbert space `H` is the Hilbert sum of a family `G i` along isometries
`V i : G i → H`, and a bounded operator `A` on `H` is carried by every `V i` to a
contraction `B i` of the fibre (`V i (B i u) = A (V i u)`), then under the canonical unitary
`H ≃ ℓ²-⨁ G i` the operator `A` **is** the fibrewise operator `(B i)`.

This is the abstract step used to assemble the cyclic pieces of a projection-valued measure
into a single system (`BookProof.ChapterPvmInducedSystem`) and to recognise the multiplication
system on `L²(X, μ; ℓ²(ι))` (`BookProof.ChapterL2FibreSum`).

Everything is `sorry`-free and uses only the standard axioms.
-/

open scoped InnerProductSpace

namespace BookProof.ChapterHilbertSumIntertwine

section Fibres

variable {ι : Type*}
variable {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)]

/-- A fibrewise family of contractions applied to a member of the `ℓ²`-sum stays in the
`ℓ²`-sum. -/
theorem memℓp_fibrewise (B : ∀ i, G i →L[ℂ] G i) (hB : ∀ i u, ‖B i u‖ ≤ ‖u‖)
    (w : lp G 2) : Memℓp (fun i => B i (w i)) 2 := by
  have htr : ((2 : ENNReal)).toReal = (2 : ℝ) := by norm_num
  have hw : Summable fun i => ‖w i‖ ^ (2 : ℝ) := by
    have h := (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).1 (lp.memℓp w)
    simpa only [htr] using h
  refine memℓp_gen ?_
  simp only [htr]
  refine Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (norm_nonneg _) _)
    (fun i => ?_) hw
  exact Real.rpow_le_rpow (norm_nonneg _) (hB i (w i)) (by norm_num)

end Fibres

section HilbertSum

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)]

/-- **An operator intertwined with a fibrewise family acts fibrewise on the Hilbert sum.** -/
theorem linearIsometryEquiv_intertwine {V : ∀ i, G i →ₗᵢ[ℂ] H} (hsum : IsHilbertSum ℂ G V)
    (A : H →L[ℂ] H) (B : ∀ i, G i →L[ℂ] G i) (hB : ∀ i u, ‖B i u‖ ≤ ‖u‖)
    (hcomm : ∀ i u, V i (B i u) = A (V i u)) (v : H) (i : ι) :
    hsum.linearIsometryEquiv (A v) i = B i (hsum.linearIsometryEquiv v i) := by
  set w := hsum.linearIsometryEquiv v with hw
  have hmem : Memℓp (fun i => B i (w i)) 2 := memℓp_fibrewise B hB w
  set w' : lp G 2 := ⟨_, hmem⟩ with hw'
  have hsymm : hsum.linearIsometryEquiv.symm w' = A v := by
    have h1 : HasSum (fun i => V i (w' i)) (hsum.linearIsometryEquiv.symm w') :=
      hsum.hasSum_linearIsometryEquiv_symm w'
    have h2 : HasSum (fun i => V i (w i)) (hsum.linearIsometryEquiv.symm w) :=
      hsum.hasSum_linearIsometryEquiv_symm w
    have h3 : HasSum (fun i => A (V i (w i))) (A (hsum.linearIsometryEquiv.symm w)) :=
      h2.mapL A
    have h5 : HasSum (fun i => V i (w' i)) (A (hsum.linearIsometryEquiv.symm w)) := by
      refine h3.congr_fun ?_
      intro i
      exact hcomm i (w i)
    have h6 : hsum.linearIsometryEquiv.symm w' = A (hsum.linearIsometryEquiv.symm w) :=
      h1.unique h5
    rw [h6, hw, LinearIsometryEquiv.symm_apply_apply]
  have hA : hsum.linearIsometryEquiv (A v) = w' := by
    rw [← hsymm, LinearIsometryEquiv.apply_symm_apply]
  rw [hA]

end HilbertSum

end BookProof.ChapterHilbertSumIntertwine
