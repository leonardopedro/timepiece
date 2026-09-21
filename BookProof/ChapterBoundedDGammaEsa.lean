import Mathlib
import BookProof.ChapterScalarDGammaEsa
import BookProof.ChapterTensorOperatorBound

/-!
# Second quantization of an arbitrary bounded symmetric one-particle operator

The main theorem of `BookProof/ChapterSecondQuantizationCoreEsa.lean` carries, sector by
sector, the hypothesis that the derivation `dΓ(A)⁽ⁿ⁾` is essentially self-adjoint on the full
tensor power of the domain of the closure.  `BookProof/ChapterScalarDGammaEsa.lean` discharged
that hypothesis for the *scalar* one-particle operators `c • id`.  This module discharges it
for **every bounded symmetric one-particle operator** `A`, with **no positivity or
semiboundedness assumption**: `A` may have spectrum on both sides of `0` (for instance
`A = -id`, whose second quantization `dΓ(A)` is unbounded below).

The one new analytic ingredient is the tensor operator bound of
`BookProof/ChapterTensorOperatorBound.lean`; feeding it into the Leibniz recursion
`dΓ⁽ⁿ⁺¹⁾ = A ⊗ 1 + 1 ⊗ dΓ⁽ⁿ⁾` gives the sector estimate `‖dΓ(A)⁽ⁿ⁾ x‖ ≤ n ‖A‖ ‖x‖`, after
which the sector hypothesis follows from the elementary criterion
`BookProof.GraphCore.essentiallySelfAdjointOn_of_bounded_dense` and the passage to an
arbitrary dense core `D ⊆ H` is the core transfer principle.

## Contents

* `norm_derPow_le` — the sector estimate `‖dΓ(A)⁽ⁿ⁾ x‖ ≤ n C ‖x‖` for `‖A‖ ≤ C`, on the
  tensor power of an arbitrary domain;
* `norm_sectorOp_le`, `norm_fockSectorOp_le` — the same inside `H^{⊗n}` and inside the
  completed sector;
* `isGraphCore_of_bounded` — every dense subspace is a core for an everywhere-defined bounded
  operator;
* `essentiallySelfAdjointOn_fockSectorDom_bounded` — the sector hypothesis, proved;
* `dGamma_bounded_essentiallySelfAdjointOn_fockCore` — **the theorem**: for any bounded
  symmetric `A` (no positivity) and any dense subspace `D ⊆ H`, `dΓ(A)` is essentially
  self-adjoint on the finite-particle domain `𝓕_fin(D)`.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.BoundedDGamma

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
  BookProof.SecondQuantizationCore BookProof.DirectSumEsa BookProof.TensorOpBound

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)

/-! ## The sector estimate -/

/-- **The sector estimate.**  If the one-particle operator is bounded by `C`, the `n`-sector
derivation `dΓ(A)⁽ⁿ⁾` is bounded by `n C`.  This is the Leibniz recursion
`dΓ⁽ⁿ⁺¹⁾ = A ⊗ 1 + 1 ⊗ dΓ⁽ⁿ⁾` together with the tensor operator bound; no positivity of `A` is
used, only the norm bound. -/
theorem norm_derPow_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ a : D₂, ‖A a‖ ≤ C * ‖a‖) :
    ∀ (n : ℕ) (x : ((domSpace Hs D₂).pow n)), ‖derPow Hs D₂ A n x‖ ≤ ((n : ℝ) * C) * ‖x‖ := by
  intro n
  induction n with
  | zero => intro x; simp [derPow]
  | succ n ih =>
      intro x
      have hfirst : ‖TensorProduct.map A (inclPow Hs D₂ n).toLinearMap x‖ ≤ C * 1 * ‖x‖ :=
        norm_map_le A (inclPow Hs D₂ n).toLinearMap hC0 zero_le_one hC
          (fun b => le_of_eq (by rw [one_mul]; exact (inclPow Hs D₂ n).norm_map b)) x
      have hsecond : ‖TensorProduct.map D₂.subtype (derPow Hs D₂ A n) x‖
          ≤ 1 * ((n : ℝ) * C) * ‖x‖ :=
        norm_map_le D₂.subtype (derPow Hs D₂ A n) zero_le_one (by positivity)
          (fun a => le_of_eq (by rw [one_mul]; rfl)) ih x
      have hsplit : derPow Hs D₂ A (n + 1) x
          = TensorProduct.map A (inclPow Hs D₂ n).toLinearMap x
            + TensorProduct.map D₂.subtype (derPow Hs D₂ A n) x := rfl
      have hnn : 0 ≤ ‖x‖ := norm_nonneg _
      calc ‖derPow Hs D₂ A (n + 1) x‖ ≤ ‖TensorProduct.map A (inclPow Hs D₂ n).toLinearMap x‖
            + ‖TensorProduct.map D₂.subtype (derPow Hs D₂ A n) x‖ := by
              rw [hsplit]; exact norm_add_le _ _
        _ ≤ C * 1 * ‖x‖ + 1 * ((n : ℝ) * C) * ‖x‖ := add_le_add hfirst hsecond
        _ = (((n : ℕ) + 1 : ℝ) * C) * ‖x‖ := by ring
        _ = ((((n + 1 : ℕ) : ℝ)) * C) * ‖x‖ := by push_cast; ring

/-- The sector estimate inside `H^{⊗n}`. -/
theorem norm_sectorOp_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ a : D₂, ‖A a‖ ≤ C * ‖a‖) (n : ℕ)
    (x : sectorDom Hs D₂ n) :
    ‖sectorOp Hs D₂ A n x‖ ≤ ((n : ℝ) * C) * ‖(x : (Hs.pow n).carrier)‖ := by
  obtain ⟨x₀, hx₀⟩ := x.2
  have hx : (x : (Hs.pow n).carrier) = inclPow Hs D₂ n x₀ := hx₀.symm
  rw [sectorOp_apply Hs D₂ A n x x₀ hx, hx, (inclPow Hs D₂ n).norm_map]
  exact norm_derPow_le Hs D₂ A hC0 hC n x₀

/-- The sector estimate inside the completed sector. -/
theorem norm_fockSectorOp_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ a : D₂, ‖A a‖ ≤ C * ‖a‖) (n : ℕ)
    (x : fockSectorDom Hs D₂ n) :
    ‖fockSectorOp Hs D₂ A n x‖ ≤ ((n : ℝ) * C) * ‖(x : fockSector Hs n)‖ := by
  obtain ⟨x₀, hx₀, hxe⟩ := x.2
  have hx' : (x : fockSector Hs n)
      = sectorEmb Hs n ((⟨x₀, hx₀⟩ : sectorDom Hs D₂ n) : (Hs.pow n).carrier) := hxe.symm
  have hop : fockSectorOp Hs D₂ A n x
      = sectorEmb Hs n (sectorOp Hs D₂ A n ⟨x₀, hx₀⟩) :=
    pushOp_apply (sectorEmb Hs n) (sectorOp Hs D₂ A n) x ⟨x₀, hx₀⟩ hx'
  rw [hop, (sectorEmb Hs n).norm_map, hx', (sectorEmb Hs n).norm_map]
  exact norm_sectorOp_le Hs D₂ A hC0 hC n ⟨x₀, hx₀⟩

/-! ## Everywhere-defined bounded operators -/

variable (B : (⊤ : Submodule ℂ Hs.carrier) →ₗ[ℂ] Hs.carrier)

/-- **Every dense subspace is a core for an everywhere-defined bounded operator.**  The graph
norm of a bounded operator is equivalent to the norm, so graph-norm density is plain
density. -/
theorem isGraphCore_of_bounded {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ a : (⊤ : Submodule ℂ Hs.carrier), ‖B a‖ ≤ C * ‖(a : Hs.carrier)‖)
    {D : Submodule ℂ Hs.carrier} (hdense : Dense (D : Set Hs.carrier)) : IsGraphCore D B := by
  intro x ε hε
  have hden : (0 : ℝ) < 1 + C := by linarith
  have hpos : 0 < ε / (1 + C) := by positivity
  obtain ⟨y, hyD, hy⟩ := Metric.mem_closure_iff.mp (hdense (x : Hs.carrier)) _ hpos
  have hxy : ‖(x : Hs.carrier) - y‖ < ε / (1 + C) := by rw [← dist_eq_norm]; exact hy
  have hmul : (1 + C) * ‖(x : Hs.carrier) - y‖ < ε := by
    calc (1 + C) * ‖(x : Hs.carrier) - y‖ < (1 + C) * (ε / (1 + C)) :=
          mul_lt_mul_of_pos_left hxy hden
      _ = ε := by field_simp
  have hnn : 0 ≤ ‖(x : Hs.carrier) - y‖ := norm_nonneg _
  refine ⟨⟨y, trivial⟩, hyD, ?_, ?_⟩
  · nlinarith
  · have hsub : B x - B ⟨y, trivial⟩ = B (x - ⟨y, trivial⟩) := (map_sub B _ _).symm
    have hval : ((x - ⟨y, trivial⟩ : (⊤ : Submodule ℂ Hs.carrier)) : Hs.carrier)
        = (x : Hs.carrier) - y := rfl
    rw [hsub]
    have := hC (x - ⟨y, trivial⟩)
    rw [hval] at this
    nlinarith

/-- **The sector hypothesis for a bounded symmetric one-particle operator.**  On the
`n`-particle sector the derivation is bounded by `n C` on a dense domain, hence essentially
self-adjoint there.  No positivity is used. -/
theorem essentiallySelfAdjointOn_fockSectorDom_bounded (hB : SymmetricOn ⊤ B) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ a : (⊤ : Submodule ℂ Hs.carrier), ‖B a‖ ≤ C * ‖(a : Hs.carrier)‖)
    (n : ℕ) :
    EssentiallySelfAdjointOn (fockSectorDom Hs ⊤ n) (fockSectorOp Hs ⊤ B n) :=
  essentiallySelfAdjointOn_of_bounded_dense _
    (symmetricOn_fockSectorOp Hs ⊤ B hB n) (by positivity)
    (norm_fockSectorOp_le Hs ⊤ B hC0 hC n)
    (BookProof.ScalarDGamma.dense_fockSectorDom Hs n)

/-! ## The theorem -/

/-- **Second quantization over a core, for an arbitrary bounded symmetric one-particle
operator.**  Let `B` be symmetric on all of `H` with `‖B a‖ ≤ C ‖a‖` — *no positivity or
semiboundedness is assumed*, so the spectrum of `B` may straddle `0` — and let `D ⊆ H` be any
dense subspace.  Then `dΓ(B)` is essentially self-adjoint on the finite-particle domain
`𝓕_fin(D)` built from `D` alone.  `D` is only a core: it is not invariant under anything, and
no resolvent of `B` on `D` is used. -/
theorem dGamma_bounded_essentiallySelfAdjointOn_fockCore (hB : SymmetricOn ⊤ B) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ a : (⊤ : Submodule ℂ Hs.carrier), ‖B a‖ ≤ C * ‖(a : Hs.carrier)‖)
    {D : Submodule ℂ Hs.carrier} (hdense : Dense (D : Set Hs.carrier)) :
    EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs ⊤ D n))
      (dGammaCoreOp Hs ⊤ B D) :=
  dGamma_essentiallySelfAdjointOn_fockCore Hs ⊤ B D
    (isGraphCore_of_bounded Hs B hC0 hC hdense)
    (essentiallySelfAdjointOn_fockSectorDom_bounded Hs B hB hC0 hC)

/-! ## An operator that is unbounded below

The scalar operator `-id` is symmetric with `‖-id‖ = 1`, and its second quantization is the
negative of the number operator, whose spectrum `{-n : n ∈ ℕ}` is unbounded below.  It is an
instance of the theorem above: nothing in the argument needs a spectral lower bound. -/

/-- The second quantization of `-id` — minus the number operator, which is unbounded below —
is essentially self-adjoint on the finite-particle domain over any dense subspace. -/
theorem dGamma_neg_id_essentiallySelfAdjointOn_fockCore {D : Submodule ℂ Hs.carrier}
    (hdense : Dense (D : Set Hs.carrier)) :
    EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs ⊤ D n))
      (dGammaCoreOp Hs ⊤ (BookProof.ScalarDGamma.scalarOp Hs (-1)) D) :=
  dGamma_bounded_essentiallySelfAdjointOn_fockCore Hs _
    (BookProof.ScalarDGamma.symmetricOn_scalarOp Hs (-1)) zero_le_one
    (fun a => by
      rw [BookProof.ScalarDGamma.scalarOp_apply, norm_smul]
      simp) hdense

end

end BookProof.BoundedDGamma
