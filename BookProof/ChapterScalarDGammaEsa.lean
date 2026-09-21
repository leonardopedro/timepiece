import Mathlib
import BookProof.ChapterSecondQuantizationCoreEsa

/-!
# An unconditional instance: second quantization of a scalar one-particle operator

The main theorem of `BookProof/ChapterSecondQuantizationCoreEsa.lean` carries one hypothesis,
sector by sector: essential self-adjointness of the derivation `dΓ(A)⁽ⁿ⁾` on the *full*
tensor power `D₂^{⊗n}` of the domain of the closure.  This module discharges that hypothesis
completely in a concrete family of examples — the **scalar** one-particle operators
`A = c • id` with `c : ℝ`, defined on all of `H` — and thereby produces an unconditional
statement of the second quantization theorem over an arbitrary dense core `D`:

> If `D ⊆ H` is any dense subspace, then `dΓ(c • id)` is essentially self-adjoint on the
> finite-particle domain `𝓕_fin(D)`.

Here `D` is a core for `c • id` but is in general *not* invariant under anything and carries
no resolvent; the passage from `H` to `D` is exactly the core transfer principle.  On the
`n`-particle sector the derivation is the scalar `n · c`, which is bounded, so the
sector hypothesis follows from the elementary criterion
`BookProof.GraphCore.essentiallySelfAdjointOn_of_bounded_dense`.

## Contents

* `scalarOp` — the one-particle operator `c • id` on `⊤`;
* `symmetricOn_scalarOp`, `isGraphCore_scalarOp` — it is symmetric, and every dense subspace
  is a core for it;
* `derPow_scalar` — the sector derivation of a scalar operator is the scalar `n · c`;
* `essentiallySelfAdjointOn_fockSectorDom_scalar` — the sector hypothesis, proved;
* `dGamma_scalar_essentiallySelfAdjointOn_fockCore` — **the unconditional theorem**.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.ScalarDGamma

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
  BookProof.SecondQuantizationCore BookProof.DirectSumEsa

noncomputable section

variable (Hs : IPSpace) (c : ℝ)

/-! ## The scalar one-particle operator -/

/-- The scalar one-particle operator `A = c • id`, defined on all of `H`. -/
def scalarOp : (⊤ : Submodule ℂ Hs.carrier) →ₗ[ℂ] Hs.carrier :=
  (c : ℂ) • (⊤ : Submodule ℂ Hs.carrier).subtype

@[simp] theorem scalarOp_apply (x : (⊤ : Submodule ℂ Hs.carrier)) :
    scalarOp Hs c x = (c : ℂ) • (x : Hs.carrier) := rfl

/-- A real scalar operator is symmetric. -/
theorem symmetricOn_scalarOp : SymmetricOn ⊤ (scalarOp Hs c) := by
  intro x y
  rw [scalarOp_apply, scalarOp_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal]

/-- **Every dense subspace is a core for a scalar operator.** -/
theorem isGraphCore_scalarOp {D : Submodule ℂ Hs.carrier}
    (hdense : Dense (D : Set Hs.carrier)) : IsGraphCore D (scalarOp Hs c) := by
  intro x ε hε
  have hden : (0 : ℝ) < 1 + |c| := by positivity
  have hpos : 0 < ε / (1 + |c|) := by positivity
  obtain ⟨y, hyD, hy⟩ := Metric.mem_closure_iff.mp (hdense (x : Hs.carrier)) _ hpos
  have hxy : ‖(x : Hs.carrier) - y‖ < ε / (1 + |c|) := by rw [← dist_eq_norm]; exact hy
  have hmul : (1 + |c|) * ‖(x : Hs.carrier) - y‖ < ε := by
    have := (mul_lt_mul_of_pos_left hxy hden)
    calc (1 + |c|) * ‖(x : Hs.carrier) - y‖ < (1 + |c|) * (ε / (1 + |c|)) := this
      _ = ε := by field_simp
  have hnn : 0 ≤ ‖(x : Hs.carrier) - y‖ := norm_nonneg _
  refine ⟨⟨y, trivial⟩, hyD, ?_, ?_⟩
  · nlinarith [abs_nonneg c]
  · have hEq : scalarOp Hs c x - scalarOp Hs c ⟨y, trivial⟩
        = (c : ℂ) • ((x : Hs.carrier) - y) := by
      simp only [scalarOp_apply]
      rw [smul_sub]
    rw [hEq, norm_smul]
    have hc : ‖(c : ℂ)‖ = |c| := by simp
    rw [hc]
    nlinarith

/-! ## The sector derivation of a scalar operator -/

/-- The sector derivation of the scalar operator `c • id` is the scalar `n · c`. -/
theorem derPow_scalar (n : ℕ) (x : ((domSpace Hs ⊤).pow n)) :
    derPow Hs ⊤ (scalarOp Hs c) n x = ((n : ℂ) * c) • inclPow Hs ⊤ n x := by
  induction n with
  | zero => simp [derPow]
  | succ n ih =>
      have hx : x ∈ Submodule.span ℂ
          {t : ((⊤ : Submodule ℂ Hs.carrier) ⊗[ℂ] ((domSpace Hs ⊤).pow n).carrier) |
            ∃ (p : (⊤ : Submodule ℂ Hs.carrier)) (q : ((domSpace Hs ⊤).pow n)),
              p ⊗ₜ[ℂ] q = t} := by
        rw [TensorProduct.span_tmul_eq_top]; trivial
      induction hx using Submodule.span_induction with
      | mem t ht =>
          obtain ⟨a, b, rfl⟩ := ht
          rw [derPow_tmul, inclPow_tmul, ih b, scalarOp_apply, TensorProduct.tmul_smul,
            TensorProduct.smul_tmul', TensorProduct.smul_tmul', ← TensorProduct.add_tmul,
            ← add_smul]
          have hcoef : (c : ℂ) + (n : ℂ) * c = ((n + 1 : ℕ) : ℂ) * c := by push_cast; ring
          rw [hcoef]
      | zero => simp
      | add s t _ _ hs ht => rw [map_add, map_add, hs, ht, smul_add]
      | smul r s _ hs => rw [map_smul, map_smul, hs, smul_comm]

/-! ## The sector domain is everything -/

/-- With the full domain `⊤`, the inclusion of tensor powers is surjective. -/
theorem inclPow_top_surjective (n : ℕ) : Function.Surjective (inclPow Hs ⊤ n) := by
  induction n with
  | zero => exact fun x => ⟨x, rfl⟩
  | succ n ih =>
      have h1 : Function.Surjective ((⊤ : Submodule ℂ Hs.carrier).subtype) :=
        fun x => ⟨⟨x, trivial⟩, rfl⟩
      exact TensorProduct.map_surjective h1 ih

theorem sectorDom_top (n : ℕ) : sectorDom Hs ⊤ n = ⊤ :=
  LinearMap.range_eq_top.mpr (inclPow_top_surjective Hs n)

/-- The sector derivation of a scalar operator, seen inside `H^{⊗n}`, is the scalar
`n · c`. -/
theorem sectorOp_scalar (n : ℕ) (x : sectorDom Hs ⊤ n) :
    sectorOp Hs ⊤ (scalarOp Hs c) n x = ((n : ℂ) * c) • (x : (Hs.pow n).carrier) := by
  obtain ⟨x₀, hx₀⟩ := x.2
  have hx : (x : (Hs.pow n).carrier) = inclPow Hs ⊤ n x₀ := hx₀.symm
  rw [sectorOp_apply Hs ⊤ _ n x x₀ hx, derPow_scalar, hx]

/-! ## The sector hypothesis, discharged -/

/-- The domain of the sector derivation is dense in the completed sector. -/
theorem dense_fockSectorDom (n : ℕ) :
    Dense ((fockSectorDom Hs ⊤ n : Submodule ℂ (fockSector Hs n)) :
      Set (fockSector Hs n)) := by
  have h : ((fockSectorDom Hs ⊤ n : Submodule ℂ (fockSector Hs n)) : Set (fockSector Hs n))
      = Set.range (sectorEmb Hs n) := by
    rw [fockSectorDom, sectorDom_top, pushDom, Submodule.map_top, LinearMap.coe_range]
    rfl
  rw [h]
  exact UniformSpace.Completion.denseRange_coe

/-- The sector derivation of a scalar operator is bounded, with bound `n · |c|`. -/
theorem norm_fockSectorOp_scalar_le (n : ℕ) (x : fockSectorDom Hs ⊤ n) :
    ‖fockSectorOp Hs ⊤ (scalarOp Hs c) n x‖ ≤ ((n : ℝ) * |c|) * ‖(x : fockSector Hs n)‖ := by
  obtain ⟨x₀, hx₀, hxe⟩ := x.2
  have hx' : (x : fockSector Hs n) = sectorEmb Hs n ((⟨x₀, hx₀⟩ : sectorDom Hs ⊤ n) :
      (Hs.pow n).carrier) := hxe.symm
  have hop : fockSectorOp Hs ⊤ (scalarOp Hs c) n x
      = sectorEmb Hs n (sectorOp Hs ⊤ (scalarOp Hs c) n ⟨x₀, hx₀⟩) :=
    pushOp_apply (sectorEmb Hs n) (sectorOp Hs ⊤ (scalarOp Hs c) n) x ⟨x₀, hx₀⟩ hx'
  rw [hop, (sectorEmb Hs n).norm_map, hx', (sectorEmb Hs n).norm_map,
    sectorOp_scalar Hs c n ⟨x₀, hx₀⟩, norm_smul]
  have hc : ‖((n : ℂ) * c)‖ = (n : ℝ) * |c| := by
    rw [norm_mul]
    simp
  rw [hc]

/-- **The sector hypothesis for a scalar one-particle operator.**  On the `n`-particle
sector the derivation acts as the bounded scalar `n · c` on a dense domain, hence is
essentially self-adjoint there. -/
theorem essentiallySelfAdjointOn_fockSectorDom_scalar (n : ℕ) :
    EssentiallySelfAdjointOn (fockSectorDom Hs ⊤ n) (fockSectorOp Hs ⊤ (scalarOp Hs c) n) :=
  essentiallySelfAdjointOn_of_bounded_dense _
    (symmetricOn_fockSectorOp Hs ⊤ (scalarOp Hs c) (symmetricOn_scalarOp Hs c) n)
    (by positivity) (norm_fockSectorOp_scalar_le Hs c n) (dense_fockSectorDom Hs n)

/-! ## The unconditional theorem -/

/-- **Unconditional second quantization over a core.**  For the scalar one-particle operator
`A = c • id` and *any* dense subspace `D ⊆ H`, the second quantization `dΓ(A)` is essentially
self-adjoint on the finite-particle domain `𝓕_fin(D)` built from `D` alone.  No hypothesis is
carried: the sector statement is proved, and the passage from `H` to the core `D` is the core
transfer principle. -/
theorem dGamma_scalar_essentiallySelfAdjointOn_fockCore {D : Submodule ℂ Hs.carrier}
    (hdense : Dense (D : Set Hs.carrier)) :
    EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs ⊤ D n))
      (dGammaCoreOp Hs ⊤ (scalarOp Hs c) D) :=
  dGamma_essentiallySelfAdjointOn_fockCore Hs ⊤ (scalarOp Hs c) D
    (isGraphCore_scalarOp Hs c hdense)
    (essentiallySelfAdjointOn_fockSectorDom_scalar Hs c)

end

end BookProof.ScalarDGamma
