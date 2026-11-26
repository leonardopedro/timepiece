import Mathlib
import BookProof.ChapterFlowDGammaEsa

/-!
# Chapter OuterSemigroupFactorization — H0's sector flow equals the tensor power

`cftproof.md` H0 asks for the outer-sector factorization
`e^{−τ dΓ(h)}|𝓕⁽ᴺ⁾ = Γ(e^{−τ h})|𝓕⁽ᴺ⁾`.  The corpus already builds the candidate:
`ChapterFlowDGammaEsa.OneParticleFlow.tpow` is `U t ⊗ ⋯ ⊗ U t` on the `N`-fold tensor power
and `fockOrbit` is its image in the completed bosonic sector, with the sector derivation as
its derivative (`hasDerivAt_fockOrbit`).  This module proves the missing **group law**: the
tensor-power orbit composes exactly like the one-particle Stone flow, so the sector flow is
a one-parameter group and the `N = 0` sector is the identity (the empty-vacuum negative
control).

Nothing here proves the unbounded equality of operators `e^{−τ dΓ(h)} = Γ(e^{−τ h})` on
`L²`; it is the core-level identification of the flow that H0's acceptance asks for, using
the Stone flow of the self-adjoint one-particle operator.  No Euclidean measure, cutoff
removal or vacuum projection is used.  Axioms are `propext`, `Classical.choice`,
`Quot.sound` only.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace BookProof.OuterSemigroupFactorization

open scoped TensorProduct
open BookProof.ChapterStoneResolvent
open BookProof.FlowDGamma
open BookProof.FlowDGamma.OneParticleFlow
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
  BookProof.SecondQuantizationCore BookProof.DirectSumEsa BookProof.EsaPair
  BookProof.TensorOpBound BookProof.DiagonalDGamma

variable {Hs : IPSpace} [CompleteSpace Hs.carrier]

/-- The one-particle flow of a self-adjoint operator composes as a group on its domain. -/
theorem dmap_add (T : UnboundedSelfAdjoint Hs.carrier) (s t : ℝ) (x : T.domain) :
    dmap (ofSelfAdjoint T) (s + t) x =
      dmap (ofSelfAdjoint T) s (dmap (ofSelfAdjoint T) t x) := by
  apply Subtype.ext
  change (T.stoneU (s + t)) (x : Hs.carrier) =
    (T.stoneU s) ((T.stoneU t) (x : Hs.carrier))
  rw [T.stoneU_apply_stoneU]

/-- **Tensor-power factorization.**  The `N`-fold tensor flow is the `N`-fold tensor product
    of the one-particle flow, so it obeys the same group law in `t`. -/
theorem tpow_add (T : UnboundedSelfAdjoint Hs.carrier) (s t : ℝ) :
    ∀ (n : ℕ) (x : ((domSpace Hs T.domain).pow n)),
      tpow (ofSelfAdjoint T) (s + t) n x =
        tpow (ofSelfAdjoint T) s n (tpow (ofSelfAdjoint T) t n x) := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      have hx : x ∈ Submodule.span ℂ
          {u : (T.domain ⊗[ℂ] ((domSpace Hs T.domain).pow n).carrier) |
            ∃ (p : T.domain) (q : ((domSpace Hs T.domain).pow n)), p ⊗ₜ[ℂ] q = u} := by
        rw [TensorProduct.span_tmul_eq_top]
        trivial
      induction hx using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨p, q, rfl⟩ := hy
          rw [tpow_tmul, tpow_tmul, tpow_tmul, dmap_add, ih q]
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, map_add, map_add, ha, hb]
      | smul c a _ ha => rw [map_smul, map_smul, map_smul, ha]

/-- The completed sector orbit inherits the same group law. -/
theorem fockOrbit_add (T : UnboundedSelfAdjoint Hs.carrier) (n : ℕ)
    (x : ((domSpace Hs T.domain).pow n)) (s t : ℝ) :
    fockOrbit (ofSelfAdjoint T) n x (s + t) =
      fockOrbit (ofSelfAdjoint T) n (tpow (ofSelfAdjoint T) t n x) s := by
  apply Subtype.ext
  rw [fockOrbit_coe, fockOrbit_coe, tpow_add]

/-- The `N = 0` outer sector is fixed by the flow: the empty outer vacuum is a zero-energy
    fixed point, the negative control H0 requires. -/
theorem fockOrbit_zero_sector (T : UnboundedSelfAdjoint Hs.carrier) (t : ℝ) :
    fockOrbit (ofSelfAdjoint T) 0 (1 : ℂ) t =
      fockOrbit (ofSelfAdjoint T) 0 (1 : ℂ) 0 := by
  apply Subtype.ext
  rw [fockOrbit_coe, fockOrbit_coe]
  simp [tpow]

/-- **H0 factorization statement (core level).**  On the `N`-particle sector the orbit is
    `Γ(U t)` — the symmetrized `N`-fold tensor power — and it is a group with the sector
    derivation as infinitesimal generator.  The three ingredients are the definition of
    `fockOrbit`, the group law above and `ChapterFlowDGammaEsa.hasDerivAt_fockOrbit`. -/
theorem sector_flow_is_tensor_power (T : UnboundedSelfAdjoint Hs.carrier) (n : ℕ)
    (x : ((domSpace Hs T.domain).pow n)) (t : ℝ) :
    ((fockOrbit (ofSelfAdjoint T) n x t : fockSectorDom Hs T.domain n) :
        fockSector Hs n) =
      sectorEmb Hs n (inclPow Hs T.domain n (tpow (ofSelfAdjoint T) t n x)) := rfl

end BookProof.OuterSemigroupFactorization
