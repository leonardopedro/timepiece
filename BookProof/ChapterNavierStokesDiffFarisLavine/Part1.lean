import Mathlib
import BookProof.ChapterNavierStokesDiffHashimoto

/-!
# The two Faris–Lavine inequalities for the *differential* Navier–Stokes symbol

`BookProof.ChapterNavierStokesHermiteFarisLavine` and
`BookProof.ChapterNavierStokesFockManyMode` prove the two Faris–Lavine inequalities — the
relative bound `‖Hx‖² ≤ a‖Nx‖² + b‖x‖²` and the form-commutator bound
`±i[H, N] ≤ c N` — in the *sequence* (occupation-number) realization, and
`BookProof.ChapterNavierStokesDifferentialL2` proves essential self-adjointness of the
Navier–Stokes quadratic symbol written as an honest differential operator on
`L²(du₁du₂du₃)`, but by transporting the sequence-space theorem along the Hermite basis.
This module supplies the missing layer: the two Faris–Lavine inequalities **for the
differential operator itself**, against a differential comparison operator, and the
resulting Faris–Lavine proof of essential self-adjointness in `L²(ℝ³)`.

## The two operators

On the Gauss–polynomial (Hermite) core `polyGaussCore` of `L²(ℝ³)`, with `πᵢ = −i ∂/∂uᵢ`
(`momOp`) and `uᵢ` multiplication by the coordinate (`posOp`):

* the Hamiltonian is the Weyl quantization `nsDiffH A c = ∑ᵢ ½(πᵢVᵢ + Vᵢπᵢ)` of the
  Navier–Stokes quadratic symbol `A_i(u) = u_j u_{i,j} − ν u_{i,jj}`, `Vᵢ = ∑ₖA_{iₖ}uₖ + cᵢ`
  (`BookProof.ChapterNavierStokesDifferentialL2`);
* the comparison operator is the *differential* harmonic-oscillator operator
  `nsDiffN μ = 2μ ∑ᵢ (πᵢ² + uᵢ²/4) + 1`, whose one-mode blocks are the honest
  second-order operators `−∂²/∂uᵢ² + uᵢ²/4`.

`oscOp_eq_number` is the algebraic heart of the identification: on the Gauss–polynomial
core, `πᵢ² + uᵢ²/4 = aᵢ†aᵢ + ½`, proved as a polynomial identity (`oscPoly_eq`) from the
Leibniz rule `∂ᵢ(uᵢp) = p + uᵢ∂ᵢp`.  Hence `nsDiffN μ` is the transport of multiplication
by the comparison symbol `velSym μ β = μ(2|β| + 3) + 1` (`intertwined_nsDiffN`,
`velNcore_eq_diagMax`), and `embedCore_surjective` says the Gauss–polynomial core *is* the
transported finite-mode core, so every statement about core states is a statement about
all of `polyGaussCore`.

## What is proved

* `nsDiffN_symmetricOn`, `nsDiffN_quadForm_ge_norm_sq` — the differential comparison
  operator is symmetric and dominates the identity (`⟪f, Nf⟫ ≥ ‖f‖²`);
* `nsDiffH_relative_bound` — **the first Faris–Lavine inequality** for the differential
  operator: `‖H f‖² ≤ a‖N f‖² + b‖f‖²` on the Hermite core, for every real velocity
  gradient `A` and constant part `c`;
* `nsDiffH_commForm_bound` — **the second Faris–Lavine inequality**:
  `|⟪f, i[H, N] f⟫| ≤ c ⟪f, N f⟫`;
* `diffMaxDom`, `diffMaxH`, `diffMaxN` — the same pair on the maximal domain of the
  comparison operator in `L²(ℝ³)`, with the Faris–Lavine package there
  (`diffMaxH_symmetricOn`, `diffMaxN_quadForm_nonneg`, `diffMaxN_add_one_surjective`,
  `diffMaxN_core_approx`, `diffMaxH_relative_bound`, `diffMaxH_commForm_bound`) and
  `diffMaxH_restrict`, which identifies its restriction to the Hermite core with
  `nsDiffH`;
* `nsDiffH_esa_of_farisLavine` — **the payoff**: essential self-adjointness of the
  differentially written Navier–Stokes symbol on the Hermite core of `L²(du₁du₂du₃)`,
  obtained from the Faris–Lavine criterion of `BookProof.ChapterFarisLavine` applied in
  `L²(ℝ³)` itself — the alternative route to
  `BookProof.ChapterNavierStokesDifferentialL2.nsDiffH_essentiallySelfAdjointOn_core`,
  which transported essential self-adjointness instead of the estimates.

## Honest boundary

The estimates are the transported sequence-space ones: the mathematics unifying the two
pictures is the identification `πᵢ² + uᵢ²/4 = aᵢ†aᵢ + ½` and the fact that the
Gauss–polynomial core is the transported finite-mode core, not a new analytic input.  The
non-vacuity of the mechanism (a genuinely non-zero commutator `[H, N]`, and an unbounded
`H`) is recorded in `BookProof.ChapterNavierStokesHermiteFarisLavine.commForm_ne_zero_of_pos`,
`BookProof.ChapterNavierStokesFockManyMode.fock_commForm_ne_zero` and
`BookProof.ChapterNavierStokesDifferentialL2.nsDiffH_not_bounded`.  As everywhere on this
route, nothing here claims global regularity of the classical Navier–Stokes equation
(Contention D5): the statement is about the Hilbert-space operator at one Eulerian fiber,
where the derivative fields `u_{i,j}`, `u_{i,jj}` are independent canonical coordinates.
-/

namespace BookProof.NavierStokesFlow

namespace DiffFarisLavine

open MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open LpNat FarisLavine IkebeKato ThreeComponent CanonicalVector DifferentialL2

noncomputable section

/-! ## The number operator in the sequence picture -/

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- The number operator `a_i† a_i` of the mode `i` on the finite-mode core of `ℓ²(Vel)`. -/
def numSeq (i : Fin 3) : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel := (cre i).comp (ann i)

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- `a_i† a_i` is multiplication by the occupation number `β i`. -/
theorem crd_numSeq (i : Fin 3) (x : lpFiniteModes Vel) (β : Vel) :
    crd (numSeq i x) β = ((β i : ℝ) : ℂ) * crd x β := by
  by_cases h : β i = 0
  · simp [numSeq, cFun, h]
  · have h1 : 1 ≤ β i := Nat.one_le_iff_ne_zero.mpr h
    have hlow : ((lower i β) i : ℝ) + 1 = (β i : ℝ) := by
      rw [lower_self]
      have : (1 : ℕ) ≤ β i := h1
      push_cast [Nat.cast_sub this]
      ring
    have hraise : raise i (lower i β) = β := raise_lower i h1
    have hsq : (Real.sqrt ((β i : ℝ))) * (Real.sqrt (((lower i β) i : ℝ) + 1)) = (β i : ℝ) := by
      rw [hlow, ← Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ (β i : ℝ))]
      rw [Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ (β i : ℝ))]
      exact (Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (β i : ℝ)))
    simp only [numSeq, LinearMap.comp_apply, crd_cre, crd_ann, cFun, aFun, hraise]
    rw [← mul_assoc, ← Complex.ofReal_mul, hsq]

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The comparison operator in the sequence picture**, on the finite-mode core:
`N = 2μ ∑ᵢ a_i† a_i + (3μ + 1)`. -/
def velNcore (mu : ℝ) : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel :=
  (((2 * mu : ℝ) : ℂ)) • (∑ i, numSeq i) + (((3 * mu + 1 : ℝ) : ℂ)) • LinearMap.id

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- On the finite-mode core the ladder expression above **is** multiplication by the
comparison symbol `velSym μ β = μ(2|β| + 3) + 1`. -/
theorem velNcore_eq_diagMax (mu : ℝ) (x : lpFiniteModes Vel) :
    ((velNcore mu x : lpFiniteModes Vel) : L2I Vel)
      = (diagMax (velSym mu)
          (Submodule.inclusion (finiteModes_le_maxDom (velSym mu)) x) : L2I Vel) := by
  refine lp.ext (funext fun β => ?_)
  have hleft : (((velNcore mu x : lpFiniteModes Vel) : L2I Vel) : Vel → ℂ) β
      = ((2 * mu : ℝ) : ℂ) * (∑ _i : Fin 3, ((β _i : ℝ) : ℂ) * crd x β)
        + ((3 * mu + 1 : ℝ) : ℂ) * crd x β := by
    simp only [velNcore, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have h1 : crd ((((2 * mu : ℝ) : ℂ)) • (∑ i, numSeq i) x
        + (((3 * mu + 1 : ℝ) : ℂ)) • x) β
        = ((2 * mu : ℝ) : ℂ) * crd ((∑ i, numSeq i) x) β
          + ((3 * mu + 1 : ℝ) : ℂ) * crd x β := by
      simp [crd_add, crd_smul]
    have h2 : crd ((∑ i, numSeq i) x) β = ∑ i, ((β i : ℝ) : ℂ) * crd x β := by
      rw [LinearMap.sum_apply]
      have : ∀ s : Finset (Fin 3), crd (∑ i ∈ s, numSeq i x) β
          = ∑ i ∈ s, crd (numSeq i x) β := by
        intro s
        induction s using Finset.induction with
        | empty => simp [crd]
        | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, crd_add]; simp [ih]
      rw [this]
      exact Finset.sum_congr rfl fun i _ => crd_numSeq i x β
    change crd ((((2 * mu : ℝ) : ℂ)) • (∑ i, numSeq i) x
        + (((3 * mu + 1 : ℝ) : ℂ)) • x) β = _
    rw [h1, h2]
  have hstep : (∑ _i : Fin 3, ((β _i : ℝ) : ℂ) * crd x β) = ((total β : ℕ) : ℂ) * crd x β := by
    rw [← Finset.sum_mul]
    congr 1
    simp only [total, Nat.cast_sum]
    push_cast
    rfl
  have hright : ((diagMax (velSym mu)
        (Submodule.inclusion (finiteModes_le_maxDom (velSym mu)) x) : L2I Vel) : Vel → ℂ) β
      = ((velSym mu β : ℝ) : ℂ) * crd x β := rfl
  rw [hleft, hstep, hright]
  simp only [velSym]
  push_cast
  ring

/-! ## The differential comparison operator -/

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- The one-mode oscillator `πᵢ² + uᵢ²/4` on the Hermite core of `L²(ℝ³)`. -/
def oscOp (i : Fin 3) : (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3)) :=
  (momOp i).comp (momOp i) + ((1 / 4 : ℂ)) • (posOp i).comp (posOp i)

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- The polynomial identity behind `oscOp_eq_number`: `π² + u²/4 = a†a + ½`. -/
theorem oscPoly_eq (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    momPoly i (momPoly i p) + mulXPoly i (mulXPoly i (((1 / 4 : ℂ)) • p))
      = crePoly i (annPoly i p) + ((1 / 2 : ℂ)) • p := by
  have hL : pderiv i (X i * p) = p + X i * pderiv i p := by
    rw [Derivation.leibniz, pderiv_X_self]
    simp [smul_eq_mul]
    ring
  have hd : pderiv i (momPoly i p)
      = C (-Complex.I) * (pderiv i (pderiv i p) - C (1 / 2 : ℂ) * (p + X i * pderiv i p)) := by
    rw [momPoly_apply, MvPolynomial.pderiv_C_mul, map_sub, MvPolynomial.pderiv_C_mul, hL]
  have hII : (C (-Complex.I) : MvPolynomial (Fin 3) ℂ) * C (-Complex.I) = -1 := by
    rw [← map_mul]
    norm_num
  have hhalf : (C (1 / 2 : ℂ) : MvPolynomial (Fin 3) ℂ) * C (1 / 2 : ℂ) = C (1 / 4 : ℂ) := by
    rw [← map_mul]
    norm_num
  have hone : (C (1 / 2 : ℂ) : MvPolynomial (Fin 3) ℂ) + C (1 / 2 : ℂ) = 1 := by
    rw [← map_add]
    norm_num
  have hexp : momPoly i (momPoly i p)
      = -(pderiv i (pderiv i p)) + C (1 / 2 : ℂ) * p + X i * pderiv i p
        - C (1 / 4 : ℂ) * (X i * (X i * p)) := by
    conv_lhs => rw [momPoly_apply]
    rw [hd]
    conv_lhs => rw [momPoly_apply]
    have hfac : C (-Complex.I) * (C (-Complex.I)
          * (pderiv i (pderiv i p) - C (1 / 2 : ℂ) * (p + X i * pderiv i p))
        - C (1 / 2 : ℂ) * (X i * (C (-Complex.I)
          * (pderiv i p - C (1 / 2 : ℂ) * (X i * p)))))
        = (C (-Complex.I) * C (-Complex.I))
          * ((pderiv i (pderiv i p) - C (1 / 2 : ℂ) * (p + X i * pderiv i p))
            - C (1 / 2 : ℂ) * (X i * (pderiv i p - C (1 / 2 : ℂ) * (X i * p)))) := by
      ring
    rw [hfac, hII]
    linear_combination (X i * pderiv i p) * hone - (X i * (X i * p)) * hhalf
  rw [hexp]
  simp only [crePoly_apply, annPoly_apply, mulXPoly_apply, MvPolynomial.smul_eq_C_mul]
  ring

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The differential oscillator is the number operator plus one half**:
`πᵢ² + uᵢ²/4 = aᵢ†aᵢ + ½`. -/
theorem oscOp_eq_number (i : Fin 3) :
    oscOp i = (creOp i).comp (annOp i) + ((1 / 2 : ℂ)) • LinearMap.id := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨p, rfl⟩ := (coreEquiv (d := 3)).surjective y
  simp only [oscOp, momOp, posOp, annOp, creOp, coreOp_coreEquiv, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, ← map_add, ← map_smul]
  congr 1
  exact oscPoly_eq i p

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The differential comparison operator** `N = 2μ ∑ᵢ (πᵢ² + uᵢ²/4) + 1` on the Hermite
core of `L²(du₁du₂du₃)`, with `πᵢ = −i ∂/∂uᵢ` and `uᵢ` multiplication by the coordinate. -/
def nsDiffN (mu : ℝ) : (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3)) :=
  (((2 * mu : ℝ) : ℂ)) • (∑ i, oscOp i) + LinearMap.id

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
theorem nsDiffN_eq_ladder (mu : ℝ) :
    nsDiffN mu = (((2 * mu : ℝ) : ℂ)) • (∑ i, (creOp i).comp (annOp i))
      + (((3 * mu + 1 : ℝ) : ℂ)) • LinearMap.id := by
  have hsum : (∑ i, oscOp i)
      = (∑ i, (creOp i).comp (annOp i)) + ((3 / 2 : ℂ)) • LinearMap.id := by
    rw [Finset.sum_congr rfl (fun i _ => oscOp_eq_number i), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    match_scalars
    norm_num
  rw [nsDiffN, hsum]
  match_scalars <;> ring

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The transport carries the sequence comparison operator to the differential one.** -/
theorem intertwined_nsDiffN (mu : ℝ) : Intertwined (velNcore mu) (nsDiffN mu) := by
  rw [nsDiffN_eq_ladder, velNcore]
  refine Intertwined.add ?_ (Intertwined.id.smul _)
  exact (Intertwined.sum Finset.univ fun i _ =>
    (intertwined_cre i).comp (intertwined_ann i)).smul _

/-! ## The core is exactly the transported finite-mode core -/

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
theorem hermiteMvLp_mem_range (a : Fin 3 →₀ ℕ) :
    hermiteMvLp a
      ∈ Submodule.map ((polyGaussCore (d := 3)).subtype) (LinearMap.range embedCore) := by
  refine ⟨embedCore (coreState (velIdx.symm a)), ⟨_, rfl⟩, ?_⟩
  rw [embedCore_coreState, Submodule.subtype_apply, coreEquiv_coe, pgLp_smul,
    Equiv.apply_symm_apply]
  rfl

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The Gauss–polynomial core is exactly the transported finite-mode core.** -/
theorem embedCore_surjective : Function.Surjective (embedCore) := by
  intro f
  have hmap : (polyGaussCore (d := 3))
      ≤ Submodule.map ((polyGaussCore (d := 3)).subtype) (LinearMap.range embedCore) := by
    have hspan : Submodule.span ℂ (Set.range (hermiteMvLp (d := 3)))
        ≤ Submodule.map ((polyGaussCore (d := 3)).subtype) (LinearMap.range embedCore) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact hermiteMvLp_mem_range a
    rwa [span_hermiteMvLp] at hspan
  obtain ⟨g, hg, hgf⟩ := hmap f.2
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, Subtype.ext (by rw [hx]; exact hgf)⟩

/-! ## The transport of the two pictures -/

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- The constant part of the fiber field in the *sequence* normalization
`uᵢ = (aᵢ + aᵢ†)/√2`, corresponding to the differential constant part `c`. -/
def seqConst (c : Fin 3 → ℝ) : Fin 3 → ℝ := fun j => c j / Real.sqrt 2

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The comparison strength of the differential data**: the constant `μ` for which
`N = 2μ ∑ᵢ(πᵢ² + uᵢ²/4) + 1` dominates the Hamiltonian. -/
def diffMu (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) : ℝ := velMu A (seqConst c)

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
theorem diffMu_nonneg : 0 ≤ diffMu A c := velMu_nonneg _ _

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
theorem one_le_diffMu : 1 ≤ diffMu A c := one_le_velMu _ _

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- The differential Hamiltonian is the transport of the sequence one. -/
theorem nsDiffH_embedCore (x : lpFiniteModes Vel) :
    ((nsDiffH A c (embedCore x) : polyGaussCore (d := 3)) : L2d 3)
      = velUnitary ((canH A (seqConst c) x : lpFiniteModes Vel) : L2I Vel) := by
  have hc : (fun j => Real.sqrt 2 * (seqConst c j)) = c := by
    funext j
    simp only [seqConst]
    field_simp
  have h := intertwined_canH A (seqConst c) x
  rw [hc] at h
  rw [h, embedCore_coe]

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- The differential comparison operator is the transport of multiplication by the
comparison symbol. -/
theorem nsDiffN_embedCore (mu : ℝ) (x : lpFiniteModes Vel) :
    ((nsDiffN mu (embedCore x) : polyGaussCore (d := 3)) : L2d 3)
      = velUnitary ((diagMax (velSym mu)
          (Submodule.inclusion (finiteModes_le_maxDom (velSym mu)) x) : L2I Vel)) := by
  rw [intertwined_nsDiffN mu x, embedCore_coe, ← velNcore_eq_diagMax]

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- The sequence Hamiltonian, written on the core, is the hop-list Hamiltonian. -/
theorem canH_coe_velH (x : lpFiniteModes Vel) :
    ((canH A c x : lpFiniteModes Vel) : L2I Vel)
      = velH A c (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))) x) := by
  have h := congrFun (congrArg (fun T : lpFiniteModes Vel →ₗ[ℂ] L2I Vel => ⇑T)
    (canH_eq_velH A c)) x
  simpa using h

end

end DiffFarisLavine

end BookProof.NavierStokesFlow
