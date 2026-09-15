import Mathlib
import BookProof.ChapterNavierStokesDiffHashimoto
import BookProof.ChapterNavierStokesDiffFarisLavine.Part1

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

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
/-! ## The Faris–Lavine package in the differential picture -/

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The differential comparison operator is symmetric** on the Hermite core. -/
theorem nsDiffN_symmetricOn (mu : ℝ) :
    SymmetricOn (polyGaussCore (d := 3))
      ((polyGaussCore (d := 3)).subtype.comp (nsDiffN mu)) := by
  intro f g
  obtain ⟨x, rfl⟩ := embedCore_surjective f
  obtain ⟨y, rfl⟩ := embedCore_surjective g
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  rw [nsDiffN_embedCore, nsDiffN_embedCore, embedCore_coe, embedCore_coe,
    velUnitary.inner_map_map, velUnitary.inner_map_map]
  exact diagMax_symmetricOn (velSym mu) (Submodule.inclusion (finiteModes_le_maxDom (velSym mu)) x)
    (Submodule.inclusion (finiteModes_le_maxDom (velSym mu)) y)

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- The quadratic form of the differential comparison operator is the sequence one. -/
theorem quadForm_nsDiffN_embedCore (mu : ℝ) (x : lpFiniteModes Vel) :
    quadForm ((polyGaussCore (d := 3)).subtype.comp (nsDiffN mu)) (embedCore x)
      = quadForm (diagMax (velSym mu))
          (Submodule.inclusion (finiteModes_le_maxDom (velSym mu)) x) := by
  simp only [quadForm, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [nsDiffN_embedCore, embedCore_coe, velUnitary.inner_map_map]
  rfl

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The differential comparison operator dominates the identity**: `⟪f, N f⟫ ≥ ‖f‖²`. -/
theorem nsDiffN_quadForm_ge_norm_sq (mu : ℝ) (hmu : 0 ≤ mu) (f : polyGaussCore (d := 3)) :
    ‖(f : L2d 3)‖ ^ 2
      ≤ quadForm ((polyGaussCore (d := 3)).subtype.comp (nsDiffN mu)) f := by
  obtain ⟨x, rfl⟩ := embedCore_surjective f
  rw [quadForm_nsDiffN_embedCore, embedCore_coe, velUnitary.norm_map]
  exact diagMax_quadForm_ge_norm_sq (velSym mu) (fun β => velSym_ge_one hmu β)
    (Submodule.inclusion (finiteModes_le_maxDom (velSym mu)) x)

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- The commutator form of the differential pair is the sequence one. -/
theorem commForm_embedCore (x : lpFiniteModes Vel) :
    commForm ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c))
        ((polyGaussCore (d := 3)).subtype.comp (nsDiffN (velMu A (seqConst c)))) (embedCore x)
      = commForm (velH A (seqConst c)) (diagMax (velSym (velMu A (seqConst c))))
          (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A (seqConst c)))) x) := by
  simp only [commForm, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [nsDiffH_embedCore, nsDiffN_embedCore, canH_coe_velH, velUnitary.inner_map_map,
    velUnitary.inner_map_map]

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The first Faris–Lavine inequality for the differential Navier–Stokes symbol**:
`‖H f‖² ≤ a‖N f‖² + b‖f‖²` on the Hermite core of `L²(du₁du₂du₃)`. -/
theorem nsDiffH_relative_bound :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ f : polyGaussCore (d := 3),
      ‖((nsDiffH A c f : polyGaussCore (d := 3)) : L2d 3)‖ ^ 2
        ≤ a * ‖((nsDiffN (diffMu A c) f : polyGaussCore (d := 3)) : L2d 3)‖ ^ 2
          + b * ‖(f : L2d 3)‖ ^ 2 := by
  obtain ⟨a, b, ha, hb, hbound⟩ :=
    SignedShift.listH_relative_bound (hopList A (seqConst c))
  refine ⟨a, b, ha, hb, fun f => ?_⟩
  obtain ⟨x, rfl⟩ := embedCore_surjective f
  have hx := hbound (Submodule.inclusion (finiteModes_le_maxDom (velSym (diffMu A c))) x)
  rw [nsDiffH_embedCore, nsDiffN_embedCore, canH_coe_velH, embedCore_coe,
    velUnitary.norm_map, velUnitary.norm_map, velUnitary.norm_map]
  exact hx

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The second Faris–Lavine inequality for the differential Navier–Stokes symbol**:
`|⟪f, i[H, N] f⟫| ≤ c ⟪f, N f⟫` on the Hermite core of `L²(du₁du₂du₃)`. -/
theorem nsDiffH_commForm_bound :
    ∃ cst : ℝ, 0 ≤ cst ∧ ∀ f : polyGaussCore (d := 3),
      |commForm ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c))
          ((polyGaussCore (d := 3)).subtype.comp (nsDiffN (diffMu A c))) f|
        ≤ cst * quadForm ((polyGaussCore (d := 3)).subtype.comp (nsDiffN (diffMu A c))) f := by
  obtain ⟨cst, hcst, hbound⟩ :=
    SignedShift.listH_commForm_bound (hopList A (seqConst c))
      (fun β => velSym_ge_one (velMu_nonneg A (seqConst c)) β)
  refine ⟨cst, hcst, fun f => ?_⟩
  obtain ⟨x, rfl⟩ := embedCore_surjective f
  simp only [diffMu]
  rw [commForm_embedCore, quadForm_nsDiffN_embedCore]
  exact hbound _

/-! ## Essential self-adjointness by the Faris–Lavine criterion, in `L²(du₁du₂du₃)` -/

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The maximal domain of the differential comparison operator** in `L²(ℝ³)`. -/
def diffMaxDom (mu : ℝ) : Submodule ℂ (L2d 3) :=
  Submodule.map (velUnitary.toLinearEquiv : L2I Vel →ₗ[ℂ] L2d 3) (maxDom (velSym mu))

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- The maximal domain of `L²(ℝ³)` is the unitary image of the sequence one. -/
def diffMaxEquiv (mu : ℝ) : maxDom (velSym mu) ≃ₗ[ℂ] diffMaxDom mu :=
  (velUnitary.toLinearEquiv).submoduleMap (maxDom (velSym mu))

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
theorem diffMaxEquiv_coe (mu : ℝ) (z : maxDom (velSym mu)) :
    ((diffMaxEquiv mu z : diffMaxDom mu) : L2d 3) = velUnitary ((z : L2I Vel)) := rfl

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The differential comparison operator on its maximal domain.** -/
def diffMaxN (mu : ℝ) : diffMaxDom mu →ₗ[ℂ] L2d 3 :=
  (velUnitary.toLinearEquiv : L2I Vel →ₗ[ℂ] L2d 3).comp
    ((diagMax (velSym mu)).comp (diffMaxEquiv mu).symm.toLinearMap)

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The differential Navier–Stokes Hamiltonian on the maximal domain** of the
comparison operator. -/
def diffMaxH : diffMaxDom (velMu A (seqConst c)) →ₗ[ℂ] L2d 3 :=
  (velUnitary.toLinearEquiv : L2I Vel →ₗ[ℂ] L2d 3).comp
    ((velH A (seqConst c)).comp (diffMaxEquiv (velMu A (seqConst c))).symm.toLinearMap)

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
theorem diffMaxN_apply (mu : ℝ) (z : maxDom (velSym mu)) :
    diffMaxN mu (diffMaxEquiv mu z) = velUnitary ((diagMax (velSym mu) z : L2I Vel)) := by
  simp only [diffMaxN, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
theorem diffMaxH_apply (z : maxDom (velSym (velMu A (seqConst c)))) :
    diffMaxH A c (diffMaxEquiv (velMu A (seqConst c)) z)
      = velUnitary ((velH A (seqConst c) z : L2I Vel)) := by
  simp only [diffMaxH, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- The Hermite core sits inside the maximal domain. -/
theorem polyGaussCore_le_diffMaxDom (mu : ℝ) : (polyGaussCore (d := 3)) ≤ diffMaxDom mu := by
  intro v hv
  obtain ⟨x, hx⟩ := embedCore_surjective ⟨v, hv⟩
  refine ⟨(x : L2I Vel), finiteModes_le_maxDom (velSym mu) x.2, ?_⟩
  have hcoe := congrArg (fun w : polyGaussCore (d := 3) => (w : L2d 3)) hx
  simpa [embedCore_coe] using hcoe

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
theorem diffMaxH_symmetricOn :
    SymmetricOn (diffMaxDom (velMu A (seqConst c))) (diffMaxH A c) := by
  intro z w
  obtain ⟨z', rfl⟩ := (diffMaxEquiv (velMu A (seqConst c))).surjective z
  obtain ⟨w', rfl⟩ := (diffMaxEquiv (velMu A (seqConst c))).surjective w
  rw [diffMaxH_apply, diffMaxH_apply, diffMaxEquiv_coe, diffMaxEquiv_coe,
    velUnitary.inner_map_map, velUnitary.inner_map_map]
  exact velH_symmetricOn A (seqConst c) z' w'

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
theorem diffMaxN_symmetricOn (mu : ℝ) :
    SymmetricOn (diffMaxDom mu) (diffMaxN mu) := by
  intro z w
  obtain ⟨z', rfl⟩ := (diffMaxEquiv mu).surjective z
  obtain ⟨w', rfl⟩ := (diffMaxEquiv mu).surjective w
  rw [diffMaxN_apply, diffMaxN_apply, diffMaxEquiv_coe, diffMaxEquiv_coe,
    velUnitary.inner_map_map, velUnitary.inner_map_map]
  exact diagMax_symmetricOn (velSym mu) z' w'

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
theorem diffMaxN_quadForm_nonneg (mu : ℝ) (hmu : 0 ≤ mu) (z : diffMaxDom mu) :
    0 ≤ quadForm (diffMaxN mu) z := by
  obtain ⟨z', rfl⟩ := (diffMaxEquiv mu).surjective z
  have h : quadForm (diffMaxN mu) (diffMaxEquiv mu z')
      = quadForm (diagMax (velSym mu)) z' := by
    simp only [quadForm]
    rw [diffMaxN_apply, diffMaxEquiv_coe, velUnitary.inner_map_map]
  rw [h]
  exact diagMax_quadForm_nonneg (velSym mu)
    (fun β => le_trans zero_le_one (velSym_ge_one hmu β)) z'

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
theorem diffMaxN_add_one_surjective (mu : ℝ) (hmu : 0 ≤ mu) (f : L2d 3) :
    ∃ z : diffMaxDom mu, diffMaxN mu z + (z : L2d 3) = f := by
  obtain ⟨x, hx⟩ := diagMax_add_one_surjective (velSym mu)
    (fun β => le_trans zero_le_one (velSym_ge_one hmu β)) (velUnitary.symm f)
  refine ⟨diffMaxEquiv mu x, ?_⟩
  rw [diffMaxN_apply, diffMaxEquiv_coe, ← map_add, hx]
  simp

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
theorem diffMaxN_core_approx (mu : ℝ) (z : diffMaxDom mu) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : diffMaxDom mu, (y : L2d 3) ∈ (polyGaussCore (d := 3)) ∧
      ‖(y : L2d 3) - (z : L2d 3)‖ < ε ∧ ‖diffMaxN mu y - diffMaxN mu z‖ < ε := by
  obtain ⟨z', rfl⟩ := (diffMaxEquiv mu).surjective z
  obtain ⟨y', hy1, hy2, hy3⟩ := exists_finiteModes_graph_approx (velSym mu) z' ε hε
  refine ⟨diffMaxEquiv mu y', ?_, ?_, ?_⟩
  · rw [diffMaxEquiv_coe]
    exact velUnitary_mem_core ⟨(y' : L2I Vel), hy1⟩
  · rw [diffMaxEquiv_coe, diffMaxEquiv_coe, ← map_sub, velUnitary.norm_map]
    exact hy2
  · rw [diffMaxN_apply, diffMaxN_apply, ← map_sub, velUnitary.norm_map]
    exact hy3

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
theorem diffMaxH_relative_bound :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ z : diffMaxDom (velMu A (seqConst c)),
      ‖diffMaxH A c z‖ ^ 2
        ≤ a * ‖diffMaxN (velMu A (seqConst c)) z‖ ^ 2 + b * ‖(z : L2d 3)‖ ^ 2 := by
  obtain ⟨a, b, ha, hb, hbound⟩ :=
    SignedShift.listH_relative_bound (hopList A (seqConst c))
  refine ⟨a, b, ha, hb, fun z => ?_⟩
  obtain ⟨z', rfl⟩ := (diffMaxEquiv (velMu A (seqConst c))).surjective z
  rw [diffMaxH_apply, diffMaxN_apply, diffMaxEquiv_coe, velUnitary.norm_map,
    velUnitary.norm_map, velUnitary.norm_map]
  exact hbound z'

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
theorem diffMaxH_commForm_bound :
    ∃ cst : ℝ, 0 ≤ cst ∧ ∀ z : diffMaxDom (velMu A (seqConst c)),
      |commForm (diffMaxH A c) (diffMaxN (velMu A (seqConst c))) z|
        ≤ cst * quadForm (diffMaxN (velMu A (seqConst c))) z := by
  obtain ⟨cst, hcst, hbound⟩ :=
    SignedShift.listH_commForm_bound (hopList A (seqConst c))
      (fun β => velSym_ge_one (velMu_nonneg A (seqConst c)) β)
  refine ⟨cst, hcst, fun z => ?_⟩
  obtain ⟨z', rfl⟩ := (diffMaxEquiv (velMu A (seqConst c))).surjective z
  have hcomm : commForm (diffMaxH A c) (diffMaxN (velMu A (seqConst c)))
        (diffMaxEquiv (velMu A (seqConst c)) z')
      = commForm (velH A (seqConst c)) (diagMax (velSym (velMu A (seqConst c)))) z' := by
    simp only [commForm]
    rw [diffMaxH_apply, diffMaxN_apply, velUnitary.inner_map_map, velUnitary.inner_map_map]
  have hquad : quadForm (diffMaxN (velMu A (seqConst c)))
        (diffMaxEquiv (velMu A (seqConst c)) z')
      = quadForm (diagMax (velSym (velMu A (seqConst c)))) z' := by
    simp only [quadForm]
    rw [diffMaxN_apply, diffMaxEquiv_coe, velUnitary.inner_map_map]
  rw [hcomm, hquad]
  exact hbound z'

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- The restriction of the maximal-domain differential Hamiltonian to the Hermite core is
the differential Navier–Stokes Hamiltonian. -/
theorem diffMaxH_restrict :
    (diffMaxH A c).comp
        (Submodule.inclusion (polyGaussCore_le_diffMaxDom (velMu A (seqConst c))))
      = (polyGaussCore (d := 3)).subtype.comp (nsDiffH A c) := by
  refine LinearMap.ext fun f => ?_
  obtain ⟨x, rfl⟩ := embedCore_surjective f
  have hz : (Submodule.inclusion (polyGaussCore_le_diffMaxDom (velMu A (seqConst c)))
        (embedCore x))
      = diffMaxEquiv (velMu A (seqConst c))
          (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A (seqConst c)))) x) :=
    Subtype.ext rfl
  rw [LinearMap.comp_apply, hz, diffMaxH_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    nsDiffH_embedCore, canH_coe_velH]

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **Essential self-adjointness of the differential Navier–Stokes symbol, by the
Faris–Lavine criterion** — the alternative route to
`BookProof.NavierStokesFlow.DifferentialL2.nsDiffH_essentiallySelfAdjointOn_core`, run with
the two differential Faris–Lavine inequalities instead of the Hermite-basis transport of
essential self-adjointness. -/
theorem nsDiffH_esa_of_farisLavine :
    EssentiallySelfAdjointOn (polyGaussCore (d := 3))
      ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c)) := by
  obtain ⟨a, b, _, _, hrel⟩ := diffMaxH_relative_bound A c
  obtain ⟨cst, hcst, hcomm⟩ := diffMaxH_commForm_bound A c
  have hesa := essentiallySelfAdjointOn_core_of_farisLavine
    (polyGaussCore_le_diffMaxDom (velMu A (seqConst c))) (diffMaxH A c)
    (diffMaxN (velMu A (seqConst c))) a b cst (diffMaxH_symmetricOn A c)
    (diffMaxN_symmetricOn _) hcst
    (diffMaxN_quadForm_nonneg _ (velMu_nonneg A (seqConst c)))
    (diffMaxN_add_one_surjective _ (velMu_nonneg A (seqConst c))) hcomm hrel
    (fun z ε hε => diffMaxN_core_approx _ z ε hε)
  rwa [diffMaxH_restrict] at hesa

end

end DiffFarisLavine

end BookProof.NavierStokesFlow
