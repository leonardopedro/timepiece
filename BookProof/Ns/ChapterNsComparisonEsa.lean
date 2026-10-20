import Mathlib
import BookProof.Ns.ChapterNsLagrangianOuterFockEsa

/-!
# NS-L-C.1 / NS-L-C.2 — the transformed Lagrangian operator with a constraint term, and the
completed-square comparison operator

`CONSOLIDATED_PLAN.md` §"2026-10-15b", rows NS-L-C.1 and NS-L-C.2.

The canonical (Hermite/ladder) realization of the transformed Lagrangian Navier–Stokes
Hamiltonian on the one-parcel trajectory space `ℓ²(Fin 3 → ℕ)`,

  `h = ½ Σᵢ Pᵢ² + ν Σᵢ Qᵢ² + Σᵢ fᵢ Pᵢ`,

is `BookProof.NavierStokesFlow.LagrangianCanonical.lagCanData` (constraint term `0`).  This
module

* **NS-L-C.1** — adds the constraint (penalty / pressure) term: `lagConstrData nu f C` is the
  same data with an arbitrary **bounded symmetric** constraint operator `C` on the Hermite
  core, and `lagConstr_esa` / `lagConstr_hasZeroDeficiencyOn` prove that the full transformed
  operator `ĥ_full = ½ΣPᵢ² + νΣQᵢ² + ΣfᵢPᵢ + C` is essentially self-adjoint on the Hermite
  core.  (In the canonical realization `Pᵢ` and `Qᵢ` do **not** commute, so the
  common-eigenvector criterion `hasZeroDeficiencyOn_of_commonEigenvectors` cannot be
  instantiated here — a common eigenvector of `Pᵢ` and `Qᵢ` would violate `[Pᵢ, Qᵢ] = −i`;
  the closing route is the Kato–Rellich theorem
  `hFull_essentiallySelfAdjointOn_of_drive_eq_P` on top of the diagonalization of the
  second-order part by the Hermite states.)
* **NS-L-C.2** — the **completed-square comparison operator**
  `N = h + ½|f|² = ½ Σᵢ (Pᵢ + fᵢ)² + ν Σᵢ Qᵢ²` (`lagCompN`), i.e. the instance
  `C = ½|f|² · 1`, with
  - `lagCompN_eq` — `N = h + ½|f|²` as operators on the Hermite core,
  - `lagCompN_symmetricOn`, **`lagCompN_esa`** — `N` is symmetric and essentially
    self-adjoint on the Hermite core,
  - **`lagCompN_nonneg`** — `N ≥ 0` (the completed square), and `lagCompN_add_one_ge` —
    the form bound `⟪v, (N + 1) v⟫ ≥ ‖v‖²`.

## Honest boundary

The completed square `N` is the comparison operator **of the canonical one-parcel
Hamiltonian `h`**.  It does *not* discharge the hypothesis of
`NsLagrangianDetFL.lagKoopman_esa_of_comparison_esa`, which is about a different operator —
the comparison `N_L = H_L² + E` of the Koopman–von Neumann generator `H_L` of the Galerkin
Lagrangian flow with the exact degree-five determinant force, acting on `L²(ℝ^{PIdx K})`.
That hypothesis remains an explicit hypothesis.
-/

namespace BookProof.NsComparisonEsa

open BookProof.FarisLavine
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FullEsa
  BookProof.NavierStokesFlow.LagrangianEsa BookProof.NavierStokesFlow.LagrangianKatoRellich
  BookProof.NavierStokesFlow.LagrangianCanonical BookProof.NavierStokesFlow.IkebeKato
  BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NsLagrangianOuterFock

noncomputable section

variable (nu : ℝ)

/-! ## 1. NS-L-C.1: the full transformed operator with a constraint term -/

/-- The canonical Lagrangian data with the constraint (penalty / pressure) term `C`. -/
def lagConstrData (hnu : 0 < nu) (f : Fin 3 → ℝ)
    (C : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel) (hC : IsSymmetricDom C) :
    LagrangianFullData (L2I Vel) :=
  { lagCanData nu hnu f with constraintOp := C, constraint_symm := hC }

/-- **NS-L-C.1.**  For every bounded symmetric constraint operator `C` on the Hermite core,
the full transformed Lagrangian operator `½ΣPᵢ² + νΣQᵢ² + ΣfᵢPᵢ + C` is essentially
self-adjoint on the Hermite core of `ℓ²(Fin 3 → ℕ)`. -/
theorem lagConstr_esa (hnu : 0 < nu) (f : Fin 3 → ℝ)
    (C : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel) (hC : IsSymmetricDom C)
    {cc : ℝ} (hcc : 0 ≤ cc)
    (hCb : ∀ v : lpFiniteModes Vel, ‖(C v : L2I Vel)‖ ≤ cc * ‖(v : L2I Vel)‖) :
    EssentiallySelfAdjointOn (lagConstrData nu hnu f C hC).D
      (lagrangianCore (lagConstrData nu hnu f C hC)) :=
  hFull_essentiallySelfAdjointOn_of_drive_eq_P (lagConstrData nu hnu f C hC) rfl hcc hCb
    ((essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn (lagConstrData nu hnu f C hC).D
      (secondOrder (lagConstrData nu hnu f C hC))).mpr
      (lagCan_secondOrder_hasZeroDeficiencyOn nu hnu f))

/-- NS-L-C.1 in the vanishing-adjoint-deficiency form used by the Fock-of-Fock chapters. -/
theorem lagConstr_hasZeroDeficiencyOn (hnu : 0 < nu) (f : Fin 3 → ℝ)
    (C : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel) (hC : IsSymmetricDom C)
    {cc : ℝ} (hcc : 0 ≤ cc)
    (hCb : ∀ v : lpFiniteModes Vel, ‖(C v : L2I Vel)‖ ≤ cc * ‖(v : L2I Vel)‖) :
    HasZeroDeficiencyOn (lagConstrData nu hnu f C hC).D (lagConstrData nu hnu f C hC).hFull :=
  hFull_hasZeroDeficiencyOn_of_drive_eq_P (lagConstrData nu hnu f C hC) rfl hcc hCb
    (lagCan_secondOrder_hasZeroDeficiencyOn nu hnu f)

/-! ## 2. NS-L-C.2: the completed-square comparison operator -/

/-- The completing constant `½|f|²`. -/
def halfForceSq (f : Fin 3 → ℝ) : ℝ := (1 / 2) * ∑ i : Fin 3, f i ^ 2

theorem halfForceSq_nonneg (f : Fin 3 → ℝ) : 0 ≤ halfForceSq f := by
  unfold halfForceSq
  have : 0 ≤ ∑ i : Fin 3, f i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

theorem isSymmetricDom_real_smul_id (c : ℝ) :
    IsSymmetricDom ((c : ℂ) • (LinearMap.id : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel)) := by
  intro x y
  simp only [LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal]

/-- The data of the completed square: constraint term `½|f|² · 1`. -/
def lagCompData (hnu : 0 < nu) (f : Fin 3 → ℝ) : LagrangianFullData (L2I Vel) :=
  lagConstrData nu hnu f ((halfForceSq f : ℂ) • LinearMap.id)
    (isSymmetricDom_real_smul_id (halfForceSq f))

/-- **The completed-square comparison operator** `N = ½Σ(Pᵢ + fᵢ)² + νΣQᵢ² = h + ½|f|²` on
the Hermite core of `ℓ²(Fin 3 → ℕ)`. -/
def lagCompN (hnu : 0 < nu) (f : Fin 3 → ℝ) : lpFiniteModes Vel →ₗ[ℂ] L2I Vel :=
  lagrangianCore (lagCompData nu hnu f)

/-- `N = h + ½|f|²`. -/
theorem lagCompN_eq (hnu : 0 < nu) (f : Fin 3 → ℝ) (v : lpFiniteModes Vel) :
    (lagCompN nu hnu f v : L2I Vel)
      = (show L2I Vel from lagOneOp nu hnu f v) + (halfForceSq f : ℂ) • (v : L2I Vel) := by
  simp [lagCompN, lagCompData, lagConstrData, lagOneOp, lagrangianCore,
    LagrangianFullData.hFull, lagCanData]
  rfl

omit nu in
theorem re_inner_real_smul_self (c : ℝ) (x : L2I Vel) :
    (inner ℂ x ((c : ℂ) • x) : ℂ).re = c * ‖x‖ ^ 2 := by
  rw [inner_smul_right, Complex.re_ofReal_mul]
  congr 1
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) x)

theorem lagCompN_symmetricOn (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    SymmetricOn (lpFiniteModes Vel) (lagCompN nu hnu f) :=
  lagrangianCore_symmetricOn (lagCompData nu hnu f)

/-- **NS-L-C.2.**  The completed-square comparison operator is essentially self-adjoint on
the Hermite core. -/
theorem lagCompN_esa (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn (lpFiniteModes Vel) (lagCompN nu hnu f) :=
  lagConstr_esa nu hnu f _ (isSymmetricDom_real_smul_id (halfForceSq f))
    (halfForceSq_nonneg f) (fun v => by
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul, norm_smul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (halfForceSq_nonneg f)]
      exact le_rfl)

/-- **The completed square is nonnegative**: `⟪v, N v⟫ ≥ 0`, because
`⟪v, N v⟫ = ½ Σ ‖(Pᵢ + fᵢ) v‖² + ν Σ ‖Qᵢ v‖²`. -/
theorem lagCompN_nonneg (hnu : 0 < nu) (f : Fin 3 → ℝ) (v : lpFiniteModes Vel) :
    0 ≤ (inner ℂ (v : L2I Vel) (lagCompN nu hnu f v) : ℂ).re := by
  have hdecomp : (lagCompN nu hnu f v : L2I Vel)
      = ((lagCompData nu hnu f).kinetic v : L2I Vel)
        + ((lagCompData nu hnu f).viscous v : L2I Vel)
        + (∑ i : Fin 3, ((f i : ℝ) : ℂ) • (lagP nu i v : L2I Vel))
        + (halfForceSq f : ℂ) • (v : L2I Vel) := by
    simp only [lagCompN, lagrangianCore, LinearMap.comp_apply, Submodule.subtype_apply,
      LagrangianFullData.hFull, LinearMap.add_apply, Submodule.coe_add,
      LagrangianFullData.drift, LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply,
      Submodule.coe_smul]
    rfl
  have hkin : (inner ℂ (v : L2I Vel) ((lagCompData nu hnu f).kinetic v : L2I Vel) : ℂ).re
      = (1 / 2) * ∑ i : Fin 3, ‖(lagP nu i v : L2I Vel)‖ ^ 2 := by
    rw [(lagCompData nu hnu f).kinetic_inner v, Complex.ofReal_re]
    rfl
  have hvisc : 0 ≤ (inner ℂ (v : L2I Vel) ((lagCompData nu hnu f).viscous v : L2I Vel) : ℂ).re :=
    (lagCompData nu hnu f).viscous_nonneg v
  rw [hdecomp, inner_add_right, inner_add_right, inner_add_right, Complex.add_re,
    Complex.add_re, Complex.add_re, hkin, inner_sum, Complex.re_sum,
    re_inner_real_smul_self]
  simp only [inner_smul_right, Complex.re_ofReal_mul]
  -- each direction contributes `½(‖Pᵢv‖² + 2fᵢ Re⟪v,Pᵢv⟫ + fᵢ²‖v‖²) ≥ 0`
  have hdir : ∀ i : Fin 3, 0 ≤ (1 / 2) * ‖(lagP nu i v : L2I Vel)‖ ^ 2
      + f i * (inner ℂ (v : L2I Vel) (lagP nu i v : L2I Vel) : ℂ).re
      + (1 / 2) * f i ^ 2 * ‖(v : L2I Vel)‖ ^ 2 := by
    intro i
    have hcs : |(inner ℂ (v : L2I Vel) (lagP nu i v : L2I Vel) : ℂ).re|
        ≤ ‖(v : L2I Vel)‖ * ‖(lagP nu i v : L2I Vel)‖ :=
      (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
    have hfi : f i * (inner ℂ (v : L2I Vel) (lagP nu i v : L2I Vel) : ℂ).re
        ≥ -(|f i| * (‖(v : L2I Vel)‖ * ‖(lagP nu i v : L2I Vel)‖)) := by
      have h2 : |f i * (inner ℂ (v : L2I Vel) (lagP nu i v : L2I Vel) : ℂ).re|
          ≤ |f i| * (‖(v : L2I Vel)‖ * ‖(lagP nu i v : L2I Vel)‖) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hcs (abs_nonneg _)
      linarith [neg_abs_le (f i * (inner ℂ (v : L2I Vel) (lagP nu i v : L2I Vel) : ℂ).re)]
    have hsq : 0 ≤ (‖(lagP nu i v : L2I Vel)‖ - |f i| * ‖(v : L2I Vel)‖) ^ 2 := sq_nonneg _
    have hfsq : f i ^ 2 = |f i| ^ 2 := (sq_abs _).symm
    nlinarith
  have hsum := Finset.sum_nonneg fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hdir i
  have hexp : ∑ i : Fin 3, ((1 / 2) * ‖(lagP nu i v : L2I Vel)‖ ^ 2
      + f i * (inner ℂ (v : L2I Vel) (lagP nu i v : L2I Vel) : ℂ).re
      + (1 / 2) * f i ^ 2 * ‖(v : L2I Vel)‖ ^ 2)
      = (1 / 2) * ∑ i : Fin 3, ‖(lagP nu i v : L2I Vel)‖ ^ 2
        + ∑ i : Fin 3, f i * (inner ℂ (v : L2I Vel) (lagP nu i v : L2I Vel) : ℂ).re
        + halfForceSq f * ‖(v : L2I Vel)‖ ^ 2 := by
    simp only [Finset.sum_add_distrib, halfForceSq, Finset.mul_sum, Finset.sum_mul]
  rw [hexp] at hsum
  linarith

/-- **The form bound** `⟪v, (N + 1) v⟫ ≥ ‖v‖²` — the analytic counterpart of the
finite-shadow assertion "form `≥ m + 1`" with `m = 0`. -/
theorem lagCompN_add_one_ge (hnu : 0 < nu) (f : Fin 3 → ℝ) (v : lpFiniteModes Vel) :
    ‖(v : L2I Vel)‖ ^ 2
      ≤ (inner ℂ (v : L2I Vel)
          ((lagCompN nu hnu f + ((1 : ℝ) : ℂ) • (lpFiniteModes Vel).subtype) v) : ℂ).re := by
  rw [LinearMap.add_apply, inner_add_right, Complex.add_re, LinearMap.smul_apply,
    Submodule.subtype_apply, re_inner_real_smul_self]
  have h := lagCompN_nonneg nu hnu f v
  linarith

end

end BookProof.NsComparisonEsa
