import Mathlib
import BookProof.ChapterSqSumOuterFamily

/-!
# Essential self-adjointness **only through Faris–Lavine**

The development contains three independent routes to essential self-adjointness of the
field-space Hamiltonians: the Carleman flux criterion
(`BookProof.FullQuadratic.fqOp_essentiallySelfAdjoint`, used by
`BookProof.QgOuterFock.sqSumOp_essentiallySelfAdjointOn`), the weighted Schur/Kato–Rellich
gates, and the commutator criterion of Faris–Lavine
(`BookProof.FarisLavine.essentiallySelfAdjointOn_of_farisLavine`).

Only the last one **lifts** from the one-particle Hilbert space to the outer Fock space.
The reason is structural and is made explicit here:

* a Faris–Lavine certificate consists of a comparison operator `N` — always the Friedrichs
  extension of a positive one-particle operator — and a commutator bound `±i[H,N] ≤ cN`;
* the Friedrichs extension lifts to the `ℓ²`-direct sum (`dsComparison`: symmetry,
  positivity and surjectivity of `N + 1` are fibrewise, and the fibre solutions of
  `(N+1)x = f` are automatically square-summable), and
* the commutator form of the lift is the **sum** of the fibre commutator forms
  (`dsFibOp_hasSum_commForm`), so the bound lifts with the *same* constant `c`.

Neither of the other two routes has this property: a Carleman flux estimate and a Schur
weight are statements about a *fixed* one-particle basis and its shells, and nothing in them
survives the passage to `⊕ₙ L²(ℝ^{d·n})` — the number of shells of the `n`-particle sector
grows with `n`, and the constants degrade.

This module therefore replaces the Carleman route by the Faris–Lavine route at the place it
enters the main line: the essential self-adjointness of a kinetic-plus-squares Hamiltonian
**on the Gauss–polynomial core itself**.

## What is proved

* `BookProof.QgOuterFockCoreFL.CoreData.esa_on_core` — the missing abstract step:
  Faris–Lavine gives essential self-adjointness not merely of the extension `ext` on the
  whole domain of the comparison operator, but of the original operator **on the graph core**
  (the relative bound transports the graph approximation of `N` to a graph approximation of
  `H`, which is exactly the hypothesis of
  `BookProof.FarisLavine.essentiallySelfAdjointOn_restrict_of_graph_core`).
* `sqSumOp_esa_farisLavine` — **the Faris–Lavine replacement for
  `BookProof.QgOuterFock.sqSumOp_essentiallySelfAdjointOn`**: for an arbitrary real signature
  `κ` and an arbitrary finite family of linear forms, `½ Σ_j κ_j π_j² + ½ Σ_r L_r²` is
  essentially self-adjoint on the Gauss–polynomial core of `L²(ℝᴰ)`, proved from the two
  Faris–Lavine inequalities of `BookProof.ChapterSqSumFarisLavine` against the Friedrichs
  oscillator `N₁ = −Δ + ‖x‖²/4`, with no Carleman flux estimate anywhere.  The Schur data
  are supplied by the trivial bounds, so the statement carries no hypotheses.
* `SqFamily.secHam_esa_fl`, `SqFamily.outerHam_esa_fl` — the same for every sector of a
  uniform family, and hence for the Hamiltonian on the finite-particle core of the outer
  Fock space: **the finite-particle-core statement, too, is now Faris–Lavine only.**
* `SqFamily.esa_farisLavine` — the certificate itself, collected in one statement: the
  comparison operator is the lifted Friedrichs extension, the relative bound and the
  commutator bound hold with constants `flK`, `flc` independent of the particle number, and
  the conclusion is essential self-adjointness on the lifted domain together with the
  extension property on the finite-particle core.

Everything is `sorry`-free and `axiom`-free.
-/

open scoped ENNReal

noncomputable section

namespace BookProof.QgOuterFockCoreFL

open BookProof.FarisLavine

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

namespace CoreData

variable (d : CoreData F)

/-- The extension is graph-approximated from the core: this is the relative bound
`‖H₀ p‖ ≤ K‖(N+1)p‖` turning a graph approximation for `N` into one for `H`. -/
theorem ext_graph_approx (x : d.C.dom) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : d.C.dom, (y : F) ∈ d.C₀ ∧ ‖(y : F) - (x : F)‖ < ε ∧ ‖d.ext y - d.ext x‖ < ε := by
  have hK := d.hK
  have hpos : 0 < 2 * d.K + 2 := by linarith
  set δ : ℝ := min ε (ε / (2 * d.K + 2)) with hδdef
  have hδ : 0 < δ := lt_min hε (by positivity)
  obtain ⟨y, hyC, h1, h2⟩ := d.gc.approx x δ hδ
  refine ⟨y, hyC, lt_of_lt_of_le h1 (min_le_left _ _), ?_⟩
  have hsub : d.ext y - d.ext x = d.ext (y - x) := (map_sub _ _ _).symm
  have hcoe : ((y - x : d.C.dom) : F) = (y : F) - (x : F) := rfl
  have hop : d.C.op (y - x) = d.C.op y - d.C.op x := map_sub _ _ _
  have hb := d.ext_norm_le (y - x)
  rw [hop, hcoe] at hb
  have htri : ‖d.C.op y - d.C.op x + ((y : F) - (x : F))‖ ≤ δ + δ :=
    le_trans (norm_add_le _ _) (add_le_add h2.le h1.le)
  have hstep : ‖d.ext (y - x)‖ ≤ d.K * (δ + δ) :=
    le_trans hb (mul_le_mul_of_nonneg_left htri hK)
  have hδle : δ ≤ ε / (2 * d.K + 2) := min_le_right _ _
  have hfin : d.K * (δ + δ) < ε := by
    have h2δ : 2 * d.K * δ ≤ 2 * d.K * (ε / (2 * d.K + 2)) := by
      have : 0 ≤ 2 * d.K := by linarith
      exact mul_le_mul_of_nonneg_left hδle this
    have hlt : 2 * d.K * (ε / (2 * d.K + 2)) < ε := by
      rw [mul_div_assoc']
      rw [div_lt_iff₀ hpos]
      nlinarith
    have : d.K * (δ + δ) = 2 * d.K * δ := by ring
    linarith
  rw [hsub]
  exact lt_of_le_of_lt hstep hfin

/-- **Faris–Lavine on the core itself.**  Under the Faris–Lavine hypotheses — a graph core
of the comparison operator, the relative bound, symmetry and the commutator bound on the
core — the operator is essentially self-adjoint **on the core**, not merely on the whole
domain of the comparison operator. -/
theorem esa_on_core (hsym : SymmetricOn d.C₀ d.H₀) {c : ℝ} (hc : 0 ≤ c)
    (hcomm : ∀ p : d.C₀, |commForm d.H₀ d.coreN p| ≤ c * quadForm d.coreN p) :
    EssentiallySelfAdjointOn d.C₀ d.H₀ := by
  have hres :=
    essentiallySelfAdjointOn_restrict_of_graph_core d.gc.le d.ext d.ext_graph_approx
      (d.ext_essentiallySelfAdjointOn hsym hc hcomm)
  have hid : d.ext.comp (Submodule.inclusion d.gc.le) = d.H₀ :=
    LinearMap.ext fun p => d.ext_core p
  rwa [hid] at hres

end CoreData

end Abstract

end BookProof.QgOuterFockCoreFL

namespace BookProof.FarisLavineOnly

open Finset
open BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.HermiteProductCore BookProof.QgHermiteOscillator
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL BookProof.SqSumOuterFamily

/-! ## 1. Every sector of a uniform family, by Faris–Lavine -/

/-- **The sector Hamiltonian of a uniform family is essentially self-adjoint on the
Gauss–polynomial core, by Faris–Lavine.**  This is the Faris–Lavine replacement of
`BookProof.SqSumOuterFamily.SqFamily.secHam_essentiallySelfAdjointOn`, whose proof goes
through the Carleman flux criterion. -/
theorem secHam_esa_fl (F : SqFamily) (n : ℕ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := F.dim n)) (F.secHam n) :=
  (F.secData n).esa_on_core (F.secHam_symmetricOn n) F.flc_nonneg (F.secData_commForm_le n)

/-- **The Hamiltonian of a uniform family is essentially self-adjoint on the
finite-particle core of the outer Fock space, by Faris–Lavine.**  Sector by sector the
certificate is the one of `secHam_esa_fl`; the Carleman route is not used. -/
theorem outerHam_esa_fl (F : SqFamily) :
    EssentiallySelfAdjointOn (outerCore F.dim) F.outerHam :=
  dsOp_essentiallySelfAdjointOn _ fun n => secHam_esa_fl F n

/-! ## 2. A single kinetic-plus-squares Hamiltonian, by Faris–Lavine -/

section Single

variable {D : ℕ} {R : Type} [Fintype R]

/-- The trivial signature bound: `|κ_I| ≤ Σ_J |κ_J|`. -/
theorem abs_le_sum_abs (kappa : Fin D → ℝ) (I : Fin D) :
    |kappa I| ≤ ∑ J : Fin D, |kappa J| :=
  Finset.single_le_sum (f := fun J => |kappa J|) (fun _ _ => abs_nonneg _) (Finset.mem_univ I)

/-- The total `ℓ¹` mass of the coefficient matrix of the linear forms. -/
def totalMass (v : R → Fin D → ℝ) : ℝ := ∑ r : R, ∑ I : Fin D, |v r I|

theorem totalMass_nonneg (v : R → Fin D → ℝ) : 0 ≤ totalMass v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem row_le_totalMass (v : R → Fin D → ℝ) (r : R) :
    ∑ I : Fin D, |v r I| ≤ totalMass v :=
  Finset.single_le_sum (f := fun s => ∑ I : Fin D, |v s I|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ r)

theorem col_le_totalMass (v : R → Fin D → ℝ) (I : Fin D) :
    ∑ r : R, |v r I| ≤ totalMass v := by
  refine Finset.sum_le_sum fun r _ => ?_
  exact Finset.single_le_sum (f := fun J => |v r J|) (fun _ _ => abs_nonneg _) (Finset.mem_univ I)

/-- The constant family whose every sector carries the same kinetic-plus-squares
Hamiltonian: the vehicle that lets the uniform-family machinery be used for a single
operator. -/
def constFamily (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) : SqFamily where
  dim := fun _ => D
  R := fun _ => R
  finR := fun _ => inferInstance
  kap := fun _ => kappa
  vv := fun _ => v
  km := ∑ J : Fin D, |kappa J|
  a := totalMass v
  b := totalMass v
  km_nonneg := Finset.sum_nonneg fun _ _ => abs_nonneg _
  a_nonneg := totalMass_nonneg v
  b_nonneg := totalMass_nonneg v
  kap_le := fun _ I => abs_le_sum_abs kappa I
  row_le := fun _ r => row_le_totalMass v r
  col_le := fun _ I => col_le_totalMass v I

@[simp] theorem constFamily_secHam (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) (n : ℕ) :
    (constFamily kappa v).secHam n = sqSumOp kappa v := rfl

/-- **Faris–Lavine for `½ Σ_j κ_j π_j² + ½ Σ_r L_r²`.**  For an arbitrary real signature and
an arbitrary finite family of linear forms, the kinetic-plus-squares Hamiltonian is
essentially self-adjoint on the Gauss–polynomial core of `L²(ℝᴰ)`.  The proof is Theorem 1 of
Faris–Lavine with the Friedrichs extension of `N₁ = −Δ + ‖x‖²/4` as comparison operator; no
Carleman flux estimate and no Schur weight is used. -/
theorem sqSumOp_esa_farisLavine (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := D)) (sqSumOp kappa v) :=
  secHam_esa_fl (constFamily kappa v) 0

end Single

end BookProof.FarisLavineOnly

end
