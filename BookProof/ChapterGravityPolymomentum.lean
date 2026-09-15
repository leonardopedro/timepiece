import Mathlib
import BookProof.ChapterGravityProjector

/-!
# Chapter "Diffeomorphisms and gravity": the projected polymomenta and the
Legendre transform of the Einstein–Cartan Hamiltonian

Source: `book.tex`, chapter *"Diffeomorphisms and gravity"*, §*"Classical
Hamiltonian"* (line ~8091).  After varying the teleparallel Lagrangian density in
the vielbein velocities the manuscript obtains the **polymomentum**

`p^{ab} = e ( S^{ab} − (4/3) T η^{ab} − 𝒯^{ab} + 2 𝒯^{ac}{}_c v^b )`,

where, relative to the globally defined unit timelike vector `v` (`v^a v_a = −1`)
and the spatial projector `χ_a{}^b = δ_a{}^b + v_a v^b` of
`ChapterGravityProjector`:

* `S^{ab}` is the **spatial, symmetric, traceless** part of the torsion tensor
  `T_{ab}` (the irreducible piece isolated in `ChapterGravityIrrep`),
* `T` is its **trace**,
* `𝒯^{ab}` is a **spatial antisymmetric** tensor, and
* `e = det e_μ^a` is the vielbein determinant.

The manuscript then reads off the *projected* polymomenta

* `𝒜^{ab} = χ^a{}_{a₁}χ^b{}_{a₂}(p^{a₁a₂} − p^{a₂a₁}) = −2 e 𝒯^{ab}`,
* `𝒫 = η_{ab} χ^a{}_{a₁}χ^b{}_{a₂} p^{a₁a₂} = −4 e T`,
* `𝒮^{ab} = χ^a{}_{a₁}χ^b{}_{a₂}(p^{a₁a₂} + p^{a₂a₁} − (2/3) η^{a₁a₂} 𝒫) = 2 e S^{ab}`,

and uses them to rewrite the 3-dimensional Hamiltonian density in terms of the
momenta,

`ℋ = (1/16e) 𝒮^{ab}𝒮_{ab} − (1/24e) 𝒫² + (1/2) 𝒮^{ab}E_{ab} + (1/3) 𝒫 E_a{}^a − e(…)`,

which the manuscript asserts to be the same as its velocity form

`ℋ ≈ e( (1/4) S^{ab}S_{ab} − (2/3) T² + S^{ab}E_{ab} − (4/3) T E_a{}^a − (…) )`.

This file proves all four statements: the three inversion formulas, and the
equality of the momentum form and the velocity form of the Hamiltonian density
(the Legendre-transform consistency of the two displays).

## Model

Contravariant `(2,0)` tensors are real `4×4` matrices; `η = diag(−1,1,1,1)`
(`ChapterGravityProjector.metric`, which is its own inverse, so the same matrix
also represents `η^{ab}`), index lowering is `lower v`, and the spatial projector
is `spatialProj v`.  A tensor `M` is **spatial** (`IsSpatial`) when both of its
contractions with `v_·` vanish, which is exactly the condition for it to be
unchanged by the double `χ`-projection.

## Deliverables

* `metric_mul_metric`, `metric_mulVec_lower` — `η` is an involution;
* `proj` — the double spatial projection `M ↦ χ M χᵀ`, with its linearity, its
  compatibility with transposition, and its values on spatial tensors
  (`proj_eq_self_of_spatial`), on the term `2 𝒯^{ac}{}_c v^b`
  (`proj_vecMulVec_right`) and on the inverse metric (`proj_metric`, producing
  the spatial metric `h^{ab} = η^{ab} + v^a v^b`);
* `polyMom` — the book's `p^{ab}`, and `proj_polyMom` its projection;
* `calA_eq`, `calP_eq`, `calS_eq` — **the three inversion formulas**
  `𝒜 = −2e𝒯`, `𝒫 = −4eT`, `𝒮 = 2eS`;
* `polyMom_contract_v`, `polyMom_contract_v_spatial` — the remaining contraction
  `v_b p^{ab}`, computed honestly; see the note below;
* `contract` — the `η`-contraction `A^{ab}B_{ab}`, with its bilinearity;
* `hamiltonian_momentum_eq_velocity` — **the Legendre-transform consistency**:
  the momentum form and the velocity form of the Hamiltonian density agree.

## A note on `p^a`

The manuscript also lists `p^a = v_b p^{ab} = 2 e 𝒯^{ac}{}_c`.  With the
conventions fixed above (mostly-plus `η`, `v^a v_a = −1`, `p^{ab}` exactly as
displayed) the honest computation, recorded in `polyMom_contract_v`, gives

`v_b p^{ab} = −e ( (4/3) T v^a + 2 u^a )`,   `u^a := 𝒯^{ac}{}_c`,

whose spatial projection is `−2 e u^a` (`polyMom_contract_v_spatial`).  So this
last entry of the manuscript's list agrees with the computation only up to the
overall sign of the contraction with `v`, and after projecting away the part
along `v`; the three formulas `𝒜`, `𝒫`, `𝒮`, which are the ones entering the
Hamiltonian, hold exactly as printed.  Nothing else in this file depends on it.
-/

namespace BookProof.ChapterGravityPolymomentum

open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

/-! ## Preliminaries -/

/-- Right multiplication of a rank-one matrix. -/
theorem vecMulVec_mul (w u : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    vecMulVec w u * M = vecMulVec w (M.vecMul u) := by
  ext a b
  simp [Matrix.mul_apply, vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]

/-- Left multiplication of a rank-one matrix. -/
theorem mul_vecMulVec (M : Matrix (Fin 4) (Fin 4) ℝ) (w u : Fin 4 → ℝ) :
    M * vecMulVec w u = vecMulVec (M.mulVec w) u := by
  ext a b
  simp [Matrix.mul_apply, vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

/-- The trace of a rank-one matrix is the contraction of its two vectors. -/
theorem trace_vecMulVec (w u : Fin 4 → ℝ) :
    (vecMulVec w u).trace = ∑ a, w a * u a := by
  simp [Matrix.trace, vecMulVec_apply]

/-- `η² = 1`: the Minkowski metric is an involution, so the same matrix
represents both `η_{ab}` and `η^{ab}`. -/
theorem metric_mul_metric : metric * metric = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [metric, Matrix.mul_apply, Matrix.diagonal]

/-- The Minkowski metric is symmetric. -/
theorem metric_transpose : (metric : Matrix (Fin 4) (Fin 4) ℝ)ᵀ = metric := by
  ext a b
  by_cases h : a = b
  · subst h; rfl
  · simp [metric, Matrix.diagonal, Matrix.transpose_apply, h, Ne.symm h]

/-- Lowering and raising cancel: `η^{ab} v_b = v^a`. -/
theorem metric_mulVec_lower (v : Fin 4 → ℝ) : metric.mulVec (lower v) = v := by
  calc metric.mulVec (lower v) = (metric * metric).mulVec v := by
        simp [lower, Matrix.mulVec_mulVec]
    _ = v := by simp [metric_mul_metric]

/-- `χ = 1 + v ⊗ v_·`. -/
theorem spatialProj_eq (v : Fin 4 → ℝ) : spatialProj v = 1 + vecMulVec v (lower v) := rfl

/-- `χᵀ = 1 + v_· ⊗ v`. -/
theorem spatialProj_transpose (v : Fin 4 → ℝ) :
    (spatialProj v)ᵀ = 1 + vecMulVec (lower v) v := by
  ext a b
  simp [spatialProj, vecMulVec_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm, mul_comm]

/-- Left multiplication by `χ` adds a rank-one correction. -/
theorem spatialProj_mul (v : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    spatialProj v * M = M + vecMulVec v (M.vecMul (lower v)) := by
  rw [spatialProj_eq, Matrix.add_mul, Matrix.one_mul, vecMulVec_mul]

/-- Right multiplication by `χᵀ` adds a rank-one correction. -/
theorem mul_spatialProj_transpose (v : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    M * (spatialProj v)ᵀ = M + vecMulVec (M.mulVec (lower v)) v := by
  rw [spatialProj_transpose, Matrix.mul_add, Matrix.mul_one, mul_vecMulVec]

/-! ## The double spatial projection of a `(2,0)` tensor -/

/-- The double spatial projection `(χ M χᵀ)^{ab} = χ^a{}_{a₁} χ^b{}_{a₂} M^{a₁a₂}`. -/
noncomputable def proj (v : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  spatialProj v * M * (spatialProj v)ᵀ

theorem proj_add (v : Fin 4 → ℝ) (M N : Matrix (Fin 4) (Fin 4) ℝ) :
    proj v (M + N) = proj v M + proj v N := by
  simp [proj, Matrix.mul_add, Matrix.add_mul]

theorem proj_sub (v : Fin 4 → ℝ) (M N : Matrix (Fin 4) (Fin 4) ℝ) :
    proj v (M - N) = proj v M - proj v N := by
  simp [proj, Matrix.mul_sub, Matrix.sub_mul]

theorem proj_smul (v : Fin 4 → ℝ) (c : ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    proj v (c • M) = c • proj v M := by
  simp [proj]

theorem proj_transpose (v : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    proj v (Mᵀ) = (proj v M)ᵀ := by
  simp [proj, Matrix.transpose_mul, Matrix.mul_assoc]

/-- A `(2,0)` tensor is **spatial** when both of its contractions with `v_·`
vanish; equivalently, when the double `χ`-projection leaves it unchanged. -/
structure IsSpatial (v : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop where
  right : M.mulVec (lower v) = 0
  left : M.vecMul (lower v) = 0

/-- A spatial tensor is unchanged by the double projection. -/
theorem proj_eq_self_of_spatial (v : Fin 4 → ℝ) {M : Matrix (Fin 4) (Fin 4) ℝ}
    (h : IsSpatial v M) : proj v M = M := by
  rw [proj, spatialProj_mul, h.left]
  simp [mul_spatialProj_transpose, h.right]

/-- The term `2 𝒯^{ac}{}_c v^b` of the polymomentum is annihilated by the double
projection, because `χ v = 0`. -/
theorem proj_vecMulVec_right (v : Fin 4 → ℝ) (hv : minkSq v = -1) (u : Fin 4 → ℝ) :
    proj v (vecMulVec u v) = 0 := by
  have hXv : (spatialProj v).mulVec v = 0 := spatialProj_mulVec_self v hv
  have h1 : (spatialProj v)ᵀ.vecMul v = 0 := by
    rw [Matrix.vecMul_transpose, hXv]
  rw [proj, mul_vecMulVec, vecMulVec_mul, h1]
  simp

/-- The double projection of the inverse metric is the **spatial metric**
`h^{ab} = η^{ab} + v^a v^b`. -/
theorem proj_metric (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    proj v metric = metric + vecMulVec v v := by
  have hml : metric.mulVec (lower v) = v := metric_mulVec_lower v
  have hvm : metric.vecMul (lower v) = v := by
    have h := Matrix.vecMul_transpose (metric : Matrix (Fin 4) (Fin 4) ℝ) (lower v)
    rwa [metric_transpose, hml] at h
  have hXv : (spatialProj v).mulVec v = 0 := spatialProj_mulVec_self v hv
  have h1 : (spatialProj v)ᵀ.vecMul v = 0 := by rw [Matrix.vecMul_transpose, hXv]
  have h2 : vecMulVec v v * (spatialProj v)ᵀ = 0 := by
    rw [vecMulVec_mul, h1]; simp
  calc proj v metric = (metric + vecMulVec v v) * (spatialProj v)ᵀ := by
        rw [proj, spatialProj_mul, hvm]
    _ = metric + vecMulVec v v := by
        rw [Matrix.add_mul, h2, mul_spatialProj_transpose, hml, add_zero]

/-- The spatial metric is symmetric. -/
theorem vecMulVec_self_transpose (v : Fin 4 → ℝ) :
    (vecMulVec v v)ᵀ = vecMulVec v v := by
  ext a b; simp [vecMulVec_apply, Matrix.transpose_apply, mul_comm]

theorem spatialMetric_transpose (v : Fin 4 → ℝ) :
    (metric + vecMulVec v v)ᵀ = metric + vecMulVec v v := by
  rw [Matrix.transpose_add, metric_transpose, vecMulVec_self_transpose]

/-- The `η`-trace of the spatial metric is `3`: the spatial slice is
`3`-dimensional. -/
theorem trace_metric_mul_spatialMetric (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (metric * (metric + vecMulVec v v)).trace = 3 := by
  have h1 : metric * (metric + vecMulVec v v) = 1 + vecMulVec (metric.mulVec v) v := by
    rw [Matrix.mul_add, metric_mul_metric, mul_vecMulVec]
  have h2 : (vecMulVec (metric.mulVec v) v).trace = -1 := by
    rw [trace_vecMulVec]
    have : ∑ a, metric.mulVec v a * v a = minkSq v := by
      simp [minkSq, lower, mul_comm]
    rw [this, hv]
  rw [h1, Matrix.trace_add, h2]
  simp [Matrix.trace_one]
  norm_num

/-- The `η`-trace of an antisymmetric tensor vanishes. -/
theorem trace_metric_mul_of_antisymm {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : Mᵀ = -M) :
    (metric * M).trace = 0 := by
  have h1 : (metric * M).trace = ((metric * M)ᵀ).trace := (Matrix.trace_transpose _).symm
  have h2 : ((metric * M)ᵀ).trace = (Mᵀ * metric).trace := by
    rw [Matrix.transpose_mul, metric_transpose]
  have h3 : (Mᵀ * metric).trace = -(metric * M).trace := by
    rw [hM, Matrix.neg_mul, Matrix.trace_neg, Matrix.trace_mul_comm]
  have := h1.trans (h2.trans h3)
  linarith

/-! ## The polymomentum and its projections -/

/-- The book's polymomentum
`p^{ab} = e ( S^{ab} − (4/3) T η^{ab} − 𝒯^{ab} + 2 u^a v^b )`, with
`u^a = 𝒯^{ac}{}_c`. -/
noncomputable def polyMom (e T : ℝ) (S Tc : Matrix (Fin 4) (Fin 4) ℝ) (u v : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  e • (S - ((4 / 3) * T) • metric - Tc + (2 : ℝ) • vecMulVec u v)

/-- The projected antisymmetric part `𝒜^{ab}`. -/
noncomputable def calA (v : Fin 4 → ℝ) (p : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ := proj v (p - pᵀ)

/-- The projected trace `𝒫 = η_{ab} χ^a{}_{a₁} χ^b{}_{a₂} p^{a₁a₂}`. -/
noncomputable def calP (v : Fin 4 → ℝ) (p : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (metric * proj v p).trace

/-- The projected symmetric traceless part `𝒮^{ab}`. -/
noncomputable def calS (v : Fin 4 → ℝ) (p : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  proj v (p + pᵀ) - ((2 / 3) * calP v p) • proj v metric

variable {e T : ℝ} {S Tc : Matrix (Fin 4) (Fin 4) ℝ} {u v : Fin 4 → ℝ}

/-- The projection of the polymomentum: the `v`-term drops out and the inverse
metric becomes the spatial metric. -/
theorem proj_polyMom (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc) :
    proj v (polyMom e T S Tc u v)
      = e • (S - ((4 / 3) * T) • (metric + vecMulVec v v) - Tc) := by
  rw [polyMom, proj_smul, proj_add, proj_sub, proj_sub, proj_smul, proj_smul,
    proj_eq_self_of_spatial v hS, proj_eq_self_of_spatial v hTc,
    proj_metric v hv, proj_vecMulVec_right v hv u]
  simp

/-- **`𝒜^{ab} = −2 e 𝒯^{ab}`.** -/
theorem calA_eq (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc)
    (hSsymm : Sᵀ = S) (hTcanti : Tcᵀ = -Tc) :
    calA v (polyMom e T S Tc u v) = (-2 * e) • Tc := by
  have hp := proj_polyMom (e := e) (T := T) (u := u) hv hS hTc
  have hAt : (proj v (polyMom e T S Tc u v))ᵀ
      = e • (S - ((4 / 3) * T) • (metric + vecMulVec v v) + Tc) := by
    rw [hp]
    simp only [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_add, hSsymm,
      metric_transpose, vecMulVec_self_transpose, hTcanti]
    module
  rw [calA, proj_sub, proj_transpose, hAt, hp]
  module

/-- **`𝒫 = −4 e T`.** -/
theorem calP_eq (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc)
    (hStraceless : (metric * S).trace = 0) (hTcanti : Tcᵀ = -Tc) :
    calP v (polyMom e T S Tc u v) = -4 * e * T := by
  have hp := proj_polyMom (e := e) (T := T) (u := u) hv hS hTc
  have htrTc : (metric * Tc).trace = 0 := trace_metric_mul_of_antisymm hTcanti
  have htrh := trace_metric_mul_spatialMetric v hv
  rw [calP, hp]
  simp only [Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub,
    smul_eq_mul, hStraceless, htrTc, htrh]
  ring

/-- **`𝒮^{ab} = 2 e S^{ab}`.** -/
theorem calS_eq (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc)
    (hSsymm : Sᵀ = S) (hStraceless : (metric * S).trace = 0) (hTcanti : Tcᵀ = -Tc) :
    calS v (polyMom e T S Tc u v) = (2 * e) • S := by
  have hp := proj_polyMom (e := e) (T := T) (u := u) hv hS hTc
  have hAt : (proj v (polyMom e T S Tc u v))ᵀ
      = e • (S - ((4 / 3) * T) • (metric + vecMulVec v v) + Tc) := by
    rw [hp]
    simp only [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_add, hSsymm,
      metric_transpose, vecMulVec_self_transpose, hTcanti]
    module
  have hP := calP_eq (e := e) (T := T) (u := u) hv hS hTc hStraceless hTcanti
  rw [calS, proj_add, proj_transpose, hAt, hp, hP, proj_metric v hv]
  module

/-- The remaining contraction `v_b p^{ab}`, computed with the conventions of this
file (see the note in the module docstring). -/
theorem polyMom_contract_v (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc) :
    (polyMom e T S Tc u v).mulVec (lower v) = (-e) • (((4 / 3) * T) • v + (2 : ℝ) • u) := by
  have hvv : (vecMulVec u v).mulVec (lower v) = -u := by
    ext a
    have hsum : ∑ c, v c * lower v c = -1 := by simpa [minkSq] using hv
    simp [vecMulVec_apply, Matrix.mulVec, dotProduct, mul_assoc, ← Finset.mul_sum, hsum]
  have hml : metric.mulVec (lower v) = v := metric_mulVec_lower v
  rw [polyMom]
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, hS.right, hTc.right, hvv, hml]
  module

/-- The spatial projection of the previous contraction is `−2 e u^a`. -/
theorem polyMom_contract_v_spatial (hv : minkSq v = -1) (hS : IsSpatial v S)
    (hTc : IsSpatial v Tc) :
    (spatialProj v).mulVec ((polyMom e T S Tc u v).mulVec (lower v))
      = (-2 * e) • (spatialProj v).mulVec u := by
  have hXv : (spatialProj v).mulVec v = 0 := spatialProj_mulVec_self v hv
  rw [polyMom_contract_v hv hS hTc, Matrix.mulVec_smul, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, hXv]
  module

/-! ## The Legendre transform: the momentum form of `ℋ` equals the velocity form -/

/-- The `η`-contraction `A^{ab} B_{ab} = η_{ac} η_{bd} A^{ab} B^{cd}`. -/
noncomputable def contract (A B : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (metric * A * metric * Bᵀ).trace

theorem contract_smul_left (c : ℝ) (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    contract (c • A) B = c * contract A B := by
  simp [contract]

theorem contract_smul_right (c : ℝ) (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    contract A (c • B) = c * contract A B := by
  simp [contract, Matrix.transpose_smul]

/-- **Legendre-transform consistency of the two displayed forms of the
3-dimensional Hamiltonian density.**

With the inversion formulas `𝒮 = 2eS` and `𝒫 = −4eT` (`calS_eq`, `calP_eq`) the
momentum form

`(1/16e) 𝒮·𝒮 − (1/24e) 𝒫² + (1/2) 𝒮·E + (1/3) 𝒫 trE − e·R`

of the manuscript coincides with its velocity form

`e ( (1/4) S·S − (2/3) T² + S·E − (4/3) T trE − R )`

for every non-degenerate vielbein (`e ≠ 0`).  Here `E` is the tensor `E_{ab}` of
the manuscript, `trE` its trace `E_a{}^a`, and `R` collects the remaining terms
(those built from `𝒯`), which are literally the same in the two displays. -/
theorem hamiltonian_momentum_eq_velocity (he : e ≠ 0) (Scal E : Matrix (Fin 4) (Fin 4) ℝ)
    (P trE R : ℝ) (hS : Scal = (2 * e) • S) (hP : P = -4 * e * T) :
    (1 / (16 * e)) * contract Scal Scal - (1 / (24 * e)) * P ^ 2
        + (1 / 2) * contract Scal E + (1 / 3) * P * trE - e * R
      = e * ((1 / 4) * contract S S - (2 / 3) * T ^ 2 + contract S E
        - (4 / 3) * T * trE - R) := by
  subst hS hP
  rw [contract_smul_left, contract_smul_right, contract_smul_left]
  field_simp
  ring

end BookProof.ChapterGravityPolymomentum
