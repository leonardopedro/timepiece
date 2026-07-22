import Mathlib
import BookProof.ChapterGravityProjector

/-!
# Chapter — Diffeomorphisms and gravity: the temporal projector `Π = δ − χ = −v⊗v♭`

Source: `book.tex`, chapter *"Diffeomorphisms and gravity"*, §*"Classical
Hamiltonian"* (line ~8091).  Continuing the standing directive (mine the next
self-contained mathematical claim from `book.tex`) and building directly on
`ChapterGravityProjector` (Wave 69), we treat the **complementary temporal
projector**

`Π^a{}_b = δ^a{}_b − χ^a{}_b = −v^a v_b`,

i.e. `Π = δ − χ`, where `χ^a{}_b = δ^a{}_b + v^a v_b` is the spatial projector
onto `v^⊥`.  Relative to a globally defined **unit timelike vector** `v`
(`minkSq v = −1` in the mostly-plus Minkowski metric `η = diag(−1,1,1,1)`), the
pair `(χ, Π)` is the orthogonal split of spacetime into the spatial hyperplane
`v^⊥` and the `1`-dimensional time direction spanned by `v`.  This file records
the self-contained linear-algebra facts of that decomposition, reusing `metric`,
`lower`, `minkSq`, `spatialProj` from `ChapterGravityProjector`.

Formalized here (all under `minkSq v = -1`):

* `timeProj v` — the projector `Π^a{}_b = −v^a v_b`;
* `spatialProj_add_timeProj` — **completeness** `χ + Π = δ` (the identity split);
* `timeProj_idempotent` — `Π² = Π` (a genuine projector);
* `trace_timeProj` — `tr Π = 1` (rank `1`: the time direction);
* `timeProj_mulVec_self` — `Π v = v`: `v` is fixed, spanning the image of `Π`;
* `spatialProj_mul_timeProj` — `χ · Π = 0` (the two projectors are orthogonal);
* `timeProj_mul_spatialProj` — `Π · χ = 0`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis, no `axiom`.
-/

namespace BookProof.ChapterGravityTimeProj

open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

/-- The temporal projector `Π^a{}_b = −v^a v_b = δ^a{}_b − χ^a{}_b`, as a `4×4`
matrix acting on contravariant vectors. -/
noncomputable def timeProj (v : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (fun a b => -(v a * lower v b))

/-
**Completeness**: the spatial and temporal projectors sum to the identity,
`χ + Π = δ`.
-/
theorem spatialProj_add_timeProj (v : Fin 4 → ℝ) :
    spatialProj v + timeProj v = 1 := by
  ext a b; simp +decide [ spatialProj, timeProj ] ;

/-
`Π` is idempotent: `Π² = Π`, a genuine (rank-1) projector.
-/
theorem timeProj_idempotent (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    timeProj v * timeProj v = timeProj v := by
  unfold timeProj;
  ext a b; simp +decide [ Matrix.mul_apply, Fin.sum_univ_four ] ; ring;
  unfold minkSq at hv; simp_all +decide [ Fin.sum_univ_four, lower ] ;
  linear_combination' hv * v a * ( metric *ᵥ v ) b

/-
`Π` has trace `1`: it is a rank-`1` projector onto the time direction.
-/
theorem trace_timeProj (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (timeProj v).trace = 1 := by
  unfold timeProj; simp +decide [ hv, Matrix.trace ] ; ring;
  linarith!

/-
`Π` fixes the timelike vector `v`: `Π v = v`, so `v` spans the image of the
temporal projector.
-/
theorem timeProj_mulVec_self (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (timeProj v).mulVec v = v := by
  ext a;
  simp [minkSq, timeProj] at hv ⊢;
  simp_all +decide [ Matrix.mulVec, dotProduct, Fin.sum_univ_four ];
  linear_combination -hv * v a

/-
The spatial and temporal projectors are orthogonal: `χ · Π = 0`.
-/
theorem spatialProj_mul_timeProj (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    spatialProj v * timeProj v = 0 := by
  rw [ show timeProj v = 1 - spatialProj v from _ ];
  · simp +decide [ mul_sub, spatialProj_idempotent v hv ];
  · exact eq_sub_of_add_eq' ( spatialProj_add_timeProj v )

/-
The spatial and temporal projectors are orthogonal: `Π · χ = 0`.
-/
theorem timeProj_mul_spatialProj (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    timeProj v * spatialProj v = 0 := by
  -- Since timeProj = 1 - spatialProj (from spatialProj_add_timeProj), we can rewrite the goal using this equality.
  have h_timeProj : timeProj v = 1 - spatialProj v := by
    exact eq_sub_of_add_eq' ( spatialProj_add_timeProj v );
  simp +decide [ h_timeProj, sub_mul,mul_sub,spatialProj_idempotent v hv ]

end BookProof.ChapterGravityTimeProj