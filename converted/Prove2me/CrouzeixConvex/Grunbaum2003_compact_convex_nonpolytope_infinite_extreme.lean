/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 224054d5-0471-4884-9f01-38fd1c0d574d
* original name       : `Grunbaum2003.compact_convex_nonpolytope_infinite_extreme`
* title               : Compact convex non-polytope has infinitely many extreme points (Lemma B)
* statement author    : junyihjy
* solution author     : junyihjy (submission 82cfbcee-7209-4f0a-bead-02e5f92c420e,
                        accepted 2026-10-11T04:05:06.161911+00:00)
* source              : None
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/crouzeix-convex/Grunbaum2003.compact_convex_nonpolytope_infinite_extreme.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/Grunbaum2003_compact_convex_nonpolytope_infinite_extreme.diff`.
-/
import Mathlib

set_option autoImplicit false

/-- Lemma B (Krein–Milman step): a compact convex K that is not a finite hull
    has infinitely many extreme points. By contradiction: finitely many extreme
    points would make K = closure (hull (extreme)) = hull (extreme), a finite hull. -/
theorem _root_.Prove2me.Solution.Grunbaum2003_compact_convex_nonpolytope_infinite_extreme (d : ℕ)
    (K : Set (Fin d → ℝ)) (hcompact : IsCompact K)
    (hconvex : Convex ℝ K)
    (hnotpoly : ¬ ∃ V : Set (Fin d → ℝ), V.Finite ∧ K = convexHull ℝ V) :
    (K.extremePoints ℝ).Infinite := by
  by_contra h
  rw [Set.not_infinite] at h
  have hclosed : IsClosed (convexHull ℝ (K.extremePoints ℝ)) :=
    h.isCompact_convexHull.isClosed
  have hkm := closure_convexHull_extremePoints hcompact hconvex
  rw [hclosed.closure_eq] at hkm
  exact hnotpoly ⟨K.extremePoints ℝ, h, hkm.symm⟩

theorem Grunbaum2003.compact_convex_nonpolytope_infinite_extreme :
    ∀ (d : ℕ) (K : Set (Fin d → ℝ)) (hcompact : IsCompact K)
      (hconvex : Convex ℝ K)
      (hnotpoly : ¬ ∃ V : Set (Fin d → ℝ), V.Finite ∧ K = convexHull ℝ V),
      (K.extremePoints ℝ).Infinite := _root_.Prove2me.Solution.Grunbaum2003_compact_convex_nonpolytope_infinite_extreme

/-! ## Platform statement

The solution file above already declares the platform theorem
`Grunbaum2003.compact_convex_nonpolytope_infinite_extreme` with the registered formal statement
(manifest `formal_statement`), so no separate statement block is appended. -/
