import Mathlib
import BookProof.OSReconstruction.HalfSpaceFreeState

/-!
# The free-field infinite-volume Gaussian state

Plan: `cftproof.md`, **E3** — the reconstruction takes an abstract `HalfSpaceState` and, in
`HalfSpaceFreeState`, a *finite-volume* concrete one (a finite Gibbs grid).  A projective limit of
those grid states does not exist: `gibbsMeasure V` lives on the *fixed* configuration space
`Config = Fin latticeDim → ℝ` for every volume `V`, so there is no system of finite-volume
measures to take a limit of.  The honest infinite-volume object is instead the *free field*:
independent Gaussian coordinates, with the measure built from a consistent family of
finite-dimensional laws.

This module builds that state, following the corpus's mass term rather than an abstract Gaussian:
the one-block law is the existing `freeFieldMeasure`, the product of `latticeDim` Gaussians of
variance `1/2` (`exp(-x²)` weights, the same mass term as `halfAction`), and the infinite-volume
law is `Measure.infinitePi` over `ℕ` independent blocks.

## Contents

* `freeFieldInfinite` — **the infinite-volume free-field state** on `ℕ → Config`, the product
  of the block laws over all time slices; `freeFieldInfinite_isProbability` says it is a
  probability measure;
* `freeFieldInfinite_eq_infinitePiNat` — **the state is the Ionescu–Tulcea measure**: Mathlib's
  `Measure.infinitePiNat` is the composition of the Ionescu–Tulcea kernel `traj` with the initial
  law, and the two measures have the same projective limit, hence coincide;
* `freeFieldInfinite_restrict`, `freeFieldInfinite_pi` — the cylinder marginals: restricting to a
  finite set of blocks gives the finite product `Measure.pi`, and boxes have product mass;
* `blockProj`, `measurable_blockProj`, `map_blockProj_freeFieldInfinite` — **the pushforward to
  one block**: evaluating the chain at one time gives back `freeFieldMeasure`, so the
  finite-volume reference law is the marginal of the infinite-volume state.

## Boundary

* `Measure.infinitePi` is a product of *probability* measures indexed by `ℕ`; the lattice indices
  inside a block are not infinite here.  An infinite space direction would need the same
  construction on `Fin nComponents × ℤ`, which is not built.
* The pushforward is along the coordinate projection to one block.  As an operator between
  coordinate spaces this projection has finite rank — hence is Hilbert–Schmidt — but the corpus
  has no `ℓ²` structure, so no operator norm or Hilbert–Schmidt norm is claimed here; what is
  proved is the distributional statement, that the pushforward is `freeFieldMeasure`.
* The blocks are *independent*, so the covariance of the state is the identity: this is the
  ultralocal free field.  The massive covariance `(−Δ+m²)⁻¹` would need its Hilbert–Schmidt
  square root applied to the product law, which is not built (see `E3_RECONSTRUCTION_CHAIN.md`
  §4.2.3 item 5).
* This is a *Gaussian reference* state, not the interacting Gibbs measure.  In particular the
  corpus still has no DLR/specification notion, so no statement is made that `freeFieldInfinite` is
  a Gibbs measure for `halfAction` in infinite volume; `gibbsMeasure V` remains the finite-volume
  object and is not a marginal of this state.
-/

namespace BookProof.OSReconstruction

open MeasureTheory
open BookProof.BalabanRG BookProof.ReflectionPositivity

noncomputable section

/-! ## The infinite-volume state -/

/-- **The infinite-volume free-field Gaussian state**: `ℕ` independent blocks, each distributed by
the one-block Gaussian reference law `freeFieldMeasure` of `HalfSpaceFreeState`. -/
def freeFieldInfinite : Measure (ℕ → Config) :=
  Measure.infinitePi (fun _ : ℕ => freeFieldMeasure)

instance freeFieldInfinite_isProbability : IsProbabilityMeasure freeFieldInfinite := by
  unfold freeFieldInfinite
  infer_instance

/-- **The state is the Ionescu–Tulcea measure.**  `Measure.infinitePiNat` is by construction the
composition of the Ionescu–Tulcea kernel `ProbabilityTheory.Kernel.traj` with the initial law;
both it and `Measure.infinitePi` are projective limits of the same finite products, so they
coincide. -/
theorem freeFieldInfinite_eq_infinitePiNat :
    freeFieldInfinite = Measure.infinitePiNat (fun _ : ℕ => freeFieldMeasure) :=
  (Measure.isProjectiveLimit_infinitePi (fun _ : ℕ => freeFieldMeasure)).unique
    (Measure.isProjectiveLimit_infinitePiNat (fun _ : ℕ => freeFieldMeasure))

/-! ## Cylinder marginals -/

/-- **The finite-volume marginals of the state**: restricting to a finite set of blocks gives the
product of the block laws. -/
theorem freeFieldInfinite_restrict (I : Finset ℕ) :
    freeFieldInfinite.map I.restrict = Measure.pi (fun _ : I => freeFieldMeasure) :=
  Measure.infinitePi_map_restrict (fun _ : ℕ => freeFieldMeasure)

/-- **Boxes have product mass** in the infinite-volume state. -/
theorem freeFieldInfinite_pi {s : Finset ℕ} {t : ℕ → Set Config}
    (ht : ∀ n ∈ s, MeasurableSet (t n)) :
    freeFieldInfinite (Set.pi (↑s) t) = ∏ n ∈ s, freeFieldMeasure (t n) :=
  Measure.infinitePi_pi (fun _ : ℕ => freeFieldMeasure) ht

/-- A block is a box of its component values. -/
theorem freeFieldMeasure_pi (t : Fin latticeDim → Set ℝ) :
    freeFieldMeasure (Set.pi Set.univ t)
      = ∏ i, ProbabilityTheory.gaussianReal 0 ⟨1 / 2, by norm_num⟩ (t i) :=
  Measure.pi_pi
    (fun _ : Fin latticeDim => ProbabilityTheory.gaussianReal 0 ⟨1 / 2, by norm_num⟩) t

/-! ## The pushforward to one block -/

/-- The projection to the block at time `k`. -/
def blockProj (k : ℕ) (x : ℕ → Config) : Config := x k

theorem measurable_blockProj (k : ℕ) : Measurable (blockProj k) :=
  measurable_pi_apply k

/-- **The finite-volume law is the pushforward of the infinite-volume state.**  Evaluating the
chain at the block `k` returns the one-block Gaussian reference law. -/
theorem map_blockProj_freeFieldInfinite (k : ℕ) :
    freeFieldInfinite.map (blockProj k) = freeFieldMeasure := by
  refine (Measure.pi_eq (μ' := freeFieldInfinite.map (blockProj k)) fun t ht => ?_).symm
  rw [Measure.map_apply (measurable_blockProj k) (MeasurableSet.univ_pi ht)]
  have hpre : blockProj k ⁻¹' Set.pi Set.univ t
      = Set.pi (({k} : Finset ℕ) : Set ℕ)
          (fun n => if n = k then Set.pi Set.univ t else (Set.univ : Set Config)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_singleton_iff, true_implies,
      Finset.coe_singleton, blockProj]
    constructor
    · rintro h n rfl
      simpa using h
    · rintro h i
      have hk : x k ∈ Set.pi Set.univ t := by simpa using h k rfl
      exact Set.mem_pi.mp hk i (Set.mem_univ i)
  rw [hpre, freeFieldInfinite_pi (s := ({k} : Finset ℕ)) (t := fun n =>
    if n = k then Set.pi Set.univ t else (Set.univ : Set Config)) ?_]
  · simp [freeFieldMeasure_pi]
  · intro n hn
    rw [Finset.mem_singleton] at hn
    subst hn
    simpa using MeasurableSet.univ_pi ht

end

end BookProof.OSReconstruction
