import Mathlib
import BookProof.OSReconstruction.HalfSpaceCovariantReflectionPositivity

/-!
# The covariance matrix of the shared-shift state

Plan: `cftproof.md`, **E3**.  `HalfSpaceCovariantReflectionPositivity` builds the state
`covState ν` — the law of `(T + X, T + Y)` with `T ~ ν` and `X`, `Y` independent white noise — and
proves it reflection positive.  A covariance matrix was only *described* there, not proved; this
module supplies the proof.  The state's covariance matrix is

  `[[Cov T + 1, Cov T], [Cov T, Cov T + 1]]`

blockwise: `covState_cov_fst_fst`, `covState_cov_snd_snd` (diagonal blocks, `Cov T + 1`) and
`covState_cov_fst_snd` (off-diagonal block, `Cov T`).  The `+ 1` is the white noise of the halves
and `Cov T` is the shared shift, which is exactly the source of the coupling.

Feeding a **banded** shift law — the chain state `chainLaw σ ρ` of `HalfSpaceChainCovariance` —
therefore couples the two halves by a banded matrix:
`covState_chainLaw_cov_fst_snd` identifies the off-diagonal block with `chainCov σ ρ`, and
`covState_chainLaw_cov_fst_snd_eq_zero` exhibits the band: the cross-covariance vanishes off the
star `{i, σ i, σ⁻¹ i}`.

## Contents

* `covariance_add_add_gen`, `covariance_fst_fst_prod`, `covariance_snd_snd_prod` — the measure
  bookkeeping: a covariance only sees the marginal of the coordinates it reads;
* `shiftCov` — the covariance of the shift law `ν`;
* **`covState_cov_fst_fst`**, **`covState_cov_snd_snd`**, **`covState_cov_fst_snd`** — the three
  blocks of the covariance matrix of `covState ν`;
* `memLp_eval_chainLaw` — the chain state has second moments;
* `covState_chainLaw_cov_fst_fst`, `covState_chainLaw_cov_snd_snd`,
  **`covState_chainLaw_cov_fst_snd`**, **`covState_chainLaw_cov_fst_snd_eq_zero`** — the banded
  coupled state.

## Boundary

* The shift law must be a probability with finite second moments (`hν`); no Gaussian assumption is
  used, and no independence between `T` and the halves beyond the product construction is claimed.
* This is the covariance of a Gaussian *mixture*; it does not identify `ν` with an interacting
  Gibbs measure, and the halves are coupled by `Cov T`, not by a transfer operator.
-/

namespace BookProof.OSReconstruction

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-! ## Covariances on a product measure -/

/-- Expansion of the covariance of a sum of two pairs, for an arbitrary finite measure. -/
theorem covariance_add_add_gen {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (a b c d : Ω → ℝ) (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (hc : MemLp c 2 μ) (hd : MemLp d 2 μ) :
    cov[a + c, b + d; μ]
      = cov[a, b; μ] + cov[a, d; μ] + cov[c, b; μ] + cov[c, d; μ] := by
  rw [covariance_add_left ha hc (hb.add hd), covariance_add_right ha hb hd,
    covariance_add_right hc hb hd]
  ring

/-- **A covariance only reads the marginal it uses** (first factor). -/
theorem covariance_fst_fst_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X Y : α → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[fun p : α × β => X p.1, fun p : α × β => Y p.1; μ.prod ν] = cov[X, Y; μ] := by
  have hmap : Measure.map Prod.fst (μ.prod ν) = μ := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have h := covariance_map (X := X) (Y := Y) (Z := Prod.fst (α := α) (β := β))
    (μ := μ.prod ν) (by rw [hmap]; exact hX.aestronglyMeasurable)
    (by rw [hmap]; exact hY.aestronglyMeasurable) measurable_fst.aemeasurable
  rw [hmap] at h
  exact h.symm

/-- **A covariance only reads the marginal it uses** (second factor). -/
theorem covariance_snd_snd_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X Y : β → ℝ} (hX : MemLp X 2 ν) (hY : MemLp Y 2 ν) :
    cov[fun p : α × β => X p.2, fun p : α × β => Y p.2; μ.prod ν] = cov[X, Y; ν] := by
  have hmap : Measure.map Prod.snd (μ.prod ν) = ν := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have h := covariance_map (X := X) (Y := Y) (Z := Prod.snd (α := α) (β := β))
    (μ := μ.prod ν) (by rw [hmap]; exact hX.aestronglyMeasurable)
    (by rw [hmap]; exact hY.aestronglyMeasurable) measurable_snd.aemeasurable
  rw [hmap] at h
  exact h.symm

/-! ## The covariance of the shared-shift state -/

/-- **The covariance matrix of the shift law**, entrywise. -/
def shiftCov {ι : Type*} (ν : Measure (ι → ℝ)) (i j : ι) : ℝ :=
  cov[fun t : ι → ℝ => t i, fun t : ι → ℝ => t j; ν]

/-- The first component of the coupling, on the triple product. -/
theorem covMap_fst {ι : Type*} (p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ))) :
    (covMap p).1 = p.1 + p.2.1 := rfl

/-- The second component of the coupling, on the triple product. -/
theorem covMap_snd {ι : Type*} (p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ))) :
    (covMap p).2 = p.1 + p.2.2 := rfl

/-- **The `(1,1)` block of the covariance matrix of `covState ν`** is `Cov T + 1`. -/
theorem covState_cov_fst_fst {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν]
    (hν : ∀ i : ι, MemLp (fun t : ι → ℝ => t i) 2 ν) (i j : ι) :
    cov[fun z : (ι → ℝ) × (ι → ℝ) => z.1 i, fun z => z.1 j; covState ν]
      = shiftCov ν i j + (if i = j then 1 else 0) := by
  classical
  set γ := whiteNoise ι with hγ
  have h1 : MemLp (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.1 i) 2 (ν.prod (γ.prod γ)) :=
    (hν i).comp_fst (γ.prod γ)
  have h2 : MemLp (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.1 j) 2 (ν.prod (γ.prod γ)) :=
    (hν j).comp_fst (γ.prod γ)
  have h3 : MemLp (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.2.1 i)
      2 (ν.prod (γ.prod γ)) :=
    ((memLp_eval i).comp_fst γ).comp_snd ν
  have h4 : MemLp (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.2.1 j)
      2 (ν.prod (γ.prod γ)) :=
    ((memLp_eval j).comp_fst γ).comp_snd ν
  rw [covState, covariance_map (Z := covMap (ι := ι)) (X := fun z => z.1 i)
    (Y := fun z => z.1 j) (μ := ν.prod (γ.prod γ))
    (Measurable.aestronglyMeasurable (by fun_prop))
    (Measurable.aestronglyMeasurable (by fun_prop)) (measurable_covMap (ι := ι)).aemeasurable]
  change cov[((fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.1 i) + fun p => p.2.1 i),
      ((fun p => p.1 j) + fun p => p.2.1 j); ν.prod (γ.prod γ)]
    = shiftCov ν i j + (if i = j then 1 else 0)
  rw [covariance_add_add_gen (ν.prod (γ.prod γ)) (fun p => p.1 i) (fun p => p.1 j)
    (fun p => p.2.1 i) (fun p => p.2.1 j) h1 h2 h3 h4]
  have hA : cov[fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.1 i,
      fun p => p.1 j; ν.prod (γ.prod γ)] = shiftCov ν i j :=
    covariance_fst_fst_prod (μ := ν) (ν := γ.prod γ) (X := fun t => t i) (Y := fun t => t j)
      (hν i) (hν j)
  have hB : cov[fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.1 i,
      fun p => p.2.1 j; ν.prod (γ.prod γ)] = 0 :=
    covariance_fst_snd_prod (μ := ν) (ν := γ.prod γ) (X := fun t => t i)
      (Y := fun q : (ι → ℝ) × (ι → ℝ) => q.1 j) (hν i) ((memLp_eval j).comp_fst γ)
  have hC : cov[fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.2.1 i,
      fun p => p.1 j; ν.prod (γ.prod γ)] = 0 := by
    rw [covariance_comm]
    exact covariance_fst_snd_prod (μ := ν) (ν := γ.prod γ) (X := fun t => t j)
      (Y := fun q : (ι → ℝ) × (ι → ℝ) => q.1 i) (hν j) ((memLp_eval i).comp_fst γ)
  have hD : cov[fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.2.1 i,
      fun p => p.2.1 j; ν.prod (γ.prod γ)] = (if i = j then 1 else 0) := by
    rw [covariance_snd_snd_prod (μ := ν) (ν := γ.prod γ)
      (X := fun q : (ι → ℝ) × (ι → ℝ) => q.1 i) (Y := fun q => q.1 j)
      ((memLp_eval i).comp_fst γ) ((memLp_eval j).comp_fst γ)]
    rw [covariance_fst_fst_prod (μ := γ) (ν := γ) (X := fun t => t i) (Y := fun t => t j)
      (memLp_eval i) (memLp_eval j), covariance_eval_eval i j]
  rw [hA, hB, hC, hD]
  ring

/-- **The `(2,2)` block of the covariance matrix of `covState ν`** is `Cov T + 1`. -/
theorem covState_cov_snd_snd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν]
    (hν : ∀ i : ι, MemLp (fun t : ι → ℝ => t i) 2 ν) (i j : ι) :
    cov[fun z : (ι → ℝ) × (ι → ℝ) => z.2 i, fun z => z.2 j; covState ν]
      = shiftCov ν i j + (if i = j then 1 else 0) := by
  classical
  set γ := whiteNoise ι with hγ
  have h1 : MemLp (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.1 i) 2 (ν.prod (γ.prod γ)) :=
    (hν i).comp_fst (γ.prod γ)
  have h2 : MemLp (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.1 j) 2 (ν.prod (γ.prod γ)) :=
    (hν j).comp_fst (γ.prod γ)
  have h3 : MemLp (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.2.2 i)
      2 (ν.prod (γ.prod γ)) :=
    ((memLp_eval i).comp_snd γ).comp_snd ν
  have h4 : MemLp (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.2.2 j)
      2 (ν.prod (γ.prod γ)) :=
    ((memLp_eval j).comp_snd γ).comp_snd ν
  rw [covState, covariance_map (Z := covMap (ι := ι)) (X := fun z => z.2 i)
    (Y := fun z => z.2 j) (μ := ν.prod (γ.prod γ))
    (Measurable.aestronglyMeasurable (by fun_prop))
    (Measurable.aestronglyMeasurable (by fun_prop)) (measurable_covMap (ι := ι)).aemeasurable]
  change cov[((fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.1 i) + fun p => p.2.2 i),
      ((fun p => p.1 j) + fun p => p.2.2 j); ν.prod (γ.prod γ)]
    = shiftCov ν i j + (if i = j then 1 else 0)
  rw [covariance_add_add_gen (ν.prod (γ.prod γ)) (fun p => p.1 i) (fun p => p.1 j)
    (fun p => p.2.2 i) (fun p => p.2.2 j) h1 h2 h3 h4]
  have hA : cov[fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.1 i,
      fun p => p.1 j; ν.prod (γ.prod γ)] = shiftCov ν i j :=
    covariance_fst_fst_prod (μ := ν) (ν := γ.prod γ) (X := fun t => t i) (Y := fun t => t j)
      (hν i) (hν j)
  have hB : cov[fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.1 i,
      fun p => p.2.2 j; ν.prod (γ.prod γ)] = 0 :=
    covariance_fst_snd_prod (μ := ν) (ν := γ.prod γ) (X := fun t => t i)
      (Y := fun q : (ι → ℝ) × (ι → ℝ) => q.2 j) (hν i) ((memLp_eval j).comp_snd γ)
  have hC : cov[fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.2.2 i,
      fun p => p.1 j; ν.prod (γ.prod γ)] = 0 := by
    rw [covariance_comm]
    exact covariance_fst_snd_prod (μ := ν) (ν := γ.prod γ) (X := fun t => t j)
      (Y := fun q : (ι → ℝ) × (ι → ℝ) => q.2 i) (hν j) ((memLp_eval i).comp_snd γ)
  have hD : cov[fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.2.2 i,
      fun p => p.2.2 j; ν.prod (γ.prod γ)] = (if i = j then 1 else 0) := by
    rw [covariance_snd_snd_prod (μ := ν) (ν := γ.prod γ)
      (X := fun q : (ι → ℝ) × (ι → ℝ) => q.2 i) (Y := fun q => q.2 j)
      ((memLp_eval i).comp_snd γ) ((memLp_eval j).comp_snd γ)]
    rw [covariance_snd_snd_prod (μ := γ) (ν := γ) (X := fun t => t i) (Y := fun t => t j)
      (memLp_eval i) (memLp_eval j), covariance_eval_eval i j]
  rw [hA, hB, hC, hD]
  ring

/-- **The `(1,2)` block of the covariance matrix of `covState ν`** is `Cov T`: the off-diagonal
coupling between the two halves is exactly the covariance of the shared shift. -/
theorem covState_cov_fst_snd {ι : Type*} [Fintype ι]
    (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν]
    (hν : ∀ i : ι, MemLp (fun t : ι → ℝ => t i) 2 ν) (i j : ι) :
    cov[fun z : (ι → ℝ) × (ι → ℝ) => z.1 i, fun z => z.2 j; covState ν] = shiftCov ν i j := by
  classical
  set γ := whiteNoise ι with hγ
  have h1 : MemLp (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.1 i) 2 (ν.prod (γ.prod γ)) :=
    (hν i).comp_fst (γ.prod γ)
  have h2 : MemLp (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.1 j) 2 (ν.prod (γ.prod γ)) :=
    (hν j).comp_fst (γ.prod γ)
  have h3 : MemLp (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.2.1 i)
      2 (ν.prod (γ.prod γ)) :=
    ((memLp_eval i).comp_fst γ).comp_snd ν
  have h4 : MemLp (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.2.2 j)
      2 (ν.prod (γ.prod γ)) :=
    ((memLp_eval j).comp_snd γ).comp_snd ν
  rw [covState, covariance_map (Z := covMap (ι := ι)) (X := fun z => z.1 i)
    (Y := fun z => z.2 j) (μ := ν.prod (γ.prod γ))
    (Measurable.aestronglyMeasurable (by fun_prop))
    (Measurable.aestronglyMeasurable (by fun_prop)) (measurable_covMap (ι := ι)).aemeasurable]
  change cov[((fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.1 i) + fun p => p.2.1 i),
      ((fun p => p.1 j) + fun p => p.2.2 j); ν.prod (γ.prod γ)] = shiftCov ν i j
  rw [covariance_add_add_gen (ν.prod (γ.prod γ)) (fun p => p.1 i) (fun p => p.1 j)
    (fun p => p.2.1 i) (fun p => p.2.2 j) h1 h2 h3 h4]
  have hA : cov[fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.1 i,
      fun p => p.1 j; ν.prod (γ.prod γ)] = shiftCov ν i j :=
    covariance_fst_fst_prod (μ := ν) (ν := γ.prod γ) (X := fun t => t i) (Y := fun t => t j)
      (hν i) (hν j)
  have hB : cov[fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.1 i,
      fun p => p.2.2 j; ν.prod (γ.prod γ)] = 0 :=
    covariance_fst_snd_prod (μ := ν) (ν := γ.prod γ) (X := fun t => t i)
      (Y := fun q : (ι → ℝ) × (ι → ℝ) => q.2 j) (hν i) ((memLp_eval j).comp_snd γ)
  have hC : cov[fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.2.1 i,
      fun p => p.1 j; ν.prod (γ.prod γ)] = 0 := by
    rw [covariance_comm]
    exact covariance_fst_snd_prod (μ := ν) (ν := γ.prod γ) (X := fun t => t j)
      (Y := fun q : (ι → ℝ) × (ι → ℝ) => q.1 i) (hν j) ((memLp_eval i).comp_fst γ)
  have hD : cov[fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => p.2.1 i,
      fun p => p.2.2 j; ν.prod (γ.prod γ)] = 0 := by
    rw [covariance_snd_snd_prod (μ := ν) (ν := γ.prod γ)
      (X := fun q : (ι → ℝ) × (ι → ℝ) => q.1 i) (Y := fun q => q.2 j)
      ((memLp_eval i).comp_fst γ) ((memLp_eval j).comp_snd γ)]
    exact covariance_fst_snd_prod (μ := γ) (ν := γ) (X := fun t => t i) (Y := fun t => t j)
      (memLp_eval i) (memLp_eval j)
  rw [hA, hB, hC, hD]
  ring

/-! ## Feeding a banded shift into the state -/

/-- **The chain state has second moments**: its coordinates are the band models. -/
theorem memLp_eval_chainLaw {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ) (i : ι) :
    MemLp (fun z : ι → ℝ => z i) 2 (chainLaw σ ρ) := by
  have h : MemLp (chainModel σ ρ i) 2 (whiteNoise ι) := memLp_chainModel σ ρ i
  unfold chainLaw
  rw [memLp_map_measure_iff (Measurable.aestronglyMeasurable (measurable_eval i))
    (measurable_chainMap σ ρ).aemeasurable]
  exact h

/-- **The `(1,1)` block of the banded coupled state**: `chainCov + 1`. -/
theorem covState_chainLaw_cov_fst_fst {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (ρ : ℝ) (i j : ι) :
    cov[fun z : (ι → ℝ) × (ι → ℝ) => z.1 i, fun z => z.1 j; covState (chainLaw σ ρ)]
      = chainCov σ ρ i j + (if i = j then 1 else 0) := by
  rw [covState_cov_fst_fst (chainLaw σ ρ) (fun k => memLp_eval_chainLaw σ ρ k) i j, shiftCov,
    chainLaw_cov σ ρ i j]

/-- **The `(2,2)` block of the banded coupled state**: `chainCov + 1`. -/
theorem covState_chainLaw_cov_snd_snd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (ρ : ℝ) (i j : ι) :
    cov[fun z : (ι → ℝ) × (ι → ℝ) => z.2 i, fun z => z.2 j; covState (chainLaw σ ρ)]
      = chainCov σ ρ i j + (if i = j then 1 else 0) := by
  rw [covState_cov_snd_snd (chainLaw σ ρ) (fun k => memLp_eval_chainLaw σ ρ k) i j, shiftCov,
    chainLaw_cov σ ρ i j]

/-- **The off-diagonal block of the banded coupled state is the banded chain covariance**: the two
halves are coupled by `chainCov σ ρ`, not by the identity. -/
theorem covState_chainLaw_cov_fst_snd {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (ρ : ℝ) (i j : ι) :
    cov[fun z : (ι → ℝ) × (ι → ℝ) => z.1 i, fun z => z.2 j; covState (chainLaw σ ρ)]
      = chainCov σ ρ i j := by
  rw [covState_cov_fst_snd (chainLaw σ ρ) (fun k => memLp_eval_chainLaw σ ρ k) i j, shiftCov,
    chainLaw_cov σ ρ i j]

/-- **The coupled state is banded**: off the star `{i, σ i, σ⁻¹ i}` the cross-covariance of the two
halves vanishes. -/
theorem covState_chainLaw_cov_fst_snd_eq_zero {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (ρ : ℝ) {i j : ι} (h1 : j ≠ i) (h2 : j ≠ σ i)
    (h3 : j ≠ σ.symm i) :
    cov[fun z : (ι → ℝ) × (ι → ℝ) => z.1 i, fun z => z.2 j; covState (chainLaw σ ρ)] = 0 := by
  rw [covState_chainLaw_cov_fst_snd σ ρ i j]
  exact chainCov_eq_zero σ ρ h1 h2 h3

end

end BookProof.OSReconstruction
