import Mathlib
import BookProof.ReflectionPositivity.GFFNormalization

/-!
# The chain partition function and its effective-mass closed form

`BookProof.ReflectionPositivity.GFFNormalization` evaluates the lattice free-field partition
function only up to two-sided bounds, and records in its `Honest boundary` that the exact value

`Z = (2π)^{N/2} / √det K`

needs the slice-by-slice recursion of the effective mass

`μ₀ = m/2,   μ_{j+1} = m/2 + μ_j/(1 + μ_j)`.

This chapter carries out that recursion.  The engine is the one-step Gaussian identity of
`GFFNormalization` (**`integral_exp_neg_slice_step`**): integrating out a slice carrying total
coefficient `c` and one gradient link to the next slice multiplies the integral by
`(√(π/(1+c)))^{|S|}` and replaces `c` by `δ(c) = c/(1+c)` on the next slice.

## Contents

* `sliceFactor`, `chainForm`, `chainZ` — the factor, the quadratic form and the partition
  function of a *chain* of `N + 1` slices, the outermost slice carrying the total coefficient `c`;
* **`chainForm_cons`** — splitting off the outermost slice: `chainForm` of a chain prepended with
  `w` is `c‖w‖² + ‖w − f 0‖² + chainForm` of the rest with mass coefficient `m/2`;
* **`chainForm_linear`** — `chainForm` depends on the coefficient `c` only through `c·‖y 0‖²`, so
  the outermost coefficient can be shifted at will;
* **`lintegral_exp_neg_mul_sqSum`**, **`lintegral_exp_neg_slice_step`** — the one-slice Gaussian
  and the effective-mass step in `ℝ≥0∞` (so no integrability is ever assumed);
* **`chainZ_succ`** — **the recursion**: `Z_{N+1}(c) = (√(π/(1+c)))^{|S|} · Z_N(m/2 + δ(c))`;
* **`chainZ_closed`** — **the closed form**:
  `Z_N(c) = (∏_{j<N} (√(π/(1+c_j)))^{|S|}) · (√(π/c_N))^{|S|}` with `c_0 = c`,
  `c_{j+1} = m/2 + δ(c_j)`;
* **`chainZ_closed_half`** — the same with `c = m/2`, where `c_j = effMass m j` is exactly the
  effective mass of the recursion `μ₀ = m/2`, `μ_{j+1} = m/2 + μ_j/(1 + μ_j)`;
* **`halfAction_split`**, **`chainForm_chain`** — **the chain re-indexing**: a half-space
  configuration `(z, y)` is a chain whose outermost slice is the reflection slice `z`, and its
  half-space action is the chain form with any chosen total coefficient on `z`;
* **`latticeAction_chain`** — the lattice action of `LatticeFreeField`, split at the reflection
  slice, is the sum of two such chain forms (the boundary mass placed on `z` in one of them);
* **`lintegral_fkKernel_eq_chainZ`** — **the measure-level re-indexing**: integrating
  `ρ(z)·ν_z(y)` over the boundary and one half-space is the chain partition function
  `chainZ m (m/2) n` of `n + 1` slices whose outermost slice is the reflection slice;
* **`chainMatrix`** — the symmetric tridiagonal matrix of the single-site chain form;
  **`chainMatrix_zero`**, **`chainMatrix_one`** — its determinant for one and two slices,
  `det = c₀` and `det = (1 + c₀)·c₁`, i.e. one step of elimination *is* the effective-mass step;
* **`det_corner_schur`** — the block elimination at a `1 × 1` corner,
  `det A = A 0 0 · det (A₀₀ − (A_{·0}/A 0 0)·A_{0·})`, proved by factoring the matrix into the
  lower block-triangular elimination matrix and the eliminated matrix and reading both determinants
  off `det_fromBlocks_zero₁₂`;
* **`chainMatrix_succ_det`** — **the elimination step**: `det K_{N+1}(c) =
  (1 + c) · det K_N(m/2 + δ(c))`, i.e. the effective-mass recursion *is* the Schur complement of
  the corner;
* **`chainMatrix_det`** — **the determinant identity** `det K_N = ∏_{j<N}(1 + c_j) · c_N` in
  general, by iterating the elimination step;
* **`chainMatrix_det_half`** — the same with `c_j = effMass m j`: `det K_N =
  ∏_{j<N}(1 + μ_j) · μ_N`;
* **`prod_sqrt_sliceFactor_eq_sqrt_det`**, **`chainZ_closed_det`** — **the closed form in
  determinant form**: `Z_N = π^{(N+1)|S|/2} / (det K_N)^{|S|/2}`, the textbook normalising
  constant of a Gaussian (for the standard lattice operator `K = 2·chainMatrix` this reads
  `(2π)^{(N+1)|S|/2}/√(det K)^{|S|}`);
* **`chainForm_symm`** — with the uniform coefficient `m/2` the chain form is the sum of all mass
  terms and all links, and **`chainForm_symm_rev`** — it is invariant under reversing the chain;
* `foldIdx`, **`foldChainInvEquiv`**, **`foldChainEquiv`** — **the `2n + 1` slices of the lattice
  read as a chain**: the past half backwards, the reflection slice, then the future half, with
  **`volume_preserving_foldChainEquiv`**: the re-indexing is a measure-preserving permutation of
  `volume`.  **`foldChainEquiv_center`**, **`foldChainEquiv_past`**, **`foldChainEquiv_future`**
  read off the reflection slice and the two halves, and **`sum_foldChain_sqSum`** matches the
  total mass term of the folded chain with `sqSum z + ∑ ‖y₁‖² + ∑ ‖y₂‖²`;
* **`foldChainEquiv_past_chain`**, **`foldChainEquiv_future_chain`** — the two halves of the fold
  sliced as `chain z y₁` and `chain z y₂`: position `n − j` of the fold is the `j`-th slice of
  the past chain and position `n + j` the `j`-th slice of the future one;
* **`sum_foldChain_diffSq`** — **the link terms match**: the `2n` links of the folded chain are
  exactly the links of the two half-space chains (`sum_foldIdx_split` splits the sum at the
  reflection slice — the past half read backwards, the future half read forwards);
* **`halfAction_eq_sum`**, **`latticeAction_eq_chainForm`** — hence the lattice action *is* the
  chain form of the folded slices, with the boundary term supplying the mass of the reflection
  slice;
* **`latticeGFFMass_eq_chainZ`** — **the lattice partition function *is* a chain partition
  function**: `latticeGFFMass m n = chainZ m (m/2) (2n)`, by the measure-preserving relabelling
  `foldChainEquiv`; with `chainZ_closed_det` this puts the whole lattice in closed form,
  `Z = π^{(2n+1)|S|/2} / (det K_{2n})^{|S|/2}`.

## Honest boundary

The chain chapter is complete: the recursion (`chainZ_succ`), its closed form
(`chainZ_closed`, `chainZ_closed_half`), its determinant form (`chainZ_closed_det`), the
determinant identity `det K_N = ∏_{j<N}(1 + c_j)·c_N` (`chainMatrix_det`), and the measure-level
re-indexing `∫⁻ (z,y), ρ(z)·ν_z(y) = chainZ m (m/2) n` (`lintegral_fkKernel_eq_chainZ`) — which,
unlike the action-level `chainForm_chain`, is a statement about the integrals themselves, obtained
with the same measure-preserving relabelling `(z, y) ↦ Fin.cons z y` as `chainZ_succ`.

Sections 7 and 8 close the identification of the **whole** lattice partition function
`GFFNormalization.latticeGFFMass` — the `2n + 1` slices of `LatticeFreeField` with the mass term on
every slice, rather than a chain with a chosen outermost coefficient — with `chainZ m (m/2) (2n)`.
Section 7 supplies the permutation of the slices (`foldChainEquiv`, measure preserving, with its
three slice projections) and the **mass** term (`sum_foldChain_sqSum`); Section 8 supplies the
matching of the **link** terms (`sum_foldChain_diffSq`), so that the lattice action is the chain
form of the folded slices (`latticeAction_eq_chainForm`) and the two integrands agree, whence
**`latticeGFFMass m n = chainZ m (m/2) (2n)`**.  Together with `chainZ_closed_half` /
`chainZ_closed_det` this is the closed form of the lattice partition function.  What this does
*not* give: the same identity for the *interacting* Wilson measure, whose density does not
factorise along the links in this way.
-/

namespace BookProof.ReflectionPositivity

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {S : Type*} [Fintype S]

/-! ## 1. The chain and its partition function -/

/-- The factor by which integrating out a slice of total coefficient `c` multiplies the chain
integral, `(√(π/(1+c)))^{|S|}`. -/
def sliceFactor (c : ℝ) : ℝ := Real.sqrt (Real.pi / (1 + c)) ^ Fintype.card S

/-- The quadratic form of a chain of `N + 1` slices `y`, the outermost being `y 0`.  Written by
recursion on the number of links: every slice but the outermost carries the mass term
`(m/2)‖·‖²`, consecutive slices are joined by the gradient link `‖y (k+1) − y k‖²`, and the
outermost slice carries the *total* coefficient `c` (its mass included). -/
def chainForm (m c : ℝ) : (N : ℕ) → (Fin (N + 1) → (S → ℝ)) → ℝ
  | 0, y => c * sqSum (y 0)
  | (N + 1), y =>
      c * sqSum (y 0) + sqSum (fun i => y 1 i - y 0 i)
        + chainForm m (m / 2) N (fun j => y j.succ)

/-- **The chain partition function** `Z_N(c) = ∫ exp(−chainForm)`, as a number in `ℝ≥0∞`. -/
def chainZ (m c : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ y : Fin (N + 1) → (S → ℝ), ENNReal.ofReal (Real.exp (-(chainForm (S := S) m c N y)))

theorem sqSum_sub_comm (v w : S → ℝ) :
    sqSum (fun i => v i - w i) = sqSum (fun i => w i - v i) := by
  simp only [sqSum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Splitting off the outermost slice**: prepending `w` to the chain `f` adds the mass term
`c‖w‖²` of the outermost slice and its single link `‖w − f 0‖²`, and leaves the chain `f` with
mass coefficient `m/2`. -/
theorem chainForm_cons (m c : ℝ) (N : ℕ) (w : S → ℝ) (f : Fin (N + 1) → (S → ℝ)) :
    chainForm m c (N + 1) (Fin.cons w f) =
      c * sqSum w + diffSq (f 0) w + chainForm m (m / 2) N f := by
  simp only [chainForm, diffSq, sqSum, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_zero_eq_one]
  rw [show (fun j : Fin (N + 1) => f j) = f from rfl]
  have hsum : (∑ x, (f 0 x - w x) ^ 2) = ∑ i, (w i - f 0 i) ^ 2 :=
    Finset.sum_congr rfl fun x _ => by ring
  rw [hsum]

/-- **The coefficient of a chain is linear in `c`**: changing the total coefficient of the
outermost slice only changes its mass term. -/
theorem chainForm_linear (m c c' : ℝ) (N : ℕ) (y : Fin (N + 1) → (S → ℝ)) :
    chainForm m c' N y = chainForm m c N y + (c' - c) * sqSum (y 0) := by
  induction N generalizing c c' with
  | zero =>
    simp only [chainForm]
    ring
  | succ N ih =>
    simp only [chainForm]
    ring

/-! ## 2. The one-slice step in `ℝ≥0∞` -/

/-- The Gaussian integral of a single slice, in `ℝ≥0∞`: `∫⁻ exp(−c‖x‖²) = (√(π/c))^{|S|}`. -/
theorem lintegral_exp_neg_mul_sqSum {c : ℝ} (hc : 0 < c) :
    ∫⁻ x : S → ℝ, ENNReal.ofReal (Real.exp (-(c * sqSum x)))
      = ENNReal.ofReal (Real.sqrt (Real.pi / c) ^ Fintype.card S) := by
  have hmeas : AEStronglyMeasurable (fun x : S → ℝ => Real.exp (-(c * sqSum x)))
      (volume : Measure (S → ℝ)) :=
    (((measurable_sqSum (ι := S)).const_mul c).neg).exp.aestronglyMeasurable
  have h := integral_eq_lintegral_of_nonneg_ae
    (μ := (volume : Measure (S → ℝ)))
    (f := fun x : S → ℝ => Real.exp (-(c * sqSum x)))
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le) hmeas
  rw [integral_exp_neg_mul_sqSum hc] at h
  have hpos : 0 < Real.sqrt (Real.pi / c) ^ Fintype.card S :=
    pow_pos (Real.sqrt_pos.mpr (by positivity)) _
  have hne : (∫⁻ x : S → ℝ, ENNReal.ofReal (Real.exp (-(c * sqSum x)))) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at h
    exact hpos.ne' h
  rw [← ENNReal.ofReal_toReal hne]
  congr 1
  simpa using h.symm

/-- **The effective-mass step in `ℝ≥0∞`**: integrating one slice of total coefficient `c` with
its single link to the next slice `v` gives the slice factor and hands the coefficient
`δ(c) = c/(1+c)` to `v`. -/
theorem lintegral_exp_neg_slice_step {c : ℝ} (hc : 0 < c) (v : S → ℝ) :
    ∫⁻ w : S → ℝ, ENNReal.ofReal (Real.exp (-(diffSq v w + c * sqSum w)))
      = ENNReal.ofReal (sliceFactor (S := S) c * Real.exp (-(effCorr c * sqSum v))) := by
  have hd : Measurable fun w : S → ℝ => diffSq v w := by
    simp only [diffSq]
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).sub measurable_const).pow_const 2
  have hmeas : AEStronglyMeasurable
      (fun w : S → ℝ => Real.exp (-(diffSq v w + c * sqSum w)))
      (volume : Measure (S → ℝ)) :=
    ((hd.add ((measurable_sqSum (ι := S)).const_mul c)).neg).exp.aestronglyMeasurable
  have h := integral_eq_lintegral_of_nonneg_ae
    (μ := (volume : Measure (S → ℝ)))
    (f := fun w : S → ℝ => Real.exp (-(diffSq v w + c * sqSum w)))
    (Filter.Eventually.of_forall fun w => (Real.exp_pos _).le) hmeas
  rw [integral_exp_neg_slice_step (S := S) hc v] at h
  have hpos : 0 < sliceFactor (S := S) c * Real.exp (-(effCorr c * sqSum v)) :=
    mul_pos (pow_pos (Real.sqrt_pos.mpr (by positivity)) _) (Real.exp_pos _)
  have hne : (∫⁻ w : S → ℝ,
      ENNReal.ofReal (Real.exp (-(diffSq v w + c * sqSum w)))) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at h
    exact hpos.ne' h
  rw [← ENNReal.ofReal_toReal hne]
  congr 1
  simpa [sliceFactor] using h.symm

/-! ## 3. The recursion -/

theorem measurable_chainForm (m c : ℝ) (N : ℕ) :
    Measurable fun y : Fin (N + 1) → (S → ℝ) => chainForm (S := S) m c N y := by
  induction N generalizing c with
  | zero =>
    simp only [chainForm]
    exact measurable_const.mul ((measurable_sqSum (ι := S)).comp (measurable_pi_apply 0))
  | succ N ih =>
    simp only [chainForm]
    refine Measurable.add (Measurable.add (measurable_const.mul ?_) ?_) ?_
    · exact (measurable_sqSum (ι := S)).comp (measurable_pi_apply 0)
    · refine (measurable_sqSum (ι := S)).comp ?_
      exact measurable_pi_iff.mpr fun i =>
        ((measurable_pi_apply i).comp (measurable_pi_apply (1 : Fin (N + 2)))).sub
          ((measurable_pi_apply i).comp (measurable_pi_apply 0))
    · exact (ih (m / 2)).comp (measurable_pi_iff.mpr fun j => measurable_pi_apply j.succ)

set_option maxHeartbeats 1000000 in
-- the `Fin (N + 1)` measure-space unifications need more than the default budget
/-- **The effective-mass recursion for the chain**: eliminating the outermost slice of total
coefficient `c` multiplies the partition function by `(√(π/(1+c)))^{|S|}` and hands the
coefficient `m/2 + δ(c)` to the next slice in. -/
theorem chainZ_succ (m c : ℝ) (hc : 0 < c) (N : ℕ) :
    chainZ (S := S) m c (N + 1)
      = ENNReal.ofReal (sliceFactor (S := S) c) * chainZ (S := S) m (m / 2 + effCorr c) N := by
  have hp := volume_preserving_piFinSuccAbove
    (fun _ : Fin ((N + 1) + 1) => (S → ℝ)) (0 : Fin ((N + 1) + 1))
  have hcons : ∀ a : (S → ℝ) × (Fin (N + 1) → (S → ℝ)),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin ((N + 1) + 1) => (S → ℝ))
        (0 : Fin ((N + 1) + 1))).symm a = Fin.cons a.1 a.2 := by
    intro a
    funext j
    rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
      Fin.insertNth_zero']
  have hbase : chainZ (S := S) m c (N + 1)
      = ∫⁻ p : (S → ℝ) × (Fin (N + 1) → (S → ℝ)),
          ENNReal.ofReal (Real.exp (-(chainForm m c (N + 1) (Fin.cons p.1 p.2)))) := by
    rw [chainZ]
    rw [← hp.symm.lintegral_comp (f := fun y : Fin ((N + 1) + 1) → (S → ℝ) =>
      ENNReal.ofReal (Real.exp (-(chainForm m c (N + 1) y)))) ?_]
    · exact lintegral_congr fun a => by rw [hcons a]
    · exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (Measurable.neg (measurable_chainForm (S := S) m c (N + 1))))
  rw [hbase]
  have hmeas : Measurable fun p : (S → ℝ) × (Fin (N + 1) → (S → ℝ)) =>
      ENNReal.ofReal (Real.exp (-(chainForm m c (N + 1) (Fin.cons p.1 p.2)))) := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine Real.measurable_exp.comp ?_
    refine Measurable.neg ?_
    refine (measurable_chainForm (S := S) m c (N + 1)).comp ?_
    refine measurable_pi_iff.mpr fun i => ?_
    induction i using Fin.cases with
    | zero => simpa using measurable_fst
    | succ j => simpa using (measurable_pi_apply j).comp measurable_snd
  rw [show (volume : Measure ((S → ℝ) × (Fin (N + 1) → (S → ℝ))))
      = (volume : Measure (S → ℝ)).prod
          (volume : Measure (Fin (N + 1) → (S → ℝ))) from rfl]
  rw [lintegral_prod_symm'
    (μ := (volume : Measure (S → ℝ)))
    (ν := (volume : Measure (Fin (N + 1) → (S → ℝ))))
    (f := fun p : (S → ℝ) × (Fin (N + 1) → (S → ℝ)) =>
      ENNReal.ofReal (Real.exp (-(chainForm m c (N + 1) (Fin.cons p.1 p.2))))) hmeas]
  have hinner : ∀ f : Fin (N + 1) → (S → ℝ),
      ∫⁻ w : S → ℝ, ENNReal.ofReal (Real.exp (-(chainForm m c (N + 1) (Fin.cons w f))))
        = ENNReal.ofReal (sliceFactor (S := S) c)
            * ENNReal.ofReal (Real.exp (-(chainForm m (m / 2 + effCorr c) N f))) := by
    intro f
    have hstep : ∀ w : S → ℝ,
        ENNReal.ofReal (Real.exp (-(chainForm m c (N + 1) (Fin.cons w f))))
          = ENNReal.ofReal (Real.exp (-(diffSq (f 0) w + c * sqSum w)))
              * ENNReal.ofReal (Real.exp (-(chainForm m (m / 2) N f))) := by
      intro w
      rw [chainForm_cons, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    have hdw : Measurable fun w : S → ℝ => diffSq (f 0) w := by
      simp only [diffSq]
      exact Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).sub measurable_const).pow_const 2
    have hmw : Measurable fun w : S → ℝ =>
        ENNReal.ofReal (Real.exp (-(diffSq (f 0) w + c * sqSum w))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (Measurable.neg (hdw.add ((measurable_sqSum (ι := S)).const_mul c))))
    simp only [hstep]
    rw [lintegral_mul_const _ hmw]
    rw [lintegral_exp_neg_slice_step (S := S) hc (f 0)]
    have hreal : sliceFactor (S := S) c * Real.exp (-(effCorr c * sqSum (f 0)))
        * Real.exp (-(chainForm m (m / 2) N f))
        = sliceFactor (S := S) c
          * Real.exp (-(chainForm m (m / 2 + effCorr c) N f)) := by
      rw [chainForm_linear (m := m) (m / 2) (m / 2 + effCorr c) N f, mul_assoc,
        ← Real.exp_add]
      congr 2
      ring
    have hsf : 0 < sliceFactor (S := S) c :=
      pow_pos (Real.sqrt_pos.mpr (by positivity)) _
    rw [← ENNReal.ofReal_mul (mul_nonneg hsf.le (Real.exp_pos _).le), hreal,
      ENNReal.ofReal_mul hsf.le]
  simp only [hinner]
  rw [lintegral_const_mul _ (by
    refine ENNReal.measurable_ofReal.comp ?_
    refine Real.measurable_exp.comp ?_
    exact Measurable.neg (measurable_chainForm (S := S) m (m / 2 + effCorr c) N))]
  rfl

/-- The effective coefficients of a chain of slices: `c₀ = c`, `c_{j+1} = m/2 + c_j/(1 + c_j)`. -/
def effSeq (m c : ℝ) : ℕ → ℝ
  | 0 => c
  | (j + 1) => m / 2 + effCorr (effSeq m c j)

theorem effSeq_zero (m c : ℝ) : effSeq m c 0 = c := rfl

/-- The effective-mass sequence of the free field is `effSeq` started at `m/2`. -/
theorem effSeq_half (m : ℝ) (j : ℕ) : effSeq m (m / 2) j = effMass m j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [effSeq, effMass, ih]

theorem effSeq_succ (m c : ℝ) (j : ℕ) : effSeq m c (j + 1) = m / 2 + effCorr (effSeq m c j) :=
  rfl

theorem effSeq_shift (m c : ℝ) (j : ℕ) :
    effSeq m (m / 2 + effCorr c) j = effSeq m c (j + 1) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [effSeq, ih]

theorem effSeq_pos (m : ℝ) (hm : 0 < m) (c : ℝ) (hc : 0 < c) (j : ℕ) : 0 < effSeq m c j := by
  induction j with
  | zero => exact hc
  | succ j ih => exact add_pos (by linarith) (effCorr_pos ih)

set_option maxHeartbeats 1000000 in
-- the base case re-indexes `Fin (0 + 1) → (S → ℝ)` onto a single slice
/-- **The closed form of the chain partition function**: iterating the recursion `N` times. -/
theorem chainZ_closed (m c : ℝ) (hm : 0 < m) (hc : 0 < c) (N : ℕ) :
    chainZ (S := S) m c N
      = ENNReal.ofReal ((∏ j ∈ Finset.range N, sliceFactor (S := S) (effSeq m c j))
          * Real.sqrt (Real.pi / effSeq m c N) ^ Fintype.card S) := by
  induction N generalizing c with
  | zero =>
    have hbase : chainZ (S := S) m c 0
        = ∫⁻ x : S → ℝ, ENNReal.ofReal (Real.exp (-(c * sqSum x))) := by
      haveI : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
      rw [chainZ]
      rw [show (volume : Measure (Fin (0 + 1) → (S → ℝ)))
          = Measure.pi (fun _ => (volume : Measure (S → ℝ))) from rfl]
      have hp := measurePreserving_piUnique
        (X := fun _ : Fin (0 + 1) => (S → ℝ)) (fun _ => (volume : Measure (S → ℝ)))
      rw [← hp.symm.lintegral_comp (f := fun y : Fin (0 + 1) → (S → ℝ) =>
        ENNReal.ofReal (Real.exp (-(chainForm m c 0 y)))) ?_]
      · refine lintegral_congr fun x => ?_
        simp only [MeasurableEquiv.piUnique_symm_apply, chainForm]
        simp
      · exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          (Measurable.neg (measurable_chainForm (S := S) m c 0)))
    rw [hbase, lintegral_exp_neg_mul_sqSum (S := S) hc]
    simp only [Finset.range_zero, Finset.prod_empty, one_mul, effSeq_zero]
  | succ N ih =>
    rw [chainZ_succ (S := S) m c hc N,
      ih (m / 2 + effCorr c) (by exact add_pos (by linarith) (effCorr_pos hc))]
    simp only [effSeq_shift]
    rw [Finset.prod_range_succ']
    simp only [effSeq_zero]
    have hpos1 : 0 ≤ sliceFactor (S := S) c := by
      have h1 : 0 < Real.sqrt (Real.pi / (1 + c)) := Real.sqrt_pos.mpr (by positivity)
      exact (pow_pos h1 (Fintype.card S)).le
    rw [← ENNReal.ofReal_mul hpos1]
    congr 1
    ring

/-- **The free field's chain partition function**: the same closed form with the effective
masses `μ_j = effMass m j` of the recursion `μ₀ = m/2`, `μ_{j+1} = m/2 + μ_j/(1 + μ_j)`. -/
theorem chainZ_closed_half (m : ℝ) (hm : 0 < m) (N : ℕ) :
    chainZ (S := S) m (m / 2) N
      = ENNReal.ofReal ((∏ j ∈ Finset.range N, sliceFactor (S := S) (effMass m j))
          * Real.sqrt (Real.pi / effMass m N) ^ Fintype.card S) := by
  rw [chainZ_closed (S := S) m (m / 2) hm (by linarith) N]
  simp only [effSeq_half]

/-- `diffSq` is symmetric in its two arguments. -/
theorem diffSq_comm {S : Type*} [Fintype S] (v w : S → ℝ) : diffSq v w = diffSq w v := by
  simp only [diffSq]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## 4. Chain re-indexing: the lattice action is a pair of chain forms -/

section Reindex

variable {m : ℝ}

/-- The `k`-th slice of `chain z y` for `k` a successor is the interior slice `y k`. -/
theorem chain_succ_eq {n : ℕ} (z : S → ℝ) (y : Fin n → S → ℝ) (k : Fin n) :
    chain z y k.succ = y k := by
  simp [chain]

/-- The zeroth slice of `chain z y` is the reflection slice `z`. -/
theorem chain_zero_eq {n : ℕ} (z : S → ℝ) (y : Fin n → S → ℝ) :
    chain z y (0 : Fin (n + 1)) = z := by
  simp [chain]

/-- Prepending the reflection slice and then dropping the first interior slice recovers the
interior chain: the two labellings agree. -/
theorem chain_cons_eq {n : ℕ} (z : S → ℝ) (y : Fin n → S → ℝ) :
    chain z y = Fin.cons z y := by
  funext k i
  induction k using Fin.cases with
  | zero => simp [chain]
  | succ j => simp [chain]

/-- The half-space chain with the reflection slice dropped is the interior chain. -/
theorem chain_self_tail {n : ℕ} (y : Fin (n + 1) → S → ℝ) :
    chain (y 0) (Fin.tail y) = y := by
  funext k i
  induction k using Fin.cases with
  | zero => simp [chain]
  | succ j => simp [chain, Fin.tail]

/-- **Splitting the half-space action at its first interior slice.**  The link from the
reflection slice and the mass term of the first interior slice come off, and what remains is the
same half-space action started at the first interior slice — the recursion that makes the
half-space a chain. -/
theorem halfAction_split {n : ℕ} (z : S → ℝ) (y : Fin (n + 1) → S → ℝ) :
    halfAction (S := S) m z y =
      diffSq z (y 0) + (m / 2) * sqSum (y 0)
        + halfAction (S := S) m (y 0) (Fin.tail y) := by
  have h0 : (∑ i, (chain z y (0 : Fin (n + 1)).succ i - chain z y (0 : Fin (n + 1)).castSucc i) ^ 2)
      = diffSq z (y 0) := by
    have hy : chain z y (0 : Fin (n + 1)).succ = y 0 := chain_succ_eq z y 0
    have hz : chain z y (0 : Fin (n + 1)).castSucc = z := chain_zero_eq z y
    simp only [diffSq, hy, hz]
  have hm0 : (∑ i, (chain z y (0 : Fin (n + 1)).succ i) ^ 2) = sqSum (y 0) := by
    rw [chain_succ_eq]
    rfl
  have hrest : ∀ j : Fin n,
      (∑ i, (chain z y j.succ.succ i - chain z y (j.succ : Fin (n + 1)).castSucc i) ^ 2)
        = ∑ i, (chain (y 0) (Fin.tail y) j.succ i
            - chain (y 0) (Fin.tail y) j.castSucc i) ^ 2 := by
    intro j
    have h1 : chain z y j.succ.succ = y j.succ := chain_succ_eq z y j.succ
    have h2 : chain z y (j.succ : Fin (n + 1)).castSucc = y j.castSucc := by
      have he : (j.succ : Fin (n + 1)).castSucc = (j.castSucc : Fin (n + 1)).succ :=
        Fin.ext rfl
      rw [he]
      exact chain_succ_eq z y j.castSucc
    simp only [h1, h2, chain_self_tail]
  have hmass : ∀ j : Fin n,
      (∑ i, (chain z y j.succ.succ i) ^ 2)
        = ∑ i, (chain (y 0) (Fin.tail y) j.succ i) ^ 2 := by
    intro j
    have h1 : chain z y j.succ.succ = y j.succ := chain_succ_eq z y j.succ
    simp only [h1, chain_self_tail]
  unfold halfAction
  rw [Fin.sum_univ_succ (f := fun k : Fin (n + 1) =>
        ∑ i, (chain z y k.succ i - chain z y k.castSucc i) ^ 2),
      Fin.sum_univ_succ (f := fun k : Fin (n + 1) =>
        ∑ i, (chain z y k.succ i) ^ 2),
      Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hrest j),
      Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hmass j), h0, hm0]
  ring

/-- **The re-indexing lemma.**  A half-space 'past' configuration `(z, y)` — the reflection slice
together with `n` interior slices — is a *chain*: its half-space action is the chain form whose
outermost slice is `z` carrying the (chosen) total coefficient `c`. -/
theorem chainForm_chain (c : ℝ) {n : ℕ} (z : S → ℝ) (y : Fin n → S → ℝ) :
    chainForm (S := S) m c n (chain z y) = c * sqSum z + halfAction (S := S) m z y := by
  induction n generalizing c z with
  | zero =>
    simp only [chainForm, chain_zero_eq, halfAction, Finset.univ_eq_empty, Finset.sum_empty,
      add_zero, mul_zero]
  | succ n ih =>
    rw [chain_cons_eq z y, chainForm_cons]
    rw [halfAction_split (m := m) (n := n) (z := z) (y := y)]
    have hih := ih (m / 2) (y 0) (Fin.tail y)
    rw [chain_self_tail y] at hih
    rw [hih, diffSq_comm (v := y 0) (w := z)]
    ring

/-- **The chain re-indexing of the lattice action.**  The action of the `2n + 1`-slice lattice,
split at the reflection slice, is the sum of two chain forms: the past half-space is the chain
whose outermost slice is `z` with total coefficient `0` (its links only), and the future
half-space is the same chain with the boundary mass `m/2` placed on `z`. -/
theorem latticeAction_chain {n : ℕ} (z : S → ℝ) (y₁ y₂ : Fin n → S → ℝ) :
    latticeAction (S := S) m (z, (y₁, y₂))
      = chainForm (S := S) m 0 n (chain z y₁)
        + chainForm (S := S) m (m / 2) n (chain z y₂) := by
  rw [latticeAction, chainForm_chain (c := 0), chainForm_chain (c := m / 2), boundaryTerm]
  simp only [sqSum]
  ring

end Reindex

/-! ## 5. The half-space measure is a chain -/

/-- **The mass of the half-space kernel is the chain partition function.**  In the notation of
`LatticeFreeField`, `ρ = exp(−d)` is the boundary weight and `ν_z = exp(−h(z,·))` the weight of one
half-space.  Integrating the product `ρ(z)·ν_z(y)` against the product Lebesgue measure on
`z` and `y` gives the chain partition function of `n + 1` slices whose *outermost* slice is the
reflection slice `z`, carrying the boundary mass `m/2` as its total coefficient — the
measure-level counterpart of the action-level re-indexing `chainForm_chain`.  (The iterated form
`∫⁻ z, ρ(z)·(∫⁻ y, ν_z y)` is the same statement by Tonelli.) -/
theorem lintegral_fkKernel_eq_chainZ (m : ℝ) (n : ℕ) :
    ∫⁻ p : (S → ℝ) × (Fin n → S → ℝ),
        ENNReal.ofReal (boundaryWeight m p.1 * halfWeight (S := S) m p.1 p.2)
      = chainZ (S := S) m (m / 2) n := by
  have hstep : ∀ p : (S → ℝ) × (Fin n → S → ℝ),
      ENNReal.ofReal (boundaryWeight m p.1 * halfWeight (S := S) m p.1 p.2)
        = ENNReal.ofReal
            (Real.exp (-(chainForm (S := S) m (m / 2) n (chain p.1 p.2)))) := by
    intro p
    have hexp : boundaryWeight m p.1 * halfWeight (S := S) m p.1 p.2
        = Real.exp (-(chainForm (S := S) m (m / 2) n (chain p.1 p.2))) := by
      rw [boundaryWeight, halfWeight, ← Real.exp_add, chainForm_chain (c := m / 2)]
      congr 1
      simp only [boundaryTerm, sqSum]
      ring
    rw [hexp]
  simp only [hstep]
  have hp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => (S → ℝ)) (0 : Fin (n + 1))
  have hcons : ∀ a : (S → ℝ) × (Fin n → S → ℝ),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => (S → ℝ))
        (0 : Fin (n + 1))).symm a = Fin.cons a.1 a.2 := by
    intro a
    funext j
    rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
      Fin.insertNth_zero']
  rw [chainZ]
  rw [← hp.symm.lintegral_comp (f := fun y : Fin (n + 1) → (S → ℝ) =>
    ENNReal.ofReal (Real.exp (-(chainForm (S := S) m (m / 2) n y)))) ?_]
  · refine lintegral_congr fun a => ?_
    simp only [hcons a, chain_cons_eq]
  · exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (Measurable.neg (measurable_chainForm (S := S) m (m / 2) n)))

/-! ## 6. The tridiagonal operator of the chain -/

section Determ

/-- **The tridiagonal matrix of the chain.**  On one site, the quadratic form `chainForm m c L` is
`xᵀ (chainMatrix m c L) x`: the outermost slice carries the total coefficient `c` together with its
single link (`1 + c`), the interior slices carry the mass `m/2` and two links (`2 + m/2`), the
innermost slice the mass and one link (`1 + m/2`), and neighbouring slices are coupled by `−1`.
The single-slice chain has no link, so its matrix is just `!![c]`.  The definition is written
directly in terms of the index values rather than by recursion on `L`, so that its entries reduce
for a symbolic `L`. -/
def chainMatrix (m c : ℝ) (L : ℕ) : Matrix (Fin (L + 1)) (Fin (L + 1)) ℝ :=
  fun i j =>
    if i.val = j.val then
      (if i.val = 0 then (if L = 0 then c else 1 + c)
       else if i.val = L then 1 + m / 2 else 2 + m / 2)
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then (-1 : ℝ) else 0

/-- The determinant of the one-slice chain is its total coefficient: `det = c₀`. -/
theorem chainMatrix_zero (m c : ℝ) : (chainMatrix m c 0).det = c := by
  rw [Matrix.det_fin_one]
  simp [chainMatrix]

/-- **The determinant of the two-slice chain**: `det = (1 + c₀)·c₁`, i.e. the mass recursion
`c₁ = m/2 + c₀/(1 + c₀)` is exactly one step of Gaussian elimination on the tridiagonal operator. -/
theorem chainMatrix_one (m c : ℝ) (hc : 0 < c) :
    (chainMatrix m c 1).det = (1 + effSeq m c 0) * effSeq m c 1 := by
  have h1c : (1 + c) ≠ 0 := by positivity
  rw [Matrix.det_fin_two]
  simp only [effSeq_zero, effSeq_succ, effCorr]
  simp [chainMatrix]
  field_simp
  ring

/-- `{0} ⊔ {1, …, n}` re-indexed as `{0, …, n}`: the split used to read the outermost slice of a
chain matrix as a `1 × 1` corner. -/
def finSumOneEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
  (finSumFinEquiv (m := 1) (n := n)).trans (finCongr (Nat.add_comm 1 n))

theorem finSumOneEquiv_left (n : ℕ) : finSumOneEquiv n (Sum.inl 0) = (0 : Fin (n + 1)) := by
  simp [finSumOneEquiv, Fin.ext_iff]

theorem finSumOneEquiv_right (n : ℕ) (j : Fin n) : finSumOneEquiv n (Sum.inr j) = j.succ := by
  apply Fin.ext
  simp [finSumOneEquiv, Fin.val_succ]

set_option maxHeartbeats 1000000 in
-- the block re-indexing and the entry computation need more than the default budget
/-- **Block elimination at the outermost slice** (the Schur complement of a `1 × 1` corner):
for any `A` with `A 0 0 ≠ 0`,
`det A = A 0 0 · det (A₀₀ − (A_{·0}/A 0 0) ⊗ A_{0·})`,
where `A₀₀` is `A` with its first row and column deleted and the rank-one matrix is the outer
product of the first column (divided by `A 0 0`) with the first row.

The matrix is written as the product of the lower block-triangular elimination matrix with the
eliminated matrix, both read as `2 × 2` blocks along `{0} ⊔ {1, …, n}`, and each determinant is
`Matrix.det_fromBlocks_zero₁₂`.  This is the step that Mathlib provides only through
`Matrix.det_fromBlocks₁₁` (which needs an `Invertible` top-left block). -/
theorem det_corner_schur {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (ha : A 0 0 ≠ 0) :
    A.det =
      A 0 0 *
        (A.submatrix Fin.succ Fin.succ -
            Matrix.vecMulVec (fun i : Fin n => A i.succ 0 / A 0 0)
              (fun j : Fin n => A 0 j.succ)).det := by
  have hs0 : (finSumOneEquiv n).symm (0 : Fin (n + 1)) = Sum.inl 0 := by
    rw [Equiv.symm_apply_eq]
    exact (finSumOneEquiv_left n).symm
  have hs1 : ∀ j : Fin n, (finSumOneEquiv n).symm j.succ = Sum.inr j := by
    intro j
    rw [Equiv.symm_apply_eq]
    exact (finSumOneEquiv_right n j).symm
  have hblk : (Matrix.fromBlocks (fun _ _ : Fin 1 => A 0 0)
        (fun (_ : Fin 1) (j : Fin n) => A 0 j.succ)
        (fun (i : Fin n) (_ : Fin 1) => A i.succ 0)
        (A.submatrix Fin.succ Fin.succ)).submatrix (finSumOneEquiv n).symm
        (finSumOneEquiv n).symm = A := by
    ext i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp [Matrix.submatrix_apply, hs0]
      | succ q => simp [Matrix.submatrix_apply, hs0, hs1]
    | succ p =>
      induction j using Fin.cases with
      | zero => simp [Matrix.submatrix_apply, hs0, hs1]
      | succ q => simp [Matrix.submatrix_apply, hs1]
  have hprod :
      Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin n) ℝ)
          (Matrix.of fun (i : Fin n) (_ : Fin 1) => A i.succ 0 / A 0 0)
          (1 : Matrix (Fin n) (Fin n) ℝ) *
        Matrix.fromBlocks (fun _ _ : Fin 1 => A 0 0) (fun (_ : Fin 1) (j : Fin n) => A 0 j.succ)
          (0 : Matrix (Fin n) (Fin 1) ℝ)
          (A.submatrix Fin.succ Fin.succ -
            Matrix.vecMulVec (fun i : Fin n => A i.succ 0 / A 0 0)
              (fun j : Fin n => A 0 j.succ)) =
      Matrix.fromBlocks (fun _ _ : Fin 1 => A 0 0) (fun (_ : Fin 1) (j : Fin n) => A 0 j.succ)
        (fun (i : Fin n) (_ : Fin 1) => A i.succ 0) (A.submatrix Fin.succ Fin.succ) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp
    · ext i j
      fin_cases j
      simp [Matrix.mul_apply, ha]
    · simp only [Matrix.one_mul]
      ext i j
      simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  have hdet : A.det = (Matrix.fromBlocks (fun _ _ : Fin 1 => A 0 0)
        (fun (_ : Fin 1) (j : Fin n) => A 0 j.succ)
        (fun (i : Fin n) (_ : Fin 1) => A i.succ 0)
        (A.submatrix Fin.succ Fin.succ)).det := by
    conv_lhs => rw [← hblk]
    exact Matrix.det_submatrix_equiv_self (finSumOneEquiv n).symm _
  rw [hdet, ← hprod, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_fin_one]
  simp

set_option maxHeartbeats 2000000 in
-- the entrywise comparison of the two tridiagonal matrices needs more than the default budget
/-- **One step of elimination on the chain matrix.**  Peeling off the outermost slice of a chain
with total coefficient `c` leaves the chain matrix of the *remaining* slices with total coefficient
`m/2 + c/(1 + c)`: the mass recursion of `effSeq` is the Schur complement of the corner. -/
theorem chainMatrix_succ_det (m c : ℝ) (hc : 0 < c) (N : ℕ) :
    (chainMatrix m c (N + 1)).det = (1 + c) * (chainMatrix m (m / 2 + effCorr c) N).det := by
  have ha : chainMatrix m c (N + 1) 0 0 = 1 + c := by simp [chainMatrix]
  have ha0 : chainMatrix m c (N + 1) 0 0 ≠ 0 := by
    rw [ha]
    positivity
  have hkey : (chainMatrix m c (N + 1)).submatrix Fin.succ Fin.succ
      - Matrix.vecMulVec
          (fun i : Fin (N + 1) => chainMatrix m c (N + 1) i.succ 0 / chainMatrix m c (N + 1) 0 0)
          (fun j : Fin (N + 1) => chainMatrix m c (N + 1) 0 j.succ)
      = chainMatrix m (m / 2 + effCorr c) N := by
    have h1c : (1 + c) ≠ 0 := by positivity
    ext i j
    simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.vecMulVec_apply, chainMatrix,
      Fin.val_succ, Fin.val_zero, effCorr]
    split_ifs
    all_goals simp only [or_false, false_or, not_false_eq_true] at *
    all_goals try (exfalso; omega)
    all_goals first | (ring; done) | (field_simp; ring)
  rw [det_corner_schur (A := chainMatrix m c (N + 1)) ha0, hkey, ha]

/-- **The determinant of the chain matrix**: `det K_N = ∏_{j<N} (1 + c_j) · c_N`, the general
form of `chainMatrix_zero` and `chainMatrix_one`, obtained by iterating the elimination step
`chainMatrix_succ_det`. -/
theorem chainMatrix_det (m c : ℝ) (hm : 0 < m) (hc : 0 < c) (N : ℕ) :
    (chainMatrix m c N).det = (∏ j ∈ Finset.range N, (1 + effSeq m c j)) * effSeq m c N := by
  induction N generalizing c with
  | zero =>
    rw [chainMatrix_zero]
    simp [effSeq_zero]
  | succ N ih =>
    rw [chainMatrix_succ_det (m := m) (c := c) hc N,
      ih (m / 2 + effCorr c) (by have := effCorr_pos hc; linarith)]
    simp only [effSeq_shift]
    rw [Finset.prod_range_succ', effSeq_zero]
    ring

/-- **The determinant of the free field's chain matrix**, with the effective masses
`μ_j = effMass m j`: `det K_N = ∏_{j<N} (1 + μ_j) · μ_N`.  This is the algebraic half of the
closed form `Z = π^{(N+1)|S|/2}/(det K_N)^{|S|/2}` of `chainZ_closed_det`. -/
theorem chainMatrix_det_half (m : ℝ) (hm : 0 < m) (N : ℕ) :
    (chainMatrix m (m / 2) N).det =
      (∏ j ∈ Finset.range N, (1 + effMass m j)) * effMass m N := by
  rw [chainMatrix_det m (m / 2) hm (by linarith) N]
  simp only [effSeq_half]

/-- The product of the slice factors of a chain is one square root of the reciprocal determinant:
`(∏_{j<N} √(π/(1 + μ_j))) · √(π/μ_N) = √(π^{N+1} / det K_N)`. -/
theorem prod_sqrt_sliceFactor_eq_sqrt_det (m : ℝ) (hm : 0 < m) (N : ℕ) :
    (∏ j ∈ Finset.range N, Real.sqrt (Real.pi / (1 + effMass m j))) *
        Real.sqrt (Real.pi / effMass m N)
      = Real.sqrt (Real.pi ^ (N + 1) / (chainMatrix m (m / 2) N).det) := by
  have hpos : ∀ j ∈ Finset.range N, 0 ≤ Real.pi / (1 + effMass m j) := fun j _ =>
    div_nonneg Real.pi_pos.le (by have := effMass_pos m hm j; linarith)
  have hPpos : 0 < ∏ j ∈ Finset.range N, (1 + effMass m j) := by
    refine Finset.prod_pos fun j _ => ?_
    have := effMass_pos m hm j
    linarith
  have hμ : 0 < effMass m N := effMass_pos m hm N
  have hA : 0 ≤ ∏ j ∈ Finset.range N, Real.pi / (1 + effMass m j) :=
    Finset.prod_nonneg hpos
  rw [← Real.sqrt_prod (Finset.range N) hpos, ← Real.sqrt_mul hA]
  congr 1
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
    chainMatrix_det_half m hm N]
  field_simp
  ring

/-- **The free-field normalising constant in determinant form**:
`Z_N = π^{(N+1)|S|/2} / (det K_N)^{|S|/2}`, i.e. `chainZ_closed_half` with the product of slice
factors evaluated by `chainMatrix_det_half`.  Against the *standard* lattice operator
`K = 2·chainMatrix` this is the textbook `(2π)^{(N+1)|S|/2} / √(det K)^{|S|}`. -/
theorem chainZ_closed_det (m : ℝ) (hm : 0 < m) (N : ℕ) :
    chainZ (S := S) m (m / 2) N
      = ENNReal.ofReal
          (Real.sqrt (Real.pi ^ (N + 1) / (chainMatrix m (m / 2) N).det) ^ Fintype.card S) := by
  rw [chainZ_closed_half m hm N]
  congr 1
  simp only [sliceFactor, Finset.prod_pow, ← mul_pow]
  rw [prod_sqrt_sliceFactor_eq_sqrt_det m hm N]

end Determ

/-! ## 7. The slices of the lattice as a chain

`chainForm m (m/2)` — the chain form with the uniform coefficient — is the sum of the mass terms
and the links (**`chainForm_symm`**) and is invariant under reversing the chain
(**`chainForm_symm_rev`**).  On that basis `foldIdx` indexes the `2n + 1` slices of the lattice as
a chain — the past half read backwards, the reflection slice, then the future half — and
`foldChainInvEquiv` / `foldChainEquiv` realise that indexing as a measure-preserving permutation
of `volume` (**`volume_preserving_foldChainEquiv`**).Proved here: the inverse permutation reads off the reflection slice and the two halves
(**`foldChainEquiv_center`**, **`foldChainEquiv_past`**, **`foldChainEquiv_future`**, whose
statements are the `succAbove`-projections of `MeasurableEquiv.piFinSuccAbove`), and the **mass
term** of the folded chain is the total mass term of the lattice
(**`sum_foldChain_sqSum`**).  Section 8 does the same for the **links**. -/
/-- The chain form with the uniform coefficient `m/2` is the sum of the mass terms and the
links. -/
theorem chainForm_symm (m : ℝ) (N : ℕ) (y : Fin (N + 1) → (S → ℝ)) :
    chainForm (S := S) m (m / 2) N y
      = (m / 2) * ∑ k : Fin (N + 1), sqSum (y k)
        + ∑ k : Fin N, diffSq (y k.succ) (y k.castSucc) := by
  induction N with
  | zero => simp [chainForm]
  | succ N ih =>
    have hy : (1 : Fin (N + 1 + 1)) = Fin.succ 0 := Fin.ext rfl
    have h1 : chainForm (S := S) m (m / 2) (N + 1) y
        = (m / 2) * sqSum (y 0) + diffSq (y 0) (y (Fin.succ 0))
          + chainForm (S := S) m (m / 2) N (fun j => y j.succ) := by
      simp only [chainForm, diffSq, sqSum, hy]
    rw [h1, ih (fun j : Fin (N + 1) => y j.succ)]
    rw [Fin.sum_univ_succ (f := fun k : Fin (N + 2) => sqSum (y k)),
      Fin.sum_univ_succ (f := fun k : Fin (N + 1) => diffSq (y k.succ) (y k.castSucc))]
    simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero]
    have hkey : (∑ k : Fin N, diffSq (y k.succ.succ) (y k.castSucc.succ))
        = (∑ k : Fin N, diffSq (y k.succ.succ) (y k.succ.castSucc)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (k.succ : Fin (N + 1)).castSucc = (k.castSucc : Fin (N + 1)).succ
        from Fin.ext rfl]
    rw [hkey, hy, diffSq_comm (v := y 0) (w := y (Fin.succ 0))]
    simp only [diffSq, sqSum]
    ring

/-- **The chain form with uniform coefficient is reversal invariant.** -/
theorem chainForm_symm_rev (m : ℝ) (N : ℕ) (y : Fin (N + 1) → (S → ℝ)) :
    chainForm (S := S) m (m / 2) N (fun k => y (Fin.rev k))
      = chainForm (S := S) m (m / 2) N y := by
  rw [chainForm_symm, chainForm_symm]
  have hm : (∑ k : Fin (N + 1), sqSum ((fun k => y (Fin.rev k)) k))
      = (∑ k : Fin (N + 1), sqSum (y k)) :=
    Equiv.sum_comp Fin.revPerm (fun k => sqSum (y k))
  have hl : (∑ k : Fin N, diffSq ((fun k => y (Fin.rev k)) k.succ)
        ((fun k => y (Fin.rev k)) k.castSucc))
      = (∑ k : Fin N, diffSq (y k.succ) (y k.castSucc)) := by
    have hterm : ∀ k : Fin N,
        diffSq (y (k.succ.rev)) (y (k.castSucc.rev))
          = diffSq (y k.rev.succ) (y k.rev.castSucc) := by
      intro k
      rw [Fin.rev_succ, Fin.rev_castSucc, diffSq_comm]
    calc (∑ k : Fin N, diffSq (y (k.succ.rev)) (y (k.castSucc.rev)))
        = ∑ k : Fin N, diffSq (y k.rev.succ) (y k.rev.castSucc) :=
          Finset.sum_congr rfl fun k _ => hterm k
      _ = _ := Equiv.sum_comp Fin.revPerm (fun k => diffSq (y k.succ) (y k.castSucc))
  rw [hm, hl]

/-- A chain slice that is not the boundary slice is an interior slice. -/
theorem chain_of_ne_zero {n : ℕ} (z : S → ℝ) (y : Fin n → S → ℝ) (i : Fin (n + 1))
    (h : i ≠ 0) : chain z y i = y (Fin.pred i h) := by
  conv_lhs => rw [← Fin.succ_pred i h]
  exact chain_succ_eq z y _

/-! ## The folded chain -/

/-- The inverse of the slice indexing of the folded chain: a position of the chain is either in
the past half (read backwards), the reflection slice, or in the future half. -/
def foldInvFun (n : ℕ) : Fin (2 * n) → Fin n ⊕ Fin n :=
  fun k => if h : k.val < n then Sum.inl ⟨n - 1 - k.val, by have := k.isLt; omega⟩
            else Sum.inr ⟨k.val - n, by have := k.isLt; omega⟩

theorem foldInvFun_of_lt (n : ℕ) (k : Fin (2 * n)) (h : k.val < n) :
    foldInvFun n k = Sum.inl (⟨n - 1 - k.val, by have := k.isLt; omega⟩ : Fin n) := by
  unfold foldInvFun
  rw [dif_pos h]

theorem foldInvFun_of_le (n : ℕ) (k : Fin (2 * n)) (h : n ≤ k.val) :
    foldInvFun n k = Sum.inr (⟨k.val - n, by have := k.isLt; omega⟩ : Fin n) := by
  unfold foldInvFun
  rw [dif_neg (by omega)]

/-- The `2n + 1` slices of the folded lattice chain.  The past half is indexed *backwards* —
position `k < n` is the slice `y (n - 1 - k)`, counting inwards from the far wall — position `n`
is the reflection slice, and position `n + 1 + j` is the `j`-th slice of the future half.  This is
the order in which the slices of the lattice form a chain. -/
def foldIdx (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (2 * n) where
  toFun x :=
    match x with
    | Sum.inl j => ⟨n - 1 - j.val, by have := j.isLt; omega⟩
    | Sum.inr j => ⟨n + j.val, by have := j.isLt; omega⟩
  invFun := foldInvFun n
  left_inv := by
    rintro (j | j)
    · rw [foldInvFun_of_lt n _ (by show n - 1 - ↑j < n; have := j.isLt; omega)]
      congr 1
      exact Fin.ext (by show n - 1 - (n - 1 - ↑j) = ↑j; omega)
    · rw [foldInvFun_of_le n _ (by show n ≤ n + ↑j; omega)]
      congr 1
      exact Fin.ext (by show n + ↑j - n = ↑j; omega)
  right_inv := by
    intro k
    by_cases h : k.val < n
    · rw [foldInvFun_of_lt n k h]
      exact Fin.ext (by show n - 1 - (n - 1 - k.val) = k.val; omega)
    · rw [foldInvFun_of_le n k (by omega)]
      exact Fin.ext (by show n + (k.val - n) = k.val; omega)

@[simp] theorem foldIdx_inl_val (n : ℕ) (j : Fin n) : (foldIdx n (Sum.inl j)).val = n - 1 - j.val :=
  rfl

@[simp] theorem foldIdx_inr_val (n : ℕ) (j : Fin n) : (foldIdx n (Sum.inr j)).val = n + j.val := rfl

theorem foldIdx_symm_of_lt (n : ℕ) (k : Fin (2 * n)) (h : k.val < n) :
    (foldIdx n).symm k = Sum.inl (⟨n - 1 - k.val, by have := k.isLt; omega⟩ : Fin n) :=
  foldInvFun_of_lt n k h

theorem foldIdx_symm_of_le (n : ℕ) (k : Fin (2 * n)) (h : n ≤ k.val) :
    (foldIdx n).symm k = Sum.inr (⟨k.val - n, by have := k.isLt; omega⟩ : Fin n) :=
  foldInvFun_of_le n k h

section Fold

/-- **The permutation of the `2n + 1` slices** that presents the lattice as a chain: from the
`2n + 1` slices it reads the reflection slice and the two half-spaces. -/
def foldChainInvEquiv (n : ℕ) :
    (Fin (2 * n + 1) → (S → ℝ)) ≃ᵐ
      ((S → ℝ) × ((Fin n → (S → ℝ)) × (Fin n → (S → ℝ)))) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (2 * n + 1) => (S → ℝ)) ⟨n, by omega⟩).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (S → ℝ))
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin n ⊕ Fin n => (S → ℝ))
          (foldIdx n).symm).trans
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => (S → ℝ)))))

/-- The permutation of the slices, in the direction the lattice uses. -/
def foldChainEquiv (n : ℕ) :
    ((S → ℝ) × ((Fin n → (S → ℝ)) × (Fin n → (S → ℝ)))) ≃ᵐ
      (Fin (2 * n + 1) → (S → ℝ)) :=
  (foldChainInvEquiv (S := S) n).symm

theorem volume_preserving_foldChainInvEquiv (n : ℕ) :
    MeasurePreserving (foldChainInvEquiv (S := S) n) := by
  have h1 := MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin (2 * n + 1) => (S → ℝ)) ⟨n, by omega⟩
  have h2 : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (S → ℝ))
        ((MeasurableEquiv.piCongrLeft (fun _ : Fin n ⊕ Fin n => (S → ℝ))
            (foldIdx n).symm).trans
          (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => (S → ℝ))))) := by
    refine MeasureTheory.MeasurePreserving.prod ?_ ?_
    · exact MeasureTheory.MeasurePreserving.id volume
    · exact (MeasureTheory.volume_measurePreserving_sumPiEquivProdPi _).comp
        (MeasureTheory.volume_measurePreserving_piCongrLeft _ (foldIdx n).symm)
  exact h2.comp h1

theorem volume_preserving_foldChainEquiv (n : ℕ) :
    MeasurePreserving (foldChainEquiv (S := S) n) :=
  (volume_preserving_foldChainInvEquiv (S := S) n).symm

end Fold

section FoldVal

variable {n : ℕ}

/-- Transporting along an equality with a constant motive changes nothing. -/
theorem eqRec_constMotive {α β : Sort*} {x y : α} (a : β) (h : x = y) :
    @Eq.rec α x (fun _ _ => β) a y h = a := by
  cases h
  rfl

theorem foldChainInvEquiv_fst (φ : Fin (2 * n + 1) → (S → ℝ)) :
    (foldChainInvEquiv (S := S) n φ).1 = φ ⟨n, by omega⟩ := by
  simp only [foldChainInvEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.coe_mk,
    MeasurableEquiv.prodCongr, Equiv.prodCongr_apply, Prod.map_fst,
    MeasurableEquiv.refl_toEquiv, MeasurableEquiv.piFinSuccAbove_apply,
    Fin.insertNthEquiv_symm_apply, Equiv.refl_apply, id]

theorem foldChainInvEquiv_snd_fst (φ : Fin (2 * n + 1) → (S → ℝ)) (i : Fin n) :
    (foldChainInvEquiv (S := S) n φ).2.1 i =
      φ ((⟨n, by omega⟩ : Fin (2 * n + 1)).succAbove (foldIdx n (Sum.inl i))) := by
  simp only [foldChainInvEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.coe_mk,
    MeasurableEquiv.prodCongr, Equiv.prodCongr_apply, Prod.map_snd,
    Equiv.sumPiEquivProdPi_apply, Equiv.trans_apply, MeasurableEquiv.refl_apply,
    MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
    Fin.removeNth_apply, MeasurableEquiv.trans_toEquiv, MeasurableEquiv.coe_toEquiv,
    MeasurableEquiv.coe_sumPiEquivProdPi, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply, Equiv.symm_symm]
  rw [eqRec_constMotive]

theorem foldChainInvEquiv_snd_snd (φ : Fin (2 * n + 1) → (S → ℝ)) (i : Fin n) :
    (foldChainInvEquiv (S := S) n φ).2.2 i =
      φ ((⟨n, by omega⟩ : Fin (2 * n + 1)).succAbove (foldIdx n (Sum.inr i))) := by
  simp only [foldChainInvEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.coe_mk,
    MeasurableEquiv.prodCongr, Equiv.prodCongr_apply, Prod.map_snd,
    Equiv.sumPiEquivProdPi_apply, Equiv.trans_apply, MeasurableEquiv.refl_apply,
    MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
    Fin.removeNth_apply, MeasurableEquiv.trans_toEquiv, MeasurableEquiv.coe_toEquiv,
    MeasurableEquiv.coe_sumPiEquivProdPi, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply, Equiv.symm_symm]
  rw [eqRec_constMotive]

end FoldVal

section FoldSums

variable {n : ℕ}

theorem foldChainEquiv_center
    (p : (S → ℝ) × ((Fin n → (S → ℝ)) × (Fin n → (S → ℝ)))) :
    foldChainEquiv (S := S) n p ⟨n, by omega⟩ = p.1 := by
  have h := (foldChainInvEquiv (S := S) n).apply_symm_apply p
  have h1 := congrArg Prod.fst h
  rw [foldChainInvEquiv_fst] at h1
  simp only [foldChainEquiv]
  exact h1

theorem foldChainEquiv_past
    (p : (S → ℝ) × ((Fin n → (S → ℝ)) × (Fin n → (S → ℝ)))) (i : Fin n) :
    foldChainEquiv (S := S) n p
      ((⟨n, by omega⟩ : Fin (2 * n + 1)).succAbove (foldIdx n (Sum.inl i))) = p.2.1 i := by
  have h := (foldChainInvEquiv (S := S) n).apply_symm_apply p
  have h2 := congrArg (fun q => q.2.1 i) h
  beta_reduce at h2
  rw [foldChainInvEquiv_snd_fst] at h2
  simp only [foldChainEquiv]
  exact h2

theorem foldChainEquiv_future
    (p : (S → ℝ) × ((Fin n → (S → ℝ)) × (Fin n → (S → ℝ)))) (i : Fin n) :
    foldChainEquiv (S := S) n p
      ((⟨n, by omega⟩ : Fin (2 * n + 1)).succAbove (foldIdx n (Sum.inr i))) = p.2.2 i := by
  have h := (foldChainInvEquiv (S := S) n).apply_symm_apply p
  have h2 := congrArg (fun q => q.2.2 i) h
  beta_reduce at h2
  rw [foldChainInvEquiv_snd_snd] at h2
  simp only [foldChainEquiv]
  exact h2

/-- The mass sum over the folded chain splits into the reflection slice and the two halves. -/
theorem sum_foldChain_sqSum
    (p : (S → ℝ) × ((Fin n → (S → ℝ)) × (Fin n → (S → ℝ)))) :
    (∑ k : Fin (2 * n + 1), sqSum (foldChainEquiv (S := S) n p k))
      = sqSum p.1 + (∑ i : Fin n, sqSum (p.2.1 i)) + ∑ i : Fin n, sqSum (p.2.2 i) := by
  rw [Fin.sum_univ_succAbove (f := fun k : Fin (2 * n + 1) =>
    sqSum (foldChainEquiv (S := S) n p k)) ⟨n, by omega⟩,
    foldChainEquiv_center]
  rw [← Equiv.sum_comp (foldIdx n) (fun j : Fin (2 * n) =>
    sqSum (foldChainEquiv (S := S) n p ((⟨n, by omega⟩ : Fin (2 * n + 1)).succAbove j)))]
  rw [Fintype.sum_sum_type]
  rw [show (∑ i : Fin n, sqSum (foldChainEquiv (S := S) n p
        ((⟨n, by omega⟩ : Fin (2 * n + 1)).succAbove (foldIdx n (Sum.inl i)))))
      = ∑ i : Fin n, sqSum (p.2.1 i) from
    Finset.sum_congr rfl fun i _ => by rw [foldChainEquiv_past]]
  rw [show (∑ i : Fin n, sqSum (foldChainEquiv (S := S) n p
        ((⟨n, by omega⟩ : Fin (2 * n + 1)).succAbove (foldIdx n (Sum.inr i)))))
      = ∑ i : Fin n, sqSum (p.2.2 i) from
    Finset.sum_congr rfl fun i _ => by rw [foldChainEquiv_future]]
  ring

end FoldSums

/-! ## 8. The links of the folded chain, and the lattice partition function

Section 7 matched the mass term of the `2n + 1`-slice lattice with the mass term of the folded
chain.  Here the **links** are matched, and the two together give the identity of the actions and
then of the partition functions.

`sum_foldIdx_split` splits the `2n` links of the fold at the reflection slice — the past half is
traversed backwards, the future half forwards — and `foldChainEquiv_past_chain` /
`foldChainEquiv_future_chain` say that position `n − j` of the fold is the `j`-th slice of
`chain z y₁` and position `n + j` is the `j`-th slice of `chain z y₂`.  Hence
**`sum_foldChain_diffSq`**: the links of the fold are the links of the two half-space chains.
With `sum_foldChain_sqSum` and `boundaryTerm` this makes the lattice action the chain form of the
folded slices (**`latticeAction_eq_chainForm`**), and since `foldChainEquiv` is measure preserving,
**`latticeGFFMass m n = chainZ m (m/2) (2n)`**. -/

section Linking

variable {n : ℕ}

/-- The `j`-th slice of the past chain is position `n − j` of the folded chain. -/
theorem foldChainEquiv_past_chain
    (p : (S → ℝ) × ((Fin n → (S → ℝ)) × (Fin n → (S → ℝ)))) (j : Fin (n + 1)) :
    foldChainEquiv (S := S) n p ⟨n - j.val, by have := j.isLt; omega⟩
      = chain p.1 p.2.1 j := by
  induction j using Fin.cases with
  | zero =>
    have hidx : (⟨n - (0 : Fin (n + 1)).val, by omega⟩ : Fin (2 * n + 1))
        = ⟨n, by omega⟩ := Fin.ext (by simp)
    rw [hidx, foldChainEquiv_center]
    rfl
  | succ k =>
    have hlt : (foldIdx n (Sum.inl k)).castSucc < (⟨n, by omega⟩ : Fin (2 * n + 1)) := by
      change ((foldIdx n (Sum.inl k)) : Fin (2 * n)).val < n
      rw [foldIdx_inl_val]
      have := k.isLt
      omega
    have hidx : (⟨n - (k.succ).val, by have := k.isLt; omega⟩ : Fin (2 * n + 1))
        = (⟨n, by omega⟩ : Fin (2 * n + 1)).succAbove (foldIdx n (Sum.inl k)) := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_succ, foldIdx_inl_val]
      omega
    rw [hidx, foldChainEquiv_past, chain_succ_eq]

/-- The `j`-th slice of the future chain is position `n + j` of the folded chain. -/
theorem foldChainEquiv_future_chain
    (p : (S → ℝ) × ((Fin n → (S → ℝ)) × (Fin n → (S → ℝ)))) (j : Fin (n + 1)) :
    foldChainEquiv (S := S) n p ⟨n + j.val, by have := j.isLt; omega⟩
      = chain p.1 p.2.2 j := by
  induction j using Fin.cases with
  | zero =>
    have hidx : (⟨n + (0 : Fin (n + 1)).val, by omega⟩ : Fin (2 * n + 1))
        = ⟨n, by omega⟩ := Fin.ext (by simp)
    rw [hidx, foldChainEquiv_center]
    rfl
  | succ k =>
    have hle : (⟨n, by omega⟩ : Fin (2 * n + 1)) ≤ (foldIdx n (Sum.inr k)).castSucc := by
      change n ≤ ((foldIdx n (Sum.inr k)) : Fin (2 * n)).val
      rw [foldIdx_inr_val]
      omega
    have hidx : (⟨n + (k.succ).val, by have := k.isLt; omega⟩ : Fin (2 * n + 1))
        = (⟨n, by omega⟩ : Fin (2 * n + 1)).succAbove (foldIdx n (Sum.inr k)) := by
      rw [Fin.succAbove_of_le_castSucc _ _ hle]
      apply Fin.ext
      simp only [Fin.val_succ, foldIdx_inr_val]
      omega
    rw [hidx, foldChainEquiv_future, chain_succ_eq]

/-- **Splitting the `2n` links of the fold at the reflection slice**: the first `n` of them belong
to the past half (in reverse order) and the last `n` to the future half. -/
theorem sum_foldIdx_split {A : Type*} [AddCommMonoid A] (f : Fin (2 * n) → A) :
    (∑ k : Fin (2 * n), f k)
      = (∑ j : Fin n, f (foldIdx n (Sum.inl j))) + ∑ j : Fin n, f (foldIdx n (Sum.inr j)) := by
  rw [← Equiv.sum_comp (foldIdx n) f, Fintype.sum_sum_type]

/-- **The link terms of the folded chain are those of the two half-space chains.** -/
theorem sum_foldChain_diffSq
    (p : (S → ℝ) × ((Fin n → (S → ℝ)) × (Fin n → (S → ℝ)))) :
    (∑ k : Fin (2 * n),
        diffSq (foldChainEquiv (S := S) n p k.succ) (foldChainEquiv (S := S) n p k.castSucc))
      = (∑ k : Fin n, diffSq (chain p.1 p.2.1 k.succ) (chain p.1 p.2.1 k.castSucc))
        + ∑ k : Fin n, diffSq (chain p.1 p.2.2 k.succ) (chain p.1 p.2.2 k.castSucc) := by
  rw [sum_foldIdx_split]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hs : foldChainEquiv (S := S) n p ((foldIdx n (Sum.inl j)).succ)
        = chain p.1 p.2.1 j.castSucc := by
      have hidx : ((foldIdx n (Sum.inl j)).succ : Fin (2 * n + 1))
          = (⟨n - (j.castSucc).val, by have := j.isLt; omega⟩ : Fin (2 * n + 1)) := by
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_castSucc, foldIdx_inl_val]
        omega
      rw [hidx]
      exact foldChainEquiv_past_chain p j.castSucc
    have hc : foldChainEquiv (S := S) n p ((foldIdx n (Sum.inl j)).castSucc)
        = chain p.1 p.2.1 j.succ := by
      have hidx : ((foldIdx n (Sum.inl j)).castSucc : Fin (2 * n + 1))
          = (⟨n - (j.succ).val, by have := j.isLt; omega⟩ : Fin (2 * n + 1)) := by
        apply Fin.ext
        simp only [Fin.val_castSucc, Fin.val_succ, foldIdx_inl_val]
        omega
      rw [hidx]
      exact foldChainEquiv_past_chain p j.succ
    rw [hs, hc, diffSq_comm]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hs : foldChainEquiv (S := S) n p ((foldIdx n (Sum.inr j)).succ)
        = chain p.1 p.2.2 j.succ := by
      have hidx : ((foldIdx n (Sum.inr j)).succ : Fin (2 * n + 1))
          = (⟨n + (j.succ).val, by have := j.isLt; omega⟩ : Fin (2 * n + 1)) := by
        apply Fin.ext
        simp only [Fin.val_succ, foldIdx_inr_val]
        omega
      rw [hidx]
      exact foldChainEquiv_future_chain p j.succ
    have hc : foldChainEquiv (S := S) n p ((foldIdx n (Sum.inr j)).castSucc)
        = chain p.1 p.2.2 j.castSucc :=
      foldChainEquiv_future_chain p j.castSucc
    rw [hs, hc]

/-- The half-space action is the chain sum of the same chain: the links and the mass term of its
interior slices. -/
theorem halfAction_eq_sum {m : ℝ} (z : S → ℝ) (y : Fin n → S → ℝ) :
    halfAction (S := S) m z y
      = (∑ k : Fin n, diffSq (chain z y k.succ) (chain z y k.castSucc))
        + (m / 2) * ∑ k : Fin n, sqSum (chain z y k.succ) := by
  unfold halfAction
  have hlink : (∑ k : Fin n, ∑ i, (chain z y k.succ i - chain z y k.castSucc i) ^ 2)
      = ∑ k : Fin n, diffSq (chain z y k.succ) (chain z y k.castSucc) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [diffSq]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hlink]
  rfl

/-- **The lattice action *is* the chain form of the folded slices.** -/
theorem latticeAction_eq_chainForm (m : ℝ)
    (p : (S → ℝ) × ((Fin n → (S → ℝ)) × (Fin n → (S → ℝ)))) :
    latticeAction (S := S) m p
      = chainForm (S := S) m (m / 2) (2 * n) (foldChainEquiv (S := S) n p) := by
  rw [latticeAction, halfAction_eq_sum (m := m) (z := p.1) (y := p.2.1),
    halfAction_eq_sum (m := m) (z := p.1) (y := p.2.2),
    chainForm_symm, sum_foldChain_sqSum, sum_foldChain_diffSq]
  simp only [boundaryTerm, sqSum, chain_succ_eq]
  ring

/-- **The partition function of the lattice free field is a chain partition function**:
`Z = ∫ exp(−S) dφ = chainZ m (m/2) (2n)`, by the measure-preserving relabelling of the `2n + 1`
slices as a chain.  With `chainZ_closed_det` this is the closed form
`Z = π^{(2n+1)|S|/2} / (det K_{2n})^{|S|/2}` of the whole lattice. -/
theorem latticeGFFMass_eq_chainZ (m : ℝ) {n : ℕ} :
    @latticeGFFMass (S := S) _ m n = chainZ (S := S) m (m / 2) (2 * n) := by
  rw [latticeGFFMass_eq_lintegral, chainZ, gffBaseMeasure]
  simp only [latticeAction_eq_chainForm]
  exact (volume_preserving_foldChainEquiv (S := S) n).lintegral_comp
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (Measurable.neg (measurable_chainForm (S := S) m (m / 2) (2 * n)))))

end Linking

end

end BookProof.ReflectionPositivity
