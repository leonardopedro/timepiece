import Mathlib
import BookProof.MCMC.FockLangevinOperator
import BookProof.YangMillsMagneticQuartic

/-!
# Chapter YangMillsFieldStrength — the field-strength components on the core

`softmodes.md` §2.3 and `BookProof.YangMillsMagneticQuartic` use the field-strength components
`B_a(n) = ∑ i, A_{a i} nᵢ` (`magComp`), *assuming* that the magnetic components are linear in the
occupation. This module derives a diagonal sandwich model; comparison with the field strength

`F_{μν} = ∂_μ A_ν − ∂_ν A_μ + g [A_μ, A_ν]`   (Weyl gauge `A_0 = 0`),

on the Gauss–polynomial core remains a separate identification obligation.

## Ordered pairs and the limit of the sandwich model

In the nested Fock space the gauge potential is not an arbitrary operator: every component is a
*pair*, `c† M c` — an outer creation–annihilation pair with the inner (self-adjoint) operator `M`
in between (`sandwich`). The definition is the ordinary number-preserving lift of a finite
matrix. On the one-outer-particle restriction, composition gives the inner matrix product.
On the full outer Fock space, `dΓ(M) dΓ(N)` also acts on distinct particles and generally differs
from `dΓ(M N)`. For example `dΓ(I) = N_out` but `N_out² ≠ N_out`. Form the physical magnetic
square inside `h` before outer enclosure. No rule deleting extra outer terms is proved here.

The one place where a subtraction could hide is the ordering of the pair itself: on the basis
vector `n` the ordered pair `c_j† c_j` acts by `n_j`, while the reverse ordering `c_j c_j†` acts by
`n_j + 1`.  `hopWord_pair_same` pins this down: the pair with the annihilation applied first acts
by exactly `n_j`, with **no constant term**.  The constant that the reversed pair would contribute
is precisely what normal ordering would have to remove, and it never appears.

## Contents

* `pairWord`, `sandwich` — the nested pair `c† M c` on the core `CoreCoeff d`, built from the
  corpus ladder words of `BookProof.MCMC.FockLangevin`;
* **`hopWord_pair_same`** — the contraction is the occupation, with no vacuum subtraction;
* **`hopWord_pair_reverse`** — the reversed pair acts by the occupation *plus one*: the constant
  `1` is exactly the normal-ordering subtraction, and it is what the ordered pair omits.  For the
two-component model the same constant is what the coefficient model's `:N²:` weight already
lacks (`YangMillsMagneticQuartic.quartic_eq_magnetic_add_cross`);
* **`sandwich_diag_single`** — a *Cartan* sandwich (diagonal inner operator `diag m`) is diagonal in
  the occupation basis with eigenvalue the linear form `∑ j, m_j n_j`: this is `magComp`;
* **`sandwich_diag_apply`**, **`magneticEnergyForm_eq`** — the magnetic energy form is the sum of
  squares of the derived components, i.e. the `magneticEnergyForm` the barrier bound consumes.
* **`hopWord_pair_offdiag`**, **`hopWord_pair_offdiag_sqrt_mul`** — the off-diagonal (root) pair
  `c_i† c_j` hops one quantum from mode `j` to mode `i` with amplitude `√((nᵢ+1) nⱼ)`; the root
  sector of the mode expansion is thus off-diagonal in the occupation basis, where the Cartan pair
  is diagonal.
* **`offdiag_amp_normSq`**, **`offdiag_amp_decomp`** — its squared amplitude is `nᵢ nⱼ + nⱼ`: the
  cross term of the two distinct occupations plus the diagonal occupation, the `+1` being the
  normal-ordering constant that survives off the diagonal.
* **`hopWord_pair_offdiag_ne`** — with mode `j` occupied the root pair changes the index, so no
  off-diagonal component is diagonal in the occupation basis.
* **`sum_offdiag_amp_sq`** — summed over the ordered pairs, the root amplitudes give the cross
  weight `∑_{i≠j} nᵢ nⱼ` plus `d − 1` copies of the occupation, matching
  `YangMillsMagneticQuartic.quarticDegreeForm_eq_magnetic_add_root`;
* **`vacuum_lower_zero`**, **`vacuum_raise_normSq`**, **`vacuum_field_raw`** — on the coefficient
  model's vacuum annihilation vanishes and creation fills exactly one quantum, so
  `(a_j† + a_j) Ω = |e_j⟩` has squared norm `1`;
* **`fieldOp`**, **`fieldOp_vacuum`**, **`sum_fieldOp_vacuum`**, **`abelian_vacuum_energy`** —
  with the oscillator normalisation `A_j = (a_j + a_j†)/√2` the vacuum magnetic energy is `1/2`
  per field component (`d/2` in total), while the normal-ordered `:N²:` form
  (`YangMillsMagneticQuartic.magneticEnergyForm_vacuum`) is `0` there: the `1/2` per component is
  the normal-ordering constant in explicit numerical form;
* **`hopWord_two_pairs`**, **`two_pairs_normSq`** — the two-pair amplitude on a single mode is the
  **product** of the two one-pair amplitudes, `√((nᵢ+1)nⱼ)·√((n_k+1)n_l)`, so the quartic weight of
  two distinct pairs factorises into the root weights of §4;
* **`hopWord_two_pairs_same`**, **`two_pairs_same_normSq`** — the same pair twice gives the shifted
  weight `(nᵢ+2)(nⱼ−1)(nᵢ+1)nⱼ`: the second hop sees the mode after the first, which is where the
  two-particle structure (and the `−1`) enters;
* **`hopWord_two_pairs_diag`** — the diagonal pair twice acts by `nⱼ²`, i.e. exactly one summand of
  the per-mode magnetic weight `∑ a, n_a²` of `magneticEnergyForm_diag`.

## Honest boundary

The derivative term `∂_μ A_ν` is not modelled here: the module derives the *contraction
structure* of the nested algebra and the Cartan eigenvalue, which is what fixes the components
`B_a` as linear forms, but the assembly `F = ∂A + g[A,A]` as an operator identity (and hence
`commutator_cartan`) is stated only through the inner matrices.  The off-diagonal (root) sector is
now analysed at the level of the *amplitudes in the occupation basis*: one pair
(`hopWord_pair_offdiag`, its weight `nᵢ nⱼ + nⱼ`, and the summed form `sum_offdiag_amp_sq`) and two
pairs
(`hopWord_two_pairs`, the factorised weight of `two_pairs_normSq`, the same-pair shift
`hopWord_two_pairs_same`, and the diagonal `hopWord_two_pairs_diag`, which is the `:N²:` weight per
component).  What is still not done is the **assembly over the core**: summing the `24` components
with the `ε`/`f` weights and matching the result to `magneticEnergyForm diagA` through the
isometry `coeffToCore` — that is the form-level identification `ModeIdentification` isolates in
`BookProof.Qym.ChapterYangMillsFieldStrengthSplit`.  The polynomial side is proved there for the
field strength the corpus uses (`magPoly_eq_deriv_add`, the bracket identity
`two_smul_levi_contract`, and the root-sector quartic energy `root_energy`); the amplitudes here and
that polynomial are the two halves still to be matched.
-/

noncomputable section

namespace BookProof.YangMillsFieldStrength

open Finset
open BookProof.ReferenceGap
open BookProof.MCMC.FockLangevin
open BookProof.YangMillsMagneticQuartic

variable {d : ℕ}

/-! ## 1. The nested pair and the contraction -/

/-- The ladder word of the pair `c_i† c_j`: the annihilation `c_j` acts first, the creation `c_i†`
second — creation on the left, annihilation on the right, as the nested form requires. -/
def pairWord (i j : Fin d) : List (Fin d × Bool) := [(j, false), (i, true)]

/-- **The nested sandwich** `c† M c` on the core: the sum of outer pairs weighted by the inner
operator `M`. Products of such lifts need not themselves have this form. -/
def sandwich (M : Fin d → Fin d → ℂ) (c : CoreCoeff d) : CoreCoeff d :=
  ∑ i, ∑ j, M i j • hopWord (pairWord i j) c

/-- One lowering step on a basis vector. -/
theorem hopStep_lower_single (j : Fin d) (n : Fin d → ℕ) (z : ℂ) :
    hopStep (j, false) (Finsupp.single n z)
      = Finsupp.single (lowerIdx j n) (((Real.sqrt (n j) : ℝ) : ℂ) * z) := by
  simp [hopStep, stepIdx, stepAmp]

/-- One raising step on a basis vector. -/
theorem hopStep_raise_single (j : Fin d) (m : Fin d → ℕ) (w : ℂ) :
    hopStep (j, true) (Finsupp.single m w)
      = Finsupp.single (raiseIdx j m) (((Real.sqrt (m j + 1) : ℝ) : ℂ) * w) := by
  simp [hopStep, stepIdx, stepAmp]

/-- Raising after lowering returns the index, provided the mode is occupied. -/
theorem raiseIdx_lowerIdx (j : Fin d) (n : Fin d → ℕ) (h : n j ≠ 0) :
    raiseIdx j (lowerIdx j n) = n := by
  have hpos : 0 < n j := Nat.pos_of_ne_zero h
  funext k
  by_cases hk : k = j
  · subst hk
    simp [raiseIdx, lowerIdx, Nat.sub_add_cancel hpos]
  · simp [raiseIdx, lowerIdx, hk]

/-- **The contraction is the occupation — no vacuum subtraction.**  The pair `c_j† c_j`
(annihilation applied first, creation second) acts on the basis vector `n` by `n_j`, exactly, with
no constant term.  Its reverse ordering would act by `n_j + 1`; that constant is what normal
ordering would have to subtract, and in the nested form it never appears. -/
theorem hopWord_pair_same (j : Fin d) (n : Fin d → ℕ) (z : ℂ) :
    hopWord [(j, false), (j, true)] (Finsupp.single n z) = Finsupp.single n ((n j : ℂ) * z) := by
  change hopStep (j, true) (hopStep (j, false) (Finsupp.single n z)) = _
  rw [hopStep_lower_single, hopStep_raise_single]
  by_cases h : n j = 0
  · rw [h]
    simp
  · rw [raiseIdx_lowerIdx j n h]
    have hpos : 0 < n j := Nat.pos_of_ne_zero h
    have hm : (lowerIdx j n) j + 1 = n j := by
      simp [lowerIdx, Nat.sub_add_cancel hpos]
    have hidx : (((lowerIdx j n) j : ℝ) + 1) = (n j : ℝ) := by exact_mod_cast hm
    rw [hidx, ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp

/-- **The reversed pair is the occupation plus one.**  With the *creation* applied first the pair
`c_j c_j†` acts on `n` by `n_j + 1`.  The constant `1`, present for every mode in every state, is
exactly the vacuum subtraction that normal ordering would have to remove; the ordered pair of
`hopWord_pair_same` never produces it.  Comparing the two orderings therefore isolates the
normal-ordering constant of a single component. -/
theorem hopWord_pair_reverse (j : Fin d) (n : Fin d → ℕ) (z : ℂ) :
    hopWord [(j, true), (j, false)] (Finsupp.single n z)
      = Finsupp.single n (((n j : ℂ) + 1) * z) := by
  change hopStep (j, false) (hopStep (j, true) (Finsupp.single n z)) = _
  rw [hopStep_raise_single, hopStep_lower_single]
  have hidx : lowerIdx j (raiseIdx j n) = n := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp [lowerIdx, raiseIdx]
    · simp [lowerIdx, raiseIdx, hk]
  have hj : (raiseIdx j n) j = n j + 1 := by simp [raiseIdx]
  rw [hidx, hj]
  congr 1
  have hcast : (((n j + 1 : ℕ)) : ℝ) = (n j : ℝ) + 1 := by push_cast; ring
  have hx : Real.sqrt (((n j + 1 : ℕ)) : ℝ) * Real.sqrt (((n j + 1 : ℕ)) : ℝ)
      = (n j : ℝ) + 1 := by
    rw [Real.mul_self_sqrt (Nat.cast_nonneg _), hcast]
  rw [← hcast, ← mul_assoc, ← Complex.ofReal_mul, hx]
  push_cast
  ring

/-! ## 2. The Cartan sandwich is diagonal -/

/-- A finite sum of basis vectors at the same index is the basis vector of the sum. -/
theorem sum_single_same (f : Fin d → ℂ) (n : Fin d → ℕ) :
    (∑ j, Finsupp.single n (f j)) = Finsupp.single n (∑ j, f j) := by
  ext k
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  by_cases h : k = n <;> simp [h]

/-- **A Cartan sandwich is diagonal, with eigenvalue the occupation-weighted linear form.**  For a
diagonal inner operator `diag m` the sandwich `c† (diag m) c = ∑ j, m_j c_j† c_j` acts on `n` by
`∑ j, m_j n_j` — the component formula of `magComp`, here derived rather than assumed. -/
theorem sandwich_diag_single (m : Fin d → ℂ) (n : Fin d → ℕ) (z : ℂ) :
    sandwich (fun i j => if i = j then m j else 0) (Finsupp.single n z)
      = Finsupp.single n ((∑ j, m j * (n j : ℂ)) * z) := by
  unfold sandwich
  have hterm : ∀ i j : Fin d,
      (if i = j then m j else 0) • hopWord (pairWord i j) (Finsupp.single n z)
        = if i = j then Finsupp.single n (m j * (n j : ℂ) * z) else 0 := by
    intro i j
    by_cases hij : i = j
    · rw [hij, if_pos rfl,
        show hopWord (pairWord j j) (Finsupp.single n z)
          = Finsupp.single n ((n j : ℂ) * z) from hopWord_pair_same j n z,
        Finsupp.smul_single]
      simp [mul_assoc]
    · rw [if_neg hij, if_neg hij]
      exact zero_smul _ _
  simp only [hterm]
  rw [Finset.sum_comm]
  have hdiag : ∀ j : Fin d, (∑ i : Fin d, if i = j then Finsupp.single n (m j * (n j : ℂ) * z)
      else 0) = Finsupp.single n (m j * (n j : ℂ) * z) := by
    intro j
    rw [Finset.sum_ite_eq']
    simp
  simp only [hdiag]
  rw [sum_single_same]
  congr 1
  rw [← Finset.sum_mul]

/-- **The field-strength component of a Cartan potential is `magComp`.**  Feeding the inner
operator `diag (A a ·)` — the `a`-th component of the potential in the Cartan background — into
the sandwich gives, on every basis vector, multiplication by `magComp A a n = ∑ i, A a i nᵢ`.  This
is the derivation of the component formula that `YangMillsMagneticQuartic` had assumed: it is the
eigenvalue of the nested pair `c† diag(A a) c`, with no constant term (no vacuum subtraction). -/
theorem sandwich_diag_magComp (A : Fin d → Fin d → ℝ) (a : Fin d) (n : Fin d → ℕ) (z : ℂ) :
    sandwich (fun i j => if i = j then (A a j : ℂ) else 0) (Finsupp.single n z)
      = Finsupp.single n ((magComp A a n : ℂ) * z) := by
  have hcast : ((magComp A a n : ℝ) : ℂ) = ∑ j : Fin d, (A a j : ℂ) * (n j : ℂ) := by
    rw [magComp]
    push_cast
    rfl
  rw [sandwich_diag_single, hcast]

/-! ## 3. The magnetic energy form -/

/-- **The magnetic energy form is the sum of the squares of the derived components**: the quadratic
form of `½ ∑_a B_a²` is `magneticEnergyForm`, read component by component.  This is the form
`barrierBound_quartic` consumes, now attached to the derived `B_a` rather than to an assumed
linear form. -/
theorem magneticEnergyForm_eq_sum (A : Fin d → Fin d → ℝ) (c : CoreCoeff d) :
    magneticEnergyForm A c
      = ∑ a, ∑ n ∈ c.support, (magComp A a n) ^ 2 * ‖c n‖ ^ 2 := by
  unfold magneticEnergyForm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_mul]

/-! ## 4. The off-diagonal (root) pair, and the mode expansion in the occupation basis -/

/-- **The off-diagonal pair hops.**  For `i ≠ j` the pair `c_i† c_j` does not leave the basis
vector where it is: it moves one quantum from mode `j` to mode `i`, with amplitude
`√(nᵢ+1) · √(nⱼ)`.  This is the mode expansion of the root sector in the occupation basis — the
Cartan pair of `hopWord_pair_same` acts diagonally by `n_j`, the root pair acts off-diagonally. -/
theorem hopWord_pair_offdiag {i j : Fin d} (hij : i ≠ j) (n : Fin d → ℕ) (z : ℂ) :
    hopWord [(j, false), (i, true)] (Finsupp.single n z)
      = Finsupp.single (raiseIdx i (lowerIdx j n))
          ((((Real.sqrt ((n i : ℝ) + 1) : ℝ) : ℂ) *
            (((Real.sqrt (n j : ℝ) : ℝ) : ℂ) * z))) := by
  change hopStep (i, true) (hopStep (j, false) (Finsupp.single n z)) = _
  rw [hopStep_lower_single, hopStep_raise_single]
  have hdiff : (lowerIdx j n) i = n i := by simp [lowerIdx, hij]
  rw [hdiff]

/-- The root amplitude in the merged form: `√((nᵢ+1) nⱼ)`, the square root of the cross-term
weight of the pair. -/
theorem hopWord_pair_offdiag_sqrt_mul {i j : Fin d} (hij : i ≠ j) (n : Fin d → ℕ) (z : ℂ) :
    hopWord [(j, false), (i, true)] (Finsupp.single n z)
      = Finsupp.single (raiseIdx i (lowerIdx j n))
          (((Real.sqrt (((n i : ℝ) + 1) * (n j : ℝ)) : ℝ) : ℂ) * z) := by
  rw [hopWord_pair_offdiag hij n z]
  congr 1
  rw [show (((Real.sqrt ((n i : ℝ) + 1) : ℝ) : ℂ) *
        (((Real.sqrt (n j : ℝ) : ℝ) : ℂ) * z))
      = ((((Real.sqrt ((n i : ℝ) + 1) : ℝ) : ℂ) *
        ((Real.sqrt (n j : ℝ) : ℝ) : ℂ)) * z) from (mul_assoc _ _ _).symm]
  rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]

/-- **The squared root amplitude is `(nᵢ+1) nⱼ`**: the pair weight of two *distinct* modes.  The
diagonal pair's weight is `nⱼ` (`hopWord_pair_same`); the extra `nᵢ` is the cross term, and the
`+1` is the vacuum contribution that survives off the diagonal because the annihilation acts on a
different mode from the creation. -/
theorem offdiag_amp_normSq {i j : Fin d} (n : Fin d → ℕ) :
    ‖(((Real.sqrt (((n i : ℝ) + 1) * (n j : ℝ)) : ℝ) : ℂ))‖ ^ 2
      = ((n i : ℝ) + 1) * (n j : ℝ) := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]

/-- The root amplitude splits into the cross term plus the occupation:
`(nᵢ+1) nⱼ = nᵢ nⱼ + nⱼ`. -/
theorem offdiag_amp_decomp {i j : Fin d} (n : Fin d → ℕ) :
    ((n i : ℝ) + 1) * (n j : ℝ) = (n i : ℝ) * (n j : ℝ) + (n j : ℝ) := by
  ring

/-- **The root pair leaves the diagonal**: with mode `j` occupied the new index differs from `n`.
So an off-diagonal component is genuinely a hopping operator in the occupation basis, not a
diagonal one — the statement `sandwich_diag_magComp` makes for the Cartan components. -/
theorem hopWord_pair_offdiag_ne {i j : Fin d} (hij : i ≠ j) (n : Fin d → ℕ)
    (hn : n j ≠ 0) : raiseIdx i (lowerIdx j n) ≠ n := by
  intro h
  have hji : j ≠ i := fun hji => hij hji.symm
  have h1 : (raiseIdx i (lowerIdx j n)) j = (lowerIdx j n) j := by
    simp [raiseIdx, hji]
  have h2 : (lowerIdx j n) j = n j - 1 := by simp [lowerIdx]
  have h3 : n j - 1 = n j := by rw [← h2, ← h1, h]
  omega

/-- **The mode expansion of the root sector.**  Summed over all ordered pairs of distinct modes,
the squared root amplitudes are the cross weight plus `d − 1` copies of the occupation:
`∑_{i≠j} (nᵢ+1) nⱼ = ∑_{i≠j} nᵢ nⱼ + (d−1) ∑ j, nⱼ`.  The first term is the root share of the
`:N²:` weight (`rootCrossWeight`), the second the residual normal-ordering constant that the
off-diagonal amplitude carries — `d − 1` per quantum, since the pair hops into any of the other
`d − 1` modes.  So the quartic weight is the Cartan part plus this root part, mode by mode. -/
theorem sum_offdiag_amp_sq (n : Fin d → ℕ) :
    (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin d)).erase i, ((n i : ℝ) + 1) * (n j : ℝ))
      = rootCrossWeight n + ((d : ℝ) - 1) * ∑ j, (n j : ℝ) := by
  have hterm : ∀ i j : Fin d, ((n i : ℝ) + 1) * (n j : ℝ)
      = (n i : ℝ) * (n j : ℝ) + (n j : ℝ) := fun i j => by ring
  simp only [hterm, Finset.sum_add_distrib]
  rw [rootCrossWeight]
  congr 1
  have hsub : ∀ i : Fin d, (∑ j ∈ (Finset.univ : Finset (Fin d)).erase i, (n j : ℝ))
      = (∑ j, (n j : ℝ)) - (n i : ℝ) := by
    intro i
    have h := Finset.add_sum_erase (s := (Finset.univ : Finset (Fin d)))
      (f := fun j => (n j : ℝ)) (a := i) (Finset.mem_univ i)
    linarith
  simp only [hsub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-! ## 5. The abelian vacuum magnetic energy is one half per component -/

/-- The `ℓ²` norm of a single basis vector is the squared modulus of its coefficient. -/
theorem coreNormSq_single (m : Fin d → ℕ) (z : ℂ) :
    coreNormSq (Finsupp.single m z) = ‖z‖ ^ 2 := by
  by_cases hz : z = 0
  · subst hz
    simp [coreNormSq]
  · rw [coreNormSq, Finsupp.support_single_ne_zero _ hz, Finset.sum_singleton,
      Finsupp.single_eq_same]

/-- The `ℓ²` norm of a scalar multiple: `‖k c‖² = ‖k‖²‖c‖²`. -/
theorem coreNormSq_smul (k : ℂ) (z : CoreCoeff d) :
    coreNormSq (k • z) = ‖k‖ ^ 2 * coreNormSq z := by
  by_cases hk : k = 0
  · subst hk
    simp [coreNormSq]
  · rw [coreNormSq, coreNormSq, Finsupp.support_smul_eq hk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, norm_mul, mul_pow]

/-- **Annihilation kills the vacuum.**  The lowering amplitude `√(nⱼ)` is `√0 = 0` on the vacuum,
so `a_j Ω = 0` — the `ℓ²` statement, not merely the amplitude. -/
theorem vacuum_lower_zero (j : Fin d) :
    hopStep (j, false) (vacuumCoeff d) = 0 := by
  rw [vacuumCoeff, hopStep_lower_single]
  have h : Real.sqrt ((fun _ => (0 : ℕ) : Fin d → ℕ) j : ℝ) = 0 := by simp
  rw [h]
  simp

/-- **Creation fills one quantum, with amplitude one**: `‖a_j† Ω‖² = 1`. -/
theorem vacuum_raise_normSq (j : Fin d) :
    coreNormSq (hopStep (j, true) (vacuumCoeff d)) = 1 := by
  rw [vacuumCoeff, hopStep_raise_single, coreNormSq_single]
  have h : ((Real.sqrt ((fun _ => (0 : ℕ) : Fin d → ℕ) j + 1) : ℝ) : ℂ) = 1 := by
    simp
  rw [h]
  norm_num

/-- The field component `A_j = (a_j + a_j†)/√2` of the oscillator model. -/
def fieldOp (j : Fin d) (c : CoreCoeff d) : CoreCoeff d :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • (hopStep (j, true) c + hopStep (j, false) c)

/-- **The field applied to the vacuum is one quantum, unnormalised**: `(a_j† + a_j) Ω = |e_j⟩`, so
its squared norm is `1`.  This is the statement before the `1/√2` of the field normalisation, and
it is what makes the vacuum value a *half* rather than a fitted constant. -/
theorem vacuum_field_raw (j : Fin d) :
    coreNormSq (hopStep (j, true) (vacuumCoeff d) + hopStep (j, false) (vacuumCoeff d)) = 1 := by
  rw [vacuum_lower_zero, add_zero, vacuum_raise_normSq]

/-- **The abelian vacuum magnetic energy is one half per component.**  With the standard
oscillator normalisation `A_j = (a_j + a_j†)/√2` the field lifts the vacuum to one quantum and the
energy of the component is `‖A_j Ω‖² = 1/2`.  Compare `magneticEnergyForm_vacuum`: the
normal-ordered `:N²:` weight is `0` on the same state.  The abelian magnetic operator therefore
carries exactly `1/2` per component that the normal-ordered model does not, which is the constant
behind `not_modeIdentification_abelian`. -/
theorem fieldOp_vacuum (j : Fin d) :
    coreNormSq (fieldOp j (vacuumCoeff d)) = 1 / 2 := by
  rw [fieldOp, vacuum_lower_zero, add_zero, coreNormSq_smul, vacuum_raise_normSq]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.sqrt 2)]
  have hsq : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hsq, mul_one]

/-- **Summed over the components**, the vacuum energy is `d/2`: one half for each of the `d` field
components, with no cross terms — the components are independent at the vacuum. -/
theorem sum_fieldOp_vacuum :
    ∑ j : Fin d, coreNormSq (fieldOp j (vacuumCoeff d)) = (d : ℝ) / 2 := by
  simp only [fieldOp_vacuum]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The abelian vacuum magnetic energy against the normal-ordered model**: every field component
contributes `1/2` on the vacuum, while the `:N²:` form `magneticEnergyForm diagA` is `0` there.
The `1/2` per component is the normal-ordering constant in its explicit numerical form. -/
theorem abelian_vacuum_energy (j : Fin d) :
    coreNormSq (fieldOp j (vacuumCoeff d)) = 1 / 2 ∧
      magneticEnergyForm (d := d) diagA (vacuumCoeff d) = 0 :=
  ⟨fieldOp_vacuum j, magneticEnergyForm_vacuum⟩

/-! ## 6. The two-pair amplitude on a single mode -/

/-- The squared modulus of a product of two square-root amplitudes:
`‖√A (√B z)‖² = A B ‖z‖²`. -/
theorem normSq_sqrt_mul_sqrt {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (z : ℂ) :
    ‖(((Real.sqrt A : ℝ) : ℂ) * ((((Real.sqrt B : ℝ) : ℂ)) * z))‖ ^ 2
      = A * B * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, norm_mul, mul_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, Real.sq_sqrt hA, Real.sq_sqrt hB]
  ring

/-- **The two-pair amplitude.**  The product of two root pairs `c_i† c_j c_k† c_l` acts on a single
mode by a pair of hops with the *product* of the two one-pair amplitudes
(`hopWord_pair_offdiag_sqrt_mul`): `√((nᵢ+1) nⱼ) · √((n_k+1) n_l)`, the first factor evaluated at
the mode reached by the second pair.  The hypotheses are only the distinctness of the four indices,
which is what makes the intermediate occupations independent of the hops. -/
theorem hopWord_two_pairs {i j k l : Fin d} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (n : Fin d → ℕ) (z : ℂ) :
    hopWord (pairWord k l ++ pairWord i j) (Finsupp.single n z)
      = Finsupp.single (raiseIdx i (lowerIdx j (raiseIdx k (lowerIdx l n))))
          (((Real.sqrt (((n i : ℝ) + 1) * (n j : ℝ)) : ℝ) : ℂ) *
            (((Real.sqrt (((n k : ℝ) + 1) * (n l : ℝ)) : ℝ) : ℂ) * z)) := by
  change hopStep (i, true) (hopStep (j, false)
    (hopStep (k, true) (hopStep (l, false) (Finsupp.single n z)))) = _
  rw [show hopStep (k, true) (hopStep (l, false) (Finsupp.single n z))
      = hopWord [(l, false), (k, true)] (Finsupp.single n z) from rfl]
  rw [hopWord_pair_offdiag_sqrt_mul hkl n z]
  rw [show hopStep (i, true) (hopStep (j, false)
      (Finsupp.single (raiseIdx k (lowerIdx l n))
        (((Real.sqrt (((n k : ℝ) + 1) * (n l : ℝ)) : ℝ) : ℂ) * z)))
      = hopWord [(j, false), (i, true)] (Finsupp.single (raiseIdx k (lowerIdx l n))
        (((Real.sqrt (((n k : ℝ) + 1) * (n l : ℝ)) : ℝ) : ℂ) * z)) from rfl]
  rw [hopWord_pair_offdiag_sqrt_mul hij]
  have hi : raiseIdx k (lowerIdx l n) i = n i := by
    simp [raiseIdx, lowerIdx, hik, hil]
  have hj : raiseIdx k (lowerIdx l n) j = n j := by
    simp [raiseIdx, lowerIdx, hjk, hjl]
  rw [hi, hj]

/-- **The two-pair weight**: the squared modulus of the two-pair amplitude is the product of the two
one-pair weights, `(nᵢ+1)nⱼ · (n_k+1)n_l`.  So the quartic weight of two distinct pairs factorises
into the root weights of §4 — the algebraic content the mode expansion needs. -/
theorem two_pairs_normSq {i j k l : Fin d} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (n : Fin d → ℕ) (z : ℂ) :
    coreNormSq (hopWord (pairWord k l ++ pairWord i j) (Finsupp.single n z))
      = ((n i : ℝ) + 1) * (n j : ℝ) * (((n k : ℝ) + 1) * (n l : ℝ)) * ‖z‖ ^ 2 := by
  rw [hopWord_two_pairs hij hkl hik hil hjk hjl n z, coreNormSq_single,
    normSq_sqrt_mul_sqrt (by positivity) (by positivity)]

/-- **The same pair twice.**  For `c_i† c_j c_i† c_j` the second hop sees the mode *after* the
first, so its weight is the shifted one: the amplitude is `√((nᵢ+2)(nⱼ−1))·√((nᵢ+1)nⱼ)`.  Nothing
commutes here — the two factors differ, and the `−1` is the quantum the first pair removed from mode
`j`. -/
theorem hopWord_two_pairs_same {i j : Fin d} (hij : i ≠ j) (n : Fin d → ℕ)
    (hn : n j ≠ 0) (z : ℂ) :
    hopWord (pairWord i j ++ pairWord i j) (Finsupp.single n z)
      = Finsupp.single (raiseIdx i (lowerIdx j (raiseIdx i (lowerIdx j n))))
          (((Real.sqrt (((n i : ℝ) + 2) * ((n j : ℝ) - 1)) : ℝ) : ℂ) *
            (((Real.sqrt (((n i : ℝ) + 1) * (n j : ℝ)) : ℝ) : ℂ) * z)) := by
  change hopStep (i, true) (hopStep (j, false)
    (hopStep (i, true) (hopStep (j, false) (Finsupp.single n z)))) = _
  rw [show hopStep (i, true) (hopStep (j, false) (Finsupp.single n z))
      = hopWord [(j, false), (i, true)] (Finsupp.single n z) from rfl]
  rw [hopWord_pair_offdiag_sqrt_mul hij n z]
  rw [show hopStep (i, true) (hopStep (j, false)
      (Finsupp.single (raiseIdx i (lowerIdx j n))
        (((Real.sqrt (((n i : ℝ) + 1) * (n j : ℝ)) : ℝ) : ℂ) * z)))
      = hopWord [(j, false), (i, true)] (Finsupp.single (raiseIdx i (lowerIdx j n))
        (((Real.sqrt (((n i : ℝ) + 1) * (n j : ℝ)) : ℝ) : ℂ) * z)) from rfl]
  rw [hopWord_pair_offdiag_sqrt_mul hij]
  have hpos : 1 ≤ n j := Nat.one_le_iff_ne_zero.mpr hn
  have hi : raiseIdx i (lowerIdx j n) i = n i + 1 := by
    simp [raiseIdx, lowerIdx, hij]
  have hj : raiseIdx i (lowerIdx j n) j = n j - 1 := by
    simp [lowerIdx, raiseIdx, Ne.symm hij]
  have hcast : (((n j - 1 : ℕ)) : ℝ) = (n j : ℝ) - 1 := by
    rw [Nat.cast_sub hpos]
    norm_num
  have harg : (((raiseIdx i (lowerIdx j n) i : ℕ) : ℝ) + 1)
      * (((raiseIdx i (lowerIdx j n) j : ℕ)) : ℝ)
      = ((n i : ℝ) + 2) * ((n j : ℝ) - 1) := by
    rw [hi, hj, hcast]
    push_cast
    ring
  rw [harg]

/-- The squared modulus of the same-pair amplitude: `(nᵢ+2)(nⱼ−1)·(nᵢ+1)nⱼ`. -/
theorem two_pairs_same_normSq {i j : Fin d} (hij : i ≠ j) (n : Fin d → ℕ)
    (hn : n j ≠ 0) (z : ℂ) :
    coreNormSq (hopWord (pairWord i j ++ pairWord i j) (Finsupp.single n z))
      = (((n i : ℝ) + 2) * ((n j : ℝ) - 1)) * (((n i : ℝ) + 1) * (n j : ℝ)) * ‖z‖ ^ 2 := by
  rw [hopWord_two_pairs_same hij n hn z, coreNormSq_single,
    normSq_sqrt_mul_sqrt (A := ((n i : ℝ) + 2) * ((n j : ℝ) - 1))
      (B := ((n i : ℝ) + 1) * (n j : ℝ))
      (by
        have h1 : (1 : ℝ) ≤ (n j : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        exact mul_nonneg (by positivity) (by linarith))
      (by positivity)]

/-- **The diagonal two-pair amplitude is the `:N²:` weight of the component.**  For the Cartan pair
applied twice, `(c_j† c_j)²` acts on the mode by `nⱼ · nⱼ = nⱼ²` — exactly the `j`-th summand of the
per-mode magnetic weight `∑ a, n_a²` of `magneticEnergyForm_diag`.  This is the precise sense in
which the diagonal part of the mode expansion reproduces the normal-ordered `:N²:` weight, and why
the root part of §4 (the cross weight) is the only piece left over. -/
theorem hopWord_two_pairs_diag (j : Fin d) (n : Fin d → ℕ) (z : ℂ) :
    hopWord (pairWord j j ++ pairWord j j) (Finsupp.single n z)
      = Finsupp.single n (((((n j : ℝ) ^ 2) : ℝ) : ℂ) * z) := by
  change hopStep (j, true) (hopStep (j, false)
    (hopStep (j, true) (hopStep (j, false) (Finsupp.single n z)))) = _
  rw [show hopStep (j, true) (hopStep (j, false) (Finsupp.single n z))
      = hopWord [(j, false), (j, true)] (Finsupp.single n z) from rfl]
  rw [hopWord_pair_same j n z]
  rw [show hopStep (j, true) (hopStep (j, false)
      (Finsupp.single n ((n j : ℂ) * z)))
      = hopWord [(j, false), (j, true)] (Finsupp.single n ((n j : ℂ) * z)) from rfl]
  rw [hopWord_pair_same j n ((n j : ℂ) * z)]
  congr 1
  push_cast
  ring

end BookProof.YangMillsFieldStrength
