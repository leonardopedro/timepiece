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
  `YangMillsMagneticQuartic.quarticDegreeForm_eq_magnetic_add_root`.

## Honest boundary

The derivative term `∂_μ A_ν` is not modelled here: the module derives the *contraction
structure* of the nested algebra and the Cartan eigenvalue, which is what fixes the components
`B_a` as linear forms, but the assembly `F = ∂A + g[A,A]` as an operator identity (and hence
`commutator_cartan`) is stated only through the inner matrices.  The off-diagonal (root) sector is
now analysed at the level of the *one-pair amplitude* — `hopWord_pair_offdiag`, its squared weight
`nᵢ nⱼ + nⱼ`, and the summed form `sum_offdiag_amp_sq` — which is the mode expansion of a single
root component in the occupation basis; what is still not done is the *product* of two root pairs
(the quartic term's amplitude on a mode), i.e. the passage from the amplitude of `c_i† c_j` to
`∑_m ‖[A,A]_m ψ_n‖²`.  That is the same form-level identification `ModeIdentification` isolates in
`BookProof.Qym.ChapterYangMillsFieldStrengthSplit`; here only the one-pair half is proved.  The
polynomial side of the same story is proved there for the field strength the corpus actually uses
(`magPoly_eq_deriv_add`, the bracket identity `two_smul_levi_contract`, and the root-sector quartic
energy `root_energy`), which is the operator the form half still has to be matched against.
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

end BookProof.YangMillsFieldStrength
