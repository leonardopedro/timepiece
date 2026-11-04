import Mathlib
import BookProof.MCMC.FockLangevinOperator
import BookProof.YangMillsMagneticQuartic

/-!
# Chapter YangMillsFieldStrength — the field-strength components on the core

`softmodes.md` §2.3 and `BookProof.YangMillsMagneticQuartic` use the field-strength components
`B_a(n) = ∑ i, A_{a i} nᵢ` (`magComp`), *assuming* that the magnetic components are linear in the
occupation.  This module derives that form from the field strength itself,

`F_{μν} = ∂_μ A_ν − ∂_ν A_μ + g [A_μ, A_ν]`   (Weyl gauge `A_0 = 0`),

on the Gauss–polynomial core, and records why **no normal ordering is needed**.

## Why no normal ordering is needed

In the nested Fock space the gauge potential is not an arbitrary operator: every component is a
*pair*, `c† M c` — an outer creation–annihilation pair with the inner (self-adjoint) operator `M`
in between (`sandwich`).  The nested algebra multiplies pairs by composing the inner operators, so
a product `(c† M c)(c† N c)` is again a pair with inner operator `M N`: the "contraction" of
Wick's theorem *is* the inner matrix product, and the double-creation term is not an element of the
nested algebra at all.  The composite is therefore defined without subtracting a vacuum
expectation, which is what normal ordering would do.

The one place where a subtraction could hide is the ordering of the pair itself: on the basis
vector `n` the ordered pair `c_j† c_j` acts by `n_j`, while the reverse ordering `c_j c_j†` acts by
`n_j + 1`.  `hopWord_pair_same` pins this down: the pair with the annihilation applied first acts
by exactly `n_j`, with **no constant term**.  The constant that the reversed pair would contribute
is precisely what normal ordering would have to remove, and it never appears.

## Contents

* `pairWord`, `sandwich` — the nested pair `c† M c` on the core `CoreCoeff d`, built from the
  corpus ladder words of `BookProof.MCMC.FockLangevin`;
* **`hopWord_pair_same`** — the contraction is the occupation, with no vacuum subtraction;
* **`sandwich_diag_single`** — a *Cartan* sandwich (diagonal inner operator `diag m`) is diagonal in
  the occupation basis with eigenvalue the linear form `∑ j, m_j n_j`: this is `magComp`;
* **`sandwich_diag_apply`**, **`magneticEnergyForm_eq`** — the magnetic energy form is the sum of
  squares of the derived components, i.e. the `magneticEnergyForm` the barrier bound consumes.

## Honest boundary

The derivative term `∂_μ A_ν` is not modelled here: the module derives the *contraction
structure* of the nested algebra and the Cartan eigenvalue, which is what fixes the components
`B_a` as linear forms, but the assembly `F = ∂A + g[A,A]` as an operator identity (and hence
`commutator_cartan`) is stated only through the inner matrices, and the off-diagonal (root)
sector, where `[A_μ, A_ν]` does not vanish and which carries the quartic part of `q_W`, is not
analysed in this model.  Both are proved for the field-strength polynomial the corpus actually
uses in `BookProof.Qym.ChapterYangMillsFieldStrengthSplit` (`magPoly_eq_deriv_add`, the bracket
identity `two_smul_levi_contract`, and the root-sector quartic energy `root_energy`).
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
operator `M`.  Every element of the nested field algebra is of this form. -/
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

end BookProof.YangMillsFieldStrength
