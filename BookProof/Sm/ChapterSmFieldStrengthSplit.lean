import Mathlib
import BookProof.Sm.ChapterSmHamiltonian

/-!
# `F = ∂A + g[A,A]` for the Standard Model field strengths

`BookProof.Qym.ChapterYangMillsFieldStrengthSplit` splits the pure Yang–Mills magnetic field
`BookProof.YangMillsHermite.magPoly` into its derivative and commutator parts.  This chapter
carries that split over to the field strengths of record for the Standard Model,
`BookProof.SmHamiltonian.smMagG` (gluons) and `smMagW` (weak bosons) — the `B`'s that enter
`smHamiltonian = ½ Σ π² + ½ Σ B²` on the Gauss–polynomial core of `L²(ℝ¹⁶³)`:

```
B^G_{a,i} = ½ ε_{ijk} (∂_j G_{k,a} − ∂_k G_{j,a} + g_s Σ_{b,d} f_{abd} G_{j,b} G_{k,d})
B^W_{m,i} = ½ ε_{ijk} (∂_j W_{k,m} − ∂_k W_{j,m} + g   Σ_{b,d} ε_{mbd} W_{j,b} W_{k,d})
```

## Contents

* `smDerivG`, `smBilinG`, `smCommG` and **`smMagG_eq_deriv_add`** — the gluon field strength is
  the sum of the derivative part (linear in the configuration) and the commutator part (the
  `g_s [G,G]` term, quadratic);
* the same for the weak field: `smDerivW`, `smBilinW`, `smCommW`, **`smMagW_eq_deriv_add`**;
* `realCoeff_smDerivG` / `realCoeff_smCommG` and their `W` counterparts — each half has real
  coefficients, so each is a symmetric multiplication operator on the core
  (`smDerivG_symmetricOn`, `smCommG_symmetricOn`, …), and the split is an identity of operators
  on the core as well (`smFieldG_apply_eq`, `smFieldW_apply_eq`);
* **`smCommG_eq_quarter_bracket`** and **`smCommW_eq_quarter_bracket`** — the commutator part is
  `¼ ε_{ijk} g [A_j, A_k]`, where `[A_j,A_k]_a = Σ_{bd} f_{abd}(A_{j,b}A_{k,d} − A_{k,b}A_{j,d})`
  is the Lie bracket: the outer `½` is the one in the definition of `B`, the inner one comes from
  antisymmetrising the `ε`-contraction (`two_smul_levi_contract`); hence
* **`smCommG_eq_zero_of_symmetric`**, **`smCommW_eq_zero_of_symmetric`** — on the commuting
  (Cartan) sector the interaction contributes nothing and the field strength is the derivative
  part alone.

## Honest boundary

As in the Yang–Mills chapter, nothing here is dynamical.  The hypercharge field `smMagB` is
abelian and has no commutator part at all (it is already linear), and the Higgs covariant
derivative `smCovD` is a bilinear form of a different kind — its non-abelian structure is the
action `tgen`/`ygen` of the generators on the doublet, a multiplication operator by given
matrices, which needs no bracket identity.  Both are left as they are.  The fermion sector is
not part of `smHamiltonian` (see its `Honest boundary`), so it plays no role here either.
-/

set_option maxHeartbeats 1000000

namespace BookProof.SmFieldStrengthSplit

open MvPolynomial
open BookProof.SmHamiltonian BookProof.SmOneParticle
open BookProof.YangMillsHermite BookProof.HermiteProductCore BookProof.FarisLavine

noncomputable section

/-! ## 1. The split for the gluon field strength -/

/-- The **derivative part** of the gluon field strength,
`½ ε_{ijk}(∂_j G_{k,a} − ∂_k G_{j,a})` — linear in the configuration. -/
def smDerivG (co : Fin 163 → Fin D) (a : Fin 8) (i : Fin 3) : MvPolynomial (Fin D) ℂ :=
  ((1 / 2 : ℝ) : ℂ) • ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) •
    (X (co (smDG a k j)) - X (co (smDG a j k)))

/-- The `(j,k)` component of the gluon **commutator bilinear form**:
`f_{abd} G_{j,b} G_{k,d}`. -/
def smBilinG (P : SmParams) (co : Fin 163 → Fin D) (j k : Fin 3) (a : Fin 8) :
    MvPolynomial (Fin D) ℂ :=
  ∑ b : Fin 8, ∑ d : Fin 8, ((P.fabc a b d : ℝ) : ℂ) • (X (co (smG b j)) * X (co (smG d k)))

/-- The **commutator part** of the gluon field strength, `½ ε_{ijk} g_s f_{abd} G_{j,b} G_{k,d}`
— the `g_s[G,G]` term, quadratic in the configuration. -/
def smCommG (P : SmParams) (co : Fin 163 → Fin D) (a : Fin 8) (i : Fin 3) :
    MvPolynomial (Fin D) ℂ :=
  ((1 / 2 : ℝ) : ℂ) • ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) •
    (((P.gs : ℝ) : ℂ) • smBilinG P co j k a)

/-- **`B^G = ∂G + g_s [G,G]`**: the gluon field strength of record splits into its derivative
and commutator parts. -/
theorem smMagG_eq_deriv_add (P : SmParams) (co : Fin 163 → Fin D) (a : Fin 8) (i : Fin 3) :
    smMagG P co a i = smDerivG co a i + smCommG P co a i := by
  simp only [smMagG, smDerivG, smCommG, smBilinG, smul_add, Finset.sum_add_distrib]

/-- The derivative part of the gluon field strength has real coefficients, hence is a symmetric
multiplication operator. -/
theorem realCoeff_smDerivG (co : Fin 163 → Fin D) (a : Fin 8) (i : Fin 3) :
    RealCoeff (smDerivG co a i) := by
  refine RealCoeff.smul (RealCoeff.sum (s := Finset.univ) fun j _ =>
    RealCoeff.sum (s := Finset.univ) fun k _ => RealCoeff.smul ?_)
  exact RealCoeff.sub' (realCoeff_X _) (realCoeff_X _)

/-- The commutator part of the gluon field strength has real coefficients: the quartic
interaction is a symmetric multiplication operator, like the linear part. -/
theorem realCoeff_smCommG (P : SmParams) (co : Fin 163 → Fin D) (a : Fin 8) (i : Fin 3) :
    RealCoeff (smCommG P co a i) := by
  refine RealCoeff.smul (RealCoeff.sum (s := Finset.univ) fun j _ =>
    RealCoeff.sum (s := Finset.univ) fun k _ => RealCoeff.smul ?_)
  exact RealCoeff.smul (RealCoeff.sum (s := Finset.univ) fun b _ =>
    RealCoeff.sum (s := Finset.univ) fun d _ =>
      RealCoeff.smul ((realCoeff_X _).mul (realCoeff_X _)))

/-! ## 2. The split for the weak field strength -/

/-- The **derivative part** of the weak field strength. -/
def smDerivW (co : Fin 163 → Fin D) (m : Fin 3) (i : Fin 3) : MvPolynomial (Fin D) ℂ :=
  ((1 / 2 : ℝ) : ℂ) • ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) •
    (X (co (smDW m k j)) - X (co (smDW m j k)))

/-- The `(j,k)` component of the weak **commutator bilinear form**:
`ε_{mbd} W_{j,b} W_{k,d}`. -/
def smBilinW (P : SmParams) (co : Fin 163 → Fin D) (j k : Fin 3) (m : Fin 3) :
    MvPolynomial (Fin D) ℂ :=
  ∑ b : Fin 3, ∑ d : Fin 3, ((P.eabc m b d : ℝ) : ℂ) • (X (co (smW b j)) * X (co (smW d k)))

/-- The **commutator part** of the weak field strength. -/
def smCommW (P : SmParams) (co : Fin 163 → Fin D) (m : Fin 3) (i : Fin 3) :
    MvPolynomial (Fin D) ℂ :=
  ((1 / 2 : ℝ) : ℂ) • ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) •
    (((P.gw : ℝ) : ℂ) • smBilinW P co j k m)

/-- **`B^W = ∂W + g [W,W]`**. -/
theorem smMagW_eq_deriv_add (P : SmParams) (co : Fin 163 → Fin D) (m : Fin 3) (i : Fin 3) :
    smMagW P co m i = smDerivW co m i + smCommW P co m i := by
  simp only [smMagW, smDerivW, smCommW, smBilinW, smul_add, Finset.sum_add_distrib]

theorem realCoeff_smDerivW (co : Fin 163 → Fin D) (m : Fin 3) (i : Fin 3) :
    RealCoeff (smDerivW co m i) := by
  refine RealCoeff.smul (RealCoeff.sum (s := Finset.univ) fun j _ =>
    RealCoeff.sum (s := Finset.univ) fun k _ => RealCoeff.smul ?_)
  exact RealCoeff.sub' (realCoeff_X _) (realCoeff_X _)

theorem realCoeff_smCommW (P : SmParams) (co : Fin 163 → Fin D) (m : Fin 3) (i : Fin 3) :
    RealCoeff (smCommW P co m i) := by
  refine RealCoeff.smul (RealCoeff.sum (s := Finset.univ) fun j _ =>
    RealCoeff.sum (s := Finset.univ) fun k _ => RealCoeff.smul ?_)
  exact RealCoeff.smul (RealCoeff.sum (s := Finset.univ) fun b _ =>
    RealCoeff.sum (s := Finset.univ) fun d _ =>
      RealCoeff.smul ((realCoeff_X _).mul (realCoeff_X _)))

/-! ## 3. The split on the core

`smField P r = (coreRepPoly 163).op (mulOp (smFormPoly P id r))`, so a split of the field
polynomial gives a split of the operator.  We record it pointwise, for the gluon and weak
components of the magnetic half of `smHamiltonian`. -/

/-- **The operator identity on the core**: the gluon magnetic-field operator is the derivative
operator plus the commutator operator. -/
theorem smFieldG_apply_eq (P : SmParams) (a : Fin 8) (i : Fin 3)
    (x : polyGaussCore (d := 163)) :
    (coreRepPoly 163).op (mulOp (smMagG P (id : Fin 163 → Fin 163) a i)) x
      = (coreRepPoly 163).op (mulOp (smDerivG (id : Fin 163 → Fin 163) a i)) x
        + (coreRepPoly 163).op (mulOp (smCommG P (id : Fin 163 → Fin 163) a i)) x := by
  have hpoly : smMagG P (id : Fin 163 → Fin 163) a i
      = smDerivG (id : Fin 163 → Fin 163) a i + smCommG P (id : Fin 163 → Fin 163) a i :=
    smMagG_eq_deriv_add P _ a i
  have hmul : mulOp (smDerivG (id : Fin 163 → Fin 163) a i
        + smCommG P (id : Fin 163 → Fin 163) a i) ((coreRepPoly 163).equiv.symm x)
      = mulOp (smDerivG (id : Fin 163 → Fin 163) a i) ((coreRepPoly 163).equiv.symm x)
        + mulOp (smCommG P (id : Fin 163 → Fin 163) a i) ((coreRepPoly 163).equiv.symm x) := by
    simp [mulOp_apply, add_mul]
  rw [CoreRep.op_apply, CoreRep.op_apply, CoreRep.op_apply, hpoly, hmul]
  exact map_add _ _ _

/-- The same for the weak field strength. -/
theorem smFieldW_apply_eq (P : SmParams) (m : Fin 3) (i : Fin 3)
    (x : polyGaussCore (d := 163)) :
    (coreRepPoly 163).op (mulOp (smMagW P (id : Fin 163 → Fin 163) m i)) x
      = (coreRepPoly 163).op (mulOp (smDerivW (id : Fin 163 → Fin 163) m i)) x
        + (coreRepPoly 163).op (mulOp (smCommW P (id : Fin 163 → Fin 163) m i)) x := by
  have hpoly : smMagW P (id : Fin 163 → Fin 163) m i
      = smDerivW (id : Fin 163 → Fin 163) m i + smCommW P (id : Fin 163 → Fin 163) m i :=
    smMagW_eq_deriv_add P _ m i
  have hmul : mulOp (smDerivW (id : Fin 163 → Fin 163) m i
        + smCommW P (id : Fin 163 → Fin 163) m i) ((coreRepPoly 163).equiv.symm x)
      = mulOp (smDerivW (id : Fin 163 → Fin 163) m i) ((coreRepPoly 163).equiv.symm x)
        + mulOp (smCommW P (id : Fin 163 → Fin 163) m i) ((coreRepPoly 163).equiv.symm x) := by
    simp [mulOp_apply, add_mul]
  rw [CoreRep.op_apply, CoreRep.op_apply, CoreRep.op_apply, hpoly, hmul]
  exact map_add _ _ _

/-- The derivative half of the gluon field strength is a symmetric operator on the core. -/
theorem smDerivG_symmetricOn (a : Fin 8) (i : Fin 3) :
    SymmetricOn (polyGaussCore (d := 163))
      ((polyGaussCore (d := 163)).subtype.comp
        ((coreRepPoly 163).op (mulOp (smDerivG (id : Fin 163 → Fin 163) a i)))) :=
  (coreRepPoly 163).symmetricOn_op
    (mulOp_polySym (realCoeff_smDerivG (id : Fin 163 → Fin 163) a i))

/-- The commutator half of the gluon field strength is a symmetric operator on the core. -/
theorem smCommG_symmetricOn (P : SmParams) (a : Fin 8) (i : Fin 3) :
    SymmetricOn (polyGaussCore (d := 163))
      ((polyGaussCore (d := 163)).subtype.comp
        ((coreRepPoly 163).op (mulOp (smCommG P (id : Fin 163 → Fin 163) a i)))) :=
  (coreRepPoly 163).symmetricOn_op
    (mulOp_polySym (realCoeff_smCommG P (id : Fin 163 → Fin 163) a i))

/-- The derivative half of the weak field strength is a symmetric operator on the core. -/
theorem smDerivW_symmetricOn (m : Fin 3) (i : Fin 3) :
    SymmetricOn (polyGaussCore (d := 163))
      ((polyGaussCore (d := 163)).subtype.comp
        ((coreRepPoly 163).op (mulOp (smDerivW (id : Fin 163 → Fin 163) m i)))) :=
  (coreRepPoly 163).symmetricOn_op
    (mulOp_polySym (realCoeff_smDerivW (id : Fin 163 → Fin 163) m i))

/-- The commutator half of the weak field strength is a symmetric operator on the core. -/
theorem smCommW_symmetricOn (P : SmParams) (m : Fin 3) (i : Fin 3) :
    SymmetricOn (polyGaussCore (d := 163))
      ((polyGaussCore (d := 163)).subtype.comp
        ((coreRepPoly 163).op (mulOp (smCommW P (id : Fin 163 → Fin 163) m i)))) :=
  (coreRepPoly 163).symmetricOn_op
    (mulOp_polySym (realCoeff_smCommW P (id : Fin 163 → Fin 163) m i))

/-! ## 4. The commutator parts are Lie brackets -/

/-- **Contracting with `ε` antisymmetrises**, in any dimension of the polynomial ring: for *any*
bilinear form `F`, `2 ε_{ijk}F_{jk} = ε_{ijk}(F_{jk} − F_{kj})`.  No hypothesis on `F` — this is
the identity that makes the non-abelian term a commutator. -/
theorem two_smul_levi_contract {d : ℕ} (F : Fin 3 → Fin 3 → MvPolynomial (Fin d) ℂ) (i : Fin 3) :
    (2 : ℂ) • (∑ j, ∑ k, ((levi i j k : ℝ) : ℂ) • F j k)
      = ∑ j, ∑ k, ((levi i j k : ℝ) : ℂ) • (F j k - F k j) := by
  fin_cases i <;> simp only [Fin.sum_univ_three, levi] <;> push_cast <;> module

/-- **The gluon commutator part is `¼ ε_{ijk} g_s [G_j, G_k]`**: the outer `½` is the one in the
definition of `B^G`, the inner one comes from antisymmetrising the `ε`-contraction.  The bracket
is `[G_j,G_k]_a = Σ_{bd} f_{abd}(G_{j,b}G_{k,d} − G_{k,b}G_{j,d})`. -/
theorem smCommG_eq_quarter_bracket (P : SmParams) (co : Fin 163 → Fin D) (a : Fin 8) (i : Fin 3) :
    smCommG P co a i
      = ((1 / 4 : ℝ) : ℂ) • ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) •
          (((P.gs : ℝ) : ℂ) • (smBilinG P co j k a - smBilinG P co k j a)) := by
  have h := two_smul_levi_contract
    (fun j k => ((P.gs : ℝ) : ℂ) • smBilinG P co j k a) i
  have hV : (∑ j, ∑ k, ((levi i j k : ℝ) : ℂ) •
        (((P.gs : ℝ) : ℂ) • smBilinG P co j k a - ((P.gs : ℝ) : ℂ) • smBilinG P co k j a))
      = ∑ j, ∑ k, ((levi i j k : ℝ) : ℂ) •
          (((P.gs : ℝ) : ℂ) • (smBilinG P co j k a - smBilinG P co k j a)) := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [smul_sub, smul_smul]
  have hT : (∑ j, ∑ k, ((levi i j k : ℝ) : ℂ) • (((P.gs : ℝ) : ℂ) • smBilinG P co j k a))
      = ((1 / 2 : ℝ) : ℂ) • ∑ j, ∑ k, ((levi i j k : ℝ) : ℂ) •
          (((P.gs : ℝ) : ℂ) • (smBilinG P co j k a - smBilinG P co k j a)) := by
    have hstep := congrArg (fun z => ((1 / 2 : ℝ) : ℂ) • z) h
    rw [hV] at hstep
    simpa [smul_smul] using hstep
  rw [smCommG, hT, smul_smul]
  norm_num

/-- **The weak commutator part is `¼ ε_{ijk} g [W_j, W_k]`**. -/
theorem smCommW_eq_quarter_bracket (P : SmParams) (co : Fin 163 → Fin D) (m : Fin 3) (i : Fin 3) :
    smCommW P co m i
      = ((1 / 4 : ℝ) : ℂ) • ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) •
          (((P.gw : ℝ) : ℂ) • (smBilinW P co j k m - smBilinW P co k j m)) := by
  have h := two_smul_levi_contract
    (fun j k => ((P.gw : ℝ) : ℂ) • smBilinW P co j k m) i
  have hV : (∑ j, ∑ k, ((levi i j k : ℝ) : ℂ) •
        (((P.gw : ℝ) : ℂ) • smBilinW P co j k m - ((P.gw : ℝ) : ℂ) • smBilinW P co k j m))
      = ∑ j, ∑ k, ((levi i j k : ℝ) : ℂ) •
          (((P.gw : ℝ) : ℂ) • (smBilinW P co j k m - smBilinW P co k j m)) := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [smul_sub, smul_smul]
  have hT : (∑ j, ∑ k, ((levi i j k : ℝ) : ℂ) • (((P.gw : ℝ) : ℂ) • smBilinW P co j k m))
      = ((1 / 2 : ℝ) : ℂ) • ∑ j, ∑ k, ((levi i j k : ℝ) : ℂ) •
          (((P.gw : ℝ) : ℂ) • (smBilinW P co j k m - smBilinW P co k j m)) := by
    have hstep := congrArg (fun z => ((1 / 2 : ℝ) : ℂ) • z) h
    rw [hV] at hstep
    simpa [smul_smul] using hstep
  rw [smCommW, hT, smul_smul]
  norm_num

/-- **The gluon commutator part vanishes when the fields commute**: if the bilinear form
`f_{abd} G_{j,b} G_{k,d}` is symmetric in `(j,b) ↔ (k,d)` — the Cartan sector — the interaction
contributes nothing and `B^G` is the derivative part alone. -/
theorem smCommG_eq_zero_of_symmetric (P : SmParams) (co : Fin 163 → Fin D) (a : Fin 8) (i : Fin 3)
    (hsym : ∀ j k : Fin 3, smBilinG P co j k a = smBilinG P co k j a) :
    smCommG P co a i = 0 := by
  have h := two_smul_levi_contract
    (fun j k => ((P.gs : ℝ) : ℂ) • smBilinG P co j k a) i
  have hzero : (∑ j, ∑ k, ((levi i j k : ℝ) : ℂ) •
      (((P.gs : ℝ) : ℂ) • smBilinG P co j k a - ((P.gs : ℝ) : ℂ) • smBilinG P co k j a)) = 0 := by
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
    rw [hsym j k, sub_self, smul_zero]
  rw [hzero] at h
  have hS : (∑ j, ∑ k, ((levi i j k : ℝ) : ℂ) •
      (((P.gs : ℝ) : ℂ) • smBilinG P co j k a)) = 0 := by
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  simp only [smCommG, hS, smul_zero]

/-- **The weak commutator part vanishes on the commuting sector**. -/
theorem smCommW_eq_zero_of_symmetric (P : SmParams) (co : Fin 163 → Fin D) (m : Fin 3) (i : Fin 3)
    (hsym : ∀ j k : Fin 3, smBilinW P co j k m = smBilinW P co k j m) :
    smCommW P co m i = 0 := by
  have h := two_smul_levi_contract
    (fun j k => ((P.gw : ℝ) : ℂ) • smBilinW P co j k m) i
  have hzero : (∑ j, ∑ k, ((levi i j k : ℝ) : ℂ) •
      (((P.gw : ℝ) : ℂ) • smBilinW P co j k m - ((P.gw : ℝ) : ℂ) • smBilinW P co k j m)) = 0 := by
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
    rw [hsym j k, sub_self, smul_zero]
  rw [hzero] at h
  have hS : (∑ j, ∑ k, ((levi i j k : ℝ) : ℂ) •
      (((P.gw : ℝ) : ℂ) • smBilinW P co j k m)) = 0 := by
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  simp only [smCommW, hS, smul_zero]

end

end BookProof.SmFieldStrengthSplit
