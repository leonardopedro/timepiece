import Mathlib
import BookProof.ChapterFarisLavineOnly
import BookProof.ChapterQgOuterFockInteractionFL
import BookProof.ChapterYangMillsAbelianEsa
import BookProof.ChapterYangMillsOuterFockFL.Part1

/-!
# The gauge-fixed Yang–Mills Hamiltonian on the outer Fock space, by Faris–Lavine

This module does for Yang–Mills what `BookProof.ChapterNsOuterFockFarisLavine` does for
Navier–Stokes and `BookProof.ChapterQgOuterFockFullFL` for quantum gravity: it puts the 3D
gauge-fixed Yang–Mills Hamiltonian on the outer Fock space `⊕ₙ L²(ℝ^{99n})` and proves it
essentially self-adjoint there **by the Faris–Lavine criterion**, against the lifted
Friedrichs extension of the positive one-particle operator `N₁ = −Δ + ‖x‖²/4`.

## The one-particle statement, re-routed through Faris–Lavine

`BookProof.YangMillsAbelianEsa.ymAbelian_essentiallySelfAdjointOn_core` proves essential
self-adjointness of the one-particle Hamiltonian by the *Carleman* route.  That route does
not lift to the Fock space.  `ymAbelian_eq_sqSumOp` identifies the same Hamiltonian as a
kinetic-plus-squares operator `½ Σ_j κ_j π_j² + ½ Σ_m B_m²` and
`ymAbelian_esa_farisLavine` re-proves essential self-adjointness through
`BookProof.FarisLavineOnly.sqSumOp_esa_farisLavine` — that is, through Theorem 1 of
Faris–Lavine with a Friedrichs comparison operator and a commutator bound, the only data
that survive second quantization.

## The parcel model

An excitation ("parcel") carries the `99 = 3 + 24 + 72` field-space coordinates of
`BookProof.ChapterYangMillsHermite`: the three spatial coordinates, the `24` gauge fields
`A_{j,a}` and the `72` **independent derivative coordinates** `∂_j A_{k,a}`.  The `n`-parcel
sector is `L²(ℝ^{99n})` and the state space is the outer Fock space `⊕ₙ L²(ℝ^{99n})`.

For every parcel `p` the Hamiltonian carries three families of squared linear forms:

* the `24` **magnetic fields** `B_{i a} = ε_{ijk} ∂_j A_{k,a}` of the parcel
  (`linForm_ymMag`);
* the `8` **Gauss/Coulomb gauge-fixing forms** `ζ Σ_j ∂_j A_{j,a}` (`linForm_ymGauss`) — the
  3D gauge condition, imposed as a squared constraint;
* the `72` **derivative-tie forms** `λ(∂_jA_{k,a} + A_{k,a} − A_{k,a}^{next})`
  (`linForm_ymTie`), which state that the independent coordinate `∂_jA_{k,a}` is the finite
  difference of the gauge field between neighbouring parcels.  These forms reach into the
  neighbouring parcel, so the Hamiltonian is genuinely **interacting**
  (`ym_interaction_nontrivial`).

The kinetic term is `½ Σ_{j,a} π_{A_{j,a}}²`, the momenta conjugate to the `24` gauge
fields of each parcel (`ymKap`).

## What is proved

* `ymKap`, `ymAbelian_eq_sqSumOp`, `ymAbelian_esa_farisLavine` — the one-particle
  Hamiltonian as a kinetic-plus-squares operator, and its essential self-adjointness by
  Faris–Lavine;
* `coordOf`, `parcelOf`, `locOf`, `sum_reindex_parcels` — the sector bookkeeping;
* `ymSame`, `ymNext`, `ymVec`, `linForm_ymVec`, `linForm_ymMag`, `linForm_ymGauss`,
  `linForm_ymTie`, `ym_interaction_nontrivial` — the linear forms, written out;
* `abs_ymSame_le`, `abs_ymNext_le`, `ymVec_row_le`, `ymVec_col_le` — the Schur data,
  uniform in the parcel number;
* `ymFamily` — the resulting uniform kinetic-plus-squares family;
* `ymOuterHam_symmetricOn`, `ymOuterHam_esa_fl` — the Hamiltonian on the finite-particle
  core, symmetric and essentially self-adjoint **by Faris–Lavine**;
* **`ymOuterFock_esa_farisLavine`** — the headline: essential self-adjointness on the
  domain of the lifted Friedrichs extension of `N₁`, with the extension property on the
  finite-particle core.

## Honest boundary

This is the **abelian** magnetic field `B_{i a} = ε_{ijk} ∂_j A_{k,a}`, i.e. the structure
constants are `f_{abc} = 0`, exactly as in `BookProof.ChapterYangMillsAbelianEsa`.  For
`f_{abc} ≠ 0` the magnetic field is quadratic in the gauge fields, so the potential is
quartic; then no comparison operator that is a function of the harmonic oscillator can
satisfy the Faris–Lavine relative bound, and the essential self-adjointness of the
one-particle operator — Kato's theorem for `−Δ + V`, `V ≥ 0`, `V ∈ L²_loc` — is not
available in this development (see `REVIEW_AND_PLAN_20260907.md`, gap G1).  What the
parcel model *does* add beyond the one-particle abelian statement is the 3D gauge fixing,
the derivative-coordinate ties and the resulting nearest-neighbour interaction, all carried
through second quantization with constants independent of the parcel number.  No mass gap
and no spectral information is claimed.

Everything is `sorry`-free and `axiom`-free.
-/

open scoped ENNReal

noncomputable section

namespace BookProof.YmOuterFockFL

open Finset MvPolynomial
open BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.HermiteProductCore BookProof.QgHermiteOscillator
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.SqSumOuterFamily BookProof.FarisLavineOnly
open BookProof.QgOuterFockInteractionFL
open BookProof.YangMillsHermite BookProof.YangMillsAbelianEsa

variable (zeta lam : ℝ)
/-! ## 4. The Schur data -/

variable {zeta lam}
variable {B : ℝ} (hB : 1 ≤ B) (hzeta : |zeta| ≤ B) (hlam : |lam| ≤ B)

theorem abs_levi_le_one (i j k : Fin 3) : |levi i j k| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [levi]

theorem abs_ymMagVec_le_nine (m : Fin 24) (l : Fin 99) : |ymMagVec m l| ≤ 9 := by
  rw [ymMagVec]
  calc |∑ j : Fin 3, ∑ k : Fin 3,
        (if l = idxD j k (decodeColor m) then levi (decodeSpace m) j k else 0)|
      ≤ ∑ j : Fin 3, |∑ k : Fin 3,
          (if l = idxD j k (decodeColor m) then levi (decodeSpace m) j k else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, (3 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        calc |∑ k : Fin 3, (if l = idxD j k (decodeColor m) then levi (decodeSpace m) j k else 0)|
            ≤ ∑ k : Fin 3, |if l = idxD j k (decodeColor m) then levi (decodeSpace m) j k else 0| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _k : Fin 3, (1 : ℝ) := by
              refine Finset.sum_le_sum fun k _ => ?_
              split_ifs
              · exact abs_levi_le_one _ _ _
              · simp
          _ = 3 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              norm_num
    _ = 9 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

include hB hzeta hlam in
/-- Every coefficient on the parcel's own coordinates is bounded by `9B`. -/
theorem abs_ymSame_le (f : YmForm) (l : Fin 99) : |ymSame zeta lam f l| ≤ 9 * B := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB
  obtain m | (a | ⟨j, k, a⟩) := f
  · exact le_trans (abs_ymMagVec_le_nine m l) (by nlinarith)
  · change |∑ j : Fin 3, (if l = idxD j j a then zeta else 0)| ≤ 9 * B
    calc |∑ j : Fin 3, (if l = idxD j j a then zeta else 0)|
        ≤ ∑ j : Fin 3, |if l = idxD j j a then zeta else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 3, B := by
          refine Finset.sum_le_sum fun j _ => ?_
          split_ifs
          · exact hzeta
          · simpa using hB0
      _ = 3 * B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
      _ ≤ 9 * B := by nlinarith
  · change |(if l = idxD j k a then lam else 0) + (if l = idxA k a then lam else 0)| ≤ 9 * B
    have h1 : |if l = idxD j k a then lam else 0| ≤ B := by
      split_ifs
      · exact hlam
      · simpa using hB0
    have h2 : |if l = idxA k a then lam else 0| ≤ B := by
      split_ifs
      · exact hlam
      · simpa using hB0
    calc |(if l = idxD j k a then lam else 0) + (if l = idxA k a then lam else 0)|
        ≤ |if l = idxD j k a then lam else 0| + |if l = idxA k a then lam else 0| :=
          abs_add_le _ _
      _ ≤ B + B := add_le_add h1 h2
      _ ≤ 9 * B := by nlinarith

include hB hlam in
/-- Every coefficient on the neighbouring parcel's coordinates is bounded by `B`. -/
theorem abs_ymNext_le (f : YmForm) (l : Fin 99) : |ymNext lam f l| ≤ B := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB
  obtain m | (a | ⟨j, k, a⟩) := f
  · change |(0 : ℝ)| ≤ B; simpa using hB0
  · change |(0 : ℝ)| ≤ B; simpa using hB0
  · change |if l = idxA k a then -lam else 0| ≤ B
    split_ifs
    · rwa [abs_neg]
    · simpa using hB0

theorem abs_ymVec_le {n : ℕ} (r : Fin n × YmForm) (p : Fin n) (l : Fin 99) :
    |ymVec zeta lam n r (coordOf p l)|
      ≤ (if p = r.1 then |ymSame zeta lam r.2 l| else 0)
        + (if p = nextPart r.1 then |ymNext lam r.2 l| else 0) := by
  rw [ymVec, parcelOf_coordOf, locOf_coordOf]
  by_cases h1 : p = r.1
  · rw [if_pos h1, if_pos h1]
    have h2 : (0 : ℝ) ≤ if p = nextPart r.1 then |ymNext lam r.2 l| else 0 := by
      split_ifs
      · exact abs_nonneg _
      · exact le_rfl
    linarith
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : p = nextPart r.1
    · rw [if_pos h2, if_pos h2]
      simp
    · rw [if_neg h2, if_neg h2]
      simp

include hB hzeta hlam in
/-- **The row bound**: every linear form of the family has `ℓ¹` norm at most `990B`,
uniformly in the parcel number.  (No attempt is made to optimize the constant: only its
independence of the parcel number matters.) -/
theorem ymVec_row_le (n : ℕ) (r : Fin n × YmForm) :
    ∑ I : Fin (n * 99), |ymVec zeta lam n r I| ≤ 990 * B := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB
  set A : Fin 99 → ℝ := fun l => |ymSame zeta lam r.2 l| with hA
  set C : Fin 99 → ℝ := fun l => |ymNext lam r.2 l| with hC
  have hstep : ∀ p : Fin n,
      ∑ l : Fin 99, ((if p = r.1 then A l else 0) + (if p = nextPart r.1 then C l else 0))
        = (if p = r.1 then ∑ l : Fin 99, A l else 0)
          + (if p = nextPart r.1 then ∑ l : Fin 99, C l else 0) := by
    intro p
    rw [Finset.sum_add_distrib]
    congr 1
    · by_cases h : p = r.1 <;> simp [h]
    · by_cases h : p = nextPart r.1 <;> simp [h]
  have hagg : ∑ p : Fin n, ∑ l : Fin 99,
      ((if p = r.1 then A l else 0) + (if p = nextPart r.1 then C l else 0))
      = (∑ l : Fin 99, A l) + ∑ l : Fin 99, C l := by
    rw [Finset.sum_congr rfl fun p _ => hstep p, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ r.1 (fun _ => ∑ l : Fin 99, A l),
      Finset.sum_ite_eq' Finset.univ (nextPart r.1) (fun _ => ∑ l : Fin 99, C l)]
    simp
  have hArow : ∑ l : Fin 99, A l ≤ 891 * B := by
    calc ∑ l : Fin 99, A l ≤ ∑ _l : Fin 99, 9 * B :=
          Finset.sum_le_sum fun l _ => abs_ymSame_le hB hzeta hlam r.2 l
      _ = 891 * B := by simp; ring
  have hCrow : ∑ l : Fin 99, C l ≤ 99 * B := by
    calc ∑ l : Fin 99, C l ≤ ∑ _l : Fin 99, B :=
          Finset.sum_le_sum fun l _ => abs_ymNext_le hB hlam r.2 l
      _ = 99 * B := by simp
  rw [sum_reindex_parcels]
  calc ∑ p : Fin n, ∑ l : Fin 99, |ymVec zeta lam n r (coordOf p l)|
      ≤ ∑ p : Fin n, ∑ l : Fin 99,
          ((if p = r.1 then A l else 0) + (if p = nextPart r.1 then C l else 0)) :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun l _ => abs_ymVec_le r p l
    _ = (∑ l : Fin 99, A l) + ∑ l : Fin 99, C l := hagg
    _ ≤ 990 * B := by linarith

include hB hzeta hlam in
/-- **The column bound**: every coordinate is touched by forms of total `ℓ¹` weight at most
`1040B`, uniformly in the parcel number — the couplings are nearest-neighbour, so a
coordinate belongs to one parcel and that parcel occurs in exactly two coupling blocks. -/
theorem ymVec_col_le (n : ℕ) (I : Fin (n * 99)) :
    ∑ r : Fin n × YmForm, |ymVec zeta lam n r I| ≤ 1040 * B := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB
  set b0 : Fin n := parcelOf I with hb0
  set c0 : Fin 99 := locOf I with hc0
  have hI : I = coordOf b0 c0 := (coordOf_parcelOf_locOf I).symm
  have hterm : ∀ (p : Fin n) (f : YmForm),
      |ymVec zeta lam n (p, f) I|
        ≤ (if b0 = p then |ymSame zeta lam f c0| else 0)
          + (if b0 = nextPart p then |ymNext lam f c0| else 0) := by
    intro p f
    rw [hI, ymVec, parcelOf_coordOf, locOf_coordOf]
    by_cases h1 : b0 = p
    · rw [if_pos h1, if_pos h1]
      have h2 : (0 : ℝ) ≤ if b0 = nextPart p then |ymNext lam f c0| else 0 := by
        split_ifs
        · exact abs_nonneg _
        · exact le_rfl
      linarith
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : b0 = nextPart p
      · rw [if_pos h2, if_pos h2]
        simp
      · rw [if_neg h2, if_neg h2]
        simp
  have hinner : ∀ p : Fin n,
      ∑ f : YmForm, ((if b0 = p then |ymSame zeta lam f c0| else 0)
          + (if b0 = nextPart p then |ymNext lam f c0| else 0))
        = (if b0 = p then ∑ f : YmForm, |ymSame zeta lam f c0| else 0)
          + (if b0 = nextPart p then ∑ f : YmForm, |ymNext lam f c0| else 0) := by
    intro p
    rw [Finset.sum_add_distrib]
    congr 1
    · by_cases h : b0 = p <;> simp [h]
    · by_cases h : b0 = nextPart p <;> simp [h]
  have hagg : ∑ p : Fin n,
      ((if b0 = p then ∑ f : YmForm, |ymSame zeta lam f c0| else 0)
        + (if b0 = nextPart p then ∑ f : YmForm, |ymNext lam f c0| else 0))
      = (∑ f : YmForm, |ymSame zeta lam f c0|) + ∑ f : YmForm, |ymNext lam f c0| := by
    rw [Finset.sum_add_distrib,
      Finset.sum_ite_eq Finset.univ b0 (fun _ => ∑ f : YmForm, |ymSame zeta lam f c0|),
      sum_comp_nextPart (fun x => if b0 = x then ∑ f : YmForm, |ymNext lam f c0| else 0),
      Finset.sum_ite_eq Finset.univ b0 (fun _ => ∑ f : YmForm, |ymNext lam f c0|)]
    simp
  have hAcol : ∑ f : YmForm, |ymSame zeta lam f c0| ≤ 936 * B := by
    calc ∑ f : YmForm, |ymSame zeta lam f c0| ≤ ∑ _f : YmForm, 9 * B :=
          Finset.sum_le_sum fun f _ => abs_ymSame_le hB hzeta hlam f c0
      _ = 936 * B := by
          rw [Finset.sum_const, Finset.card_univ, card_ymForm]
          simp; ring
  have hCcol : ∑ f : YmForm, |ymNext lam f c0| ≤ 104 * B := by
    calc ∑ f : YmForm, |ymNext lam f c0| ≤ ∑ _f : YmForm, B :=
          Finset.sum_le_sum fun f _ => abs_ymNext_le hB hlam f c0
      _ = 104 * B := by
          rw [Finset.sum_const, Finset.card_univ, card_ymForm]
          simp
  calc ∑ r : Fin n × YmForm, |ymVec zeta lam n r I|
      = ∑ p : Fin n, ∑ f : YmForm, |ymVec zeta lam n (p, f) I| := Fintype.sum_prod_type _
    _ ≤ ∑ p : Fin n, ∑ f : YmForm,
          ((if b0 = p then |ymSame zeta lam f c0| else 0)
            + (if b0 = nextPart p then |ymNext lam f c0| else 0)) :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun f _ => hterm p f
    _ = (∑ f : YmForm, |ymSame zeta lam f c0|) + ∑ f : YmForm, |ymNext lam f c0| := by
        rw [Finset.sum_congr rfl fun p _ => hinner p, hagg]
    _ ≤ 1040 * B := by linarith

/-! ## 5. The family and the Faris–Lavine theorem -/

theorem abs_ymKap_le (l : Fin 99) : |ymKap l| ≤ 24 := by
  rw [ymKap]
  calc |∑ m : Fin 24, ymMomVec m l| ≤ ∑ m : Fin 24, |ymMomVec m l| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m : Fin 24, (1 : ℝ) := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [ymMomVec]
        split_ifs <;> norm_num
    _ = 24 := by simp

include hB hzeta hlam in
/-- **The gauge-fixed Yang–Mills family** on the outer Fock space `⊕ₙ L²(ℝ^{99n})`: the
kinetic term `½ Σ_{j,a} π_{A_{j,a}}²` of every parcel together with the squared magnetic
fields, the squared Gauss gauge-fixing forms and the squared derivative ties, with Schur
constants independent of the parcel number. -/
def ymFamily : SqFamily where
  dim := fun n => n * 99
  R := fun n => Fin n × YmForm
  finR := fun _ => inferInstance
  kap := fun _ I => ymKap (locOf I)
  vv := fun n => ymVec zeta lam n
  km := 24
  a := 990 * B
  b := 1040 * B
  km_nonneg := by norm_num
  a_nonneg := by nlinarith
  b_nonneg := by nlinarith
  kap_le := fun _ I => abs_ymKap_le (locOf I)
  row_le := fun n r => ymVec_row_le hB hzeta hlam n r
  col_le := fun n I => ymVec_col_le hB hzeta hlam n I

include hB hzeta hlam in
theorem ymFamily_dim : (ymFamily hB hzeta hlam).dim = fun n => n * 99 := rfl

include hB hzeta hlam in
theorem ymFamily_vv (n : ℕ) (r : Fin n × YmForm)
    (I : Fin ((ymFamily hB hzeta hlam).dim n)) :
    (ymFamily hB hzeta hlam).vv n r I = ymVec zeta lam n r I := rfl

include hB hzeta hlam in
/-- **The full gauge-fixed Yang–Mills Hamiltonian** on the finite-particle core of the
outer Fock space, and its symmetry. -/
theorem ymOuterHam_symmetricOn :
    SymmetricOn (outerCore (ymFamily hB hzeta hlam).dim) (ymFamily hB hzeta hlam).outerHam :=
  (ymFamily hB hzeta hlam).outerHam_symmetricOn

include hB hzeta hlam in
/-- **The Hamiltonian is essentially self-adjoint on the finite-particle core, by
Faris–Lavine.** -/
theorem ymOuterHam_esa_fl :
    EssentiallySelfAdjointOn (outerCore (ymFamily hB hzeta hlam).dim)
      (ymFamily hB hzeta hlam).outerHam :=
  outerHam_esa_fl (ymFamily hB hzeta hlam)

include hB hzeta hlam in
/-- **The gauge-fixed Yang–Mills Hamiltonian on the outer Fock space is essentially
self-adjoint, by Faris–Lavine**, on the domain of the lifted Friedrichs extension of the
positive one-particle operator `N₁ = −Δ + ‖x‖²/4` — the same comparison operator as in the
gravity and Navier–Stokes sectors — and the operator so realized extends the
finite-particle-core Hamiltonian.

The Hamiltonian contains the magnetic energy of every parcel, the 3D Gauss gauge-fixing
terms, and the ties of the independent derivative coordinates to the finite differences of
the gauge field between neighbouring parcels; the last are genuine interaction terms
(`ym_interaction_nontrivial`). -/
theorem ymOuterFock_esa_farisLavine :
    EssentiallySelfAdjointOn
        (outerFriedDom (ymFamily hB hzeta hlam).dim)
        (dsFibOp (fun n : ℕ => harmFried ((ymFamily hB hzeta hlam).dim n))
          (ymFamily hB hzeta hlam).secExt
          (ymFamily hB hzeta hlam).flK
          (ymFamily hB hzeta hlam).secExt_rel) ∧
      ∀ x : outerCore (ymFamily hB hzeta hlam).dim,
        ∃ h : (x : outerFock (ymFamily hB hzeta hlam).dim)
            ∈ outerFriedDom (ymFamily hB hzeta hlam).dim,
          dsFibOp (fun n : ℕ => harmFried ((ymFamily hB hzeta hlam).dim n))
              (ymFamily hB hzeta hlam).secExt
              (ymFamily hB hzeta hlam).flK
              (ymFamily hB hzeta hlam).secExt_rel
              ⟨(x : outerFock (ymFamily hB hzeta hlam).dim), h⟩
            = (ymFamily hB hzeta hlam).outerHam x :=
  (ymFamily hB hzeta hlam).esa_farisLavine

end BookProof.YmOuterFockFL

end
