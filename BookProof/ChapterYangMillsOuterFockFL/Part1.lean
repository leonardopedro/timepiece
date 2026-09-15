import Mathlib
import BookProof.ChapterFarisLavineOnly
import BookProof.ChapterQgOuterFockInteractionFL
import BookProof.ChapterYangMillsAbelianEsa

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

/-! ## 1. The one-particle Hamiltonian as a kinetic-plus-squares operator -/

/-- **The signature of the Yang–Mills kinetic term**: `1` on the `24` coordinates
`A_{j,a}` that carry a conjugate momentum, `0` on the three spatial coordinates and on the
`72` derivative coordinates. -/
def ymKap (l : Fin 99) : ℝ := ∑ m : Fin 24, ymMomVec m l

theorem ymMomVec_mul_self (m : Fin 24) (l : Fin 99) :
    ymMomVec m l * ymMomVec m l = ymMomVec m l := by
  rw [ymMomVec]; split_ifs <;> norm_num

theorem ymMomVec_mul_of_ne {i j : Fin 99} (hij : i ≠ j) (m : Fin 24) :
    ymMomVec m i * ymMomVec m j = 0 := by
  rw [ymMomVec, ymMomVec]
  by_cases h1 : i = ymMomIdx m
  · have h2 : j ≠ ymMomIdx m := fun h => hij (h1.trans h.symm)
    rw [if_pos h1, if_neg h2, mul_zero]
  · rw [if_neg h1, zero_mul]

/-- The momentum matrix of the abelian Yang–Mills Hamiltonian is the diagonal matrix of the
signature `ymKap`. -/
theorem diagP_ymKap : diagP ymKap = ymFqP := by
  funext i j
  by_cases hij : i = j
  · subst hij
    rw [diagP, if_pos rfl, ymFqP, ymKap]
    rw [Finset.sum_congr rfl fun m _ => ymMomVec_mul_self m i]
    ring
  · rw [diagP, if_neg hij, ymFqP]
    rw [Finset.sum_congr rfl fun m _ => ymMomVec_mul_of_ne hij m]
    simp

/-- The coordinate matrix of the abelian Yang–Mills Hamiltonian is the Gram matrix of the
magnetic coefficient vectors. -/
theorem gramQ_ymMagVec : gramQ ymMagVec = ymFqQ := rfl

/-- **The abelian Yang–Mills Hamiltonian is a kinetic-plus-squares operator**
`½ Σ_j κ_j π_j² + ½ Σ_m B_m²` with signature `ymKap` and the `24` magnetic linear forms. -/
theorem ymAbelian_eq_sqSumOp :
    ymHamiltonian (coreRepPoly 99) 0 = sqSumOp ymKap ymMagVec := by
  rw [ymAbelian_eq_fqOp, sqSumOp_eq_fqOp, diagP_ymKap, gramQ_ymMagVec]

/-- **Essential self-adjointness of the one-particle abelian Yang–Mills Hamiltonian, by
Faris–Lavine.**  Unlike `ymAbelian_essentiallySelfAdjointOn_core`, whose
proof is the Carleman flux criterion, this proof is Theorem 1 of Faris–Lavine with the
Friedrichs extension of `N₁ = −Δ + ‖x‖²/4` as comparison operator — the certificate that
lifts to the outer Fock space. -/
theorem ymAbelian_esa_farisLavine :
    EssentiallySelfAdjointOn (polyGaussCore (d := 99)) (ymHamiltonian (coreRepPoly 99) 0) := by
  rw [ymAbelian_eq_sqSumOp]
  exact sqSumOp_esa_farisLavine ymKap ymMagVec

/-! ## 2. The parcels of the outer Fock space -/

/-- The coordinate of the sector `L²(ℝ^{99n})` carrying the field coordinate `l` of the
parcel `p`. -/
def coordOf {n : ℕ} (p : Fin n) (l : Fin 99) : Fin (n * 99) := finProdFinEquiv (p, l)

/-- The parcel carrying a sector coordinate. -/
def parcelOf {n : ℕ} (I : Fin (n * 99)) : Fin n := (finProdFinEquiv.symm I).1

/-- The field coordinate of a sector coordinate. -/
def locOf {n : ℕ} (I : Fin (n * 99)) : Fin 99 := (finProdFinEquiv.symm I).2

@[simp] theorem parcelOf_coordOf {n : ℕ} (p : Fin n) (l : Fin 99) :
    parcelOf (coordOf p l) = p := by simp [parcelOf, coordOf]

@[simp] theorem locOf_coordOf {n : ℕ} (p : Fin n) (l : Fin 99) :
    locOf (coordOf p l) = l := by simp [locOf, coordOf]

@[simp] theorem coordOf_parcelOf_locOf {n : ℕ} (I : Fin (n * 99)) :
    coordOf (parcelOf I) (locOf I) = I := by
  simp only [coordOf, parcelOf, locOf, Equiv.apply_symm_apply, Prod.mk.eta]

/-- The sector coordinates, as parcel-times-field-coordinate pairs. -/
def coordEquiv (n : ℕ) : Fin n × Fin 99 ≃ Fin (n * 99) := finProdFinEquiv

/-- Reindexing a sum over the `99n` sector coordinates as a sum over parcels and field
coordinates. -/
theorem sum_reindex_parcels {n : ℕ} {α : Type*} [AddCommMonoid α] (F : Fin (n * 99) → α) :
    ∑ I : Fin (n * 99), F I = ∑ p : Fin n, ∑ l : Fin 99, F (coordOf p l) := by
  calc ∑ I : Fin (n * 99), F I = ∑ pl : Fin n × Fin 99, F (coordOf pl.1 pl.2) :=
        (Fintype.sum_equiv (coordEquiv n) (fun pl => F (coordOf pl.1 pl.2)) F fun _ => rfl).symm
    _ = ∑ p : Fin n, ∑ l : Fin 99, F (coordOf p l) :=
        Fintype.sum_prod_type (fun pl : Fin n × Fin 99 => F (coordOf pl.1 pl.2))

/-! ## 3. The linear forms of the gauge-fixed Yang–Mills Hamiltonian -/

/-- **The linear forms carried by one parcel**: the `24` magnetic fields, the `8` Gauss
gauge-fixing forms and the `72` derivative ties. -/
abbrev YmForm : Type := Fin 24 ⊕ Fin 8 ⊕ (Fin 3 × Fin 3 × Fin 8)

/-- The `m`-th magnetic form. -/
def formMag (m : Fin 24) : YmForm := Sum.inl m

/-- The Gauss gauge-fixing form of colour `a`. -/
def formGauss (a : Fin 8) : YmForm := Sum.inr (Sum.inl a)

/-- The derivative tie of the coordinate `∂_j A_{k,a}`. -/
def formTie (j k : Fin 3) (a : Fin 8) : YmForm := Sum.inr (Sum.inr (j, k, a))

theorem card_ymForm : Fintype.card YmForm = 104 := by
  simp [YmForm]

variable (zeta lam : ℝ)

/-- **The coefficients of the forms on the coordinates of their own parcel.** -/
def ymSame : YmForm → Fin 99 → ℝ
  | Sum.inl m, l => ymMagVec m l
  | Sum.inr (Sum.inl a), l => ∑ j : Fin 3, (if l = idxD j j a then zeta else 0)
  | Sum.inr (Sum.inr (j, k, a)), l =>
      (if l = idxD j k a then lam else 0) + (if l = idxA k a then lam else 0)

/-- **The coefficients of the forms on the coordinates of the neighbouring parcel.**  Only
the derivative ties reach across parcels. -/
def ymNext : YmForm → Fin 99 → ℝ
  | Sum.inr (Sum.inr (_, k, a)), l => if l = idxA k a then -lam else 0
  | _, _ => 0

/-- **The coefficient vector of the form `(p, f)` of the `n`-parcel sector.** -/
def ymVec (n : ℕ) (r : Fin n × YmForm) (I : Fin (n * 99)) : ℝ :=
  if parcelOf I = r.1 then ymSame zeta lam r.2 (locOf I)
  else if parcelOf I = nextPart r.1 then ymNext lam r.2 (locOf I) else 0

/-! ### The forms, written out -/

theorem sum_single_smul_X {n : ℕ} (p : Fin n) (l₀ : Fin 99) (c : ℂ) :
    ∑ l : Fin 99, (if l = l₀ then c else 0) • (X (coordOf p l) : MvPolynomial (Fin (n * 99)) ℂ)
      = c • X (coordOf p l₀) := by
  rw [Finset.sum_eq_single l₀]
  · rw [if_pos rfl]
  · intro b _ hb; rw [if_neg hb, zero_smul]
  · intro h; exact absurd (Finset.mem_univ l₀) h

set_option maxRecDepth 8000 in
/-- **The linear form of `(p, f)`, written out**: it is supported on the coordinates of the
parcel `p` and of its cyclic neighbour. -/
theorem linForm_ymVec {n : ℕ} (p : Fin n) (f : YmForm) (hne : nextPart p ≠ p) :
    linForm (ymVec zeta lam n (p, f))
      = (∑ l : Fin 99, ((ymSame zeta lam f l : ℝ) : ℂ) • X (coordOf p l))
        + ∑ l : Fin 99, ((ymNext lam f l : ℝ) : ℂ) • X (coordOf (nextPart p) l) := by
  classical
  rw [linForm, sum_reindex_parcels]
  have hval : ∀ (q : Fin n) (l : Fin 99),
      ((ymVec zeta lam n (p, f) (coordOf q l) : ℝ) : ℂ)
          • (X (coordOf q l) : MvPolynomial (Fin (n * 99)) ℂ)
        = if q = p then ((ymSame zeta lam f l : ℝ) : ℂ) • X (coordOf q l)
          else if q = nextPart p then ((ymNext lam f l : ℝ) : ℂ) • X (coordOf q l)
          else 0 := by
    intro q l
    rw [ymVec, parcelOf_coordOf, locOf_coordOf]
    by_cases h1 : q = p
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : q = nextPart p
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2]
        simp
  have hzero : ∀ q ∈ (Finset.univ : Finset (Fin n)), q ∉ ({p, nextPart p} : Finset (Fin n)) →
      (∑ l : Fin 99, ((ymVec zeta lam n (p, f) (coordOf q l) : ℝ) : ℂ)
        • (X (coordOf q l) : MvPolynomial (Fin (n * 99)) ℂ)) = 0 := by
    intro q _ hq
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hval q l, if_neg hq.1, if_neg hq.2]
  rw [← Finset.sum_subset (Finset.subset_univ ({p, nextPart p} : Finset (Fin n))) hzero,
    Finset.sum_pair (Ne.symm hne)]
  congr 1
  · exact Finset.sum_congr rfl fun l _ => by rw [hval p l, if_pos rfl]
  · exact Finset.sum_congr rfl fun l _ => by rw [hval (nextPart p) l, if_neg hne, if_pos rfl]

/-- **The magnetic form of a parcel**: `B_{i a} = ε_{ijk} ∂_j A_{k,a}`, in the derivative
coordinates of that parcel. -/
theorem linForm_ymMag {n : ℕ} (p : Fin n) (m : Fin 24) (hne : nextPart p ≠ p) :
    linForm (ymVec zeta lam n (p, formMag m))
      = ∑ j : Fin 3, ∑ k : Fin 3, ((levi (decodeSpace m) j k : ℝ) : ℂ)
          • X (coordOf p (idxD j k (decodeColor m))) := by
  rw [linForm_ymVec zeta lam p (formMag m) hne]
  have hnz : ∑ l : Fin 99, ((ymNext lam (formMag m) l : ℝ) : ℂ)
      • (X (coordOf (nextPart p) l) : MvPolynomial (Fin (n * 99)) ℂ) = 0 :=
    Finset.sum_eq_zero fun l _ => by
      rw [show ymNext lam (formMag m) l = 0 from rfl]; simp
  rw [hnz, add_zero]
  have hsame : ∀ l : Fin 99, ((ymSame zeta lam (formMag m) l : ℝ) : ℂ)
      = ∑ j : Fin 3, ∑ k : Fin 3,
        (if l = idxD j k (decodeColor m) then ((levi (decodeSpace m) j k : ℝ) : ℂ) else 0) := by
    intro l
    change ((ymMagVec m l : ℝ) : ℂ) = _
    rw [ymMagVec]
    push_cast
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  calc ∑ l : Fin 99, ((ymSame zeta lam (formMag m) l : ℝ) : ℂ) • X (coordOf p l)
      = ∑ l : Fin 99, ∑ j : Fin 3, ∑ k : Fin 3,
          (if l = idxD j k (decodeColor m) then ((levi (decodeSpace m) j k : ℝ) : ℂ) else 0)
            • (X (coordOf p l) : MvPolynomial (Fin (n * 99)) ℂ) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hsame l, Finset.sum_smul]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_smul
    _ = ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 99,
          (if l = idxD j k (decodeColor m) then ((levi (decodeSpace m) j k : ℝ) : ℂ) else 0)
            • (X (coordOf p l) : MvPolynomial (Fin (n * 99)) ℂ) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j : Fin 3, ∑ k : Fin 3, ((levi (decodeSpace m) j k : ℝ) : ℂ)
          • X (coordOf p (idxD j k (decodeColor m))) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
          sum_single_smul_X p _ _

/-- **The Gauss/Coulomb gauge-fixing form of a parcel**: `ζ Σ_j ∂_j A_{j,a}`. -/
theorem linForm_ymGauss {n : ℕ} (p : Fin n) (a : Fin 8) (hne : nextPart p ≠ p) :
    linForm (ymVec zeta lam n (p, formGauss a))
      = ∑ j : Fin 3, ((zeta : ℝ) : ℂ) • X (coordOf p (idxD j j a)) := by
  rw [linForm_ymVec zeta lam p (formGauss a) hne]
  have hnz : ∑ l : Fin 99, ((ymNext lam (formGauss a) l : ℝ) : ℂ)
      • (X (coordOf (nextPart p) l) : MvPolynomial (Fin (n * 99)) ℂ) = 0 :=
    Finset.sum_eq_zero fun l _ => by
      rw [show ymNext lam (formGauss a) l = 0 from rfl]; simp
  rw [hnz, add_zero]
  have hsame : ∀ l : Fin 99, ((ymSame zeta lam (formGauss a) l : ℝ) : ℂ)
      = ∑ j : Fin 3, (if l = idxD j j a then ((zeta : ℝ) : ℂ) else 0) := by
    intro l
    change ((∑ j : Fin 3, (if l = idxD j j a then zeta else 0) : ℝ) : ℂ) = _
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  calc ∑ l : Fin 99, ((ymSame zeta lam (formGauss a) l : ℝ) : ℂ) • X (coordOf p l)
      = ∑ l : Fin 99, ∑ j : Fin 3, (if l = idxD j j a then ((zeta : ℝ) : ℂ) else 0)
            • (X (coordOf p l) : MvPolynomial (Fin (n * 99)) ℂ) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hsame l, Finset.sum_smul]
    _ = ∑ j : Fin 3, ∑ l : Fin 99, (if l = idxD j j a then ((zeta : ℝ) : ℂ) else 0)
            • (X (coordOf p l) : MvPolynomial (Fin (n * 99)) ℂ) := Finset.sum_comm
    _ = ∑ j : Fin 3, ((zeta : ℝ) : ℂ) • X (coordOf p (idxD j j a)) :=
        Finset.sum_congr rfl fun j _ => sum_single_smul_X p _ _

/-- **The derivative tie of a parcel**: the independent coordinate `∂_jA_{k,a}` is tied to
the finite difference of the gauge field between the parcel and its neighbour. -/
theorem linForm_ymTie {n : ℕ} (p : Fin n) (j k : Fin 3) (a : Fin 8) (hne : nextPart p ≠ p) :
    linForm (ymVec zeta lam n (p, formTie j k a))
      = ((lam : ℝ) : ℂ) • (X (coordOf p (idxD j k a)) + X (coordOf p (idxA k a))
          - X (coordOf (nextPart p) (idxA k a))) := by
  rw [linForm_ymVec zeta lam p (formTie j k a) hne]
  have hsame : ∀ l : Fin 99, ((ymSame zeta lam (formTie j k a) l : ℝ) : ℂ)
      = (if l = idxD j k a then ((lam : ℝ) : ℂ) else 0)
        + (if l = idxA k a then ((lam : ℝ) : ℂ) else 0) := by
    intro l
    change (((if l = idxD j k a then lam else 0) + (if l = idxA k a then lam else 0) : ℝ) : ℂ) = _
    push_cast
    congr 1 <;> · split_ifs <;> simp
  have hnext : ∀ l : Fin 99, ((ymNext lam (formTie j k a) l : ℝ) : ℂ)
      = (if l = idxA k a then (-(lam : ℝ) : ℂ) else 0) := by
    intro l
    change (((if l = idxA k a then -lam else 0) : ℝ) : ℂ) = _
    split_ifs <;> simp
  have h1 : ∑ l : Fin 99, ((ymSame zeta lam (formTie j k a) l : ℝ) : ℂ)
        • (X (coordOf p l) : MvPolynomial (Fin (n * 99)) ℂ)
      = ((lam : ℝ) : ℂ) • X (coordOf p (idxD j k a))
        + ((lam : ℝ) : ℂ) • X (coordOf p (idxA k a)) := by
    rw [Finset.sum_congr rfl fun l _ => by rw [hsame l, add_smul], Finset.sum_add_distrib,
      sum_single_smul_X p (idxD j k a) _, sum_single_smul_X p (idxA k a) _]
  have h2 : ∑ l : Fin 99, ((ymNext lam (formTie j k a) l : ℝ) : ℂ)
        • (X (coordOf (nextPart p) l) : MvPolynomial (Fin (n * 99)) ℂ)
      = (-(lam : ℝ) : ℂ) • X (coordOf (nextPart p) (idxA k a)) := by
    rw [Finset.sum_congr rfl fun l _ => by rw [hnext l],
      sum_single_smul_X (nextPart p) (idxA k a) _]
  rw [h1, h2]
  module

/-- **The Hamiltonian is genuinely interacting**: for a nonzero tie strength and at least
two parcels, a linear form has a nonzero coefficient on a coordinate of another parcel. -/
theorem ym_interaction_nontrivial {n : ℕ} (hn : 2 ≤ n) (hlam : lam ≠ 0) :
    ∃ (r : Fin n × YmForm) (I : Fin (n * 99)),
      parcelOf I ≠ r.1 ∧ ymVec zeta lam n r I ≠ 0 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hne : nextPart (⟨0, hn0⟩ : Fin n) ≠ ⟨0, hn0⟩ := nextPart_ne hn ⟨0, hn0⟩ rfl
  refine ⟨(⟨0, hn0⟩, formTie 0 0 0), coordOf (nextPart ⟨0, hn0⟩) (idxA 0 0), ?_, ?_⟩
  · rw [parcelOf_coordOf]; exact hne
  · rw [ymVec, parcelOf_coordOf, locOf_coordOf, if_neg hne, if_pos rfl]
    change (if idxA (0 : Fin 3) (0 : Fin 8) = idxA 0 0 then -lam else 0) ≠ 0
    rw [if_pos rfl]
    simpa using hlam

end BookProof.YmOuterFockFL

end
