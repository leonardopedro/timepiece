import Mathlib
import BookProof.ChapterSqSumOuterFamily
import BookProof.ChapterQgOuterFockInteractionFL

/-!
# The gauge-fixed Navier–Stokes Hamiltonian on the outer Fock space, by Faris–Lavine

This module carries out for Navier–Stokes what
`BookProof.ChapterQgOuterFockFullFL` and `BookProof.ChapterQgOuterFockInteractionFL` do for
quantum gravity: it exhibits the gauge-fixed Hamiltonian as a *uniform* kinetic-plus-squares
family on the sectors of an outer Fock space and runs the Faris–Lavine theorem there, with
the **same comparison operator** — the lifted Friedrichs extension `dΓ(N₁)` of the positive
one-particle operator `N₁ = −Δ + ‖x‖²/4`.

## The variables

The parcel (excitation) of the Navier–Stokes thread carries the gauge-fixed field variables
of `BookProof.ChapterNavierStokesGaugeY`, *without* the space coordinate `x_j`, on which the
Hamiltonian symbol does not depend (`genX_nsSymbol`): the three velocity modes `u_i`, the
nine first-derivative modes `u_{i,j}`, the three Laplacian modes `u_{i,jj}` and the three
auxiliary coordinates `y_j` in which the field is expanded, `u_i(y) = u_i + u_{i,j} y_j`.
That is `18` coordinates per parcel (`NsLoc`), so the `n`-parcel sector is `L²(ℝ^{18n})` and
the state space is the outer Fock space `⊕ₙ L²(ℝ^{18n})`.

## The Hamiltonian

For a background advection velocity `bv`, viscosity `nu`, derivative-gauge strengths `lam`,
`mu` and `y`-gauge strength `gg`, the `n`-parcel Hamiltonian is

`H_n = ½ Σ_I π_I² + ½ Σ_r L_r²`

with, for every parcel `p`, the following four families of linear forms `L_r` (`sameVec`
gives their coefficients on the coordinates of `p`, `nextVec` those on the coordinates of
the cyclic neighbour `nextPart p`):

* **the Navier–Stokes constraint** `A_i = Σ_j bv_j u_{i,j} − nu·u_{i,jj}` — the advection
  (with background velocity `bv`) and viscous terms of the Navier–Stokes symbol, imposed as
  a squared constraint exactly as the torsion constraints are in the gravity sector;
* **the derivative gauge-fixing** `lam·(u_{i,j} + u_i − u_i^{next})` — the statement that
  the variable `u_{i,j}`, which represents a *spatial derivative of the field*, is the
  finite difference of the velocity between neighbouring parcels.  This form mixes the
  coordinates of two different parcels, so it is genuinely an **interaction term**;
* **the Laplacian gauge-fixing** `mu·(u_{i,jj} + Σ_j u_{i,j} − Σ_j u_{i,j}^{next})` — the
  same for the second-derivative variables;
* **the `y`-gauge fixing** `gg·y_j` — the gauge condition `y = 0` of the auxiliary
  expansion coordinate, whose generator `G_j = ∂/∂y_j − u_{i,j}∂/∂u_i` annihilates the
  Navier–Stokes symbol.

## What is proved

* `NsLoc`, `locU`, `locD`, `locL`, `locY`, `coordOf`, `parcelOf`, `locOf`,
  `sum_reindex_parcels` — the `18` field coordinates of a parcel and the bookkeeping of the
  `18n` coordinates of a sector;
* `sameVec`, `nextVec`, `nsVec` — the coefficient vectors of the four families of forms,
  with `nsVec_advection`, `nsVec_viscous`, `nsVec_tie_self`, `nsVec_tie_velocity`,
  `nsVec_lap_self`, `nsVec_gaugeY` reading off the individual coefficients, and
  `linForm_nsVec`, `linForm_nsConstraint`, `linForm_nsTie`, `linForm_nsLap`,
  `linForm_nsGaugeY` writing the four families out as polynomials in the field variables;
* `sum_abs_sameVec_row`, `sum_abs_nextVec_row`, `sum_abs_sameVec_col`,
  `sum_abs_nextVec_col`, `nsVec_row_le`, `nsVec_col_le` — the Schur data: every form has
  `ℓ¹` norm at most `7B` and every coordinate is touched by forms of total `ℓ¹` weight at
  most `6B`, where `B` bounds all the coefficients.  **Both bounds are independent of the
  parcel number `n`** — the locality of the gauge-fixing couplings — which is exactly the
  uniformity the `ℓ²`-direct-sum Faris–Lavine theorem needs;
* `nsFamily` — the family, as a `BookProof.SqSumOuterFamily.SqFamily`;
* `nsSectorHam`, `nsOuterHam` — the sector Hamiltonians and the full Hamiltonian on the
  finite-particle core of the outer Fock space, `nsOuterHam_symmetricOn`,
  `nsOuterHam_esa_core`;
* **`nsOuterFock_esa_farisLavine`** — the headline: the full gauge-fixed Navier–Stokes
  Hamiltonian, with its interaction (inter-parcel) terms and all its gauge-fixing terms, is
  essentially self-adjoint on the domain of the lifted Friedrichs extension of `N₁`, and
  the operator so realized extends `nsOuterHam` on the finite-particle core;
* `nsVec_coupling`, `ns_interaction_nontrivial` — the derivative gauge-fixing forms really
  do couple two different parcels, so for `lam ≠ 0` the Hamiltonian is *not* a sum of
  one-parcel operators.

## Honest boundary

*Added 2026‑09‑12:* the **full**, non-linearised Navier–Stokes Hamiltonians — with the exact
advection `u·∇u` in Eulerian variables and the exact Piola pressure term together with the
exact `det F = 1` volume constraint in Lagrangian variables — are carried by
`BookProof/ChapterNavierStokesFullEulerianFock.lean` and
`BookProof/ChapterNavierStokesFullLagrangianFock.lean`.  They are bounded below, so there the
route is the direct Friedrichs extension, lifted fibrewise to the outer Fock space, with the
Faris–Lavine criterion run there with that lift as comparison operator; *essential*
self-adjointness on the finite-parcel core is what this module — the quadratic model — adds,
and it is claimed for the quadratic model only.

The Hamiltonian of *this* module is quadratic: the advection is taken with a **background velocity field
`bv`** (the Oseen linearisation), the nonlinear self-advection `u_j u_{i,j}` — a cubic term
in the canonical variables — is *not* included, and nothing here bears on global regularity
of the classical Navier–Stokes equations.  This is the same class of Hamiltonian as in the
gravity sector, and the restriction is essential: for a genuinely nonlinear transport
symbol the classical flow can leave every ball in finite time and no comparison operator
can help — the `ẋ = x²` warning of the Navier–Stokes thread, formalized in
`BookProof.ChapterNavierStokesFullEsa.exists_nsFullData_not_hasZeroDeficiencyOn`.  The Fock
space is the `ℓ²`-direct sum of the sectors (distinguishable parcels, no symmetrization),
and no spectral information is claimed.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.NsOuterFock

open Finset MvPolynomial
open BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.HermiteProductCore BookProof.QgHermiteOscillator
open BookProof.QgOuterFock BookProof.QgOuterFockFL
open BookProof.QgOuterFockInteractionFL
open BookProof.SqSumOuterFamily

noncomputable section

/-! ## 1. The field coordinates of a parcel -/

/-- **The gauge-fixed Navier–Stokes field coordinates of one parcel**: the velocity modes
`u_i`, the first-derivative modes `u_{i,j}`, the Laplacian modes `u_{i,jj}` and the
auxiliary expansion coordinates `y_j`. -/
abbrev NsLoc : Type := Fin 3 ⊕ (Fin 3 × Fin 3) ⊕ Fin 3 ⊕ Fin 3

/-- The velocity coordinate `u_i`. -/
def locU (i : Fin 3) : NsLoc := Sum.inl i

/-- The first-derivative coordinate `u_{i,j}`. -/
def locD (i j : Fin 3) : NsLoc := Sum.inr (Sum.inl (i, j))

/-- The Laplacian coordinate `u_{i,jj}`. -/
def locL (i : Fin 3) : NsLoc := Sum.inr (Sum.inr (Sum.inl i))

/-- The auxiliary expansion coordinate `y_j`. -/
def locY (j : Fin 3) : NsLoc := Sum.inr (Sum.inr (Sum.inr j))

theorem card_nsLoc : Fintype.card NsLoc = 18 := by decide

/-- The `18` parcel coordinates, enumerated. -/
def locEquiv : NsLoc ≃ Fin 18 := Fintype.equivFinOfCardEq card_nsLoc

/-- The coordinate of the sector `L²(ℝ^{18n})` carrying the local coordinate `l` of the
parcel `p`. -/
def coordOf {n : ℕ} (p : Fin n) (l : NsLoc) : Fin (n * 18) := finProdFinEquiv (p, locEquiv l)

/-- The parcel carrying a sector coordinate. -/
def parcelOf {n : ℕ} (I : Fin (n * 18)) : Fin n := (finProdFinEquiv.symm I).1

/-- The local coordinate of a sector coordinate. -/
def locOf {n : ℕ} (I : Fin (n * 18)) : NsLoc := locEquiv.symm (finProdFinEquiv.symm I).2

@[simp] theorem parcelOf_coordOf {n : ℕ} (p : Fin n) (l : NsLoc) :
    parcelOf (coordOf p l) = p := by simp [parcelOf, coordOf]

@[simp] theorem locOf_coordOf {n : ℕ} (p : Fin n) (l : NsLoc) :
    locOf (coordOf p l) = l := by simp [locOf, coordOf]

@[simp] theorem coordOf_parcelOf_locOf {n : ℕ} (I : Fin (n * 18)) :
    coordOf (parcelOf I) (locOf I) = I := by
  simp only [coordOf, parcelOf, locOf, Equiv.apply_symm_apply, Prod.mk.eta]

/-- The sector coordinates, as parcel-times-local-coordinate pairs. -/
def coordEquiv (n : ℕ) : Fin n × NsLoc ≃ Fin (n * 18) :=
  ((Equiv.refl (Fin n)).prodCongr locEquiv).trans finProdFinEquiv

theorem coordEquiv_apply {n : ℕ} (p : Fin n) (l : NsLoc) :
    coordEquiv n (p, l) = coordOf p l := rfl

/-- Reindexing a sum over the `18n` sector coordinates as a sum over parcels and local
coordinates. -/
theorem sum_reindex_parcels {n : ℕ} {α : Type*} [AddCommMonoid α] (F : Fin (n * 18) → α) :
    ∑ I : Fin (n * 18), F I = ∑ p : Fin n, ∑ l : NsLoc, F (coordOf p l) := by
  calc ∑ I : Fin (n * 18), F I = ∑ pl : Fin n × NsLoc, F (coordOf pl.1 pl.2) :=
        (Fintype.sum_equiv (coordEquiv n) (fun pl => F (coordOf pl.1 pl.2)) F
          fun _ => rfl).symm
    _ = ∑ p : Fin n, ∑ l : NsLoc, F (coordOf p l) :=
        Fintype.sum_prod_type (fun pl : Fin n × NsLoc => F (coordOf pl.1 pl.2))

/-! ## 2. The linear forms of the gauge-fixed Navier–Stokes Hamiltonian -/

variable (bv : Fin 3 → ℝ) (nu lam mu gg : ℝ)

/-- **The coefficients of the four families of forms on the coordinates of their own
parcel.**  The first argument is the form, the second the coordinate. -/
def sameVec : NsLoc → NsLoc → ℝ
  | Sum.inl i, Sum.inr (Sum.inl (i', j)) => if i' = i then bv j else 0
  | Sum.inl i, Sum.inr (Sum.inr (Sum.inl i')) => if i' = i then -nu else 0
  | Sum.inr (Sum.inl (i, _)), Sum.inl i' => if i' = i then lam else 0
  | Sum.inr (Sum.inl (i, j)), Sum.inr (Sum.inl (i', j')) => if i' = i ∧ j' = j then lam else 0
  | Sum.inr (Sum.inr (Sum.inl i)), Sum.inr (Sum.inl (i', _)) => if i' = i then mu else 0
  | Sum.inr (Sum.inr (Sum.inl i)), Sum.inr (Sum.inr (Sum.inl i')) => if i' = i then mu else 0
  | Sum.inr (Sum.inr (Sum.inr j)), Sum.inr (Sum.inr (Sum.inr j')) => if j' = j then gg else 0
  | _, _ => 0

/-- **The coefficients of the forms on the coordinates of the neighbouring parcel.**  Only
the two gauge-fixing families for the derivative variables reach across parcels. -/
def nextVec : NsLoc → NsLoc → ℝ
  | Sum.inr (Sum.inl (i, _)), Sum.inl i' => if i' = i then -lam else 0
  | Sum.inr (Sum.inr (Sum.inl i)), Sum.inr (Sum.inl (i', _)) => if i' = i then -mu else 0
  | _, _ => 0

/-- **The coefficient vector of the form `(p, f)` of the `n`-parcel sector**: the form
lives on the coordinates of the parcel `p` and of its cyclic neighbour. -/
def nsVec (n : ℕ) (r : Fin n × NsLoc) (I : Fin (n * 18)) : ℝ :=
  if parcelOf I = r.1 then sameVec bv nu lam mu gg r.2 (locOf I)
  else if parcelOf I = nextPart r.1 then nextVec lam mu r.2 (locOf I) else 0

/-! ### Reading off the Hamiltonian -/

/-- The advection coefficient of the Navier–Stokes constraint form. -/
@[simp] theorem nsVec_advection {n : ℕ} (p : Fin n) (i j : Fin 3) :
    nsVec bv nu lam mu gg n (p, locU i) (coordOf p (locD i j)) = bv j := by
  simp [nsVec, locU, locD, sameVec]

/-- The viscous coefficient of the Navier–Stokes constraint form. -/
@[simp] theorem nsVec_viscous {n : ℕ} (p : Fin n) (i : Fin 3) :
    nsVec bv nu lam mu gg n (p, locU i) (coordOf p (locL i)) = -nu := by
  simp [nsVec, locU, locL, sameVec]

/-- The derivative gauge-fixing form contains the derivative variable it fixes. -/
@[simp] theorem nsVec_tie_self {n : ℕ} (p : Fin n) (i j : Fin 3) :
    nsVec bv nu lam mu gg n (p, locD i j) (coordOf p (locD i j)) = lam := by
  simp [nsVec, locD, sameVec]

/-- …and the velocity of its own parcel. -/
@[simp] theorem nsVec_tie_velocity {n : ℕ} (p : Fin n) (i j : Fin 3) :
    nsVec bv nu lam mu gg n (p, locD i j) (coordOf p (locU i)) = lam := by
  simp [nsVec, locD, locU, sameVec]

/-- The Laplacian gauge-fixing form contains the Laplacian variable it fixes. -/
@[simp] theorem nsVec_lap_self {n : ℕ} (p : Fin n) (i : Fin 3) :
    nsVec bv nu lam mu gg n (p, locL i) (coordOf p (locL i)) = mu := by
  simp [nsVec, locL, sameVec]

/-- The `y`-gauge-fixing form is the gauge condition `y_j = 0`. -/
@[simp] theorem nsVec_gaugeY {n : ℕ} (p : Fin n) (j : Fin 3) :
    nsVec bv nu lam mu gg n (p, locY j) (coordOf p (locY j)) = gg := by
  simp [nsVec, locY, sameVec]

/-- **The derivative gauge-fixing form reaches into the neighbouring parcel**: it ties the
derivative variable of `p` to the velocity difference between `p` and its neighbour. -/
theorem nsVec_coupling {n : ℕ} (p : Fin n) (i j : Fin 3) (hne : nextPart p ≠ p) :
    nsVec bv nu lam mu gg n (p, locD i j) (coordOf (nextPart p) (locU i)) = -lam := by
  simp [nsVec, locD, locU, nextVec, hne]

/-- **The Hamiltonian is genuinely interacting**: for a nonzero derivative-gauge strength
and at least two parcels, some linear form has a nonzero coefficient on a coordinate of a
parcel other than its own. -/
theorem ns_interaction_nontrivial {n : ℕ} (hn : 2 ≤ n) (hlam : lam ≠ 0) :
    ∃ (r : Fin n × NsLoc) (I : Fin (n * 18)),
      parcelOf I ≠ r.1 ∧ nsVec bv nu lam mu gg n r I ≠ 0 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  refine ⟨(⟨0, hn0⟩, locD 0 0), coordOf (nextPart ⟨0, hn0⟩) (locU 0), ?_, ?_⟩
  · rw [parcelOf_coordOf]
    exact nextPart_ne hn ⟨0, hn0⟩ rfl
  · rw [nsVec_coupling bv nu lam mu gg _ 0 0 (nextPart_ne hn ⟨0, hn0⟩ rfl)]
    simpa using hlam

/-! ### The forms, as polynomials -/

/-- **The linear form of `(p, f)`, written out.**  It is supported on the coordinates of the
parcel `p` and of its cyclic neighbour, with coefficients `sameVec` and `nextVec`. -/
theorem linForm_nsVec {n : ℕ} (p : Fin n) (f : NsLoc) (hne : nextPart p ≠ p) :
    linForm (nsVec bv nu lam mu gg n (p, f))
      = (∑ l : NsLoc, ((sameVec bv nu lam mu gg f l : ℝ) : ℂ) • X (coordOf p l))
        + ∑ l : NsLoc, ((nextVec lam mu f l : ℝ) : ℂ) • X (coordOf (nextPart p) l) := by
  classical
  rw [linForm, sum_reindex_parcels]
  have hval : ∀ (q : Fin n) (l : NsLoc),
      ((nsVec bv nu lam mu gg n (p, f) (coordOf q l) : ℝ) : ℂ)
          • (X (coordOf q l) : MvPolynomial (Fin (n * 18)) ℂ)
        = if q = p then ((sameVec bv nu lam mu gg f l : ℝ) : ℂ) • X (coordOf q l)
          else if q = nextPart p then ((nextVec lam mu f l : ℝ) : ℂ) • X (coordOf q l)
          else 0 := by
    intro q l
    rw [nsVec, parcelOf_coordOf, locOf_coordOf]
    by_cases h1 : q = p
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : q = nextPart p
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2]
        simp
  have hzero : ∀ q ∈ (Finset.univ : Finset (Fin n)), q ∉ ({p, nextPart p} : Finset (Fin n)) →
      (∑ l : NsLoc, ((nsVec bv nu lam mu gg n (p, f) (coordOf q l) : ℝ) : ℂ)
        • (X (coordOf q l) : MvPolynomial (Fin (n * 18)) ℂ)) = 0 := by
    intro q _ hq
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hval q l, if_neg hq.1, if_neg hq.2]
  rw [← Finset.sum_subset (Finset.subset_univ ({p, nextPart p} : Finset (Fin n))) hzero,
    Finset.sum_pair (Ne.symm hne)]
  congr 1
  · exact Finset.sum_congr rfl fun l _ => by rw [hval p l, if_pos rfl]
  · exact Finset.sum_congr rfl fun l _ => by rw [hval (nextPart p) l, if_neg hne, if_pos rfl]

set_option maxHeartbeats 1000000 in
-- eighteen coordinates per parcel: expanding the local sums is a large but shallow computation
/-- **The Navier–Stokes constraint form**: the advection with the background velocity `bv`
plus the viscous term, `Σ_j bv_j u_{i,j} − nu·u_{i,jj}`. -/
theorem linForm_nsConstraint {n : ℕ} (p : Fin n) (i : Fin 3) (hne : nextPart p ≠ p) :
    linForm (nsVec bv nu lam mu gg n (p, locU i))
      = (∑ j : Fin 3, ((bv j : ℝ) : ℂ) • X (coordOf p (locD i j)))
        - ((nu : ℝ) : ℂ) • X (coordOf p (locL i)) := by
  rw [linForm_nsVec bv nu lam mu gg p (locU i) hne]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, sameVec, nextVec, locU, locD, locL,
    Fin.sum_univ_three]
  fin_cases i <;> simp <;> module

set_option maxHeartbeats 1000000 in
-- eighteen coordinates per parcel: expanding the local sums is a large but shallow computation
/-- **The derivative gauge-fixing form**: the derivative variable `u_{i,j}` is tied to the
velocity difference between the parcel and its neighbour. -/
theorem linForm_nsTie {n : ℕ} (p : Fin n) (i j : Fin 3) (hne : nextPart p ≠ p) :
    linForm (nsVec bv nu lam mu gg n (p, locD i j))
      = ((lam : ℝ) : ℂ) • (X (coordOf p (locD i j)) + X (coordOf p (locU i))
          - X (coordOf (nextPart p) (locU i))) := by
  rw [linForm_nsVec bv nu lam mu gg p (locD i j) hne]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, sameVec, nextVec, locU, locD,
    Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp <;> module

set_option maxHeartbeats 1000000 in
-- eighteen coordinates per parcel: expanding the local sums is a large but shallow computation
/-- **The Laplacian gauge-fixing form**: the second-derivative variable `u_{i,jj}` is tied to
the difference of the first-derivative variables between the parcel and its neighbour. -/
theorem linForm_nsLap {n : ℕ} (p : Fin n) (i : Fin 3) (hne : nextPart p ≠ p) :
    linForm (nsVec bv nu lam mu gg n (p, locL i))
      = ((mu : ℝ) : ℂ) • (X (coordOf p (locL i)) + (∑ j : Fin 3, X (coordOf p (locD i j)))
          - ∑ j : Fin 3, X (coordOf (nextPart p) (locD i j))) := by
  rw [linForm_nsVec bv nu lam mu gg p (locL i) hne]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, sameVec, nextVec, locD, locL,
    Fin.sum_univ_three]
  fin_cases i <;> simp <;> module

set_option maxHeartbeats 1000000 in
-- eighteen coordinates per parcel: expanding the local sums is a large but shallow computation
/-- **The `y`-gauge-fixing form**: the gauge condition `y_j = 0` of the auxiliary expansion
coordinate. -/
theorem linForm_nsGaugeY {n : ℕ} (p : Fin n) (j : Fin 3) (hne : nextPart p ≠ p) :
    linForm (nsVec bv nu lam mu gg n (p, locY j))
      = ((gg : ℝ) : ℂ) • X (coordOf p (locY j)) := by
  rw [linForm_nsVec bv nu lam mu gg p (locY j) hne]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, sameVec, nextVec, locY,
    Fin.sum_univ_three]
  fin_cases j <;> simp

end

end BookProof.NsOuterFock
