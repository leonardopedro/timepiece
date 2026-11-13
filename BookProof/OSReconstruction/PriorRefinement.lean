import Mathlib
import BookProof.OSReconstruction.ObservablePrior

/-!
# B0, continued: conditioning, refinement consistency and infinite information

Plan: `cftproof.md`, the clause following B0's finite packet (landed in
`OSReconstruction.ObservablePrior`):

> Refinement must implement the manuscript's conditional-probability meaning of spatial points,
> rather than assuming point-evaluation vectors in `L²`.  Keep the continuous/infinite-information
> representation and its consistency estimates as explicit further deliverables.

This module carries out the two finite/infinite halves of that clause, with no `sorry` and no new
axiom.

## 1. Conditional probability at a spatial point

The manuscript's meaning of "the field at the point `x` is informed" is a *conditional*
statement, not the evaluation of a field at a vector of `L²`.  On a finite information space this
is:

* `SpatialPrior.massOn` / `SpatialPrior.jointOn` — the prior mass of an arbitrary sub-event and of
  a conjunction.  `massOn_inf` and `jointOn_inf` show that the B0 quantities of
  `ObservablePrior` are the special case `A = inf i`, so nothing below is a new notion.
* `SpatialPrior.cond` — the law conditioned on the event `A`, with `cond_sum_one` proving it is a
  probability law again.
* `SpatialPrior.cond_mass` — the conditional mass at the point `i`,
  `jointOn A (inf i) / massOn A`: the conditional probability that `x i` is informed, given `A`.
* `SpatialPrior.cond_expect` — Bayes' rule for an observable, `ω_A(f) = ω(A·f) / ω(A)`.
* `SpatialPrior.cond_massOn_self` — conditioning makes the conditioning event certain,
  `ω_A(A) = 1`, and `SpatialPrior.cond_expect_prop` — B0's normalization survives conditioning.
  So conditioning is an honest probability operation on the finite spatial points, which is what
the plan asks refinement to implement.

## 2. Refinement consistency

A refinement splits the information space: `Ω` becomes `Ω × Γ`, keeping the resolved supports on
the `Ω` factor.  `PriorRefinement` carries an *arbitrary joint* law on the product (the plan's "no
product prior" is preserved), and `PriorRefinement.coarse` is its marginal on `Ω`.

* `refinement_mass`, `refinement_joint` — marginalization leaves the one- and two-point masses
  unchanged.
* `refinement_corr` — hence the normalized two-point function is invariant under refinement: the
  correlation is a property of the coarse information, not of the auxiliary tag.
* `refinement_expect` — the same for every coarse observable: splitting the information space does
  not change any B0 number.  This is the finite consistency estimate the plan asks for.

## 3. Infinite information

`InfSpatialPrior n Ω` drops `[Fintype Ω]`: the information space `Ω` is arbitrary (hence possibly
infinite), the law is an `ℝ`-valued mass function, and the *resolved* information is carried by an
explicit finite support `s : Finset Ω`.  States outside `s` are information that the regulator has
not resolved rather than points of `L²`, so no point-evaluation vector is assumed.

* `InfSpatialPrior.expect_prop`, `corr_eq`, `corr_eq_one_iff` — the whole B0 dictionary
  (normalization of the number-density proposition, correlation `=` joint over product of
  marginals, correlation `1` `⇔` factorization) transfers verbatim.
* `InfSpatialPrior.ofFinite` with `ofFinite_corr` — the finite packet is the special case
  `s = univ`, so the two representations agree where both are defined.
* `correlatedInformationNat` — the acceptance-test prior *on the infinite information space `ℕ`*,
  with two distinct supports sharing their information: `corr = 2`.

## Boundary

* The refined information space is the product `Ω × Γ` with a finite `Γ`; a general coarsening
  map `Ω' → Ω` is not formalized (the fiberwise sums would encode the same statement).
* `InfSpatialPrior` has a *finite* resolved support inside an infinite information space.  The
  genuinely continuous law (a measure on a continuum of field values, with no atomic support) is
  not built; that is the continuum/infinite-information limit, still an input.
* No `L²` point-evaluation vector, no continuum field measure and no spatial translation is
  assumed anywhere here; B2/B3 remain conditional as recorded in `ObservablePrior`.
-/

namespace BookProof.OSReconstruction

noncomputable section

section FiniteInfo

/-! ## 1. Conditional probability at a spatial point -/

variable {n : ℕ} {Ω : Type*} [Fintype Ω]

/-- The prior mass of an arbitrary sub-event of the information space. -/
def SpatialPrior.massOn (P : SpatialPrior n Ω) (A : Ω → Bool) : ℝ :=
  ∑ ω, if A ω then P.μ ω else 0

/-- The prior mass of a conjunction of two sub-events. -/
def SpatialPrior.jointOn (P : SpatialPrior n Ω) (A B : Ω → Bool) : ℝ :=
  ∑ ω, if A ω ∧ B ω then P.μ ω else 0

/-- The B0 mass at a point is the mass of the event "the point is informed". -/
theorem SpatialPrior.massOn_inf (P : SpatialPrior n Ω) (i : Fin n) :
    P.massOn (P.inf i) = P.mass i := rfl

/-- The B0 joint mass is the joint mass of the two informing events. -/
theorem SpatialPrior.jointOn_inf (P : SpatialPrior n Ω) (i j : Fin n) :
    P.jointOn (P.inf i) (P.inf j) = P.joint i j := rfl

/-- A prior mass of an event is nonnegative. -/
theorem SpatialPrior.massOn_nonneg (P : SpatialPrior n Ω) (A : Ω → Bool) :
    0 ≤ P.massOn A := by
  refine Finset.sum_nonneg fun ω _ => ?_
  by_cases h : A ω = true <;> simp [h, P.nonneg ω]

/-- **The law conditioned on an event `A`.**  Conditioning is by the prior mass of `A`, so the
result is again a probability law (`SpatialPrior.cond_sum_one`); the resolved supports are
unchanged, since conditioning adds no spatial information. -/
def SpatialPrior.cond (P : SpatialPrior n Ω) (A : Ω → Bool) (hA : P.massOn A ≠ 0) :
    SpatialPrior n Ω where
  μ ω := if A ω then P.μ ω / P.massOn A else 0
  nonneg := by
    intro ω
    by_cases h : A ω = true
    · simp only [h, if_true]
      exact div_nonneg (P.nonneg ω) (P.massOn_nonneg A)
    · simp [h]
  sum_one := by
    have hfun : (fun ω => if A ω then P.μ ω / P.massOn A else 0)
        = fun ω => (if A ω then P.μ ω else 0) / P.massOn A := by
      funext ω
      by_cases h : A ω = true <;> simp [h]
    rw [hfun, ← Finset.sum_div]
    exact div_self hA
  inf := P.inf

/-- Conditioning leaves the resolved supports untouched. -/
theorem SpatialPrior.cond_inf (P : SpatialPrior n Ω) (A : Ω → Bool) (hA : P.massOn A ≠ 0) :
    (P.cond A hA).inf = P.inf := rfl

/-- **The conditioned mass of any event**: `ω_A(B) = ω(A ∧ B) / ω(A)`. -/
theorem SpatialPrior.cond_massOn (P : SpatialPrior n Ω) (A B : Ω → Bool)
    (hA : P.massOn A ≠ 0) :
    (P.cond A hA).massOn B = P.jointOn A B / P.massOn A := by
  have hfun : (fun ω => if B ω then (P.cond A hA).μ ω else 0)
      = fun ω => (if A ω ∧ B ω then P.μ ω else 0) / P.massOn A := by
    funext ω
    by_cases hA' : A ω = true <;> by_cases hB' : B ω = true <;>
      simp [SpatialPrior.cond, hA', hB']
  rw [SpatialPrior.massOn, hfun, ← Finset.sum_div]
  rfl

/-- **The conditional mass at a spatial point**: given `A`, the probability that the point `i` is
informed is the joint mass of `A` and the informing event over the mass of `A`.  This is the
finite form of the manuscript's conditional reading of a spatial point. -/
theorem SpatialPrior.cond_mass (P : SpatialPrior n Ω) (A : Ω → Bool) (hA : P.massOn A ≠ 0)
    (i : Fin n) :
    (P.cond A hA).mass i = P.jointOn A (P.inf i) / P.massOn A :=
  P.cond_massOn A (P.inf i) hA

/-- **Bayes' rule**: the expectation in the conditioned law of an observable is its `A`-weighted
expectation divided by the mass of `A`. -/
theorem SpatialPrior.cond_expect (P : SpatialPrior n Ω) (A : Ω → Bool) (hA : P.massOn A ≠ 0)
    (f : Ω → ℝ) :
    (P.cond A hA).expect f
      = (∑ ω, if A ω then P.μ ω * f ω else 0) / P.massOn A := by
  have hfun : (fun ω => (P.cond A hA).μ ω * f ω)
      = fun ω => (if A ω then P.μ ω * f ω else 0) / P.massOn A := by
    funext ω
    by_cases h : A ω = true <;> simp [SpatialPrior.cond, h, div_mul_eq_mul_div]
  rw [SpatialPrior.expect, hfun, ← Finset.sum_div]

/-- The mass of a conjunction against itself is the mass of the event. -/
theorem SpatialPrior.jointOn_self (P : SpatialPrior n Ω) (A : Ω → Bool) :
    P.jointOn A A = P.massOn A := by
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : A ω = true <;> simp [h]

/-- **Conditioning makes the conditioning event certain**: `ω_A(A) = 1`.  Together with
`SpatialPrior.cond_mass` (the conditional mass of an event) and `SpatialPrior.cond_expect`
(Bayes' rule) this is the conditional-probability content of a spatial point. -/
theorem SpatialPrior.cond_massOn_self (P : SpatialPrior n Ω) (A : Ω → Bool)
    (hA : P.massOn A ≠ 0) : (P.cond A hA).massOn A = 1 := by
  rw [P.cond_massOn A A hA, P.jointOn_self, div_self hA]

/-- **B0's normalization survives conditioning**: the number-density proposition is still
normalized in the conditioned law. -/
theorem SpatialPrior.cond_expect_prop (P : SpatialPrior n Ω) (A : Ω → Bool)
    (hA : P.massOn A ≠ 0) (i : Fin n) (h : 0 < (P.cond A hA).mass i) :
    (P.cond A hA).expect ((P.cond A hA).prop i) = 1 :=
  (P.cond A hA).expect_prop i h

/-! ## 2. Refinement consistency: splitting the information space changes nothing -/

variable {Γ : Type*} [Fintype Γ]

/-- **A refinement of the finite information space**: an arbitrary joint law on `Ω × Γ` whose
resolved spatial supports live on the coarse factor `Ω`.  The law is *not* assumed to factor, so
the refinement may correlate the auxiliary tag with the coarse information. -/
structure PriorRefinement (n : ℕ) (Ω Γ : Type*) [Fintype Ω] [Fintype Γ] where
  /-- The joint law on the refined information space. -/
  μ : Ω × Γ → ℝ
  /-- It is nonnegative. -/
  nonneg : ∀ p, 0 ≤ μ p
  /-- It is normalized. -/
  sum_one : ∑ p, μ p = 1
  /-- The resolved spatial supports, read off the coarse factor. -/
  inf : Fin n → Ω → Bool

/-- The refined prior on the full information space `Ω × Γ`. -/
def PriorRefinement.refined (R : PriorRefinement n Ω Γ) : SpatialPrior n (Ω × Γ) where
  μ := R.μ
  nonneg := R.nonneg
  sum_one := R.sum_one
  inf i p := R.inf i p.1

/-- The coarse prior: the marginal of the refined law on `Ω`. -/
def PriorRefinement.coarse (R : PriorRefinement n Ω Γ) : SpatialPrior n Ω where
  μ ω := ∑ g, R.μ (ω, g)
  nonneg ω := Finset.sum_nonneg fun g _ => R.nonneg (ω, g)
  sum_one := by
    rw [← Fintype.sum_prod_type (f := R.μ)]
    exact R.sum_one
  inf := R.inf

/-- **Marginalization preserves the one-point mass.** -/
theorem PriorRefinement.mass_refined_eq_coarse (R : PriorRefinement n Ω Γ) (i : Fin n) :
    R.refined.mass i = R.coarse.mass i := by
  simp only [PriorRefinement.refined, PriorRefinement.coarse, SpatialPrior.mass]
  rw [Fintype.sum_prod_type (f := fun p : Ω × Γ => if R.inf i p.1 then R.μ p else 0)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : R.inf i ω = true <;> simp [h]

/-- **Marginalization preserves the joint mass at two points.** -/
theorem PriorRefinement.joint_refined_eq_coarse (R : PriorRefinement n Ω Γ) (i j : Fin n) :
    R.refined.joint i j = R.coarse.joint i j := by
  simp only [PriorRefinement.refined, PriorRefinement.coarse, SpatialPrior.joint]
  rw [Fintype.sum_prod_type
      (f := fun p : Ω × Γ => if R.inf i p.1 ∧ R.inf j p.1 then R.μ p else 0)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : R.inf i ω = true <;> by_cases h' : R.inf j ω = true <;> simp [h, h']

/-- **The normalized two-point function is invariant under refinement**: a correlation is a
property of the coarse information, not of the auxiliary tag with which it was refined. -/
theorem PriorRefinement.corr_refined_eq_coarse (R : PriorRefinement n Ω Γ) (i j : Fin n)
    (hi : 0 < R.coarse.mass i) (hj : 0 < R.coarse.mass j) :
    R.refined.corr i j = R.coarse.corr i j := by
  have hi' : 0 < R.refined.mass i := by rw [R.mass_refined_eq_coarse]; exact hi
  have hj' : 0 < R.refined.mass j := by rw [R.mass_refined_eq_coarse]; exact hj
  rw [SpatialPrior.corr_eq R.refined i j hi' hj', SpatialPrior.corr_eq R.coarse i j hi hj,
    R.mass_refined_eq_coarse, R.mass_refined_eq_coarse, R.joint_refined_eq_coarse]

/-- **Every coarse observable has the same expectation**: splitting the information space does not
change any B0 number.  This is the finite refinement consistency estimate. -/
theorem PriorRefinement.expect_refined_eq_coarse (R : PriorRefinement n Ω Γ) (f : Ω → ℝ) :
    R.refined.expect (fun p => f p.1) = R.coarse.expect f := by
  simp only [PriorRefinement.refined, PriorRefinement.coarse, SpatialPrior.expect]
  rw [Fintype.sum_prod_type (f := fun p : Ω × Γ => R.μ p * f p.1)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.sum_mul]

end FiniteInfo

/-! ## 3. Infinite information: the same dictionary without `[Fintype Ω]` -/

variable {n : ℕ} {Ω : Type*}

/-- **The spatial prior on an arbitrary (possibly infinite) information space.**  The law is an
`ℝ`-valued mass function whose *resolved* part is the finite support `s`; states outside `s` are
unresolved information, so no point-evaluation vector and no continuum field measure is assumed. -/
structure InfSpatialPrior (n : ℕ) (Ω : Type*) where
  /-- The resolved, finite support of the law. -/
  s : Finset Ω
  /-- The mass function. -/
  μ : Ω → ℝ
  /-- It is nonnegative. -/
  nonneg : ∀ ω, 0 ≤ μ ω
  /-- It is normalized on the resolved support. -/
  sum_one : ∑ ω ∈ s, μ ω = 1
  /-- Which resolved spatial supports are informed in each configuration. -/
  inf : Fin n → Ω → Bool

/-- Expectation in an infinite-information prior, over the resolved support. -/
def InfSpatialPrior.expect (P : InfSpatialPrior n Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω ∈ P.s, P.μ ω * f ω

/-- The mass of the event "the point `i` is informed". -/
def InfSpatialPrior.mass (P : InfSpatialPrior n Ω) (i : Fin n) : ℝ :=
  ∑ ω ∈ P.s, if P.inf i ω then P.μ ω else 0

/-- The mass of the event "the points `i` and `j` are both informed". -/
def InfSpatialPrior.joint (P : InfSpatialPrior n Ω) (i j : Fin n) : ℝ :=
  ∑ ω ∈ P.s, if P.inf i ω ∧ P.inf j ω then P.μ ω else 0

/-- The normalized number-density proposition at the point `i`. -/
def InfSpatialPrior.prop (P : InfSpatialPrior n Ω) (i : Fin n) : Ω → ℝ :=
  fun ω => if P.inf i ω then 1 / P.mass i else 0

/-- The two-point function of the normalized propositions. -/
def InfSpatialPrior.corr (P : InfSpatialPrior n Ω) (i j : Fin n) : ℝ :=
  P.expect fun ω => P.prop i ω * P.prop j ω

/-- Summing a constant against one point's indicator, over the resolved support. -/
theorem InfSpatialPrior.expect_mul_indicator (P : InfSpatialPrior n Ω) (i : Fin n) (c : ℝ) :
    ∑ ω ∈ P.s, P.μ ω * (if P.inf i ω then c else 0) = c * P.mass i := by
  rw [InfSpatialPrior.mass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : P.inf i ω = true <;> simp [h, mul_comm]

/-- Summing a constant against the joint indicator of two points. -/
theorem InfSpatialPrior.expect_mul_indicator_joint (P : InfSpatialPrior n Ω) (i j : Fin n)
    (c : ℝ) :
    ∑ ω ∈ P.s, P.μ ω * (if P.inf i ω ∧ P.inf j ω then c else 0) = c * P.joint i j := by
  rw [InfSpatialPrior.joint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : (P.inf i ω ∧ P.inf j ω) = true <;> simp [h, mul_comm]

/-- **The proposition is normalized on an infinite information space too.** -/
theorem InfSpatialPrior.expect_prop (P : InfSpatialPrior n Ω) (i : Fin n)
    (h : 0 < P.mass i) : P.expect (P.prop i) = 1 := by
  have hne : P.mass i ≠ 0 := ne_of_gt h
  have hsum := P.expect_mul_indicator i (1 / P.mass i)
  simp only [InfSpatialPrior.expect, InfSpatialPrior.prop]
  rw [hsum]
  field_simp

/-- **The correlation is joint information over the product of the marginals.** -/
theorem InfSpatialPrior.corr_eq (P : InfSpatialPrior n Ω) (i j : Fin n)
    (hi : 0 < P.mass i) (hj : 0 < P.mass j) :
    P.corr i j = P.joint i j / (P.mass i * P.mass j) := by
  have hnei : P.mass i ≠ 0 := ne_of_gt hi
  have hnej : P.mass j ≠ 0 := ne_of_gt hj
  have hfun : (fun ω => P.prop i ω * P.prop j ω)
      = fun ω => if P.inf i ω ∧ P.inf j ω then (1 / P.mass i) * (1 / P.mass j) else 0 := by
    funext ω
    by_cases hi' : P.inf i ω = true <;> by_cases hj' : P.inf j ω = true <;>
      simp [InfSpatialPrior.prop, hi', hj']
  rw [InfSpatialPrior.corr, hfun, InfSpatialPrior.expect, P.expect_mul_indicator_joint]
  field_simp

/-- **Correlation `1` exactly when the joint information factorizes** — the dictionary statement
of B0, now on an infinite information space. -/
theorem InfSpatialPrior.corr_eq_one_iff (P : InfSpatialPrior n Ω) (i j : Fin n)
    (hi : 0 < P.mass i) (hj : 0 < P.mass j) :
    P.corr i j = 1 ↔ P.joint i j = P.mass i * P.mass j := by
  have hne : P.mass i * P.mass j ≠ 0 := mul_ne_zero (ne_of_gt hi) (ne_of_gt hj)
  rw [P.corr_eq i j hi hj, div_eq_one_iff_eq hne]

/-- The finite prior of `ObservablePrior` as an infinite-information prior with support
`Finset.univ`. -/
def InfSpatialPrior.ofFinite [Fintype Ω] (P : SpatialPrior n Ω) : InfSpatialPrior n Ω where
  s := Finset.univ
  μ := P.μ
  nonneg := P.nonneg
  sum_one := P.sum_one
  inf := P.inf

/-- **The two representations agree where both are defined**: the finite packet is the special case
of the infinite-information packet with `s = univ`. -/
theorem InfSpatialPrior.ofFinite_corr [Fintype Ω] (P : SpatialPrior n Ω) (i j : Fin n) :
    (InfSpatialPrior.ofFinite P).corr i j = P.corr i j := rfl

/-- **The acceptance-test prior on the infinite information space `ℕ`**: two distinct resolved
supports (the states `0` and `1`) that share their information (both are informed at `0`), each
with prior mass `1/2`.  The information space itself is infinite. -/
def correlatedInformationNat : InfSpatialPrior 2 ℕ where
  s := {0, 1}
  μ _ := 1 / 2
  nonneg := by intro ω; norm_num
  sum_one := by
    rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
    norm_num
  inf _ ω := decide (ω = 0)

/-- The prior mass of each support in `correlatedInformationNat` is one half. -/
theorem correlatedInformationNat_mass (i : Fin 2) : correlatedInformationNat.mass i = 1 / 2 := by
  rw [InfSpatialPrior.mass, show correlatedInformationNat.s = ({0, 1} : Finset ℕ) from rfl,
    Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  simp [correlatedInformationNat]

/-- Both distinct supports are informed on the same configurations. -/
theorem correlatedInformationNat_inf (i j : Fin 2) :
    correlatedInformationNat.inf i = correlatedInformationNat.inf j := rfl

/-- The joint mass of the two supports. -/
theorem correlatedInformationNat_joint (i j : Fin 2) :
    correlatedInformationNat.joint i j = 1 / 2 := by
  rw [InfSpatialPrior.joint, show correlatedInformationNat.s = ({0, 1} : Finset ℕ) from rfl,
    Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  simp [correlatedInformationNat]

/-- **B0's acceptance test on an infinite information space**: the normalized two-point function of
two distinct supports that share their information is `2`, not `1`. -/
theorem correlatedInformationNat_corr : correlatedInformationNat.corr 0 1 = 2 := by
  have hm := correlatedInformationNat_mass 0
  have hm' := correlatedInformationNat_mass 1
  rw [InfSpatialPrior.corr_eq _ 0 1 (by rw [hm]; norm_num) (by rw [hm']; norm_num),
    correlatedInformationNat_joint, hm, hm']
  norm_num

/-- ... and it is different from the uncorrelated value. -/
theorem correlatedInformationNat_corr_ne_one : correlatedInformationNat.corr 0 1 ≠ 1 := by
  rw [correlatedInformationNat_corr]
  norm_num

end

end BookProof.OSReconstruction
