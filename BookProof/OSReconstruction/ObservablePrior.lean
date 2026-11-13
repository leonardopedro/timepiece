import Mathlib
import BookProof.OSReconstruction.HalfSpaceFreeState
import BookProof.OSReconstruction.Clustering
import BookProof.Toolbox.ChapterFockSecondQuantization

/-!
# B0 and B1 at a finite regulator: the observable / prior dictionary

Plan: `cftproof.md`, **B0** (observable and prior dictionary) and **B1** (state and time
agreement) at a finite regulator.  The plan's own "next local deliverable" reads:

> B0 for one concrete observable and B1 at a finite regulator, with an explicit unproved
> continuum estimate.

This module carries out exactly that, with no `sorry` and no new axiom.

## What B0 asks for, and what is built here

B0 has to fix, on one concrete model, the spatial prior and one observable on it, and then pass
the plan's *first acceptance test*: compute a **normalized proposition** and a **nontrivial
correlation** in the stated prior, retaining joint information at different points.

* `SpatialPrior n Ω` — the stated prior: a probability law `μ` on a finite information space `Ω`
  together with `n` resolved, distinct spatial supports `inf : Fin n → Ω → Bool` recording whether
  the point is informed in the configuration `ω`.  The law is an *arbitrary* joint law: nothing
  makes the points independent, which is what the plan insists on ("local occupation does not
  imply a product prior").
* `SpatialPrior.prop` — the **number-density proposition at the point `i`, normalized**: the
  indicator of "point `i` is informed" divided by its prior mass.  `SpatialPrior.expect_prop`
  proves `ω(prop i) = 1` for every prior with positive mass at `i`, i.e. the normalization
  requirement of the manuscript is met *by construction*, and consequently the one-point
  functions carry no information about the prior at all.
* `SpatialPrior.corr` — the two-point function of the propositions at two points.
  `SpatialPrior.corr_eq` proves `corr i j = joint i j / (mass i * mass j)`: the correlation is the
  ratio of the joint information at the two points to the product of the marginals.
  `SpatialPrior.corr_eq_one_iff` turns that into the dictionary statement: **the correlation is
  `1` exactly when the joint information factorizes**, and `SpatialPrior.corr_self` with
  `correlated_information_corr_ne_one` exhibits a prior in which two distinct supports share their
  information, so that the normalized two-point function is `1/mass ≠ 1`.  This is the plan's
  "nontrivial correlation … retaining joint information at different points".
* `emptyVacuum` — the empty outer vacuum.  It annihilates every number-preserving observable, so
  its value of both `prop` and `corr` is `0` for *every* prior
  (`emptyVacuum_cannot_distinguish`): testing only `Ω_out` tests emptiness, exactly as the plan
  says, and cannot validate or invalidate a prediction.

## The outer one-particle sector: `dΓ(O)` is `O`

The plan's second B0 check is that on the outer one-particle sector the second quantization acts
as the inner operator, so *products recover inner operator products on their common domain*.  The
corpus already proves the single-operator half,
`BookProof.FockSecondQuantization.dGamma_one_particle`; what is added here is the diagonal case
in the form needed for products
(`dGamma_diag_one_particle`) and its **multiplicativity**
(`dGamma_diag_mul_one_particle`): for diagonal one-particle operators `f`, `g` with columns
`diagCol f`, `diagCol g`, the composite `dΓ(f) ∘ dΓ(g)` on `e_k` is `dΓ(f · g)` on `e_k`.  So the
one-particle sector is a genuine representation of the inner algebra, not merely a set of vectors.

## B1 at the finite regulator

B1 asks for equality of the *separated smeared moments* of the Euclidean side with the nested
reference-state moments at ordered imaginary times.  The concrete regulator available in the corpus
is the finite-volume Gibbs state `gibbsHalfSpaceState V` of `OSReconstruction.HalfSpaceFreeState`,
whose two halves are independent draws from the same Gibbs law.  There:

* `gibbsFun_posTime_eq` — the one-point function of a half-space observable is its boundary
  average, `ω F = Σ_x w x · F (x, 0)`, because `𝔄₊` does not see the second half.
* **`gibbs_separated_moment_factorises`** — the separated two-point moment is the *product* of the
  one-point functions, `⟨F, G⟩_OS = ω F · ω G`.
* `gibbs_connected_corr_zero` — hence the connected two-point function vanishes identically at
  the regulator (for the regulator's own time translation, which is trivial), so **every** pair of
  half-space observables clusters at this finite volume.  This is the exact statement that the
  regulator carries no coupling in the Euclidean-time direction: the equality B1 asks for holds,
  but only because both sides are the empty correlation.
* **`B1ContinuumEstimate`** — the **explicit unproved continuum estimate**: the statement that
  after the continuum limit the connected two-point function of the chosen observable decays at
  rate `m > 0`.  It is a `def … : Prop`, not an axiom, and `b1ContinuumEstimate_of_clustering`
  proves it is exactly the specialization of the corpus's existing `SchwingerClustering` to one
  observable, so the estimate is the shape the clustering machinery
  (`osNorm_evol_le_of_clustering`, `genForm_gap_of_clustering`) consumes.  What is not supplied
  here — and must not be claimed — is the decay itself: Bałaban's infrared analysis.

## Boundary

* `SpatialPrior` is a *finite* information space with finitely many resolved supports; the
  continuous/infinite-information representation and its consistency estimates that B0 also lists
  are not built, and no point-evaluation vectors in `L²` are assumed.
* The propositions are number-density *indicators* normalized by their prior mass; the
  manuscript's product-of-number-densities form at distinct points is represented through the
  joint law `μ`, not through a product of independent factors — this is exactly the modelling
  choice the plan asks B0 to make explicit.
* The finite regulator's time translation is trivial (`regulatorTimeTranslation`), because the
  Gibbs state of `HalfSpaceFreeState` has no time direction: the two halves are simultaneous
  independent draws.  Consequently `gibbs_connected_corr_zero` is not a clustering theorem, and
  the rate `m` is not measured at the regulator.
* **B2/B3 remain conditional and are not touched here**: no unitary `U : Hphys → F` is built (the
  corpus's `OsFockBridge` states the conditions and proves their consequences), and no spatial
  translation, covariance or ground projection is transported.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity
open BookProof.FockSecondQuantization

noncomputable section

/-! ## 1. B0 — the finite spatial prior and its normalized propositions -/

variable {n : ℕ} {Ω : Type*} [Fintype Ω]

/-- **The stated spatial prior at a finite regulator.** A probability law `μ` on a finite
information space `Ω`, together with `n` resolved, distinct spatial supports
`inf : Fin n → Ω → Bool` recording whether the support is informed in the configuration `ω`.
The law is an arbitrary *joint* law — no independence of the supports is assumed. -/
structure SpatialPrior (n : ℕ) (Ω : Type*) [Fintype Ω] where
  /-- The prior law. -/
  μ : Ω → ℝ
  /-- It is nonnegative. -/
  nonneg : ∀ ω, 0 ≤ μ ω
  /-- It is normalized. -/
  sum_one : ∑ ω, μ ω = 1
  /-- Which resolved spatial supports are informed in each configuration. -/
  inf : Fin n → Ω → Bool

/-- Expectation in the prior. -/
def SpatialPrior.expect (P : SpatialPrior n Ω) (f : Ω → ℝ) : ℝ := ∑ ω, P.μ ω * f ω

/-- The prior mass of the set where the point `i` is informed. -/
def SpatialPrior.mass (P : SpatialPrior n Ω) (i : Fin n) : ℝ :=
  ∑ ω, if P.inf i ω then P.μ ω else 0

/-- The prior mass of the set where **both** points `i` and `j` are informed. -/
def SpatialPrior.joint (P : SpatialPrior n Ω) (i j : Fin n) : ℝ :=
  ∑ ω, if P.inf i ω ∧ P.inf j ω then P.μ ω else 0

/-- **The normalized number-density proposition at the point `i`.**  It is the indicator of
"`i` is informed", divided by its prior mass, so that its expectation is `1` for every prior with
positive mass at `i` (`SpatialPrior.expect_prop`). -/
def SpatialPrior.prop (P : SpatialPrior n Ω) (i : Fin n) : Ω → ℝ :=
  fun ω => if P.inf i ω then 1 / P.mass i else 0

/-- The two-point function of the normalized propositions at the points `i` and `j`. -/
def SpatialPrior.corr (P : SpatialPrior n Ω) (i j : Fin n) : ℝ :=
  P.expect fun ω => P.prop i ω * P.prop j ω

/-- Summing a constant against one point's indicator. -/
theorem SpatialPrior.sum_mul_indicator (P : SpatialPrior n Ω) (i : Fin n) (c : ℝ) :
    ∑ ω, P.μ ω * (if P.inf i ω then c else 0) = c * P.mass i := by
  rw [SpatialPrior.mass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : P.inf i ω = true <;> simp [h, mul_comm]

/-- Summing a constant against the joint indicator of two points. -/
theorem SpatialPrior.sum_mul_indicator_joint (P : SpatialPrior n Ω) (i j : Fin n) (c : ℝ) :
    ∑ ω, P.μ ω * (if P.inf i ω ∧ P.inf j ω then c else 0) = c * P.joint i j := by
  rw [SpatialPrior.joint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : (P.inf i ω ∧ P.inf j ω) = true <;> simp [h, mul_comm]

/-- **The proposition is normalized**: `ω (prop i) = 1` for every prior with positive mass at
`i`.  Since the normalization is by the prior mass itself, the one-point function carries no
information about the prior — only the correlations below do. -/
theorem SpatialPrior.expect_prop (P : SpatialPrior n Ω) (i : Fin n) (h : 0 < P.mass i) :
    P.expect (P.prop i) = 1 := by
  have hne : P.mass i ≠ 0 := ne_of_gt h
  have hsum := P.sum_mul_indicator i (1 / P.mass i)
  simp only [SpatialPrior.expect, SpatialPrior.prop]
  rw [hsum]
  field_simp

/-- **The correlation is joint information over the product of the marginals.** -/
theorem SpatialPrior.corr_eq (P : SpatialPrior n Ω) (i j : Fin n)
    (hi : 0 < P.mass i) (hj : 0 < P.mass j) :
    P.corr i j = P.joint i j / (P.mass i * P.mass j) := by
  have hnei : P.mass i ≠ 0 := ne_of_gt hi
  have hnej : P.mass j ≠ 0 := ne_of_gt hj
  have hfun : (fun ω => P.prop i ω * P.prop j ω)
      = fun ω => if P.inf i ω ∧ P.inf j ω then (1 / P.mass i) * (1 / P.mass j) else 0 := by
    funext ω
    by_cases hi' : P.inf i ω = true <;> by_cases hj' : P.inf j ω = true <;>
      simp [SpatialPrior.prop, hi', hj']
  rw [SpatialPrior.corr, hfun, SpatialPrior.expect, P.sum_mul_indicator_joint]
  field_simp

/-- **Joint information factorizes exactly when the correlation is `1`.**  This is the
dictionary statement B0 asks for: a correlation different from `1` *is* joint information at the
two points that the product prior does not have. -/
theorem SpatialPrior.corr_eq_one_iff (P : SpatialPrior n Ω) (i j : Fin n)
    (hi : 0 < P.mass i) (hj : 0 < P.mass j) :
    P.corr i j = 1 ↔ P.joint i j = P.mass i * P.mass j := by
  have hne : P.mass i * P.mass j ≠ 0 := mul_ne_zero (ne_of_gt hi) (ne_of_gt hj)
  rw [P.corr_eq i j hi hj, div_eq_one_iff_eq hne]

/-- **Two supports sharing their information.**  If `i` and `j` are informed on exactly the same
configurations, the normalized correlation is `1 / mass`, i.e. the joint information is *not*
the product of the marginals whenever the mass is below `1`. -/
theorem SpatialPrior.corr_of_inf_eq (P : SpatialPrior n Ω) (i j : Fin n)
    (hij : P.inf i = P.inf j) (h : 0 < P.mass i) :
    P.corr i j = 1 / P.mass i := by
  have hne : P.mass i ≠ 0 := ne_of_gt h
  have hmass : P.mass j = P.mass i := by
    rw [SpatialPrior.mass, SpatialPrior.mass, ← hij]
  have hfun : (fun ω => P.prop i ω * P.prop j ω)
      = fun ω => if P.inf i ω then (1 / P.mass i) * (1 / P.mass i) else 0 := by
    funext ω
    simp only [SpatialPrior.prop, hmass, ← hij]
    by_cases hω : P.inf i ω = true <;> simp [hω]
  rw [SpatialPrior.corr, hfun, SpatialPrior.expect, P.sum_mul_indicator]
  rw [mul_assoc, div_mul_cancel₀ _ hne, mul_one]

/-- **A prior with correlated supports.**  Two resolved spatial points whose informed sets
coincide: either both are informed or neither is, each with prior probability `1/2`. -/
def correlatedInformation : SpatialPrior 2 Bool where
  μ _ := 1 / 2
  nonneg := by intro ω; norm_num
  sum_one := by
    rw [Fintype.sum_bool]
    norm_num
  inf _ ω := ω

/-- The prior mass of each support in `correlatedInformation` is one half. -/
theorem correlatedInformation_mass (i : Fin 2) : correlatedInformation.mass i = 1 / 2 := by
  have hfun : (fun ω : Bool =>
        if correlatedInformation.inf i ω then correlatedInformation.μ ω else 0)
      = fun ω : Bool => if ω then (1 : ℝ) / 2 else 0 := by
    funext ω
    rfl
  rw [SpatialPrior.mass, hfun, Fintype.sum_bool]
  simp

/-- The two distinct supports share their information. -/
theorem correlatedInformation_inf (i : Fin 2) : correlatedInformation.inf i = id := rfl

/-- **B0's first acceptance test, nontrivial case**: the normalized two-point function at two
*distinct* supports of `correlatedInformation` is `2`, not `1`.  So the correlation does retain
joint information at different points, and the normalization has not washed it out. -/
theorem correlatedInformation_corr : correlatedInformation.corr 0 1 = 2 := by
  have h := SpatialPrior.corr_of_inf_eq correlatedInformation 0 1
    (by rw [correlatedInformation_inf, correlatedInformation_inf]) (by
      rw [correlatedInformation_mass]; norm_num)
  rw [h, correlatedInformation_mass]
  norm_num

/-- ... and it is different from the uncorrelated value. -/
theorem correlatedInformation_corr_ne_one : correlatedInformation.corr 0 1 ≠ 1 := by
  rw [correlatedInformation_corr]
  norm_num

/-! ## 2. The empty outer vacuum tests only emptiness -/

/-- **The empty outer vacuum** on the finite information space: the functional that annihilates
every number-preserving observable. -/
def emptyVacuum : (Ω → ℝ) → ℝ := fun _ => 0

/-- On the empty outer vacuum the normalized proposition reads `0`. -/
theorem emptyVacuum_prop (P : SpatialPrior n Ω) (i : Fin n) : emptyVacuum (P.prop i) = 0 := rfl

/-- On the empty outer vacuum the two-point function reads `0` as well. -/
theorem emptyVacuum_corr (P : SpatialPrior n Ω) (i j : Fin n) :
    emptyVacuum (fun ω => P.prop i ω * P.prop j ω) = 0 := rfl

/-- **Testing only `Ω_out` cannot distinguish any two priors**: the empty vacuum assigns the
same value to the proposition of `i` in every prior.  Its vanishing is therefore no constraint on
the physical construction, exactly the plan's remark. -/
theorem emptyVacuum_cannot_distinguish (P Q : SpatialPrior n Ω) (i : Fin n) :
    emptyVacuum (P.prop i) = emptyVacuum (Q.prop i) := rfl

/-! ## 3. B0 on the outer one-particle sector: `dΓ(O)` is `O`, and products are products -/

/-- The column of the diagonal one-particle operator with eigenvalues `f`. -/
def diagCol (f : ℕ → ℂ) (k : ℕ) : ℕ →₀ ℂ := Finsupp.single k (f k)

/-- **`dΓ(O)` acts as the inner `O` on the outer one-particle sector** (diagonal case).  This is
`BookProof.FockSecondQuantization.dGamma_one_particle` specialized to a diagonal column. -/
theorem dGamma_diag_one_particle (f : ℕ → ℂ) (k : ℕ) (hk : f k ≠ 0) :
    dGamma (diagCol f) (Finsupp.single (Finsupp.single k 1) 1)
      = f k • Finsupp.single (Finsupp.single k 1) 1 := by
  rw [BookProof.FockSecondQuantization.dGamma_one_particle]
  simp only [diagCol, Finsupp.support_single_ne_zero k hk, Finset.sum_singleton,
    Finsupp.single_eq_same]

/-- **Products recover inner operator products on the one-particle sector**:
`dΓ(f) (dΓ(g) e_k) = dΓ(f · g) e_k`.  Together with `dGamma_diag_one_particle` this says that
the one-particle sector carries the inner algebra, which is the check B0 asks for. -/
theorem dGamma_diag_mul_one_particle (f g : ℕ → ℂ) (k : ℕ) (hg : g k ≠ 0)
    (hfg : f k * g k ≠ 0) :
    dGamma (diagCol f) (dGamma (diagCol g) (Finsupp.single (Finsupp.single k 1) 1))
      = dGamma (diagCol (fun j => f j * g j)) (Finsupp.single (Finsupp.single k 1) 1) := by
  have hf : f k ≠ 0 := fun h => hfg (by rw [h, zero_mul])
  rw [dGamma_diag_one_particle g k hg, map_smul, dGamma_diag_one_particle f k hf,
    dGamma_diag_one_particle (fun j => f j * g j) k hfg, smul_smul]
  rw [mul_comm]

/-! ## 4. B1 at the finite regulator -/

/-- A constant weighted by the normalised Gibbs weights integrates to the constant. -/
theorem gibbsWeight_weighted_sum_const (V : GibbsVolume) (c : ℝ) :
    ∑ y ∈ V.support, gibbsWeight V y * c = c := by
  rw [← Finset.sum_mul, gibbsWeight_sum, one_mul]

/-- **The one-point function of a half-space observable is its boundary average**: `𝔄₊` does not
see the second half, so `ω F = Σ_x w x · F (x, 0)`. -/
theorem gibbsFun_posTime_eq (V : GibbsVolume) (F : PositiveTimeAlgebra) :
    gibbsFun V (F : Observable)
      = ∑ x ∈ V.support, gibbsWeight V x * (F : Observable) (configEquiv.symm (x, 0)) := by
  have hdep := (dependsOn_posTimeCoords_iff (F : Observable)).1 F.2
  simp only [gibbsFun]
  refine Finset.sum_congr rfl fun x _ => ?_
  calc ∑ y ∈ V.support,
        gibbsWeight V x * gibbsWeight V y * (F : Observable) (configEquiv.symm (x, y))
      = ∑ y ∈ V.support,
          gibbsWeight V x *
            (gibbsWeight V y * (F : Observable) (configEquiv.symm (x, 0))) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hdep x y 0]
        ring
    _ = gibbsWeight V x *
          ∑ y ∈ V.support,
            gibbsWeight V y * (F : Observable) (configEquiv.symm (x, 0)) := by
        rw [Finset.mul_sum]
    _ = gibbsWeight V x * (F : Observable) (configEquiv.symm (x, 0)) := by
        rw [gibbsWeight_weighted_sum_const]

/-- **B1 at the finite regulator: the separated smeared moment is the product of the one-point
functions.**  The two halves of the Gibbs state are independent draws, so every separated moment
factorizes. -/
theorem gibbs_separated_moment_factorises (V : GibbsVolume) (F G : PositiveTimeAlgebra) :
    hsBilin (gibbsHalfSpaceState V) F G
      = gibbsFun V (F : Observable) * gibbsFun V (G : Observable) := by
  have hdepF := (dependsOn_posTimeCoords_iff (F : Observable)).1 F.2
  have hdepG := (dependsOn_posTimeCoords_iff (G : Observable)).1 G.2
  have hterm : ∀ x y : HalfIdx → ℝ,
      gibbsWeight V x * gibbsWeight V y *
        ((thetaObs (F : Observable) * (G : Observable)) (configEquiv.symm (x, y)))
      = (gibbsWeight V y * (F : Observable) (configEquiv.symm (y, 0)))
          * (gibbsWeight V x * (G : Observable) (configEquiv.symm (x, 0))) := by
    intro x y
    simp only [Pi.mul_apply, thetaObs_apply, configEquiv_symm_fieldReflection,
      hdepF y x 0, hdepG x y 0]
    ring
  rw [hsBilin_apply]
  change gibbsFun V (thetaObs (F : Observable) * (G : Observable)) = _
  calc gibbsFun V (thetaObs (F : Observable) * (G : Observable))
      = ∑ x ∈ V.support, ∑ y ∈ V.support,
          (gibbsWeight V y * (F : Observable) (configEquiv.symm (y, 0)))
            * (gibbsWeight V x * (G : Observable) (configEquiv.symm (x, 0))) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hterm x y
    _ = ∑ x ∈ V.support,
          (∑ y ∈ V.support, gibbsWeight V y * (F : Observable) (configEquiv.symm (y, 0)))
            * (gibbsWeight V x * (G : Observable) (configEquiv.symm (x, 0))) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul]
    _ = (∑ y ∈ V.support, gibbsWeight V y * (F : Observable) (configEquiv.symm (y, 0)))
          * (∑ x ∈ V.support, gibbsWeight V x * (G : Observable) (configEquiv.symm (x, 0))) := by
        rw [Finset.mul_sum]
    _ = gibbsFun V (F : Observable) * gibbsFun V (G : Observable) := by
        rw [gibbsFun_posTime_eq V F, gibbsFun_posTime_eq V G]

/-- The regulator's time translation: the finite-volume Gibbs state of `HalfSpaceFreeState` has
no time direction (its two halves are simultaneous independent draws), so its transfer is the
identity. -/
def regulatorTimeTranslation : TimeTranslation where
  toFun _ := LinearMap.id
  map_zero := rfl
  map_add _ _ := by ext F; rfl

/-- **The connected two-point function vanishes identically at the finite regulator.**  Every
pair of half-space observables, at the regulator's (trivial) time separation, has zero connected
correlation: the equality B1 asks for holds because both sides are the empty correlation. -/
theorem gibbs_connected_corr_zero (V : GibbsVolume) (F G : PositiveTimeAlgebra) :
    connectedCorr (gibbsHalfSpaceState V).ω regulatorTimeTranslation
      (F : Observable) (G : Observable) 0 = 0 := by
  rw [connectedCorr, schwinger, timeTranslation_zero]
  rw [show osBilin (gibbsHalfSpaceState V).ω (F : Observable) (G : Observable)
      = hsBilin (gibbsHalfSpaceState V) F G from rfl,
    gibbs_separated_moment_factorises]
  simp only [show (gibbsHalfSpaceState V).ω.toFun = gibbsFun V from rfl]
  ring

/-- **The explicit unproved continuum estimate of B1.**  After the continuum limit the connected
two-point function of the chosen observable decays at rate `m > 0` with constant `C`.  This is a
`Prop`, not an axiom: nothing in the corpus derives it, and nothing here assumes it.  It is the
analytic input Bałaban's infrared analysis is supposed to supply. -/
def B1ContinuumEstimate (ω : LinearFunctional) (T : TimeTranslation) (F : Observable)
    (m C : ℝ) : Prop :=
  ∀ τ : ℝ, 0 ≤ τ → |connectedCorr ω T F F τ| ≤ C * Real.exp (-(m * τ)) * (osNorm ω F) ^ 2

/-- **The continuum estimate is exactly the clustering hypothesis at one observable**, so it is
the shape the corpus's clustering machinery consumes
(`osNorm_evol_le_of_clustering`, `genForm_gap_of_clustering`), and not a private notion. -/
theorem b1ContinuumEstimate_of_clustering {ω : LinearFunctional} {T : TimeTranslation}
    {m C : ℝ} (h : SchwingerClustering ω T m C) (F : Observable) :
    B1ContinuumEstimate ω T F m C := by
  intro τ hτ
  simpa [B1ContinuumEstimate, pow_two, mul_assoc] using h F F τ hτ

end

end BookProof.OSReconstruction
