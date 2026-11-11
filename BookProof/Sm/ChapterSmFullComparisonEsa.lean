import Mathlib
import BookProof.Sm.ChapterSmComparisonEsa
import BookProof.Sm.ChapterSmFullMatterHamiltonian
import BookProof.Toolbox.ChapterHermiteLadderOrder

/-!
# P3 — the Standard-Model comparison `N_SM` and its essential self-adjointness

Work order: `SM_ESA_COMPLETION_PLAN.md` §4 **P3**, "prove comparison ESA and its graph-core
transfer".  The comparison operator of §3 of the plan is

```text
N_SM = [2 h_B + Σ_active qᵣ² + Σ_(j : Fin 3)(p_xⱼ² + xⱼ²) + c] ⊗ I_internal,   c ≥ 1,
```

with kinetic subset the source's **43** coordinates: the 40 momentum-carrying field coordinates
of `SmMom` together with the three spatial coordinates `smX`.  The 120 jet coordinates carry no
spatial derivative; they appear only through the potential term (they are among the `Σ_r Φ_r²`,
which are degree-four polynomials in *all* 163 coordinates).

## What this module builds

1. **The kinetic subset** `smFullS = smS ∪ smXSet`: `smS` is the 40 momentum coordinates,
   `smXSet` the three spatial ones; they are disjoint (`Disjoint smS smXSet`), so
   **`card_smFullS : smFullS.card = 43`** — the plan's recount, proved from the coordinate
   labelling rather than quoted.  The jets are outside `smFullS` (`smFullS_disjoint_jet`), so no
   kinetic derivative is added in a jet coordinate.
2. **The comparison potential** `smFullPotPoly P c = Σ_r Φ_r² + Σ_m q_m² + Σ_(j : Fin 3) xⱼ² + c`,
   with `realCoeff_smFullPotPoly`, the pointwise form `polyW_smFullPotPoly` (a sum of squares
   plus `c`) and **`one_le_polyW_smFullPotPoly`** (`1 ≤ W` for `1 ≤ c`): positivity is the
   pointwise lower bound of sums of squares, not a spectral hypothesis.
3. **The operator** `smFullComparison P c := hamCoreS W smFullS` — the degenerate Schrödinger
   operator `−Δ_S + W` on the Gauss–polynomial core, which *is* the scalar comparison `N_SM` of
   the plan.
4. **The physical reading** `smFullComparisonPhys P c = 2 h_B + Σ_m q_m² + Σⱼ (πⱼ² + xⱼ²) + c`
   built from the source operators `smHamiltonian`, `smQL`, and the P2 core factors `smMom`,
   `smPos` at the spatial coordinates, and **`smFullComparisonPhys_eq`**: the two agree on the
   whole Gauss–polynomial core.  The identity is proved by evaluating both sides on `pgLp p` and
   matching the resulting polynomials (`kinPolyS` over the disjoint union, `momOp_momOp`,
   `sum_momOp_eq_kinPolyS`), not by defining one side to be the other.
5. **Symmetry, positivity, dense core and ESA.**  Symmetry is `hamCoreS_symmetricOn`; positivity
   is read off the physical form as a sum of the non-negative quadratic forms of `h_B`, of the
   harmonic `Σ q²`, of the squares `πⱼ²`, `xⱼ²` and of `c‖x‖²`; the core is dense by
   `polyGaussCore_dense`; and **`smFullComparison_esa`** is `hamCoreS_esa` at `c = 1` transported
   to arbitrary `c` by the bounded symmetric shift, exactly as `smFlN_esa` is.

## Honest boundary

The internal factor is not yet tensored in this module, and the Faris–Lavine `CoreData` package
(comparison + graph core + relative bound) is P4's: nothing here assumes the relative bound, nor
that `h_SM` is essentially self-adjoint.  The remaining P3 work is the tensor `N_SM ⊗ I_internal`
on `SmCoupledCore` and the graph-core data consumed by `BookProof.QgOuterFockCoreFL`; the scalar
comparison — its identification, symmetry, positivity, dense core and ESA — is complete here.
The comparison `N_SM` is never claimed to be the physical Hamiltonian: it adds the oscillator
coordinates `xⱼ` and the constant `c` and is used only as an operator controlling `h_SM`.
Nothing in this module freezes a gauge or Higgs background: the coupling data `P : SmParams` is a
parameter of every statement.
-/

namespace BookProof.SmFullComparisonEsa

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.DegSchrodinger BookProof.HermiteGraphApprox
open BookProof.SmOneParticle BookProof.SmHamiltonian BookProof.SmFarisLavine
open BookProof.FarisLavine
open BookProof.SmComparisonEsa BookProof.SmFullMatter BookProof.SmPhysicalData
open BookProof.YangMillsHermite BookProof.HermiteLadder BookProof.YangMillsFriedrichs

noncomputable section

/-! ## 1. The 43-coordinate kinetic subset -/

theorem smX_injective : Function.Injective smX := by
  intro a b h
  have := smIdx.injective h
  simpa using this

/-- The set of the three spatial coordinates `x₀, x₁, x₂` among the 163. -/
def smXSet : Finset (Fin 163) := Finset.image smX Finset.univ

theorem card_smXSet : smXSet.card = 3 := by
  rw [smXSet, Finset.card_image_of_injective _ smX_injective, Finset.card_univ, Fintype.card_fin]

theorem card_smS : smS.card = 40 := by
  rw [smS, Finset.card_image_of_injective _ smCoord_injective, Finset.card_univ,
    Fintype.card_fin]

/-- **The momentum coordinates and the spatial coordinates are disjoint.** -/
theorem smS_disjoint_smXSet : Disjoint smS smXSet := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [smS, Finset.mem_image] at hx
  rw [smXSet, Finset.mem_image] at hy
  obtain ⟨m, _, rfl⟩ := hx
  obtain ⟨i, _, hm⟩ := hy
  exact smMom_disjoint_spatial (smMomFin.symm m) i hm.symm

/-- **The kinetic subset of the comparison `N_SM`**: the 40 momentum-carrying field coordinates
together with the three spatial coordinates. -/
def smFullS : Finset (Fin 163) := smS ∪ smXSet

/-- **The recount of the comparison's kinetic subset: `40 + 3 = 43`.** -/
theorem card_smFullS : smFullS.card = 43 := by
  rw [smFullS, Finset.card_union_of_disjoint smS_disjoint_smXSet, card_smS, card_smXSet]

theorem mem_smFullS_of_mom {m : Fin 40} : smCoord m ∈ smFullS :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ m))

theorem mem_smFullS_of_spatial (i : Fin 3) : smX i ∈ smFullS :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

/-- **No jet coordinate is a kinetic coordinate**: the comparison adds no spatial derivative in a
jet direction. -/
theorem smFullS_disjoint_jet (j : SmJet) : smJetCoord j ∉ smFullS := by
  intro h
  rw [smFullS, Finset.mem_union, smS, smXSet, Finset.mem_image, Finset.mem_image] at h
  rcases h with ⟨m, _, hm⟩ | ⟨i, _, hi⟩
  · exact smMom_disjoint_jet (smMomFin.symm m) j (by simpa [smCoord] using hm)
  · exact spatial_disjoint_jet i j hi

/-! ## 2. The comparison potential -/

/-- **The potential of the comparison operator**: the source potential `Σ_r Φ_r² + Σ_m q_m²`
plus the oscillator squares of the three spatial coordinates plus the shift `c`. -/
def smFullPotPoly (P : SmParams) (c : ℝ) : MvPolynomial (Fin 163) ℂ :=
  smPotPoly P c + ∑ i : Fin 3, X (smX i) * X (smX i)

theorem realCoeff_smFullPotPoly (P : SmParams) (c : ℝ) : RealCoeff (smFullPotPoly P c) :=
  (realCoeff_smPotPoly P c).add (RealCoeff.sum fun i _ =>
    (realCoeff_X (smX i)).mul (realCoeff_X (smX i)))

/-- **The potential is a sum of squares plus `c`.** -/
theorem polyW_smFullPotPoly (P : SmParams) (c : ℝ) (x : Vd 163) :
    polyW (smFullPotPoly P c) x
      = (∑ r : Fin 49, (polyW (smPhi P r) x) ^ 2) + (∑ m : Fin 40, (x (smCoord m)) ^ 2)
        + (∑ i : Fin 3, (x (smX i)) ^ 2) + c := by
  set e : Fin 163 → ℂ := fun k => ((x k : ℝ) : ℂ) with he
  have hphi : ∀ r : Fin 49, MvPolynomial.eval e (smPhi P r)
      = ((polyW (smPhi P r) x : ℝ) : ℂ) :=
    fun r => (polyW_ofReal (realCoeff_smPhi P r) x).symm
  have key : MvPolynomial.eval e (smFullPotPoly P c)
      = ((∑ r : Fin 49, (polyW (smPhi P r) x) ^ 2 : ℝ) : ℂ)
        + ((∑ m : Fin 40, (x (smCoord m)) ^ 2 : ℝ) : ℂ)
        + ((c : ℝ) : ℂ) + ((∑ i : Fin 3, (x (smX i)) ^ 2 : ℝ) : ℂ) := by
    simp only [smFullPotPoly, smPotPoly, map_add, map_sum, map_mul, MvPolynomial.eval_C,
      smQPoly, MvPolynomial.eval_X, hphi, sq]
    push_cast
    ring
  rw [polyW, key]
  have hcast : ((∑ r : Fin 49, (polyW (smPhi P r) x) ^ 2 : ℝ) : ℂ)
        + ((∑ m : Fin 40, (x (smCoord m)) ^ 2 : ℝ) : ℂ)
        + ((c : ℝ) : ℂ) + ((∑ i : Fin 3, (x (smX i)) ^ 2 : ℝ) : ℂ)
      = (((∑ r : Fin 49, (polyW (smPhi P r) x) ^ 2)
          + (∑ m : Fin 40, (x (smCoord m)) ^ 2)
          + (∑ i : Fin 3, (x (smX i)) ^ 2) + c : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.ofReal_re]

/-- **The potential is bounded below by `c`.** -/
theorem one_le_polyW_smFullPotPoly (P : SmParams) {c : ℝ} (hc : 1 ≤ c) (x : Vd 163) :
    1 ≤ polyW (smFullPotPoly P c) x := by
  rw [polyW_smFullPotPoly]
  have h1 : (0 : ℝ) ≤ ∑ r : Fin 49, (polyW (smPhi P r) x) ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ ∑ m : Fin 40, (x (smCoord m)) ^ 2 := by positivity
  have h3 : (0 : ℝ) ≤ ∑ i : Fin 3, (x (smX i)) ^ 2 := by positivity
  linarith

/-! ## 3. The comparison operator -/

/-- **The comparison operator `N_SM` of the plan**: the degenerate Schrödinger operator
`−Δ_S + W` on the 43-coordinate kinetic subset of the Gauss–polynomial core. -/
def smFullComparison (P : SmParams) (c : ℝ) : (polyGaussCore (d := 163)) →ₗ[ℂ] L2d 163 :=
  hamCoreS (polyW (smFullPotPoly P c)) (continuous_polyW _) (expBounded_polyW _) smFullS

/-- The comparison evaluated on a Gauss–polynomial vector. -/
theorem smFullComparison_pgLp (P : SmParams) (c : ℝ) (p : MvPolynomial (Fin 163) ℂ) :
    smFullComparison P c ⟨pgLp p, pgLp_mem_core p⟩
      = pgLp (kinPolyS smFullS p + smFullPotPoly P c * p) := by
  rw [smFullComparison, hamCoreS_pgLp, hamPolyS, potLp_polyW (realCoeff_smFullPotPoly P c),
    pgLp_add']

/-! ## 4. The physical reading of the comparison operator -/

/-- Splitting the kinetic polynomial over a disjoint union of coordinate sets. -/
theorem kinPolyS_union {d : ℕ} {S T : Finset (Fin d)} (h : Disjoint S T)
    (p : MvPolynomial (Fin d) ℂ) : kinPolyS (S ∪ T) p = kinPolyS S p + kinPolyS T p := by
  simp only [kinPolyS, Finset.sum_union h, neg_add]

/-- The kinetic polynomial over the three spatial coordinates is the sum of the spatial
second derivatives. -/
theorem kinPolyS_smXSet (p : MvPolynomial (Fin 163) ℂ) :
    kinPolyS smXSet p = ∑ i : Fin 3, momOp (smX i) (momOp (smX i) p) := by
  rw [smXSet, kinPolyS, Finset.sum_image (fun a _ b _ h => smX_injective h),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => (momOp_momOp (smX i) p).symm

/-- The spatial momentum squared `πⱼ² = −∂ⱼ²` as an operator on the core. -/
def smSpatialMomentumSq (i : Fin 3) : (polyGaussCore (d := 163)) →ₗ[ℂ] L2d 163 :=
  (polyGaussCore (d := 163)).subtype.comp ((smMom (smX i)).comp (smMom (smX i)))

/-- The spatial oscillator square `xⱼ²` as an operator on the core. -/
def smSpatialPosSq (i : Fin 3) : (polyGaussCore (d := 163)) →ₗ[ℂ] L2d 163 :=
  (polyGaussCore (d := 163)).subtype.comp ((smPos (smX i)).comp (smPos (smX i)))

theorem smSpatialMomentumSq_pgLp (i : Fin 3) (p : MvPolynomial (Fin 163) ℂ) :
    smSpatialMomentumSq i ⟨pgLp p, pgLp_mem_core p⟩
      = pgLp (momOp (smX i) (momOp (smX i) p)) := by
  have h1 : smMom (smX i) ⟨pgLp p, pgLp_mem_core p⟩
      = ⟨pgLp (momOp (smX i) p), pgLp_mem_core _⟩ := by
    rw [show smMom (smX i) = (coreRepPoly 163).op (momOp (smX i)) from rfl, op_pgLp]
  rw [smSpatialMomentumSq, LinearMap.comp_apply, LinearMap.comp_apply, h1]
  rw [show smMom (smX i) = (coreRepPoly 163).op (momOp (smX i)) from rfl, op_pgLp]
  rfl

theorem smSpatialPosSq_pgLp (i : Fin 3) (p : MvPolynomial (Fin 163) ℂ) :
    smSpatialPosSq i ⟨pgLp p, pgLp_mem_core p⟩
      = pgLp (X (smX i) * (X (smX i) * p)) := by
  have h1 : smPos (smX i) ⟨pgLp p, pgLp_mem_core p⟩
      = ⟨pgLp (X (smX i) * p), pgLp_mem_core _⟩ := by
    rw [show smPos (smX i) = (coreRepPoly 163).op (mulOp (X (smX i))) from rfl, op_pgLp]
    exact Subtype.ext rfl
  rw [smSpatialPosSq, LinearMap.comp_apply, LinearMap.comp_apply, h1]
  rw [show smPos (smX i) = (coreRepPoly 163).op (mulOp (X (smX i))) from rfl, op_pgLp]
  rfl

/-- **The comparison operator in terms of the source operators**:
`N_SM = 2 h_B + Σ_m q_m² + Σⱼ (πⱼ² + xⱼ²) + c` on the Gauss–polynomial core. -/
def smFullComparisonPhys (P : SmParams) (c : ℝ) : (polyGaussCore (d := 163)) →ₗ[ℂ] L2d 163 :=
  (2 : ℂ) • smHamiltonian P + smQL + (∑ i : Fin 3, smSpatialMomentumSq i)
    + (∑ i : Fin 3, smSpatialPosSq i) + ((c : ℝ) : ℂ) • (polyGaussCore (d := 163)).subtype

/-- A finite sum of `pgLp`'s is the `pgLp` of the sum. -/
theorem sum_pgLp {n : ℕ} (f : Fin n → MvPolynomial (Fin 163) ℂ) :
    (∑ i : Fin n, pgLp (f i)) = pgLp (∑ i : Fin n, f i) := by
  rw [← HermiteProductCore.pgMap_apply, map_sum]
  rfl

/-- **The polynomial identity behind the comparison.** -/
theorem smFullPoly_identity (P : SmParams) (c : ℝ) (p : MvPolynomial (Fin 163) ℂ) :
    kinPolyS smFullS p + smFullPotPoly P c * p
      = (∑ m : Fin 40, momOp (smCoord m) (momOp (smCoord m) p))
        + (∑ r : Fin 49, smPhi P r * (smPhi P r * p)) + smQPoly * p
        + (∑ i : Fin 3, momOp (smX i) (momOp (smX i) p))
        + (∑ i : Fin 3, X (smX i) * (X (smX i) * p)) + C ((c : ℝ) : ℂ) * p := by
  rw [smFullS, kinPolyS_union smS_disjoint_smXSet, kinPolyS_smXSet,
    sum_momOp_eq_kinPolyS, smFullPotPoly, smPotPoly]
  simp only [add_mul, Finset.sum_mul, mul_assoc]
  ring

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core (40 + 3 momentum squares, 49 field
-- polynomials, 3 coordinate squares) exceed the default heartbeat budget, and unfolding
-- `smHamiltonian`/`weylOp` into the 89 summands exceeds the default recursion depth
/-- **The comparison is the physical combination of the source operators.** -/
theorem smFullComparisonPhys_eq (P : SmParams) (c : ℝ) :
    smFullComparison P c = smFullComparisonPhys P c := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨p, hp⟩ := x.2
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  subst hx
  have hpi : ∀ m : Fin 40,
      ((smPi m (smPi m ⟨pgLp p, pgLp_mem_core p⟩) : polyGaussCore (d := 163)) : L2d 163)
        = pgLp (momOp (smCoord m) (momOp (smCoord m) p)) := by
    intro m
    have h1 : smPi m ⟨pgLp p, pgLp_mem_core p⟩
        = ⟨pgLp (momOp (smCoord m) p), pgLp_mem_core _⟩ := by
      rw [show smPi m = (coreRepPoly 163).op (momOp (smCoord m)) from rfl, op_pgLp]
    rw [h1, show smPi m = (coreRepPoly 163).op (momOp (smCoord m)) from rfl, op_pgLp]
  have hfield : ∀ r : Fin 49,
      ((smField P r (smField P r ⟨pgLp p, pgLp_mem_core p⟩) : polyGaussCore (d := 163))
          : L2d 163)
        = pgLp (smPhi P r * (smPhi P r * p)) := by
    intro r
    have hop : smField P r = (coreRepPoly 163).op (mulOp (smPhi P r)) := rfl
    have h1 : smField P r ⟨pgLp p, pgLp_mem_core p⟩
        = ⟨pgLp (smPhi P r * p), pgLp_mem_core _⟩ := by
      rw [hop, op_pgLp]
      exact Subtype.ext rfl
    rw [h1, hop, op_pgLp]
    rfl
  have hH : smHamiltonian P ⟨pgLp p, pgLp_mem_core p⟩
      = ((1 / 2 : ℝ) : ℂ) • ((∑ m : Fin 40, pgLp (momOp (smCoord m) (momOp (smCoord m) p)))
          + ∑ r : Fin 49, pgLp (smPhi P r * (smPhi P r * p))) := by
    have hval := weylOp_apply (F := L2d 163) (D := polyGaussCore (d := 163)) smPi
      (smField P) ⟨pgLp p, pgLp_mem_core p⟩
    rw [show smHamiltonian P = weylOp smPi (smField P) from rfl, hval]
    have hs1 : (∑ m : Fin 40,
          ((smPi m (smPi m ⟨pgLp p, pgLp_mem_core p⟩ : polyGaussCore (d := 163))
            : L2d 163)))
        = ∑ m : Fin 40, pgLp (momOp (smCoord m) (momOp (smCoord m) p)) :=
      Finset.sum_congr rfl fun m _ => hpi m
    have hs2 : (∑ r : Fin 49,
          ((smField P r (smField P r ⟨pgLp p, pgLp_mem_core p⟩ : polyGaussCore (d := 163))
            : L2d 163)))
        = ∑ r : Fin 49, pgLp (smPhi P r * (smPhi P r * p)) :=
      Finset.sum_congr rfl fun r _ => hfield r
    rw [hs1, hs2]
  have hQ : smQL ⟨pgLp p, pgLp_mem_core p⟩ = pgLp (smQPoly * p) := by
    rw [smQL_apply, show smQOp = (coreRepPoly 163).op (mulOp smQPoly) from rfl, op_pgLp]
    rfl
  rw [smFullComparison_pgLp, smFullComparisonPhys]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, hH, hQ,
    smSpatialMomentumSq_pgLp, smSpatialPosSq_pgLp, Submodule.subtype_apply]
  rw [sum_pgLp, sum_pgLp, smul_smul]
  have hc : (2 : ℂ) * ((1 / 2 : ℝ) : ℂ) = 1 := by norm_num
  rw [hc, one_smul]
  have hc2 : pgLp (((c : ℝ) : ℂ) • p) = ((c : ℝ) : ℂ) • pgLp p := by
    rw [← HermiteProductCore.pgMap_apply, ← HermiteProductCore.pgMap_apply, map_smul]
  rw [← hc2, MvPolynomial.smul_eq_C_mul]
  rw [smFullPoly_identity]
  simp only [pgLp_add', sum_pgLp]

/-! ## 5. Symmetry, positivity, dense core and essential self-adjointness -/

/-- The quadratic form is additive in the operator. -/
theorem quadForm_add {D : Submodule ℂ (L2d 163)} (S T : D →ₗ[ℂ] L2d 163) (x : D) :
    quadForm (S + T) x = quadForm S x + quadForm T x := by
  simp only [quadForm, LinearMap.add_apply, inner_add_right, Complex.add_re]

/-- The quadratic form scales by a real factor. -/
theorem quadForm_ofReal_smul {D : Submodule ℂ (L2d 163)} (a : ℝ) (T : D →ₗ[ℂ] L2d 163)
    (x : D) : quadForm (((a : ℂ) • T)) x = a * quadForm T x := by
  simp only [quadForm, LinearMap.smul_apply, inner_smul_right, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The quadratic form of a finite sum of operators is the sum of the quadratic forms. -/
theorem quadForm_sum {D : Submodule ℂ (L2d 163)} {n : ℕ}
    (T : Fin n → D →ₗ[ℂ] L2d 163) (x : D) :
    quadForm (∑ i, T i) x = ∑ i, quadForm (T i) x := by
  simp only [quadForm, LinearMap.sum_apply, inner_sum, Complex.re_sum]

set_option maxHeartbeats 1000000 in
-- the `L²` coercion of the Gauss–polynomial core twice through `T` is what needs the budget
/-- **The square of a symmetric core operator has quadratic form `‖T x‖²`.** -/
theorem quadForm_comp_self {T : (polyGaussCore (d := 163)) →ₗ[ℂ] (polyGaussCore (d := 163))}
    (hT : SymmetricOn (polyGaussCore (d := 163))
      ((polyGaussCore (d := 163)).subtype.comp T)) (x : polyGaussCore (d := 163)) :
    quadForm ((polyGaussCore (d := 163)).subtype.comp (T.comp T)) x
      = ‖((T x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 := by
  have h := inner_sq_eq_normSq (F := L2d 163) hT x
  rw [quadForm, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply, h,
    Complex.ofReal_re]

/-- **The comparison operator is symmetric on the Gauss–polynomial core.** -/
theorem smFullComparison_symmetricOn (P : SmParams) (c : ℝ) :
    SymmetricOn (polyGaussCore (d := 163)) (smFullComparison P c) :=
  hamCoreS_symmetricOn _ _ _ _

set_option maxHeartbeats 1000000 in
-- unfolding the physical combination and its five quadratic forms needs more `isDefEq` work than
-- the default heartbeat budget allows
/-- **The comparison operator is positive**: its quadratic form is a sum of squares — twice the
bosonic quadratic form, the harmonic squares, the three spatial `πⱼ²` and `xⱼ²`, and `c‖x‖²`. -/
theorem smFullComparison_quadForm_nonneg (P : SmParams) {c : ℝ} (hc : 0 ≤ c)
    (x : polyGaussCore (d := 163)) : 0 ≤ quadForm (smFullComparison P c) x := by
  rw [smFullComparisonPhys_eq]
  have hkin : ∀ i : Fin 3, 0 ≤ quadForm (smSpatialMomentumSq i) x := by
    intro i
    rw [show smSpatialMomentumSq i = (polyGaussCore (d := 163)).subtype.comp
      ((smMom (smX i)).comp (smMom (smX i))) from rfl,
      quadForm_comp_self (smMom_symmetricOn (smX i)) x]
    positivity
  have hpos : ∀ i : Fin 3, 0 ≤ quadForm (smSpatialPosSq i) x := by
    intro i
    rw [show smSpatialPosSq i = (polyGaussCore (d := 163)).subtype.comp
      ((smPos (smX i)).comp (smPos (smX i))) from rfl,
      quadForm_comp_self (smPos_symmetricOn (smX i)) x]
    positivity
  have h5 : (0 : ℝ) ≤ quadForm ((polyGaussCore (d := 163)).subtype) x := by
    have h : (inner ℂ ((x : polyGaussCore (d := 163)) : L2d 163)
        ((x : polyGaussCore (d := 163)) : L2d 163) : ℂ).re
        = ‖((x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp [pow_two, Complex.mul_re]
    rw [quadForm, Submodule.subtype_apply, h]
    positivity
  have h2c : (2 : ℂ) • smHamiltonian P = ((2 : ℝ) : ℂ) • smHamiltonian P := by norm_num
  rw [smFullComparisonPhys, quadForm_add, quadForm_add, quadForm_add, quadForm_add,
    quadForm_sum, quadForm_sum, h2c, quadForm_ofReal_smul (2 : ℝ), quadForm_ofReal_smul c]
  have h1 : 0 ≤ quadForm (smHamiltonian P) x := smHamiltonian_quadForm_nonneg P x
  have h2 : 0 ≤ quadForm smQL x := smQL_quadForm_nonneg x
  have h3 : (0 : ℝ) ≤ ∑ i : Fin 3, quadForm (smSpatialMomentumSq i) x :=
    Finset.sum_nonneg fun i _ => hkin i
  have h4 : (0 : ℝ) ≤ ∑ i : Fin 3, quadForm (smSpatialPosSq i) x :=
    Finset.sum_nonneg fun i _ => hpos i
  have h6 : 0 ≤ c * quadForm ((polyGaussCore (d := 163)).subtype) x := mul_nonneg hc h5
  linarith

/-- **The Gauss–polynomial core is dense**: the comparison's domain is dense in `L²(ℝ¹⁶³)`. -/
theorem polyGaussCore_dense' :
    Dense (((polyGaussCore (d := 163)) : Submodule ℂ (L2d 163)) : Set (L2d 163)) :=
  polyGaussCore_dense

/-- **The comparison operator `N_SM` is essentially self-adjoint on the Gauss–polynomial
core**, for every shift `c ≥ 1`. -/
theorem smFullComparison_esa_one_le (P : SmParams) {c : ℝ} (hc : 1 ≤ c) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 163)) (smFullComparison P c) :=
  hamCoreS_esa (smFullPotPoly P c) (realCoeff_smFullPotPoly P c)
    (one_le_polyW_smFullPotPoly P hc) smFullS

set_option maxHeartbeats 1000000 in
-- the shift identification rewrites two unfolded physical combinations of the 163-dimensional core
/-- **The comparison operator is essentially self-adjoint for every shift.**  Changing the
constant is a bounded symmetric perturbation, exactly as for `smFlN`. -/
theorem smFullComparison_esa (P : SmParams) (c : ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 163)) (smFullComparison P c) := by
  have hbase := smFullComparison_esa_one_le P (c := 1) le_rfl
  have hsym := smFullComparison_symmetricOn P 1
  have hkey := BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded
    (smFullComparison P 1) hsym hbase
    (((c - 1 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (L2d 163)) (fun u v => by
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        inner_smul_left, inner_smul_right, Complex.conj_ofReal])
  have hid : smFullComparison P 1
      + ((((c - 1 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (L2d 163)).toLinearMap
        ∘ₗ (polyGaussCore (d := 163)).subtype) = smFullComparison P c := by
    refine LinearMap.ext fun x => ?_
    rw [smFullComparisonPhys_eq P 1, smFullComparisonPhys_eq P c]
    simp only [smFullComparisonPhys, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    module
  rwa [hid] at hkey

end

end BookProof.SmFullComparisonEsa
