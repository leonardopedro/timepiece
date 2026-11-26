import BookProof.Qym.ChapterYangMillsGaussSkewAdjoint
import BookProof.ChapterBrstReducedTransferUnbounded

/-!
# The parity symmetry of the Gauss charge: a concrete `DomPreserve` / `StrongCommute` pair

`BookProof/ChapterBrstReducedTransferUnbounded.lean` reduces the unbounded commutation of a
charge with an evolution to two hypotheses: `DomPreserve` (the evolution maps the charge's
domain into itself) and `StrongCommute` (it intertwines the charge there).  It leaves them
as hypotheses, because for the field-theoretic charge a *concrete* evolution was missing.

This module supplies one.  The field-space parity `x ↦ −x` is a measure-preserving
involution of `ℝ⁹⁹`, so `(parityU f) x = f (−x)` is a bounded operator — in fact a linear
isometry — on `L²(ℝ⁹⁹)`.  It preserves the Gauss–polynomial core `polyGaussCore`, and it
commutes with `𝒢_d` on that core, because the Gauss vector field `ymGaussVec G d` is *linear*
(hence odd: `v (−x) = −v (x)`), so the two sign flips — of the coordinate and of the
derivative — cancel:

`𝒢_d (f ∘ s) = (𝒢_d f) ∘ s` for `s x = −x`.

The commutation then extends from the core to the domain of the *closure* of `𝒢_d` by the
graph argument: a point of that domain is a limit of core points with their images, and both
`parityU` and `𝒢_d`-closedness pass the limit.

This is a bounded unitary symmetry, not the one-parameter group `e^{−it𝒢_d}` (which needs
`-i𝒢_d` to be self-adjoint, i.e. the domain inclusion left open in
`ChapterYangMillsGaussSkewAdjoint`).  As an instance of the abstract transfer chapter it is
non-vacuous: the two invariance theorems at the end are the concrete statements
"the physical (Gauss-closed) states and the exact states of `𝒢_d` are parity invariant".

## Contents

* `parityU` — the parity isometry on `L²(ℝ⁹⁹)`, with `parityU_pgLp` (`parityU (p·e^{−‖x‖²/4})
  = (p ∘ s)·e^{−‖x‖²/4}`) and `parityU_mem_core`;
* `parityPoly_ymGaussPoly` — `θ (𝒢_d p) = 𝒢_d (θ p)` for the polynomial sign flip `θ`;
* `gaussPMap_parity_commute` — the same on the core of `L²`;
* `gaussPMap_closure_parity_domPreserve` / `_strongCommute` — the two hypotheses, for the
  closure of `𝒢_d` and no hypothesis left;
* `gaussPMap_closure_physicalStates_parity_invariant`,
  `gaussPMap_closure_exactStates_parity_invariant` — the two sectors are invariant.
-/

open Filter MvPolynomial MeasureTheory Topology

namespace BookProof.Qym.GaussParity

open BookProof.Qym.GaussCasimir BookProof.BrstYmCommute BookProof.BookBrstYangMills
open BookProof.YangMillsHermite BookProof.HermiteProductCore BookProof.Qym.GaussSkew
open BookProof.Qym.GaussClosure BookProof.BrstUnbounded

noncomputable section

/-! ## The parity isometry on `L²(ℝ⁹⁹)` -/

/-- The field-space sign flip `x ↦ −x` on `ℝ⁹⁹`. -/
def negMap : Vd 99 → Vd 99 := fun x => -x

theorem measurable_negMap : Measurable negMap := measurable_neg

/-- The sign flip preserves Lebesgue measure. -/
theorem measurePreserving_negMap : MeasurePreserving negMap volume volume :=
  ⟨measurable_negMap, Measure.map_neg_eq_self volume⟩

/-- **Parity on `L²(ℝ⁹⁹)`**: `(parityU f) x = f (−x)`.  It is a linear isometry. -/
def parityU : L2d 99 →L[ℂ] L2d 99 :=
  (Lp.compMeasurePreservingₗᵢ ℂ negMap measurePreserving_negMap).toContinuousLinearMap

theorem parityU_apply (f : L2d 99) :
    parityU f = Lp.compMeasurePreserving negMap measurePreserving_negMap f := rfl

/-- Parity is an isometry. -/
theorem norm_parityU (f : L2d 99) : ‖parityU f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f measurePreserving_negMap

theorem parityU_coeFn (f : L2d 99) :
    ((parityU f : L2d 99) : Vd 99 → ℂ) =ᵐ[volume] (f : Vd 99 → ℂ) ∘ negMap :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_negMap

/-! ## The polynomial sign flip -/

/-- The sign flip on polynomials: `θ p = p(−X)`. -/
def parityAlg : MvPolynomial (Fin 99) ℂ →ₐ[ℂ] MvPolynomial (Fin 99) ℂ :=
  aeval (fun i => - X i)

/-- `parityAlg` applied to a variable. -/
@[simp] theorem parityAlg_X (i : Fin 99) : parityAlg (X i) = -X i := by
  simp [parityAlg]

/-- Evaluating the sign-flipped polynomial at `x` is evaluating the original at `−x`. -/
theorem eval_parityAlg (p : MvPolynomial (Fin 99) ℂ) (x : Vd 99) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (parityAlg p)
      = MvPolynomial.eval (fun i => -((x i : ℝ) : ℂ)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      rw [map_mul, parityAlg_X, map_mul, map_neg, mul_neg, hp]
      simp

/-- The Gaussian is even. -/
theorem gaussD_negMap (x : Vd 99) : gaussD (negMap x) = gaussD x := by
  simp [gaussD, negMap]

/-- **Parity acts on the Gauss–polynomial core by the polynomial sign flip.** -/
theorem parityU_pgLp (p : MvPolynomial (Fin 99) ℂ) :
    parityU (pgLp p) = pgLp (parityAlg p) := by
  refine Lp.ext ?_
  filter_upwards [parityU_coeFn (pgLp p),
    measurePreserving_negMap.quasiMeasurePreserving.ae (pgLp_coeFn p),
    pgLp_coeFn (parityAlg p)] with x h1 h2 h3
  rw [h1, Function.comp_apply, h2, h3, pgFun, pgFun, eval_parityAlg, gaussD_negMap]
  have hneg : (fun i => ((negMap x).ofLp i : ℂ)) = fun i => -((x.ofLp i : ℝ) : ℂ) := by
    funext i
    simp [negMap]
  rw [hneg]

/-- **Parity preserves the Gauss–polynomial core.** -/
theorem parityU_mem_core {x : L2d 99} (hx : x ∈ polyGaussCore (d := 99)) :
    parityU x ∈ polyGaussCore (d := 99) := by
  obtain ⟨p, rfl⟩ := hx
  exact ⟨parityAlg p, by simpa [pgMap_apply] using (parityU_pgLp p).symm⟩

/-! ## Parity commutes with the Gauss derivation on polynomials -/

/-- The sign flip intertwines the derivative with a sign: `θ (∂_i p) = −∂_i (θ p)`. -/
theorem parityAlg_pderiv (i : Fin 99) (p : MvPolynomial (Fin 99) ℂ) :
    parityAlg (pderiv i p) = -pderiv i (parityAlg p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      simp only [map_add, hp, hq]
      ring
  | mul_X p j hp =>
      have h1 : parityAlg (p * X j) = parityAlg p * -X j := by rw [map_mul, parityAlg_X]
      by_cases hij : i = j
      · subst hij
        rw [h1, pderiv_mul, pderiv_X, pderiv_mul, map_neg, pderiv_X]
        simp [hp]
        ring
      · rw [h1, pderiv_mul, pderiv_X, pderiv_mul, map_neg, pderiv_X]
        simp [hij, hp]

/-- One block of the Gauss vector field flips sign: it is a sum of linear monomials. -/
theorem parityAlg_sum_ite {ι : Type*} [Fintype ι] (m : Fin 99) (f : ι → Fin 99)
    (i : ι → Fin 8 → Fin 99) (c : ι → Fin 8 → ℂ) :
    parityAlg (∑ p : ι, if f p = m then (∑ g : Fin 8, c p g • X (i p g)) else 0)
      = -∑ p : ι, if f p = m then (∑ g : Fin 8, c p g • X (i p g)) else 0 := by
  rw [map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : f p = m
  · simp only [if_pos h]
    rw [map_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun g _ => by rw [map_smul, parityAlg_X, smul_neg]
  · simp only [if_neg h, map_zero, neg_zero]

/-- **The Gauss vector field is linear, hence odd**: `θ (v_m) = −v_m`. -/
theorem parityAlg_ymGaussVec (G : GaugeAlgebra 8) (d : Fin 8) (m : Fin 99) :
    parityAlg (ymGaussVec G d m) = -ymGaussVec G d m := by
  unfold ymGaussVec
  rw [map_add, neg_add]
  congr 1
  · exact parityAlg_sum_ite m (fun p : Fin 3 × Fin 8 => idxA p.1 p.2)
      (fun p g => idxA p.1 g) (fun p g => ((G.f p.2 g d : ℝ) : ℂ))
  · exact parityAlg_sum_ite m (fun p : Fin 3 × Fin 3 × Fin 8 => idxD p.1 p.2.1 p.2.2)
      (fun p g => idxD p.1 p.2.1 g) (fun p g => ((G.f p.2.2 g d : ℝ) : ℂ))

/-- **Parity commutes with the Gauss derivation on polynomials**: the two sign flips (on the
coordinate and on the derivative) cancel. -/
theorem parityAlg_ymGaussPoly (G : GaugeAlgebra 8) (d : Fin 8)
    (p : MvPolynomial (Fin 99) ℂ) :
    parityAlg (ymGaussPoly G d p) = ymGaussPoly G d (parityAlg p) := by
  have hL : ymGaussPoly G d p = ∑ i : Fin 99, ymGaussVec G d i * pderiv i p :=
    ymGaussDer_apply G d p
  have hR : ymGaussPoly G d (parityAlg p)
      = ∑ i : Fin 99, ymGaussVec G d i * pderiv i (parityAlg p) :=
    ymGaussDer_apply G d (parityAlg p)
  rw [hL, hR, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, parityAlg_pderiv, parityAlg_ymGaussVec]
  ring

/-! ## Parity commutes with `𝒢_d` on the core -/

/-- The core equivalence of `coreRepPoly` sends the sign-flipped polynomial to the parity of
the core element. -/
theorem coreRepPoly_equiv_parityAlg (p : MvPolynomial (Fin 99) ℂ) :
    (((coreRepPoly 99).equiv (parityAlg p) : polyGaussCore (d := 99)) : L2d 99)
      = parityU (pgLp p) := by
  rw [CoreRep.coe_equiv, parityU_pgLp]

set_option maxHeartbeats 1000000 in
-- the `L²` coercions in the core equivalence need more than the default budget
/-- **Parity commutes with the Gauss charge on the Gauss–polynomial core.** -/
theorem gaussPMap_polyGaussCore_parity_commute (G : GaugeAlgebra 8) (d : Fin 8)
    (x : polyGaussCore (d := 99)) :
    ∃ hx : parityU (x : L2d 99) ∈ polyGaussCore (d := 99),
      ((gaussPMap G d (coreRepPoly 99)) ⟨parityU (x : L2d 99), hx⟩ : L2d 99)
        = parityU ((gaussPMap G d (coreRepPoly 99)) x) := by
  have hx : parityU (x : L2d 99) ∈ polyGaussCore (d := 99) := parityU_mem_core x.2
  refine ⟨hx, ?_⟩
  have hsym : (coreRepPoly 99).equiv.symm ⟨parityU (x : L2d 99), hx⟩
      = parityAlg ((coreRepPoly 99).equiv.symm x) := by
    refine (coreRepPoly 99).equiv.injective ?_
    refine Subtype.ext ?_
    rw [LinearEquiv.apply_symm_apply, CoreRep.coe_equiv, ← parityU_pgLp]
    exact congrArg parityU (CoreRep.coe_symm (coreRepPoly 99) x)
  rw [gaussPMap_apply, gaussPMap_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, Submodule.subtype_apply]
  simp only [CoreRep.coe_op, hsym, ← parityAlg_ymGaussPoly, ← parityU_pgLp]

/-! ## Passage to the closure -/

set_option maxHeartbeats 1000000 in
-- the graph argument materializes both `L²` coercions repeatedly
/-- **Parity preserves the domain of the closure and commutes with it there.**  A point of
that domain is a limit of core points together with their images; `parityU` is continuous and
`𝒢_d` is closed, so both pass to the limit. -/
theorem gaussPMap_closure_parity (G : GaugeAlgebra 8) (d : Fin 8)
    (y : (gaussPMap G d (coreRepPoly 99)).closure.domain) :
    ∃ hy : parityU (y : L2d 99) ∈ (gaussPMap G d (coreRepPoly 99)).closure.domain,
      (((gaussPMap G d (coreRepPoly 99)).closure) ⟨parityU (y : L2d 99), hy⟩ : L2d 99)
        = parityU ((gaussPMap G d (coreRepPoly 99)).closure y) := by
  have hcl : (gaussPMap G d (coreRepPoly 99)).IsClosable :=
    gaussPMap_polyGaussCore_isClosable G d
  have hAcl : ((gaussPMap G d (coreRepPoly 99)).closure).IsClosed :=
    gaussPMap_closure_isClosed G d (coreRepPoly 99) polyGaussCore_dense
  have hmem : (((y : L2d 99)), ((gaussPMap G d (coreRepPoly 99)).closure y))
      ∈ (gaussPMap G d (coreRepPoly 99)).graph.topologicalClosure := by
    rw [hcl.graph_closure_eq_closure_graph]
    exact LinearPMap.mem_graph _ y
  obtain ⟨z, hz, hztend⟩ := mem_closure_iff_seq_limit.1 hmem
  choose x hx1 hx2 using fun n => (LinearPMap.mem_graph_iff _).1 (hz n)
  have hzt : ∀ n, z n = (((x n : L2d 99)), (gaussPMap G d (coreRepPoly 99)) (x n)) := by
    intro n
    exact Prod.ext (hx1 n).symm (hx2 n).symm
  have hz' : Tendsto (fun n => (((x n : L2d 99)),
      (gaussPMap G d (coreRepPoly 99)) (x n))) atTop
      (𝓝 ((y : L2d 99), ((gaussPMap G d (coreRepPoly 99)).closure y))) :=
    hztend.congr' (Filter.Eventually.of_forall fun n => hzt n)
  have hxT : Tendsto (fun n => (x n : L2d 99)) atTop (𝓝 (y : L2d 99)) := by
    have h := continuous_fst.tendsto
      (((y : L2d 99)), ((gaussPMap G d (coreRepPoly 99)).closure y))
    simpa using h.comp hz'
  have hAxT : Tendsto (fun n => (gaussPMap G d (coreRepPoly 99)) (x n)) atTop
      (𝓝 ((gaussPMap G d (coreRepPoly 99)).closure y)) := by
    have h := continuous_snd.tendsto
      (((y : L2d 99)), ((gaussPMap G d (coreRepPoly 99)).closure y))
    simpa using h.comp hz'
  choose hxc hxceq using fun n => gaussPMap_polyGaussCore_parity_commute G d (x n)
  -- the images under `parityU` converge
  have hPT : Tendsto (fun n => parityU (x n : L2d 99)) atTop (𝓝 (parityU (y : L2d 99))) :=
    parityU.continuous.continuousAt.tendsto.comp hxT
  have hPAT : Tendsto (fun n => (((gaussPMap G d (coreRepPoly 99))
      ⟨parityU (x n : L2d 99), hxc n⟩) : L2d 99)) atTop
      (𝓝 (parityU ((gaussPMap G d (coreRepPoly 99)).closure y))) := by
    have h : Tendsto (fun n => parityU ((gaussPMap G d (coreRepPoly 99)) (x n))) atTop
        (𝓝 (parityU ((gaussPMap G d (coreRepPoly 99)).closure y))) :=
      parityU.continuous.continuousAt.tendsto.comp hAxT
    exact h.congr' (Filter.Eventually.of_forall fun n => (hxceq n).symm)
  -- the graph pairs converge, and the graph is closed
  -- the core witnesses, seen in the domain of the closure
  let w : ℕ → (gaussPMap G d (coreRepPoly 99)).closure.domain := fun n =>
    Submodule.inclusion (LinearPMap.le_closure (gaussPMap G d (coreRepPoly 99))).1
      ⟨parityU (x n : L2d 99), hxc n⟩
  have hw : ∀ n, ((w n : L2d 99)) = parityU (x n : L2d 99) := fun _ => rfl
  have hwc : ∀ n, (gaussPMap G d (coreRepPoly 99)).closure (w n)
      = (gaussPMap G d (coreRepPoly 99)) ⟨parityU (x n : L2d 99), hxc n⟩ :=
    fun n => gaussPMap_closure_apply_core G d (coreRepPoly 99)
      ⟨parityU (x n : L2d 99), hxc n⟩
  have hpair : Tendsto (fun n => (((w n : L2d 99)),
      (gaussPMap G d (coreRepPoly 99)).closure (w n))) atTop
      (𝓝 ((parityU (y : L2d 99)),
        parityU ((gaussPMap G d (coreRepPoly 99)).closure y))) := by
    have h := hPT.prodMk hPAT
    rw [← nhds_prod_eq] at h
    refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
    exact Prod.ext (hw n).symm (hwc n).symm
  have hlim : ((parityU (y : L2d 99)),
      parityU ((gaussPMap G d (coreRepPoly 99)).closure y))
      ∈ (gaussPMap G d (coreRepPoly 99)).closure.graph :=
    hAcl.isSeqClosed (fun n => LinearPMap.mem_graph _ (w n)) hpair
  obtain ⟨w, hw1, hw2⟩ := (LinearPMap.mem_graph_iff _).1 hlim
  have hy : parityU (y : L2d 99) ∈ (gaussPMap G d (coreRepPoly 99)).closure.domain := by
    simpa [hw1] using w.2
  refine ⟨hy, ?_⟩
  have hweq : (⟨parityU (y : L2d 99), hy⟩ :
      (gaussPMap G d (coreRepPoly 99)).closure.domain) = w := Subtype.ext hw1.symm
  rw [hweq]
  exact hw2

/-! ## The two transfer hypotheses, and the invariance theorems -/

/-- **`DomPreserve` for parity and the Gauss closure**, with no hypothesis left. -/
theorem gaussPMap_closure_parity_domPreserve (G : GaugeAlgebra 8) (d : Fin 8) :
    BookProof.BrstReducedTransferUnbounded.DomPreserve
      (gaussPMap G d (coreRepPoly 99)).closure parityU :=
  fun y => (gaussPMap_closure_parity G d y).choose

/-- **`StrongCommute` for parity and the Gauss closure.**  This is the concrete instance of
`[H, Ω] = 0` that `ChapterBrstReducedTransferUnbounded` leaves as a hypothesis. -/
theorem gaussPMap_closure_parity_strongCommute (G : GaugeAlgebra 8) (d : Fin 8) :
    BookProof.BrstReducedTransferUnbounded.StrongCommute
      (gaussPMap G d (coreRepPoly 99)).closure parityU
      (gaussPMap_closure_parity_domPreserve G d) :=
  fun y => (gaussPMap_closure_parity G d y).choose_spec.symm

/-- **The Gauss-closed states of the field-space charge are parity invariant.** -/
theorem gaussPMap_closure_physicalStates_parity_invariant (G : GaugeAlgebra 8) (d : Fin 8)
    {x : L2d 99}
    (hx : x ∈ BookProof.BrstUnbounded.physicalStates
      (gaussPMap G d (coreRepPoly 99)).closure) :
    parityU x ∈ BookProof.BrstUnbounded.physicalStates
      (gaussPMap G d (coreRepPoly 99)).closure :=
  BookProof.BrstReducedTransferUnbounded.physicalStates_invariant
    (gaussPMap G d (coreRepPoly 99)).closure parityU
    (gaussPMap_closure_parity_strongCommute G d) hx

/-- **The exact states of the field-space charge are parity invariant.** -/
theorem gaussPMap_closure_exactStates_parity_invariant (G : GaugeAlgebra 8) (d : Fin 8)
    {x : L2d 99}
    (hx : x ∈ BookProof.BrstUnbounded.exactStates
      (gaussPMap G d (coreRepPoly 99)).closure) :
    parityU x ∈ BookProof.BrstUnbounded.exactStates
      (gaussPMap G d (coreRepPoly 99)).closure :=
  BookProof.BrstReducedTransferUnbounded.exactStates_invariant
    (gaussPMap G d (coreRepPoly 99)).closure parityU
    (gaussPMap_closure_parity_strongCommute G d) hx

end

end BookProof.Qym.GaussParity
