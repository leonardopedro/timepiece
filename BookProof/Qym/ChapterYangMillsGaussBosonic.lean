import BookProof.Qym.ChapterYangMillsGaussParity

/-!
# The bosonic part of the BRST charge: the ghost-smeared Gauss constraint

The BRST charge of the gauge-fixed theory is `Ω = Σ_a c†_a 𝒢_a + Ω_ghost`, where the sum runs
over the eight colour generators `𝒢_a` and `c†_a` are the ghost creation operators.  Its
**bosonic part** `Ω_bos = Σ_a c†_a 𝒢_a` acts on the field factor of each ghost sector through
a real linear combination `Σ_a z_a 𝒢_a` of the eight generators, with `z` the ghost
coefficients of that sector in the occupation-number basis (in which `c†_a` has real matrix
elements).

`BookProof/Qym/ChapterYangMillsGaussSkew`–`ChapterYangMillsGaussClosure` treat one generator
`𝒢_d` at a time.  This module treats the smeared combination: it packages

`Ω_bos z = Σ_a z_a 𝒢_a`,  `z : Fin 8 → ℝ`,

as a partially defined operator on `L²(ℝ⁹⁹)` and proves the whole chain for it — skewness on
the Gauss–polynomial core, formal adjointness of its negative, closability, closedness and
density of the closure's domain, and **skewness of the closure** (`A ≤ −A†`).

## Why the coefficients are real

Skewness is *not* preserved by complex scalars: `(z A)† = conj z · A† = −conj z · A`, which is
`−(z A)` only when `z` is real.  So a complex linear combination of the Gauss generators is not
skew, and it must not be claimed to be.  Real coefficients are the ones that occur for the
bosonic part of `Ω` in a ghost occupation-number sector.  Ghost *anticommutation*, the ghost
number grading and the nilpotency `Ω² = 0` are not modelled here, and skew-adjointness of
`Ω_bos z` inherits the missing reverse inclusion `dom A† ⊆ dom A` of
`ChapterYangMillsGaussSkewAdjoint`.

## Contents

* `smearedPoly`, `smearedPMap`, `negSmeared` — the ghost-smeared charge and its negative;
* `smearedPoly_apply`, `coreRep_op_smeared` — its action is the sum of the generators';
* `smearedPoly_skewOn_core` — it is skew on the core;
* `smearedPMap_isClosable`, `smearedPMap_closure_isClosed`,
  `smearedPMap_closure_domain_dense` — the operator chain;
* `closure_skew_of_graph_form` — the graph-form argument, stated once for an arbitrary
  closable operator;
* `smearedPMap_closure_skew`, `smearedPMap_closure_inner_re_zero`,
  `smearedPMap_closure_adjoint_apply`, `smearedPMap_closure_le_negAdjoint`;
* `smearedPMap_polyGaussCore_*` — the hypothesis-free field-space instances.
-/

open MvPolynomial

namespace BookProof.Qym.GaussBosonic

open BookProof.Qym.GaussCasimir BookProof.BrstYmCommute BookProof.BookBrstYangMills
open BookProof.YangMillsHermite BookProof.HermiteProductCore BookProof.Qym.GaussSkew
open BookProof.Qym.GaussClosure

noncomputable section

-- the `L²` coercions and the `Module.End` sums need more than the default budget
set_option maxHeartbeats 1000000

variable {D : Submodule ℂ (L2d 99)}

/-! ## The smeared charge on the polynomial algebra -/

/-- The **ghost-smeared Gauss charge**: the real linear combination `Σ_a z_a 𝒢_a` of the
eight Gauss generators. -/
def smearedPoly (G : GaugeAlgebra 8) (z : Fin 8 → ℝ) : Module.End ℂ YmPoly :=
  ∑ a : Fin 8, ((z a : ℝ) : ℂ) • ymGaussPoly G a

/-- The smeared charge is the sum of its generators on every polynomial. -/
theorem smearedPoly_apply (G : GaugeAlgebra 8) (z : Fin 8 → ℝ) (p : YmPoly) :
    smearedPoly G z p = ∑ a : Fin 8, ((z a : ℝ) : ℂ) • (ymGaussPoly G a p) := by
  simp [smearedPoly]

/-- The smeared operator, transported to the core, is the corresponding sum. -/
theorem coreRep_op_smeared (G : GaugeAlgebra 8) (z : Fin 8 → ℝ) (Φ : CoreRep 99 D) (x : D) :
    Φ.op (smearedPoly G z) x = ∑ a : Fin 8, ((z a : ℝ) : ℂ) • Φ.op (ymGaussPoly G a) x := by
  rw [CoreRep.op_apply, smearedPoly_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, CoreRep.op_apply]

/-! ## Skewness of the smeared charge on the core -/

/-- **Real linear combinations of skew operators are skew**: the ghost-smeared charge is skew
on the Gauss–polynomial core. -/
theorem smearedPoly_skewOn_core (G : GaugeAlgebra 8) (z : Fin 8 → ℝ) (Φ : CoreRep 99 D)
    (x y : D) :
    inner ℂ ((D.subtype.comp (Φ.op (smearedPoly G z))) x) ((y : D) : L2d 99)
      = -inner ℂ ((x : D) : L2d 99) ((D.subtype.comp (Φ.op (smearedPoly G z))) y) := by
  have hx : ((D.subtype.comp (Φ.op (smearedPoly G z))) x : L2d 99)
      = ∑ a : Fin 8, ((z a : ℝ) : ℂ) •
          ((D.subtype.comp (Φ.op (ymGaussPoly G a))) x) := by
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_sum, map_smul,
      coreRep_op_smeared]
  have hy : ((D.subtype.comp (Φ.op (smearedPoly G z))) y : L2d 99)
      = ∑ a : Fin 8, ((z a : ℝ) : ℂ) •
          ((D.subtype.comp (Φ.op (ymGaussPoly G a))) y) := by
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_sum, map_smul,
      coreRep_op_smeared]
  rw [hx, hy, sum_inner, inner_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inner_smul_left, inner_smul_right, ymGaussPoly_skewOn_core G a Φ x y, Complex.conj_ofReal]
  ring

/-! ## The operator on `L²(ℝ⁹⁹)` -/

/-- The **ghost-smeared Gauss charge** as a partially defined operator on `L²(ℝ⁹⁹)`. -/
def smearedPMap (G : GaugeAlgebra 8) (z : Fin 8 → ℝ) (Φ : CoreRep 99 D) :
    L2d 99 →ₗ.[ℂ] L2d 99 :=
  LinearPMap.mk D (D.subtype.comp (Φ.op (smearedPoly G z)))

@[simp] theorem smearedPMap_domain (G : GaugeAlgebra 8) (z : Fin 8 → ℝ)
    (Φ : CoreRep 99 D) : (smearedPMap G z Φ).domain = D := rfl

theorem smearedPMap_apply (G : GaugeAlgebra 8) (z : Fin 8 → ℝ) (Φ : CoreRep 99 D)
    (x : (smearedPMap G z Φ).domain) :
    smearedPMap G z Φ x = (D.subtype.comp (Φ.op (smearedPoly G z))) x := rfl

/-- The negative of the smeared charge, on the same domain. -/
def negSmeared (G : GaugeAlgebra 8) (z : Fin 8 → ℝ) (Φ : CoreRep 99 D) :
    L2d 99 →ₗ.[ℂ] L2d 99 :=
  LinearPMap.mk D (-(D.subtype.comp (Φ.op (smearedPoly G z))))

@[simp] theorem negSmeared_domain (G : GaugeAlgebra 8) (z : Fin 8 → ℝ) (Φ : CoreRep 99 D) :
    (negSmeared G z Φ).domain = D := rfl

/-- **Skewness as formal adjointness** for the smeared charge. -/
theorem smearedPMap_isFormalAdjoint_negSmeared (G : GaugeAlgebra 8) (z : Fin 8 → ℝ)
    (Φ : CoreRep 99 D) : (smearedPMap G z Φ).IsFormalAdjoint (negSmeared G z Φ) := by
  intro x y
  change inner ℂ ((D.subtype.comp (Φ.op (smearedPoly G z))) x) ((y : D) : L2d 99)
      = inner ℂ ((x : D) : L2d 99) (-(D.subtype.comp (Φ.op (smearedPoly G z))) y)
  rw [inner_neg_right]
  exact smearedPoly_skewOn_core G z Φ x y

/-- **The smeared charge is closable.** -/
theorem smearedPMap_isClosable (G : GaugeAlgebra 8) (z : Fin 8 → ℝ) (Φ : CoreRep 99 D)
    (hD : Dense (D : Set (L2d 99))) : (smearedPMap G z Φ).IsClosable := by
  have hdense : Dense ((negSmeared G z Φ).domain : Set (L2d 99)) := by
    rw [negSmeared_domain]
    exact hD
  have hclosed : (negSmeared G z Φ).adjoint.IsClosed := LinearPMap.adjoint_isClosed hdense
  have hle : smearedPMap G z Φ ≤ (negSmeared G z Φ).adjoint :=
    LinearPMap.IsFormalAdjoint.le_adjoint hdense
      (smearedPMap_isFormalAdjoint_negSmeared G z Φ).symm
  exact hclosed.isClosable.leIsClosable hle

/-- The closure of the smeared charge is closed. -/
theorem smearedPMap_closure_isClosed (G : GaugeAlgebra 8) (z : Fin 8 → ℝ)
    (Φ : CoreRep 99 D) (hD : Dense (D : Set (L2d 99))) :
    (smearedPMap G z Φ).closure.IsClosed :=
  (smearedPMap_isClosable G z Φ hD).closure_isClosed

/-- The closure's domain is dense. -/
theorem smearedPMap_closure_domain_dense (G : GaugeAlgebra 8) (z : Fin 8 → ℝ)
    (Φ : CoreRep 99 D) (hD : Dense (D : Set (L2d 99))) :
    Dense ((smearedPMap G z Φ).closure.domain : Set (L2d 99)) := by
  refine hD.mono ?_
  intro x hx
  exact (LinearPMap.le_closure (smearedPMap G z Φ)).1 (by rwa [smearedPMap_domain])

/-! ## The graph-form argument, generically -/

/-- **A closable operator whose graph is skew-symmetric has a skew closure.**  The alternating
form `ω (u, v) = ⟪u₂, v₁⟫ + ⟪u₁, v₂⟫` vanishes on the graph, is separately continuous, and so
vanishes on its closure, which is the graph of the closure.  This is the argument of
`gaussPMap_closure_graph_form_zero`, stated for an arbitrary operator. -/
theorem closure_skew_of_graph_form (A : L2d 99 →ₗ.[ℂ] L2d 99) (hcl : A.IsClosable)
    (hform : ∀ u ∈ A.graph, ∀ v ∈ A.graph, inner ℂ u.2 v.1 + inner ℂ u.1 v.2 = 0)
    (x y : A.closure.domain) :
    inner ℂ (A.closure x) (y : L2d 99) = -inner ℂ (x : L2d 99) (A.closure y) := by
  have hgraph := hcl.graph_closure_eq_closure_graph
  -- first argument in the closure, second in the graph
  have hfirst : ∀ u : L2d 99 × L2d 99, u ∈ A.closure.graph → ∀ v ∈ A.graph,
      inner ℂ u.2 v.1 + inner ℂ u.1 v.2 = 0 := by
    intro u hu v hv
    have hu' : u ∈ A.graph.topologicalClosure := by
      rw [hgraph]
      exact hu
    have hcont : Continuous fun w : L2d 99 × L2d 99 =>
        inner ℂ w.2 v.1 + inner ℂ w.1 v.2 :=
      (continuous_snd.inner continuous_const).add (continuous_fst.inner continuous_const)
    have hclosed : IsClosed {w : L2d 99 × L2d 99 | inner ℂ w.2 v.1 + inner ℂ w.1 v.2 = 0} :=
      isClosed_eq hcont continuous_const
    have hsub : (A.graph : Set (L2d 99 × L2d 99)) ⊆
        {w | inner ℂ w.2 v.1 + inner ℂ w.1 v.2 = 0} := by
      intro w hw
      exact hform w hw v hv
    have hcl : (A.graph.topologicalClosure : Set (L2d 99 × L2d 99)) ⊆
        {w | inner ℂ w.2 v.1 + inner ℂ w.1 v.2 = 0} := by
      rw [Submodule.topologicalClosure_coe]
      exact closure_minimal hsub hclosed
    exact hcl hu'
  -- both arguments in the closure
  have hu : ((x : L2d 99), A.closure x) ∈ A.closure.graph := LinearPMap.mem_graph _ x
  have hv : ((y : L2d 99), A.closure y) ∈ A.closure.graph := LinearPMap.mem_graph _ y
  have hv' : ((y : L2d 99), A.closure y) ∈ A.graph.topologicalClosure := by
    rw [hgraph]
    exact hv
  have hcont : Continuous fun w : L2d 99 × L2d 99 =>
      inner ℂ (A.closure x) w.1 + inner ℂ (x : L2d 99) w.2 :=
    (continuous_const.inner continuous_fst).add (continuous_const.inner continuous_snd)
  have hclosed : IsClosed {w : L2d 99 × L2d 99 |
      inner ℂ (A.closure x) w.1 + inner ℂ (x : L2d 99) w.2 = 0} :=
    isClosed_eq hcont continuous_const
  have hsub : (A.graph : Set (L2d 99 × L2d 99)) ⊆
      {w | inner ℂ (A.closure x) w.1 + inner ℂ (x : L2d 99) w.2 = 0} := by
    intro w hw
    exact hfirst _ hu w hw
  have hcl : (A.graph.topologicalClosure : Set (L2d 99 × L2d 99)) ⊆
      {w | inner ℂ (A.closure x) w.1 + inner ℂ (x : L2d 99) w.2 = 0} := by
    rw [Submodule.topologicalClosure_coe]
    exact closure_minimal hsub hclosed
  have h := hcl hv'
  rw [eq_neg_iff_add_eq_zero]
  exact h

/-! ## The closure of the smeared charge is skew -/

/-- The alternating form vanishes on the graph of the smeared charge. -/
theorem smearedPMap_graph_form_zero (G : GaugeAlgebra 8) (z : Fin 8 → ℝ) (Φ : CoreRep 99 D)
    {u v : L2d 99 × L2d 99} (hu : u ∈ (smearedPMap G z Φ).graph)
    (hv : v ∈ (smearedPMap G z Φ).graph) :
    inner ℂ u.2 v.1 + inner ℂ u.1 v.2 = 0 := by
  obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff _).1 hu
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hv
  have hu' : u = ((x : L2d 99), (D.subtype.comp (Φ.op (smearedPoly G z))) x) := by
    refine Prod.ext ?_ ?_
    · exact hx1.symm
    · rw [← hx2]
      exact smearedPMap_apply G z Φ x
  have hv' : v = ((y : L2d 99), (D.subtype.comp (Φ.op (smearedPoly G z))) y) := by
    refine Prod.ext ?_ ?_
    · exact hy1.symm
    · rw [← hy2]
      exact smearedPMap_apply G z Φ y
  subst hu'
  subst hv'
  have h := smearedPoly_skewOn_core G z Φ x y
  rw [h]
  ring

/-- **The closure of the ghost-smeared Gauss charge is skew.** -/
theorem smearedPMap_closure_skew (G : GaugeAlgebra 8) (z : Fin 8 → ℝ) (Φ : CoreRep 99 D)
    (hD : Dense (D : Set (L2d 99)))
    (x y : (smearedPMap G z Φ).closure.domain) :
    inner ℂ ((smearedPMap G z Φ).closure x) (y : L2d 99)
      = -inner ℂ (x : L2d 99) ((smearedPMap G z Φ).closure y) :=
  closure_skew_of_graph_form (smearedPMap G z Φ) (smearedPMap_isClosable G z Φ hD)
    (fun _ hu _ hv => smearedPMap_graph_form_zero G z Φ hu hv) x y

/-- The closed smeared charge has vanishing real expectation values. -/
theorem smearedPMap_closure_inner_re_zero (G : GaugeAlgebra 8) (z : Fin 8 → ℝ)
    (Φ : CoreRep 99 D) (hD : Dense (D : Set (L2d 99)))
    (x : (smearedPMap G z Φ).closure.domain) :
    (inner ℂ ((smearedPMap G z Φ).closure x) (x : L2d 99)).re = 0 := by
  have hskew := smearedPMap_closure_skew G z Φ hD x x
  have hconj : inner ℂ (x : L2d 99) ((smearedPMap G z Φ).closure x)
      = (starRingEnd ℂ)
        (inner ℂ ((smearedPMap G z Φ).closure x) (x : L2d 99)) :=
    (inner_conj_symm _ _).symm
  rw [hconj] at hskew
  have hre := congrArg Complex.re hskew
  simp only [Complex.neg_re, Complex.conj_re] at hre
  linarith

/-! ## The adjoint of the closure -/

/-- The closure's domain lies in the domain of its adjoint. -/
theorem smearedPMap_closure_adjoint_domain_ge (G : GaugeAlgebra 8) (z : Fin 8 → ℝ)
    (Φ : CoreRep 99 D) (hD : Dense (D : Set (L2d 99))) :
    (smearedPMap G z Φ).closure.domain ≤ (smearedPMap G z Φ).closure.adjoint.domain := by
  intro y hy
  refine LinearPMap.mem_adjoint_domain_of_exists (T := (smearedPMap G z Φ).closure)
    (y : L2d 99) ⟨-(smearedPMap G z Φ).closure ⟨y, hy⟩, ?_⟩
  intro x
  rw [inner_neg_left]
  have h := smearedPMap_closure_skew G z Φ hD ⟨y, hy⟩ x
  rw [h, neg_neg]

/-- On the domain of the closure the adjoint acts as the negative of the closure. -/
theorem smearedPMap_closure_adjoint_apply (G : GaugeAlgebra 8) (z : Fin 8 → ℝ)
    (Φ : CoreRep 99 D) (hD : Dense (D : Set (L2d 99)))
    (y : (smearedPMap G z Φ).closure.domain) :
    (smearedPMap G z Φ).closure.adjoint
        ⟨(y : L2d 99), smearedPMap_closure_adjoint_domain_ge G z Φ hD y.2⟩
      = -(smearedPMap G z Φ).closure y := by
  refine LinearPMap.adjoint_apply_eq (T := (smearedPMap G z Φ).closure)
    (smearedPMap_closure_domain_dense G z Φ hD) ?_ ?_
  intro x
  rw [inner_neg_left]
  have h := smearedPMap_closure_skew G z Φ hD y x
  rw [h, neg_neg]

/-- **The smeared charge lies below the negative of its adjoint**: `A ≤ −A†`, the half of
skew-adjointness that needs no new idea. -/
theorem smearedPMap_closure_le_negAdjoint (G : GaugeAlgebra 8) (z : Fin 8 → ℝ)
    (Φ : CoreRep 99 D) (hD : Dense (D : Set (L2d 99))) :
    (smearedPMap G z Φ).closure ≤ -((smearedPMap G z Φ).closure.adjoint) := by
  refine ⟨smearedPMap_closure_adjoint_domain_ge G z Φ hD, ?_⟩
  intro x y hxy
  rw [LinearPMap.neg_apply]
  have hstep : (smearedPMap G z Φ).closure.adjoint y
      = (smearedPMap G z Φ).closure.adjoint
          ⟨(x : L2d 99), smearedPMap_closure_adjoint_domain_ge G z Φ hD x.2⟩ := by
    congr 1
    exact Subtype.ext hxy.symm
  rw [hstep, smearedPMap_closure_adjoint_apply G z Φ hD]
  rw [neg_neg]

/-! ## The concrete field-space instance -/

theorem smearedPMap_polyGaussCore_isClosable (G : GaugeAlgebra 8) (z : Fin 8 → ℝ) :
    (smearedPMap G z (coreRepPoly 99)).IsClosable :=
  smearedPMap_isClosable G z (coreRepPoly 99) polyGaussCore_dense

theorem smearedPMap_polyGaussCore_closure_skew (G : GaugeAlgebra 8) (z : Fin 8 → ℝ)
    (x y : (smearedPMap G z (coreRepPoly 99)).closure.domain) :
    inner ℂ ((smearedPMap G z (coreRepPoly 99)).closure x) (y : L2d 99)
      = -inner ℂ (x : L2d 99) ((smearedPMap G z (coreRepPoly 99)).closure y) :=
  smearedPMap_closure_skew G z (coreRepPoly 99) polyGaussCore_dense x y

theorem smearedPMap_polyGaussCore_closure_le_negAdjoint (G : GaugeAlgebra 8)
    (z : Fin 8 → ℝ) :
    (smearedPMap G z (coreRepPoly 99)).closure
      ≤ -((smearedPMap G z (coreRepPoly 99)).closure.adjoint) :=
  smearedPMap_closure_le_negAdjoint G z (coreRepPoly 99) polyGaussCore_dense

end

end BookProof.Qym.GaussBosonic
