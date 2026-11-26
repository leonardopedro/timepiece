import BookProof.Qym.ChapterYangMillsGaussSkew

/-!
# The closure of the Gauss constraint

`BookProof/Qym/ChapterYangMillsGaussSkew.lean` proves that `𝒢_d` is skew on the dense
Gauss–polynomial core.  This module passes from the core to the operator: it packages
`𝒢_d` as a partially defined operator `gaussPMap` on `L²(ℝ⁹⁹)`, proves that operator
**closable**, and proves that its closure is **closed and skew**.

The route is the standard one:

* skewness makes `gaussPMap` a formal adjoint of its own negative, so it lies below the
  adjoint of `negGauss`, which is closed (`adjoint_isClosed`); a closed extension makes
  `gaussPMap` closable (`IsClosed.isClosable`, `IsClosable.leIsClosable`);
* for the closure, the alternating form `ω (u, v) = ⟪u.2, v.1⟫ + ⟪u.1, v.2⟫` vanishes on
  `graph 𝒢_d × graph 𝒢_d` by skewness, is separately continuous, and therefore vanishes
  on `closure (graph 𝒢_d) × closure (graph 𝒢_d) = graph (closure 𝒢_d)²`.

## The adjoint of the closure

Skewness read as an adjoint statement is `closure 𝒢_d ≤ −(closure 𝒢_d)†`: for every `y` in
the domain of the closure the functional `x ↦ ⟪y, 𝒢_d x⟫` is the continuous functional
`x ↦ ⟪−𝒢_d y, x⟫`, so `dom (closure 𝒢_d) ⊆ dom (closure 𝒢_d)†` with `A† y = −A y` there.
That is the "`A ⊆ −A†`" half of skew-adjointness, proved in
`gaussPMap_closure_le_negAdjoint`; the reverse inclusion `dom A† ⊆ dom A` is the missing
half.

## What is *not* here

* **Skew-adjointness of the closure.**  A skew operator `A` is skew-adjoint when in
  addition `dom A† = dom A`; only `A ≤ −A†` is proved, so no Stone theorem, no unitary
  group `e^{−it𝒢_d}`, and no statement that `i·𝒢_d` is *self*-adjoint is claimed.
* No closedness of `𝒢_d` itself: what is closed is its closure.
* The ghost sector and the quartic magnetic term are untouched; see the boundary notes of
  `ChapterYangMillsGaussSkew`.
-/

open MvPolynomial

namespace BookProof.Qym.GaussClosure

open BookProof.Qym.GaussCasimir BookProof.BrstYmCommute BookProof.BookBrstYangMills
open BookProof.YangMillsHermite BookProof.HermiteProductCore BookProof.Qym.GaussSkew

noncomputable section

variable {D : Submodule ℂ (L2d 99)}

/-! ## The operator on `L²(ℝ⁹⁹)` -/

/-- The Gauss constraint as a partially defined operator on `L²(ℝ⁹⁹)`: its domain is the
core `D` and its action is the transported polynomial operator `Φ.op (ymGaussPoly G d)`. -/
def gaussPMap (G : GaugeAlgebra 8) (d : Fin 8) (Φ : CoreRep 99 D) :
    L2d 99 →ₗ.[ℂ] L2d 99 :=
  LinearPMap.mk D (D.subtype.comp (Φ.op (ymGaussPoly G d)))

/-- The domain of `gaussPMap` is the core. -/
@[simp] theorem gaussPMap_domain (G : GaugeAlgebra 8) (d : Fin 8) (Φ : CoreRep 99 D) :
    (gaussPMap G d Φ).domain = D := rfl

/-- The action of `gaussPMap` on a core element. -/
theorem gaussPMap_apply (G : GaugeAlgebra 8) (d : Fin 8) (Φ : CoreRep 99 D)
    (x : (gaussPMap G d Φ).domain) :
    gaussPMap G d Φ x = (D.subtype.comp (Φ.op (ymGaussPoly G d))) x := rfl

/-- The same operator with the sign of its *value* flipped, on the same domain.  It is
`−𝒢_d` as an operator, written so that the domain equality is definitional: this is what
the adjoint criterion below consumes. -/
def negGauss (G : GaugeAlgebra 8) (d : Fin 8) (Φ : CoreRep 99 D) :
    L2d 99 →ₗ.[ℂ] L2d 99 :=
  LinearPMap.mk D (-(D.subtype.comp (Φ.op (ymGaussPoly G d))))

/-- The domain of the negated operator is the core. -/
@[simp] theorem negGauss_domain (G : GaugeAlgebra 8) (d : Fin 8) (Φ : CoreRep 99 D) :
    (negGauss G d Φ).domain = D := rfl

/-- The value of the negated operator. -/
theorem negGauss_apply (G : GaugeAlgebra 8) (d : Fin 8) (Φ : CoreRep 99 D)
    (x : (negGauss G d Φ).domain) :
    negGauss G d Φ x = -(D.subtype.comp (Φ.op (ymGaussPoly G d))) x := rfl

/-- **Skewness as a formal adjointness**: `𝒢_d` is a formal adjoint of `−𝒢_d`. -/
theorem gaussPMap_isFormalAdjoint_negGauss (G : GaugeAlgebra 8) (d : Fin 8)
    (Φ : CoreRep 99 D) : (gaussPMap G d Φ).IsFormalAdjoint (negGauss G d Φ) := by
  intro x y
  change inner ℂ ((D.subtype.comp (Φ.op (ymGaussPoly G d))) x) ((y : D) : L2d 99)
      = inner ℂ ((x : D) : L2d 99) (-(D.subtype.comp (Φ.op (ymGaussPoly G d))) y)
  rw [inner_neg_right]
  exact ymGaussPoly_skewOn_core G d Φ x y

/-! ## Closability -/

/-- `𝒢_d` is a densely defined skew operator, hence closable: it is dominated by the
adjoint of `−𝒢_d`, which is closed. -/
theorem gaussPMap_isClosable (G : GaugeAlgebra 8) (d : Fin 8) (Φ : CoreRep 99 D)
    (hD : Dense (D : Set (L2d 99))) : (gaussPMap G d Φ).IsClosable := by
  have hdense : Dense ((negGauss G d Φ).domain : Set (L2d 99)) := by
    rw [negGauss_domain]
    exact hD
  have hclosed : (negGauss G d Φ).adjoint.IsClosed := LinearPMap.adjoint_isClosed hdense
  have hle : gaussPMap G d Φ ≤ (negGauss G d Φ).adjoint :=
    LinearPMap.IsFormalAdjoint.le_adjoint hdense (gaussPMap_isFormalAdjoint_negGauss G d Φ).symm
  exact hclosed.isClosable.leIsClosable hle

/-- The closure of `𝒢_d` is closed. -/
theorem gaussPMap_closure_isClosed (G : GaugeAlgebra 8) (d : Fin 8) (Φ : CoreRep 99 D)
    (hD : Dense (D : Set (L2d 99))) : (gaussPMap G d Φ).closure.IsClosed :=
  (gaussPMap_isClosable G d Φ hD).closure_isClosed

/-- The closure contains the core in its domain, so its domain is dense. -/
theorem gaussPMap_closure_domain_dense (G : GaugeAlgebra 8) (d : Fin 8)
    (Φ : CoreRep 99 D) (hD : Dense (D : Set (L2d 99))) :
    Dense ((gaussPMap G d Φ).closure.domain : Set (L2d 99)) := by
  refine hD.mono ?_
  intro x hx
  exact (LinearPMap.le_closure (gaussPMap G d Φ)).1 (by rwa [gaussPMap_domain])

/-- On the core the closure acts as `𝒢_d` itself. -/
theorem gaussPMap_closure_apply_core (G : GaugeAlgebra 8) (d : Fin 8) (Φ : CoreRep 99 D)
    (x : D) :
    (gaussPMap G d Φ).closure
        (Submodule.inclusion (LinearPMap.le_closure (gaussPMap G d Φ)).1
          ⟨(x : L2d 99), by rw [gaussPMap_domain]; exact x.2⟩)
      = gaussPMap G d Φ ⟨(x : L2d 99), by rw [gaussPMap_domain]; exact x.2⟩ :=
  (LinearPMap.apply_comp_inclusion (LinearPMap.le_closure (gaussPMap G d Φ)) _).symm

/-! ## Skewness of the closure -/

/-- The alternating form `ω(u, v) = ⟪u₂, v₁⟫ + ⟪u₁, v₂⟫` vanishes on the graph of
`𝒢_d`: this is skewness read on pairs of graph elements. -/
theorem gaussPMap_graph_form_zero (G : GaugeAlgebra 8) (d : Fin 8) (Φ : CoreRep 99 D)
    {u v : L2d 99 × L2d 99} (hu : u ∈ (gaussPMap G d Φ).graph)
    (hv : v ∈ (gaussPMap G d Φ).graph) :
    inner ℂ u.2 v.1 + inner ℂ u.1 v.2 = 0 := by
  obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff _).1 hu
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hv
  have hu' : u = ((x : L2d 99), (D.subtype.comp (Φ.op (ymGaussPoly G d))) x) := by
    refine Prod.ext ?_ ?_
    · exact hx1.symm
    · rw [← hx2]
      exact gaussPMap_apply G d Φ x
  have hv' : v = ((y : L2d 99), (D.subtype.comp (Φ.op (ymGaussPoly G d))) y) := by
    refine Prod.ext ?_ ?_
    · exact hy1.symm
    · rw [← hy2]
      exact gaussPMap_apply G d Φ y
  subst hu'
  subst hv'
  have h := ymGaussPoly_skewOn_core G d Φ x y
  rw [h]
  ring

/-- The alternating form vanishes on the graph of the closure as well: it is separately
continuous and vanishes on a dense subset of each argument. -/
theorem gaussPMap_closure_graph_form_zero (G : GaugeAlgebra 8) (d : Fin 8)
    (Φ : CoreRep 99 D) (hD : Dense (D : Set (L2d 99)))
    {u v : L2d 99 × L2d 99} (hu : u ∈ (gaussPMap G d Φ).closure.graph)
    (hv : v ∈ (gaussPMap G d Φ).closure.graph) :
    inner ℂ u.2 v.1 + inner ℂ u.1 v.2 = 0 := by
  have hgraph := (gaussPMap_isClosable G d Φ hD).graph_closure_eq_closure_graph
  -- step one: the second argument ranges over the graph of `𝒢_d`
  have hfirst : ∀ u : L2d 99 × L2d 99, u ∈ (gaussPMap G d Φ).closure.graph →
      ∀ v ∈ (gaussPMap G d Φ).graph, inner ℂ u.2 v.1 + inner ℂ u.1 v.2 = 0 := by
    intro u hu v hv
    have hu' : u ∈ (gaussPMap G d Φ).graph.topologicalClosure := by
      rw [hgraph]
      exact hu
    have hcont : Continuous fun w : L2d 99 × L2d 99 =>
        inner ℂ w.2 v.1 + inner ℂ w.1 v.2 :=
      (continuous_snd.inner continuous_const).add (continuous_fst.inner continuous_const)
    have hclosed : IsClosed {w : L2d 99 × L2d 99 | inner ℂ w.2 v.1 + inner ℂ w.1 v.2 = 0} :=
      isClosed_eq hcont continuous_const
    have hsub : ((gaussPMap G d Φ).graph : Set (L2d 99 × L2d 99))
        ⊆ {w | inner ℂ w.2 v.1 + inner ℂ w.1 v.2 = 0} := by
      intro w hw
      exact gaussPMap_graph_form_zero G d Φ hw hv
    have hcl : ((gaussPMap G d Φ).graph.topologicalClosure : Set (L2d 99 × L2d 99))
        ⊆ {w | inner ℂ w.2 v.1 + inner ℂ w.1 v.2 = 0} := by
      rw [Submodule.topologicalClosure_coe]
      exact closure_minimal hsub hclosed
    exact hcl hu'
  -- step two: both arguments range over the graph of the closure
  have hv' : v ∈ (gaussPMap G d Φ).graph.topologicalClosure := by
    rw [hgraph]
    exact hv
  have hcont : Continuous fun w : L2d 99 × L2d 99 =>
      inner ℂ u.2 w.1 + inner ℂ u.1 w.2 :=
    (continuous_const.inner continuous_fst).add (continuous_const.inner continuous_snd)
  have hclosed : IsClosed {w : L2d 99 × L2d 99 | inner ℂ u.2 w.1 + inner ℂ u.1 w.2 = 0} :=
    isClosed_eq hcont continuous_const
  have hsub : ((gaussPMap G d Φ).graph : Set (L2d 99 × L2d 99))
      ⊆ {w | inner ℂ u.2 w.1 + inner ℂ u.1 w.2 = 0} := by
    intro w hw
    exact hfirst u hu w hw
  have hcl : ((gaussPMap G d Φ).graph.topologicalClosure : Set (L2d 99 × L2d 99))
      ⊆ {w | inner ℂ u.2 w.1 + inner ℂ u.1 w.2 = 0} := by
    rw [Submodule.topologicalClosure_coe]
    exact closure_minimal hsub hclosed
  exact hcl hv'

/-- **The closure of the Gauss constraint is skew**: `⟪A x, y⟫ = −⟪x, A y⟫` for all `x`,
`y` in the domain of the closure. -/
theorem gaussPMap_closure_skew (G : GaugeAlgebra 8) (d : Fin 8) (Φ : CoreRep 99 D)
    (hD : Dense (D : Set (L2d 99)))
    (x y : (gaussPMap G d Φ).closure.domain) :
    inner ℂ ((gaussPMap G d Φ).closure x) (y : L2d 99)
      = -inner ℂ (x : L2d 99) ((gaussPMap G d Φ).closure y) := by
  have hu : ((x : L2d 99), (gaussPMap G d Φ).closure x) ∈ (gaussPMap G d Φ).closure.graph :=
    LinearPMap.mem_graph _ x
  have hv : ((y : L2d 99), (gaussPMap G d Φ).closure y) ∈ (gaussPMap G d Φ).closure.graph :=
    LinearPMap.mem_graph _ y
  have h := gaussPMap_closure_graph_form_zero G d Φ hD hu hv
  linear_combination h

/-- The closed charge has vanishing real expectation values — the closure-level form of
"it generates isometries". -/
theorem gaussPMap_closure_inner_re_zero (G : GaugeAlgebra 8) (d : Fin 8)
    (Φ : CoreRep 99 D) (hD : Dense (D : Set (L2d 99)))
    (x : (gaussPMap G d Φ).closure.domain) :
    (inner ℂ ((gaussPMap G d Φ).closure x) (x : L2d 99)).re = 0 := by
  have hskew := gaussPMap_closure_skew G d Φ hD x x
  have hconj : inner ℂ (x : L2d 99) ((gaussPMap G d Φ).closure x)
      = (starRingEnd ℂ)
        (inner ℂ ((gaussPMap G d Φ).closure x) (x : L2d 99)) :=
    (inner_conj_symm _ _).symm
  rw [hconj] at hskew
  have hre := congrArg Complex.re hskew
  simp only [Complex.neg_re, Complex.conj_re] at hre
  linarith

/-! ## The adjoint of the closure

Skewness of the closure says `⟪A x, y⟫ = −⟪x, A y⟫` for `x`, `y` in the domain of `A`.
Rearranged, it says that for `y` in that domain the functional `x ↦ ⟪y, A x⟫` *is* the
functional `x ↦ ⟪−A y, x⟫`, which is continuous.  By `LinearPMap.mem_adjoint_domain_iff`
this puts `y` in the domain of the adjoint, and `LinearPMap.adjoint_apply_eq` identifies
the value as `−A y`.  The result is `A ≤ −A†`, the half of skew-adjointness that does not
need a new idea. -/

/-- The domain of the closure of `𝒢_d` lies in the domain of its adjoint. -/
theorem gaussPMap_closure_adjoint_domain_ge (G : GaugeAlgebra 8) (d : Fin 8)
    (Φ : CoreRep 99 D) (hD : Dense (D : Set (L2d 99))) :
    (gaussPMap G d Φ).closure.domain ≤ (gaussPMap G d Φ).closure.adjoint.domain := by
  intro y hy
  refine LinearPMap.mem_adjoint_domain_of_exists (T := (gaussPMap G d Φ).closure)
    (y : L2d 99) ⟨-(gaussPMap G d Φ).closure ⟨y, hy⟩, ?_⟩
  intro x
  rw [inner_neg_left]
  have h := gaussPMap_closure_skew G d Φ hD ⟨y, hy⟩ x
  rw [h]
  ring

/-- On the domain of the closure the adjoint acts as the negative of the closure. -/
theorem gaussPMap_closure_adjoint_apply (G : GaugeAlgebra 8) (d : Fin 8)
    (Φ : CoreRep 99 D) (hD : Dense (D : Set (L2d 99)))
    (y : (gaussPMap G d Φ).closure.domain) :
    (gaussPMap G d Φ).closure.adjoint
        ⟨(y : L2d 99), gaussPMap_closure_adjoint_domain_ge G d Φ hD y.2⟩
      = -(gaussPMap G d Φ).closure y := by
  refine LinearPMap.adjoint_apply_eq (T := (gaussPMap G d Φ).closure)
    (gaussPMap_closure_domain_dense G d Φ hD) ?_ ?_
  intro x
  rw [inner_neg_left]
  have h := gaussPMap_closure_skew G d Φ hD y x
  rw [h]
  ring

/-- **The closure of `𝒢_d` is contained in the negative of its own adjoint**: `A ≤ −A†`,
i.e. `dom A ⊆ dom A†` and `A† y = −A y` on that domain.  This is the half of
skew-adjointness that needs no new argument; `dom A† ⊆ dom A` is the other half. -/
theorem gaussPMap_closure_le_negAdjoint (G : GaugeAlgebra 8) (d : Fin 8)
    (Φ : CoreRep 99 D) (hD : Dense (D : Set (L2d 99))) :
    (gaussPMap G d Φ).closure ≤ -(gaussPMap G d Φ).closure.adjoint := by
  refine ⟨gaussPMap_closure_adjoint_domain_ge G d Φ hD, ?_⟩
  intro x y hxy
  rw [LinearPMap.neg_apply]
  have hstep : (gaussPMap G d Φ).closure.adjoint y
      = (gaussPMap G d Φ).closure.adjoint
          ⟨(x : L2d 99), gaussPMap_closure_adjoint_domain_ge G d Φ hD x.2⟩ := by
    congr 1
    exact Subtype.ext hxy.symm
  rw [hstep, gaussPMap_closure_adjoint_apply G d Φ hD]
  rw [neg_neg]

/-- **The closure is the minimal closed extension of `𝒢_d`**, so skewness of the closure
is a statement about every closed extension of the core operator. -/
theorem gaussPMap_closure_le_of_isClosed (G : GaugeAlgebra 8) (d : Fin 8)
    (Φ : CoreRep 99 D) (hD : Dense (D : Set (L2d 99))) {T : L2d 99 →ₗ.[ℂ] L2d 99}
    (hT : T.IsClosed) (hle : gaussPMap G d Φ ≤ T) :
    (gaussPMap G d Φ).closure ≤ T := by
  refine LinearPMap.le_of_le_graph ?_
  rw [← (gaussPMap_isClosable G d Φ hD).graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le hle) hT

/-- The core `D` is a core of the closure: restricting the closure to the Gauss–polynomial
core and closing again returns the closure. -/
theorem gaussPMap_closure_hasCore (G : GaugeAlgebra 8) (d : Fin 8) (Φ : CoreRep 99 D) :
    (gaussPMap G d Φ).closure.HasCore D := by
  have h := LinearPMap.closureHasCore (gaussPMap G d Φ)
  rwa [gaussPMap_domain] at h

/-! ## The concrete instance -/

/-- The Gauss constraint on the Gauss–polynomial core of `L²(ℝ⁹⁹)` is closable. -/
theorem gaussPMap_polyGaussCore_isClosable (G : GaugeAlgebra 8) (d : Fin 8) :
    (gaussPMap G d (coreRepPoly 99)).IsClosable :=
  gaussPMap_isClosable G d (coreRepPoly 99) polyGaussCore_dense

/-- The domain of that closure is dense, so the skewness statement below is not vacuous. -/
theorem gaussPMap_polyGaussCore_closure_domain_dense (G : GaugeAlgebra 8) (d : Fin 8) :
    Dense ((gaussPMap G d (coreRepPoly 99)).closure.domain : Set (L2d 99)) :=
  gaussPMap_closure_domain_dense G d (coreRepPoly 99) polyGaussCore_dense

/-- **The closure of the field-space Gauss constraint is skew**, with no hypothesis left:
`⟪A x, y⟫ = −⟪x, A y⟫` on the domain of the closure of `𝒢_d` acting on the
Gauss–polynomial core of `L²(ℝ⁹⁹)`. -/
theorem gaussPMap_polyGaussCore_closure_skew (G : GaugeAlgebra 8) (d : Fin 8)
    (x y : (gaussPMap G d (coreRepPoly 99)).closure.domain) :
    inner ℂ ((gaussPMap G d (coreRepPoly 99)).closure x) (y : L2d 99)
      = -inner ℂ (x : L2d 99) ((gaussPMap G d (coreRepPoly 99)).closure y) :=
  gaussPMap_closure_skew G d (coreRepPoly 99) polyGaussCore_dense x y

/-- The closed field-space charge has vanishing real expectation values. -/
theorem gaussPMap_polyGaussCore_closure_inner_re_zero (G : GaugeAlgebra 8) (d : Fin 8)
    (x : (gaussPMap G d (coreRepPoly 99)).closure.domain) :
    (inner ℂ ((gaussPMap G d (coreRepPoly 99)).closure x) (x : L2d 99)).re = 0 :=
  gaussPMap_closure_inner_re_zero G d (coreRepPoly 99) polyGaussCore_dense x

/-- On the field-space core the domain of the closure lies in the domain of its adjoint. -/
theorem gaussPMap_polyGaussCore_closure_adjoint_domain_ge (G : GaugeAlgebra 8) (d : Fin 8) :
    (gaussPMap G d (coreRepPoly 99)).closure.domain
      ≤ (gaussPMap G d (coreRepPoly 99)).closure.adjoint.domain :=
  gaussPMap_closure_adjoint_domain_ge G d (coreRepPoly 99) polyGaussCore_dense

/-- **The field-space closure is contained in the negative of its own adjoint**, with no
hypothesis left. -/
theorem gaussPMap_polyGaussCore_closure_le_negAdjoint (G : GaugeAlgebra 8) (d : Fin 8) :
    (gaussPMap G d (coreRepPoly 99)).closure
      ≤ -(gaussPMap G d (coreRepPoly 99)).closure.adjoint :=
  gaussPMap_closure_le_negAdjoint G d (coreRepPoly 99) polyGaussCore_dense

/-- The Gauss–polynomial core is a core of the field-space closure. -/
theorem gaussPMap_polyGaussCore_closure_hasCore (G : GaugeAlgebra 8) (d : Fin 8) :
    (gaussPMap G d (coreRepPoly 99)).closure.HasCore (polyGaussCore (d := 99)) :=
  gaussPMap_closure_hasCore G d (coreRepPoly 99)

end

end BookProof.Qym.GaussClosure
