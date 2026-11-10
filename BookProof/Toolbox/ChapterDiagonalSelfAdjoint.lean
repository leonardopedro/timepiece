/-
Copyright (c) 2026.  All rights reserved.

# Diagonal operators with a Hilbert basis

The abstract content of the S0 argument, extracted so that it can be applied to any operator which
is presented by its eigenvectors rather than only to the polynomial core.  Let `b` be an orthonormal
Hilbert basis of a real Hilbert space `E` and `d : ι → ℝ` a family of *real* eigenvalues.

* **Symmetry is free.**  A linear map with `A (b i) = d i • b i` satisfies
  `⟪A v, w⟫ = ⟪v, A w⟫` on the span of the basis (bilinearity plus `⟪b m, b n⟫ = δ_{mn}`), so its
  restriction to that span is a symmetric operator — over `ℝ` there is no `±i` to test, which is why
  the argument is diagonalization rather than deficiency indices.

* **The adjoint is contained in the closure.**  For a closable `T` that acts diagonally on the
  basis vectors, `y ∈ T.closure.adjoint.domain` has basis coefficients `d i · ⟪b i, y⟫`
  (`inner_adjoint_basis`), so the partial sums of the expansion of `y` lie in the closure's domain,
  their images are the partial sums of the expansion of `T.adjoint y`, and the closed graph of the
  closure identifies the limit pair as a graph point.

* **Conclusion.**  A symmetric operator sits inside its adjoint and the adjoint sits inside the
  closure, so the two agree: `IsSelfAdjoint T.closure`.  `isSelfAdjoint_closure_diagOp_symm` states
  this for the operator that is the restriction of a diagonal map to the basis span, and its only
  hypotheses are the eigenvalue equations on the basis; closability is derived, not assumed.

## Main results

* `inner_comm_of_diag` — a diagonal map is symmetric on the span of the basis;
* `isFormalAdjoint_diagOp_span` — its restriction to the span is symmetric;
* `exists_seq_of_mem_graph_closure` — a point of a closed graph is a limit of graph points;
* `closure_isFormalAdjoint` — symmetry transfers to the closure;
* `inner_adjoint_basis` — the adjoint multiplies basis coefficients by the eigenvalues;
* `adjoint_le_closure_of_diag` — the adjoint of the closure is contained in the closure;
* `isSelfAdjoint_closure_of_diag` — symmetric closable diagonal operators have self-adjoint closure;
* `isSelfAdjoint_closure_of_diag_symm` — the same without the closability input, since symmetry
  plus density already gives it;
* `isSelfAdjoint_closure_diagOp` — the end-to-end form for a restriction of a diagonal map;
* `isSelfAdjoint_closure_diagOp_symm` — that form with every hypothesis about the eigenvectors.
-/
import Mathlib
import BookProof.Toolbox.ChapterSelfAdjointMaximal

open Filter
open scoped InnerProductSpace Topology

namespace BookProof.DiagonalSelfAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*}

noncomputable section

/-- **The operator with domain `p` acting as the ambient linear map `A`.** -/
def diagOp (A : E →ₗ[ℝ] E) (p : Submodule ℝ E) : E →ₗ.[ℝ] E where
  domain := p
  toFun := A.domRestrict p

omit [CompleteSpace E] in
/-- The diagonal operator acts as the ambient map. -/
@[simp] theorem diagOp_apply (A : E →ₗ[ℝ] E) (p : Submodule ℝ E) (x : p) :
    diagOp A p x = A (x : E) := rfl

/-! ## Symmetry on the span -/

omit [CompleteSpace E] in
/-- **A linear map diagonal in an orthonormal basis is symmetric on the span of the basis.**  Both
sides are linear in each variable, so `Submodule.span_induction₂` reduces the claim to the
generators, where it reads `d m δ_{mn} = d n δ_{mn}`. -/
theorem inner_comm_of_diag (b : HilbertBasis ι ℝ E) (d : ι → ℝ)
    (A : E →ₗ[ℝ] E)
    (hdiag : ∀ i, A (b i) = d i • b i) {v w : E}
    (hv : v ∈ Submodule.span ℝ (Set.range b)) (hw : w ∈ Submodule.span ℝ (Set.range b)) :
    ⟪A v, w⟫_ℝ = ⟪v, A w⟫_ℝ := by
  classical
  refine Submodule.span_induction₂ (p := fun v w _ _ => ⟪A v, w⟫_ℝ = ⟪v, A w⟫_ℝ)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hv hw
  · rintro x y ⟨m, rfl⟩ ⟨n, rfl⟩
    rw [hdiag, hdiag, inner_smul_left, inner_smul_right,
      orthonormal_iff_ite.mp b.orthonormal]
    by_cases h : m = n <;> simp [h]
  · intro y _
    simp
  · intro x _
    simp
  · intro x y z _ _ _ hxz hyz
    simp only [map_add, inner_add_left]
    rw [hxz, hyz]
  · intro x y z _ _ _ hxy hxz
    simp only [map_add, inner_add_right]
    rw [hxy, hxz]
  · intro r x y _ _ hxy
    simp only [map_smul, inner_smul_left]
    rw [hxy]
  · intro r x y _ _ hxy
    simp only [map_smul, inner_smul_right]
    rw [hxy]

omit [CompleteSpace E] in
/-- **The restriction of a diagonal map to the basis span is symmetric.** -/
theorem isFormalAdjoint_diagOp_span (b : HilbertBasis ι ℝ E) (d : ι → ℝ)
    (A : E →ₗ[ℝ] E)
    (hdiag : ∀ i, A (b i) = d i • b i) :
    (diagOp A (Submodule.span ℝ (Set.range b))).IsFormalAdjoint
      (diagOp A (Submodule.span ℝ (Set.range b))) :=
  fun x y => inner_comm_of_diag b d A hdiag x.2 y.2

/-! ## From a closed graph point to a sequence of graph points -/

section Abstract

variable {T : E →ₗ.[ℝ] E}

omit [CompleteSpace E] in
/-- **A point of the closed graph of a closable operator is the limit of graph points.**  This is
the sequence form of `T.closure.graph = T.graph.topologicalClosure`, with the datatypes chosen so
that the two components are honest functions into the domain and into `E`. -/
theorem exists_seq_of_mem_graph_closure (hcl : T.IsClosable) {x v : E}
    (hxv : ((x, v) : E × E) ∈ T.closure.graph) :
    ∃ xk : ℕ → T.domain, Tendsto (fun k => (xk k : E)) atTop (𝓝 x) ∧
      Tendsto (fun k => T (xk k)) atTop (𝓝 v) := by
  rw [← hcl.graph_closure_eq_closure_graph] at hxv
  obtain ⟨u, hu_mem, hu_tend⟩ := mem_closure_iff_seq_limit.mp hxv
  have hchoice : ∀ k, ∃ y : T.domain, (y : E) = (u k).1 ∧ T y = (u k).2 :=
    fun k => (LinearPMap.mem_graph_iff T).mp (hu_mem k)
  refine ⟨fun k => Classical.choose (hchoice k), ?_, ?_⟩
  · have hfun : (fun k => ((Classical.choose (hchoice k) : T.domain) : E))
        = fun k => (u k).1 := funext fun k => (Classical.choose_spec (hchoice k)).1
    rw [hfun]
    exact (continuous_fst.tendsto (x, v)).comp hu_tend
  · have hfun : (fun k => T (Classical.choose (hchoice k))) = fun k => (u k).2 :=
      funext fun k => (Classical.choose_spec (hchoice k)).2
    rw [hfun]
    exact (continuous_snd.tendsto (x, v)).comp hu_tend

omit [CompleteSpace E] in
/-- **The closure of a symmetric operator is symmetric.**  Take sequences in the graph of `T` that
converge to `(x, T.closure x)` and `(y, T.closure y)`; the symmetry of `T` on those sequences reads
`⟪T xₖ, yₗ⟫ = ⟪xₖ, T yₗ⟫` for every `k`, `l`, and with both indices going to infinity both sides
converge, to `⟪T.closure x, y⟫` and to `⟪x, T.closure y⟫`.  A limit in a Hausdorff space is unique,
and `atTop ×ˢ atTop` on `ℕ × ℕ` is nontrivial, so the two limits agree. -/
theorem closure_isFormalAdjoint (hT : T.IsFormalAdjoint T) (hcl : T.IsClosable) :
    T.closure.IsFormalAdjoint T.closure := by
  intro x y
  have hxmem : (((x : E), T.closure x) : E × E) ∈ T.closure.graph :=
    (LinearPMap.mem_graph_iff T.closure).mpr ⟨x, rfl, rfl⟩
  have hymem : (((y : E), T.closure y) : E × E) ∈ T.closure.graph :=
    (LinearPMap.mem_graph_iff T.closure).mpr ⟨y, rfl, rfl⟩
  obtain ⟨xk, hxk, hvk⟩ := exists_seq_of_mem_graph_closure hcl hxmem
  obtain ⟨yl, hyl, hvl⟩ := exists_seq_of_mem_graph_closure hcl hymem
  have hleft : Tendsto (fun p : ℕ × ℕ => ⟪T (xk p.1), (yl p.2 : E)⟫_ℝ) (atTop ×ˢ atTop)
      (𝓝 ⟪T.closure x, (y : E)⟫_ℝ) :=
    (hvk.comp tendsto_fst).inner (hyl.comp tendsto_snd)
  have hright : Tendsto (fun p : ℕ × ℕ => ⟪((xk p.1 : T.domain) : E), T (yl p.2)⟫_ℝ)
      (atTop ×ˢ atTop) (𝓝 ⟪(x : E), T.closure y⟫_ℝ) :=
    (hxk.comp tendsto_fst).inner (hvl.comp tendsto_snd)
  have heq : ∀ p : ℕ × ℕ,
      ⟪T (xk p.1), (yl p.2 : E)⟫_ℝ = ⟪((xk p.1 : T.domain) : E), T (yl p.2)⟫_ℝ :=
    fun p => hT (xk p.1) (yl p.2)
  have hsame : (fun p : ℕ × ℕ => ⟪T (xk p.1), (yl p.2 : E)⟫_ℝ)
      = fun p : ℕ × ℕ => ⟪((xk p.1 : T.domain) : E), T (yl p.2)⟫_ℝ := funext heq
  rw [hsame] at hleft
  exact tendsto_nhds_unique hleft hright

end Abstract

/-! ## The adjoint is contained in the closure -/

/-- **The adjoint multiplies basis coefficients by the eigenvalues.**  The adjoint relation
`⟪T† z, x⟫ = ⟪z, T x⟫` read at `x = b n`, where `T b n = d n • b n`. -/
theorem inner_adjoint_basis (b : HilbertBasis ι ℝ E) (d : ι → ℝ) (T : E →ₗ.[ℝ] E)
    {n : ι} (hbasis : b n ∈ T.domain) (hdiag : T ⟨b n, hbasis⟩ = d n • b n)
    (hdense : Dense (T.domain : Set E)) (z : T.adjoint.domain) :
    ⟪b n, T.adjoint z⟫_ℝ = d n * ⟪b n, (z : E)⟫_ℝ := by
  have hformal : T.adjoint.IsFormalAdjoint T := LinearPMap.adjoint_isFormalAdjoint hdense
  have h := hformal z ⟨b n, hbasis⟩
  rw [hdiag, inner_smul_right] at h
  calc ⟪b n, T.adjoint z⟫_ℝ
      = ⟪T.adjoint z, b n⟫_ℝ := real_inner_comm _ _
    _ = d n * ⟪(z : E), b n⟫_ℝ := h
    _ = d n * ⟪b n, (z : E)⟫_ℝ := by rw [real_inner_comm]

/-- **The adjoint of the closure of a diagonal operator is contained in the closure.**  The
diagonal argument: expand an adjoint-domain vector in the basis, note that the partial sums lie in
the closure's domain and that their images are the partial sums of the expansion of the adjoint
value, and use that the graph of the closure is closed. -/
theorem adjoint_le_closure_of_diag (b : HilbertBasis ι ℝ E) (d : ι → ℝ) (T : E →ₗ.[ℝ] E)
    (hbasis : ∀ i, b i ∈ T.domain) (hdiag : ∀ i, T ⟨b i, hbasis i⟩ = d i • b i)
    (hcl : T.IsClosable) :
    T.closure.adjoint ≤ T.closure := by
  classical
  have hspan_le : Submodule.span ℝ (Set.range b) ≤ T.domain :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbasis i)
  have hdense : Dense (T.domain : Set E) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span |>.mono hspan_le
  have hmem : ∀ i, b i ∈ T.closure.domain :=
    fun i => (LinearPMap.le_closure T).1 (hbasis i)
  have happly : ∀ i, T.closure ⟨b i, hmem i⟩ = d i • b i := by
    intro i
    have hstep := (LinearPMap.le_closure T).2 (x := (⟨b i, hbasis i⟩ : T.domain))
      (y := (⟨b i, hmem i⟩ : T.closure.domain)) rfl
    rw [← hstep, hdiag i]
  have hpair : ∀ z : T.closure.adjoint.domain,
      (((z : E), T.closure.adjoint z)) ∈ (T.closure.graph : Set (E × E)) := by
    intro z
    have hdenseC : Dense (T.closure.domain : Set E) :=
      hdense.mono (LinearPMap.le_closure T).1
    have hcoef : ∀ i, ⟪b i, T.closure.adjoint z⟫_ℝ = d i * ⟪b i, (z : E)⟫_ℝ :=
      fun i => inner_adjoint_basis b d T.closure (hmem i) (happly i) hdenseC z
    have hsum_z : HasSum (fun i => ⟪b i, (z : E)⟫_ℝ • b i) (z : E) := by
      simpa only [HilbertBasis.repr_apply_apply] using b.hasSum_repr (z : E)
    have hsum_w : HasSum (fun i => ⟪b i, T.closure.adjoint z⟫_ℝ • b i)
        (T.closure.adjoint z) := by
      simpa only [HilbertBasis.repr_apply_apply] using b.hasSum_repr (T.closure.adjoint z)
    have hv : Tendsto (fun s : Finset ι => ((⟨∑ i ∈ s,
          ⟪b i, (z : E)⟫_ℝ • b i,
          Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)⟩ :
          T.closure.domain) : E)) atTop (𝓝 (z : E)) := hsum_z
    have hw : Tendsto (fun s : Finset ι => T.closure (⟨∑ i ∈ s,
          ⟪b i, (z : E)⟫_ℝ • b i,
          Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)⟩ :
          T.closure.domain)) atTop (𝓝 (T.closure.adjoint z)) := by
      have hfun : (fun s : Finset ι => T.closure (⟨∑ i ∈ s,
            ⟪b i, (z : E)⟫_ℝ • b i,
            Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)⟩ :
            T.closure.domain))
          = fun s : Finset ι => ∑ i ∈ s,
              ⟪b i, T.closure.adjoint z⟫_ℝ • b i := by
        funext s
        have hsplit : (⟨∑ i ∈ s,
              ⟪b i, (z : E)⟫_ℝ • b i,
              Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)⟩
              : T.closure.domain)
            = ∑ i ∈ s,
                ⟪b i, (z : E)⟫_ℝ • ⟨b i, hmem i⟩ := by
          refine Subtype.ext ?_
          simp
        have hmap : T.closure (∑ i ∈ s, ⟪b i, (z : E)⟫_ℝ • ⟨b i, hmem i⟩)
            = ∑ i ∈ s, T.closure (⟪b i, (z : E)⟫_ℝ • ⟨b i, hmem i⟩) :=
          map_sum T.closure.toFun _ _
        rw [hsplit, hmap]
        refine Finset.sum_congr rfl fun i _ => ?_
        change T.closure.toFun (⟪b i, (z : E)⟫_ℝ • ⟨b i, hmem i⟩) = _
        rw [map_smul, show T.closure.toFun ⟨b i, hmem i⟩ = d i • b i from happly i,
          hcoef i, smul_smul, mul_comm]
      rw [hfun]
      exact hsum_w
    have hclosed : _root_.IsClosed ((T.closure.graph : Submodule ℝ (E × E)) : Set (E × E)) :=
      hcl.closure_isClosed
    refine hclosed.mem_of_tendsto (hv.prodMk_nhds hw) ?_
    refine Filter.Eventually.of_forall fun k => ?_
    exact (LinearPMap.mem_graph_iff T.closure).mpr ⟨_, rfl, rfl⟩
  have hdom : ∀ z : T.closure.adjoint.domain, (z : E) ∈ T.closure.domain := by
    intro z
    obtain ⟨v, hv, -⟩ := (LinearPMap.mem_graph_iff T.closure).mp (hpair z)
    have hv' : (v : E) = (z : E) := hv
    rw [← hv']
    exact v.2
  have hval : ∀ (z : T.closure.adjoint.domain) (hz : (z : E) ∈ T.closure.domain),
      T.closure ⟨(z : E), hz⟩ = T.closure.adjoint z := by
    intro z hz
    obtain ⟨v, hv, hval⟩ := (LinearPMap.mem_graph_iff T.closure).mp (hpair z)
    rw [show (⟨(z : E), hz⟩ : T.closure.domain) = v from Subtype.ext hv.symm, hval]
  refine ⟨fun z hz => hdom ⟨z, hz⟩, ?_⟩
  intro x y hxy
  rw [← hval x (hdom x)]
  refine congrArg T.closure (Subtype.ext ?_)
  exact hxy

/-- **A closable operator with a diagonal eigenbasis and symmetric closure has a self-adjoint
closure.**  Symmetry gives `T.closure ≤ T.closure.adjoint` (`SymmetricOp.le_adjoint`) and the
diagonal argument gives the other inclusion. -/
theorem isSelfAdjoint_closure_of_diag (b : HilbertBasis ι ℝ E) (d : ι → ℝ) (T : E →ₗ.[ℝ] E)
    (hbasis : ∀ i, b i ∈ T.domain) (hdiag : ∀ i, T ⟨b i, hbasis i⟩ = d i • b i)
    (hcl : T.IsClosable) (hsym : T.closure.IsFormalAdjoint T.closure) :
    IsSelfAdjoint T.closure := by
  have hspan_le : Submodule.span ℝ (Set.range b) ≤ T.domain :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbasis i)
  have hdense : Dense (T.closure.domain : Set E) :=
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span).mono
      (hspan_le.trans (LinearPMap.le_closure T).1)
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm (adjoint_le_closure_of_diag b d T hbasis hdiag hcl)
    (BookProof.SelfAdjointMaximal.SymmetricOp.le_adjoint hsym hdense)

/-- **Symmetry plus a diagonal basis already suffices.**  Closability is not an extra input: a
densely defined symmetric operator is contained in its adjoint, the adjoint of a densely defined
operator is closed, and a suboperator of a closed operator is closable.  So
`isSelfAdjoint_closure_of_diag` needs only `T.IsFormalAdjoint T`, which is the classical statement
of the eigenbasis criterion. -/
theorem isSelfAdjoint_closure_of_diag_symm (b : HilbertBasis ι ℝ E) (d : ι → ℝ) (T : E →ₗ.[ℝ] E)
    (hbasis : ∀ i, b i ∈ T.domain) (hdiag : ∀ i, T ⟨b i, hbasis i⟩ = d i • b i)
    (hsym : T.IsFormalAdjoint T) :
    IsSelfAdjoint T.closure := by
  have hspan_le : Submodule.span ℝ (Set.range b) ≤ T.domain :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbasis i)
  have hdense : Dense (T.domain : Set E) :=
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span).mono hspan_le
  have hcl : T.IsClosable :=
    (LinearPMap.adjoint_isClosed hdense).isClosable.leIsClosable
      (LinearPMap.IsFormalAdjoint.le_adjoint hdense hsym)
  exact isSelfAdjoint_closure_of_diag b d T hbasis hdiag hcl (closure_isFormalAdjoint hsym hcl)

/-- **A closable restriction of a diagonal map to the basis span has self-adjoint closure.**  The
symmetry is `isFormalAdjoint_diagOp_span`, transferred to the closure by `closure_isFormalAdjoint`,
so closability is the only hypothesis. -/
theorem isSelfAdjoint_closure_diagOp (b : HilbertBasis ι ℝ E) (d : ι → ℝ)
    (A : E →ₗ[ℝ] E)
    (hdiag : ∀ i, A (b i) = d i • b i)
    (hcl : (diagOp A (Submodule.span ℝ (Set.range b))).IsClosable) :
    IsSelfAdjoint (diagOp A (Submodule.span ℝ (Set.range b))).closure := by
  have hsym := isFormalAdjoint_diagOp_span b d A hdiag
  refine isSelfAdjoint_closure_of_diag b d _ (fun i => Submodule.subset_span ⟨i, rfl⟩) ?_ hcl ?_
  · intro i
    exact hdiag i
  · exact closure_isFormalAdjoint hsym hcl

/-- **The end-to-end form with no closability input.**  The restriction of a diagonal map to the
basis span is symmetric (`isFormalAdjoint_diagOp_span`), so
`isSelfAdjoint_closure_of_diag_symm` applies directly; every hypothesis is a statement about the
eigenvectors. -/
theorem isSelfAdjoint_closure_diagOp_symm (b : HilbertBasis ι ℝ E) (d : ι → ℝ)
    (A : E →ₗ[ℝ] E) (hdiag : ∀ i, A (b i) = d i • b i) :
    IsSelfAdjoint (diagOp A (Submodule.span ℝ (Set.range b))).closure :=
  isSelfAdjoint_closure_of_diag_symm b d (diagOp A (Submodule.span ℝ (Set.range b)))
    (fun i => Submodule.subset_span ⟨i, rfl⟩) hdiag (isFormalAdjoint_diagOp_span b d A hdiag)

end

end BookProof.DiagonalSelfAdjoint
