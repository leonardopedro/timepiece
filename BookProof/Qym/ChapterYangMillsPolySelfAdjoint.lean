/-
Copyright (c) 2026.  All rights reserved.

# `polyOp.closure` is self-adjoint

The far end of the S0 programme: the closed polynomial core is a self-adjoint operator.  The input
is spectral and elementary — it is the orthonormal Hermite basis of `ChapterYangMillsPolyBasis` —
and no deficiency-space argument is used, which is what keeps this a *real* statement: over `ℝ`
there is no `±i` to test, so the operator is diagonalized instead.

Two halves.

* **Symmetry.**  `polyOp` is symmetric because it is diagonal in an orthonormal family with real
  eigenvalues: `⟪T b_m, b_n⟫ = m δ_{mn} = ⟪b_m, T b_n⟫` on the generators, and bilinearity
  propagates that to the span (`coreExt_inner_comm_span`, proved by `Submodule.span_induction₂`).
  `closure_isFormalAdjoint` then transfers symmetry to the closure by the sequence
  characterization of the closed graph: if `(xₖ, T xₖ) → (x, T x)` and `(yₗ, T yₗ) → (y, T y)`, the
  inner products `⟪T xₖ, yₗ⟫` converge to both `⟪T x, y⟫` and `⟪x, T y⟫`, and a limit is unique.

* **The adjoint is contained in the closure.**  This is the diagonal-operator argument.  For
  `y ∈ T.adjoint.domain` with `w = T.adjoint y`, the adjoint relation on the basis gives
  `⟪b_n, w⟫ = n ⟪b_n, y⟫`, so the basis expansion of `w` is the basis expansion of `y` with every
  coefficient multiplied by its eigenvalue.  The partial sums of the expansion of `y` therefore lie
  in `T.domain` and their images are the partial sums of the expansion of `w`; both converge,
  `yₙ → y` and `T yₙ → w`, and the closed graph of `T` gives `y ∈ T.domain` with `T y = w`.

With both halves `T.adjoint = T`, so `IsSelfAdjoint T`, and `closure_eq_of_le` then identifies the
closure of the polynomial core with the closure of `gaussOp`, given only that the latter is
symmetric.
-/
import BookProof.Qym.ChapterYangMillsPolyBasis

open Filter MeasureTheory Polynomial Topology
open scoped ENNReal InnerProductSpace

namespace BookProof.YangMillsPolySelfAdjoint

open BookProof.YangMillsPolyCore BookProof.YangMillsPolyGraphNorm BookProof.YangMillsPolyBasis
open BookProof.YangMillsPolyAnnulus BookProof.YangMillsHermiteSpectrum BookProof.YangMillsMehlerLp
open BookProof.YangMillsGaussForm BookProof.HermiteCore BookProof.SelfAdjointMaximal

noncomputable section

/-! ## From a closed graph point to a sequence of graph points -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {T : E →ₗ.[ℝ] E}

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

/-! ## `polyOp` is symmetric -/

/-- **`polyOp` on a normalized Hermite class.**  `polyOp` is read through `polyOpH`, which is
linear on the span, and `hermiteLpR n` is a nonzero multiple of `polyLp (hermiteR n)`. -/
theorem polyOpH_hermiteLpR (n : ℕ) :
    ((polyOpH ⟨hermiteLpR n, hermiteLpR_mem n⟩ : polyRange) : Lp ℝ 2 gaussMeasure)
      = (n : ℝ) • hermiteLpR n := by
  have hsub : (⟨hermiteLpR n, hermiteLpR_mem n⟩ : hermiteSpan)
      = (hermiteNorm n)⁻¹ •
        (⟨polyLp (hermiteR n), Submodule.subset_span ⟨n, rfl⟩⟩ : hermiteSpan) := by
    refine Subtype.ext ?_
    simp [hermiteLpR]
  rw [hsub, map_smul, Submodule.coe_smul, polyOpH_hermiteR, hermiteLpR]
  rw [smul_smul, smul_smul, mul_comm]

/-- **`polyOp` on a normalized Hermite class**, with the eigenvalue `n`. -/
theorem polyOp_hermiteLpR (n : ℕ) :
    polyOp ⟨hermiteLpR n, hermiteLpR_mem n⟩ = (n : ℝ) • hermiteLpR n :=
  polyOpH_hermiteLpR n

/-- **The global linear extension `coreExt` on a normalized Hermite class.** -/
theorem coreExt_hermiteLpR (n : ℕ) :
    coreExt (hermiteLpR n) = (n : ℝ) • hermiteLpR n := by
  rw [coreExt_apply_mem (hermiteLpR_mem n), polyOpH_hermiteLpR]

/-- **The Hermite classes are symmetric for the polynomial core.**  Both sides are linear in each
variable, so `Submodule.span_induction₂` reduces the claim to the generators; there it is
`m δ_{mn} = n δ_{mn}` for the orthonormal family `hermiteLpR`. -/
theorem coreExt_inner_comm_span {v w : Lp ℝ 2 gaussMeasure}
    (hv : v ∈ Submodule.span ℝ (Set.range hermiteLpR))
    (hw : w ∈ Submodule.span ℝ (Set.range hermiteLpR)) :
    ⟪coreExt v, w⟫_ℝ = ⟪v, coreExt w⟫_ℝ := by
  refine Submodule.span_induction₂ (p := fun v w _ _ =>
    ⟪coreExt v, w⟫_ℝ = ⟪v, coreExt w⟫_ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hv hw
  · rintro x y ⟨m, rfl⟩ ⟨n, rfl⟩
    rw [coreExt_hermiteLpR, coreExt_hermiteLpR, inner_smul_left, inner_smul_right,
      inner_hermiteLpR]
    by_cases h : m = n <;> simp [h]
  · intro y _
    simp
  · intro x _
    simp
  · intro x y z _ _ _ ix iy
    simp only [map_add, inner_add_left]
    rw [ix, iy]
  · intro x y z _ _ _ iy iz
    simp only [map_add, inner_add_right]
    rw [iy, iz]
  · intro c x y _ _ ix
    simp only [map_smul, inner_smul_left]
    rw [ix]
  · intro c x y _ _ ix
    simp only [map_smul, inner_smul_right]
    rw [ix]

/-- **The polynomial operator is symmetric.**  `polyOp` is `coreExt` read on the span, so this is
`coreExt_inner_comm_span` with the membership proofs supplied by the bundling. -/
theorem polyOp_isFormalAdjoint : polyOp.IsFormalAdjoint polyOp := by
  intro x y
  have hxv : (x : Lp ℝ 2 gaussMeasure) ∈ Submodule.span ℝ (Set.range hermiteLpR) := by
    rw [span_hermiteLpR]
    exact x.2
  have hyv : (y : Lp ℝ 2 gaussMeasure) ∈ Submodule.span ℝ (Set.range hermiteLpR) := by
    rw [span_hermiteLpR]
    exact y.2
  have h := coreExt_inner_comm_span hxv hyv
  rw [coreExt_apply_mem x.2, coreExt_apply_mem y.2] at h
  exact h

/-! ## The closure is symmetric -/

/-- `polyOp` is closable: it sits inside the closed `gaussOp.closure`. -/
theorem polyOp_closure_isClosable : polyOp.IsClosable :=
  polyOp_isClosable polyGraphApprox_holds

/-- **The closure of `polyOp` is symmetric**, by the sequence argument of
`closure_isFormalAdjoint`. -/
theorem polyOp_closure_isFormalAdjoint :
    polyOp.closure.IsFormalAdjoint polyOp.closure :=
  closure_isFormalAdjoint polyOp_isFormalAdjoint polyOp_closure_isClosable

/-- **`polyOp.closure` is a symmetric operator** in the `SymmetricOp` sense. -/
theorem polyOp_closure_isSymmetric : SymmetricOp polyOp.closure :=
  polyOp_closure_isFormalAdjoint

/-- The Hermite span lies in the domain of the closure: `polyOp ≤ polyOp.closure`. -/
theorem hermiteSpan_le_closureDomain : hermiteSpan ≤ polyOp.closure.domain :=
  (LinearPMap.le_closure polyOp).1

/-- The Hermite span is dense in the domain of the closure. -/
theorem dense_closureDomain :
    Dense ((polyOp.closure.domain : Submodule ℝ (Lp ℝ 2 gaussMeasure)) :
      Set (Lp ℝ 2 gaussMeasure)) :=
  dense_hermiteSpanSet.mono fun _ hv => hermiteSpan_le_closureDomain hv

/-- **The closure acts on a Hermite class by its eigenvalue**, for any membership proof. -/
theorem closure_apply_hermiteLpR (n : ℕ) (h : hermiteLpR n ∈ polyOp.closure.domain) :
    polyOp.closure ⟨hermiteLpR n, h⟩ = (n : ℝ) • hermiteLpR n := by
  have hle := hermiteSpan_le_closureDomain (hermiteLpR_mem n)
  have heq : (⟨hermiteLpR n, h⟩ : polyOp.closure.domain) = ⟨hermiteLpR n, hle⟩ :=
    Subtype.ext rfl
  rw [heq]
  have hstep := (LinearPMap.le_closure polyOp).2
    (x := (⟨hermiteLpR n, hermiteLpR_mem n⟩ : polyOp.domain))
    (y := (⟨hermiteLpR n, hle⟩ : polyOp.closure.domain)) rfl
  rw [← hstep, polyOp_hermiteLpR]

/-! ## The adjoint is contained in the closure -/

/-- **The basis coefficients of the adjoint are the coefficients of the vector, scaled by the
eigenvalues.**  The adjoint relation `⟪T† y, x⟫ = ⟪y, T x⟫` read at `x = b_n`, where
`T b_n = n b_n`. -/
theorem inner_adjoint_hermiteLpR (z : polyOp.closure.adjoint.domain) (n : ℕ) :
    ⟪hermiteLpR n, polyOp.closure.adjoint z⟫_ℝ
      = (n : ℝ) * ⟪hermiteLpR n, (z : Lp ℝ 2 gaussMeasure)⟫_ℝ := by
  have hformal : polyOp.closure.adjoint.IsFormalAdjoint polyOp.closure :=
    LinearPMap.adjoint_isFormalAdjoint dense_closureDomain
  have h := hformal z ⟨hermiteLpR n, hermiteSpan_le_closureDomain (hermiteLpR_mem n)⟩
  rw [closure_apply_hermiteLpR, inner_smul_right] at h
  calc ⟪hermiteLpR n, polyOp.closure.adjoint z⟫_ℝ
      = ⟪polyOp.closure.adjoint z, hermiteLpR n⟫_ℝ := real_inner_comm _ _
    _ = (n : ℝ) * ⟪(z : Lp ℝ 2 gaussMeasure), hermiteLpR n⟫_ℝ := h
    _ = (n : ℝ) * ⟪hermiteLpR n, (z : Lp ℝ 2 gaussMeasure)⟫_ℝ := by
        rw [real_inner_comm]

/-- **The partial sums of the basis expansion of an adjoint-domain vector lie in the closure's
domain, and their images are the partial sums of the expansion of the adjoint value.**  This is the
diagonal structure made concrete: `polyOp.closure` multiplies the `n`-th coefficient by `n`. -/
theorem exists_seq_of_mem_adjointDomain (z : polyOp.closure.adjoint.domain) :
    ∃ v : ℕ → polyOp.closure.domain,
      Tendsto (fun k => (v k : Lp ℝ 2 gaussMeasure)) atTop (𝓝 (z : Lp ℝ 2 gaussMeasure)) ∧
      Tendsto (fun k => polyOp.closure (v k)) atTop (𝓝 (polyOp.closure.adjoint z)) := by
  have hsum_z : HasSum
      (fun n => ⟪hermiteLpR n, (z : Lp ℝ 2 gaussMeasure)⟫_ℝ • hermiteLpR n)
      (z : Lp ℝ 2 gaussMeasure) := by
    simpa only [hermiteBasisR_apply, HilbertBasis.repr_apply_apply] using
      hermiteBasisR.hasSum_repr (z : Lp ℝ 2 gaussMeasure)
  have hsum_w : HasSum
      (fun n => ⟪hermiteLpR n, polyOp.closure.adjoint z⟫_ℝ • hermiteLpR n)
      (polyOp.closure.adjoint z) := by
    simpa only [hermiteBasisR_apply, HilbertBasis.repr_apply_apply] using
      hermiteBasisR.hasSum_repr (polyOp.closure.adjoint z)
  have hmem : ∀ i : ℕ, hermiteLpR i ∈ polyOp.closure.domain :=
    fun i => hermiteSpan_le_closureDomain (hermiteLpR_mem i)
  refine ⟨fun N => ⟨∑ i ∈ Finset.range N,
    ⟪hermiteLpR i, (z : Lp ℝ 2 gaussMeasure)⟫_ℝ • hermiteLpR i,
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)⟩, ?_, ?_⟩
  · exact hsum_z.tendsto_sum_nat
  · have hfun : (fun N => polyOp.closure (⟨∑ i ∈ Finset.range N,
        ⟪hermiteLpR i, (z : Lp ℝ 2 gaussMeasure)⟫_ℝ • hermiteLpR i,
        Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)⟩))
        = fun N => ∑ i ∈ Finset.range N,
            ⟪hermiteLpR i, polyOp.closure.adjoint z⟫_ℝ • hermiteLpR i := by
      funext N
      have hsplit : (⟨∑ i ∈ Finset.range N,
            ⟪hermiteLpR i, (z : Lp ℝ 2 gaussMeasure)⟫_ℝ • hermiteLpR i,
            Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)⟩
            : polyOp.closure.domain)
          = ∑ i ∈ Finset.range N,
              ⟪hermiteLpR i, (z : Lp ℝ 2 gaussMeasure)⟫_ℝ • ⟨hermiteLpR i, hmem i⟩ := by
        refine Subtype.ext ?_
        simp
      have hmap : polyOp.closure (∑ i ∈ Finset.range N,
            ⟪hermiteLpR i, (z : Lp ℝ 2 gaussMeasure)⟫_ℝ • ⟨hermiteLpR i, hmem i⟩)
          = ∑ i ∈ Finset.range N,
              polyOp.closure (⟪hermiteLpR i, (z : Lp ℝ 2 gaussMeasure)⟫_ℝ •
                ⟨hermiteLpR i, hmem i⟩) := map_sum polyOp.closure.toFun _ _
      rw [hsplit, hmap]
      refine Finset.sum_congr rfl fun i _ => ?_
      change polyOp.closure.toFun (⟪hermiteLpR i, (z : Lp ℝ 2 gaussMeasure)⟫_ℝ •
        ⟨hermiteLpR i, hmem i⟩) = _
      rw [map_smul]
      rw [show polyOp.closure.toFun ⟨hermiteLpR i, hmem i⟩ = (i : ℝ) • hermiteLpR i from
        closure_apply_hermiteLpR i (hmem i)]
      rw [inner_adjoint_hermiteLpR, smul_smul, mul_comm]
    rw [hfun]
    exact hsum_w.tendsto_sum_nat

/-- **The graph point of an adjoint-domain vector is a graph point of the closure.**  The sequence
of partial sums converges to the vector, and its image converges to the adjoint value; the graph of
the closure is closed, so the limit pair is a graph point. -/
theorem mem_graph_of_mem_adjointDomain (z : polyOp.closure.adjoint.domain) :
    (((z : Lp ℝ 2 gaussMeasure), polyOp.closure.adjoint z) :
        Lp ℝ 2 gaussMeasure × Lp ℝ 2 gaussMeasure)
      ∈ ((polyOp.closure.graph : Submodule ℝ (Lp ℝ 2 gaussMeasure × Lp ℝ 2 gaussMeasure)) :
        Set (Lp ℝ 2 gaussMeasure × Lp ℝ 2 gaussMeasure)) := by
  obtain ⟨v, hv, hw⟩ := exists_seq_of_mem_adjointDomain z
  have hclosed : _root_.IsClosed
      ((polyOp.closure.graph : Submodule ℝ (Lp ℝ 2 gaussMeasure × Lp ℝ 2 gaussMeasure)) :
        Set (Lp ℝ 2 gaussMeasure × Lp ℝ 2 gaussMeasure)) :=
    polyOp_closure_isClosable.closure_isClosed
  refine hclosed.mem_of_tendsto (hv.prodMk_nhds hw) ?_
  refine Filter.Eventually.of_forall fun k => ?_
  exact (LinearPMap.mem_graph_iff polyOp.closure).mpr ⟨v k, rfl, rfl⟩

/-- **The domain of the adjoint is contained in the domain of the closure.** -/
theorem mem_closureDomain_of_mem_adjointDomain (z : polyOp.closure.adjoint.domain) :
    (z : Lp ℝ 2 gaussMeasure) ∈ polyOp.closure.domain := by
  obtain ⟨v, hv, -⟩ :=
    (LinearPMap.mem_graph_iff polyOp.closure).mp (mem_graph_of_mem_adjointDomain z)
  have hv' : (v : Lp ℝ 2 gaussMeasure) = (z : Lp ℝ 2 gaussMeasure) := hv
  rw [← hv']
  exact v.2

/-- **On the adjoint's domain the two operators agree.** -/
theorem closure_apply_of_mem_adjointDomain (z : polyOp.closure.adjoint.domain)
    (hz : (z : Lp ℝ 2 gaussMeasure) ∈ polyOp.closure.domain) :
    polyOp.closure ⟨(z : Lp ℝ 2 gaussMeasure), hz⟩ = polyOp.closure.adjoint z := by
  obtain ⟨v, hv, hval⟩ :=
    (LinearPMap.mem_graph_iff polyOp.closure).mp (mem_graph_of_mem_adjointDomain z)
  rw [show (⟨(z : Lp ℝ 2 gaussMeasure), hz⟩ : polyOp.closure.domain) = v from
    Subtype.ext hv.symm, hval]

/-- **The adjoint of the closure is contained in the closure.**  This is the diagonal argument: the
expansion of an adjoint-domain vector converges, its image converges, and closedness identifies the
limit pair as a graph point. -/
theorem closure_adjoint_le : polyOp.closure.adjoint ≤ polyOp.closure := by
  refine ⟨fun z hz => mem_closureDomain_of_mem_adjointDomain ⟨z, hz⟩, ?_⟩
  intro x y hxy
  have hxmem : (x : Lp ℝ 2 gaussMeasure) ∈ polyOp.closure.domain :=
    mem_closureDomain_of_mem_adjointDomain x
  rw [← closure_apply_of_mem_adjointDomain x hxmem]
  refine congrArg polyOp.closure (Subtype.ext ?_)
  exact hxy

/-- **`polyOp.closure` is self-adjoint.**  The coinclusion is symmetry
(`SymmetricOp.le_adjoint`, from the diagonal basis and the sequence argument), the inclusion is the
diagonal argument `closure_adjoint_le`. -/
theorem isSelfAdjoint_polyOp_closure : IsSelfAdjoint polyOp.closure := by
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm closure_adjoint_le
    (SymmetricOp.le_adjoint polyOp_closure_isSymmetric dense_closureDomain)

/-- **`gaussOp.closure` is symmetric**, from the symmetry of `gaussOp` on its core by the same
sequence argument. -/
theorem gaussOp_closure_isSymmetric : SymmetricOp gaussOp.closure :=
  closure_isFormalAdjoint gaussOp_isFormalAdjoint gaussOp_isClosable

/-- **The identification of the polynomial core with the closure of `gaussOp`**, with no
hypotheses at all: `polyOp.closure` is self-adjoint, `gaussOp.closure` is symmetric, and
maximality identifies them. -/
theorem polyOp_closure_eq_gaussOp_closure' : polyOp.closure = gaussOp.closure :=
  polyOp_closure_eq_gaussOp_closure polyGraphApprox_holds isSelfAdjoint_polyOp_closure
    gaussOp_closure_isSymmetric

end

end BookProof.YangMillsPolySelfAdjoint
