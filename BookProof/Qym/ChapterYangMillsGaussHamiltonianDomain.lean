import BookProof.Qym.ChapterYangMillsGaussHamiltonianClosure

/-!
# The closed Hamiltonian, the charge, and the domains

`BookProof/Qym/ChapterYangMillsGaussHamiltonianClosure.lean` proves that the closed
Hamiltonian `H̄ = hamClosure G` and the closed charge `Ā = (gaussPMap G d Φ).closure`
commute **on the Gauss core**: `Ā (H̄ x) = H̄ (Ā x)` for `x` in `polyGaussCore 99`,
where both closures act as their defining operators.  That is a statement on a set of
vectors lying in both domains.

This module carries it to the domains:

* **`bounded_preserves_closure_domain`** — the unconditional half.  A *bounded* operator
  `S` that maps the core into itself and commutes with `A` there preserves the domain of
  the closure of `A` and commutes with it there.  The proof is the graph argument: core
  points converging to `y` in the graph norm are mapped to core points converging to `S y`
  in the graph norm (continuity of `S`), and the graph of the closure is closed.  This is
  the abstract content of the `DomPreserve` / `StrongCommute` pair of
  `ChapterBrstReducedTransferUnbounded`.
* **`gaussClosure_bounded_preserves`** — its Gauss instance: any bounded operator
  commuting with `𝒢_d` on the core preserves `dom (closure 𝒢_d)` and commutes with the
  closure.  (Parity is one such operator; the earlier parity chapter proves the same
  statement by the same argument, specialised.)
* **`hamClosure_comm_gaussClosure_of_core_seq`** — the unbounded half, carried as far as the
  mathematics goes.  `H̄` is not bounded, so `S xₙ → S y` is *not* available from
  continuity; what replaces it is a core sequence whose **Hamiltonian** graph-norm limits are
  known: `H̄ xₙ → H̄ y` and `H̄ (Ā xₙ) → H̄ (Ā y)` (the second is the graph-norm statement at
  `Ā y`, expressed with the core's own `gaussEndo`).  Under that input the same graph
  argument gives `H̄ y ∈ dom Ā` and `Ā (H̄ y) = H̄ (Ā y)`.

## What is *not* proved, and why

The joint-core hypothesis of the last theorem is a genuine regularity input, not a
restatement: it says the Gauss–polynomial core is dense in `dom Ā` with respect to the
graph norm of `H̄` (twice: for `y` and for `Ā y`).  This is exactly the elliptic-regularity
/ graph-norm domination statement the corpus has recorded as missing since the Friedrichs
chapters, and it is *not* derivable from symmetry and commutation alone: a closed
symmetric operator commuting with a self-adjoint operator on a dense core can fail to have
its domain preserved by the self-adjoint one.  So the module proves the graph argument in
full and names the remaining density statement precisely; it does not pretend that
`dom Ā ⊆ dom H̄` follows from what precedes it in the corpus.
-/

namespace BookProof.Qym.GaussHamiltonianDomain

open BookProof.Qym.GaussCasimir BookProof.BrstYmCommute BookProof.BookBrstYangMills
open BookProof.YangMillsHermite BookProof.HermiteProductCore BookProof.Qym.GaussSkew
open BookProof.Qym.GaussClosure BookProof.Qym.GaussHamiltonianClosure BookProof.EsaClosure
open Filter Topology

noncomputable section

/-! ## The bounded case: no hypothesis beyond commutation on the core -/

set_option maxHeartbeats 800000 in
-- the graph/pair coercions need more than the default budget
/-- **A bounded operator preserving the core and commuting there acts on the closure's
domain.**  If `S` is bounded, maps the domain of `A` into itself, and satisfies
`A (S x) = S (A x)` there, then `S` maps `dom Ā` into `dom Ā` and commutes with `Ā`. -/
theorem bounded_preserves_closure_domain {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (A : E →ₗ.[ℂ] E) (hcl : A.IsClosable) (S : E →L[ℂ] E)
    (hSmap : ∀ x : A.domain, (S (x : E) : E) ∈ A.domain)
    (hScomm : ∀ x : A.domain, A ⟨S (x : E), hSmap x⟩ = S (A x))
    (y : A.closure.domain) :
    ∃ h : (S (y : E) : E) ∈ A.closure.domain,
      A.closure ⟨S (y : E), h⟩ = S (A.closure y) := by
  have hAcl : A.closure.IsClosed := hcl.closure_isClosed
  -- a core sequence converging to `y` in the graph norm
  have hmem : ((y : E), A.closure y) ∈ A.graph.topologicalClosure := by
    rw [hcl.graph_closure_eq_closure_graph]
    exact LinearPMap.mem_graph _ y
  obtain ⟨z, hz, hztend⟩ := mem_closure_iff_seq_limit.1 hmem
  choose x hx1 hx2 using fun n => (LinearPMap.mem_graph_iff _).1 (hz n)
  have hzt : ∀ n, z n = ((x n : E), A (x n)) := fun n => Prod.ext (hx1 n).symm (hx2 n).symm
  have hseq : Tendsto (fun n => ((x n : E), A (x n))) atTop
      (𝓝 ((y : E), A.closure y)) :=
    hztend.congr' (Filter.Eventually.of_forall fun n => hzt n)
  have hxT : Tendsto (fun n => (x n : E)) atTop (𝓝 (y : E)) :=
    (continuous_fst.tendsto ((y : E), A.closure y)).comp hseq
  have hAxT : Tendsto (fun n => A (x n)) atTop (𝓝 (A.closure y)) :=
    (continuous_snd.tendsto ((y : E), A.closure y)).comp hseq
  -- the images are core points, and the graph is closed
  have hST : Tendsto (fun n => (S (x n : E) : E)) atTop (𝓝 (S (y : E))) :=
    S.continuous.continuousAt.tendsto.comp hxT
  have hSAT : Tendsto (fun n => S (A (x n))) atTop (𝓝 (S (A.closure y))) :=
    S.continuous.continuousAt.tendsto.comp hAxT
  have hpair : Tendsto (fun n => ((S (x n : E) : E), S (A (x n)))) atTop
      (𝓝 ((S (y : E)), S (A.closure y))) := by
    have := hST.prodMk hSAT
    rwa [← nhds_prod_eq] at this
  have hmemg : ∀ n, ((S (x n : E) : E), S (A (x n))) ∈ A.closure.graph := by
    intro n
    have hbase := LinearPMap.mem_graph A.closure
      (Submodule.inclusion (LinearPMap.le_closure A).1
        ⟨(S (x n : E) : E), hSmap (x n)⟩)
    have hval : A.closure (Submodule.inclusion (LinearPMap.le_closure A).1
        ⟨(S (x n : E) : E), hSmap (x n)⟩)
        = A ⟨(S (x n : E) : E), hSmap (x n)⟩ :=
      (LinearPMap.apply_comp_inclusion (LinearPMap.le_closure A) _).symm
    rw [hval, hScomm (x n)] at hbase
    exact hbase
  have hlim := hAcl.isSeqClosed hmemg hpair
  obtain ⟨w, hw1, hw2⟩ := (LinearPMap.mem_graph_iff _).1 hlim
  have hy : (S (y : E) : E) ∈ A.closure.domain := by simpa [hw1] using w.2
  refine ⟨hy, ?_⟩
  have hweq : (⟨S (y : E), hy⟩ : A.closure.domain) = w := Subtype.ext hw1.symm
  rw [hweq]
  exact hw2

/-! ## The Gauss instance of the bounded case -/

variable {D : Submodule ℂ (L2d 99)}

/-- **Any bounded operator commuting with `𝒢_d` on the core preserves the charge's
domain and commutes with its closure.**  This is `DomPreserve` / `StrongCommute` for the
closed charge and a bounded symmetry, with no further hypothesis. -/
theorem gaussClosure_bounded_preserves (G : GaugeAlgebra 8) (d : Fin 8)
    (S : L2d 99 →L[ℂ] L2d 99)
    (hSmap : ∀ x : (gaussPMap G d (coreRepPoly 99)).domain,
      (S (x : L2d 99) : L2d 99) ∈ (gaussPMap G d (coreRepPoly 99)).domain)
    (hScomm : ∀ x : (gaussPMap G d (coreRepPoly 99)).domain,
      (gaussPMap G d (coreRepPoly 99)) ⟨S (x : L2d 99), hSmap x⟩
        = S ((gaussPMap G d (coreRepPoly 99)) x))
    (y : (gaussPMap G d (coreRepPoly 99)).closure.domain) :
    ∃ h : (S (y : L2d 99) : L2d 99) ∈ (gaussPMap G d (coreRepPoly 99)).closure.domain,
      (gaussPMap G d (coreRepPoly 99)).closure ⟨S (y : L2d 99), h⟩
        = S ((gaussPMap G d (coreRepPoly 99)).closure y) :=
  bounded_preserves_closure_domain (gaussPMap G d (coreRepPoly 99))
    (gaussPMap_polyGaussCore_isClosable G d) S hSmap hScomm y

/-! ## The unbounded case: the graph argument at the Hamiltonian's closure -/

set_option maxHeartbeats 800000 in
-- the `clDom`/`graph` coercions need more than the default budget
/-- **The closed Hamiltonian acts on the charge's closure.**  A core sequence whose
Hamiltonian images converge to `H̄ y`, and whose charge images have Hamiltonian images
converging to `H̄ (Ā y)`, gives `H̄ y ∈ dom Ā` together with `Ā (H̄ y) = H̄ (Ā y)`.

Those two limit hypotheses are the graph-norm regularity the unbounded case needs (the
bounded case above gets them from continuity); everything else in the proof is the
closedness of `Ā` and the core commutation. -/
theorem hamClosure_comm_gaussClosure_of_core_seq (G : GaugeAlgebra 8) (d : Fin 8)
    (y : (gaussPMap G d (coreRepPoly 99)).closure.domain)
    (hyH : (y : L2d 99) ∈ clDom (ymHamiltonian (coreRepPoly 99) G.f))
    (hAyH : ((gaussPMap G d (coreRepPoly 99)).closure y : L2d 99)
      ∈ clDom (ymHamiltonian (coreRepPoly 99) G.f))
    (x : ℕ → polyGaussCore (d := 99))
    (hHx : Tendsto (fun n => ymHamiltonian (coreRepPoly 99) G.f (x n)) atTop
      (𝓝 (hamClosure G ⟨(y : L2d 99), hyH⟩)))
    (hHAx : Tendsto (fun n => ymHamiltonian (coreRepPoly 99) G.f (gaussEndo G d (x n))) atTop
      (𝓝 (hamClosure G ⟨((gaussPMap G d (coreRepPoly 99)).closure y : L2d 99), hAyH⟩))) :
    ∃ h : (hamClosure G ⟨(y : L2d 99), hyH⟩) ∈
        (gaussPMap G d (coreRepPoly 99)).closure.domain,
      (gaussPMap G d (coreRepPoly 99)).closure
          ⟨hamClosure G ⟨(y : L2d 99), hyH⟩, h⟩
        = hamClosure G ⟨((gaussPMap G d (coreRepPoly 99)).closure y : L2d 99), hAyH⟩ := by
  have hAcl : (gaussPMap G d (coreRepPoly 99)).closure.IsClosed :=
    gaussPMap_closure_isClosed G d (coreRepPoly 99) polyGaussCore_dense
  -- the core points `H xₙ` and their charge values
  have hAcomm : ∀ n, (gaussPMap G d (coreRepPoly 99)) ⟨(hamEndo G (x n) : L2d 99),
      (hamEndo G (x n)).2⟩
      = ymHamiltonian (coreRepPoly 99) G.f (gaussEndo G d (x n)) :=
    fun n => (ymHamiltonian_comm_gauss_core G d (x n)).symm
  have hpair : Tendsto (fun n => (((hamEndo G (x n) : polyGaussCore (d := 99)) : L2d 99),
      (gaussPMap G d (coreRepPoly 99)) ⟨(hamEndo G (x n) : L2d 99), (hamEndo G (x n)).2⟩))
      atTop (𝓝 ((hamClosure G ⟨(y : L2d 99), hyH⟩),
        hamClosure G ⟨((gaussPMap G d (coreRepPoly 99)).closure y : L2d 99), hAyH⟩)) := by
    have hfirst : Tendsto (fun n => ((hamEndo G (x n) : polyGaussCore (d := 99)) : L2d 99))
        atTop (𝓝 (hamClosure G ⟨(y : L2d 99), hyH⟩)) := by
      refine hHx.congr' (Filter.Eventually.of_forall fun n => ?_)
      exact coreOp_ymHamPoly_eq_ymHamiltonian G (x n)
    have hsecond : Tendsto (fun n => (gaussPMap G d (coreRepPoly 99))
        ⟨(hamEndo G (x n) : L2d 99), (hamEndo G (x n)).2⟩)
        atTop (𝓝 (hamClosure G ⟨((gaussPMap G d (coreRepPoly 99)).closure y : L2d 99), hAyH⟩)) :=
      hHAx.congr' (Filter.Eventually.of_forall fun n => (hAcomm n).symm)
    have := hfirst.prodMk hsecond
    rwa [← nhds_prod_eq] at this
  have hmemg : ∀ n, (((hamEndo G (x n) : polyGaussCore (d := 99)) : L2d 99),
      (gaussPMap G d (coreRepPoly 99)) ⟨(hamEndo G (x n) : L2d 99), (hamEndo G (x n)).2⟩)
      ∈ (gaussPMap G d (coreRepPoly 99)).closure.graph := by
    intro n
    have hbase := LinearPMap.mem_graph (gaussPMap G d (coreRepPoly 99)).closure
      (Submodule.inclusion (LinearPMap.le_closure (gaussPMap G d (coreRepPoly 99))).1
        ⟨(hamEndo G (x n) : L2d 99), (hamEndo G (x n)).2⟩)
    have hval : (gaussPMap G d (coreRepPoly 99)).closure
        (Submodule.inclusion (LinearPMap.le_closure (gaussPMap G d (coreRepPoly 99))).1
          ⟨(hamEndo G (x n) : L2d 99), (hamEndo G (x n)).2⟩)
        = (gaussPMap G d (coreRepPoly 99)) ⟨(hamEndo G (x n) : L2d 99), (hamEndo G (x n)).2⟩ :=
      gaussPMap_closure_apply_core G d (coreRepPoly 99) (hamEndo G (x n))
    rw [hval] at hbase
    exact hbase
  have hlim := hAcl.isSeqClosed hmemg hpair
  obtain ⟨w, hw1, hw2⟩ := (LinearPMap.mem_graph_iff _).1 hlim
  have hy : (hamClosure G ⟨(y : L2d 99), hyH⟩) ∈
      (gaussPMap G d (coreRepPoly 99)).closure.domain := by simpa [hw1] using w.2
  refine ⟨hy, ?_⟩
  have hweq : (⟨(hamClosure G ⟨(y : L2d 99), hyH⟩),
      hy⟩ : (gaussPMap G d (coreRepPoly 99)).closure.domain) = w := Subtype.ext hw1.symm
  rw [hweq]
  exact hw2

end

end BookProof.Qym.GaussHamiltonianDomain
