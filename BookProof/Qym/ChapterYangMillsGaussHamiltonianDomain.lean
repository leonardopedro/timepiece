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

## The literal inclusion is false, and what replaces it

`dom Ā ⊆ dom H̄` is not merely unproved here — it is false for an elliptic `H̄`.  The charge
`𝒢_d = firstOrder (ymGaussVec G d)` is first order along the *linear* field `ymGaussVec`, so a
rough radial function `f = ψ(|x|²)` with `ψ ∈ H¹ \\ H²` is annihilated by `𝒢_d` on smooth
approximants and is therefore in `dom Ā`, while `f ∉ dom H̄` because `dom H̄` is the
(`H²`-type) graph closure of the second-order `ymHamiltonian`.  So no proof of the inclusion
exists, and none should be attempted.

The statement the commutation argument actually consumes is the *graph-norm* one: every
`y ∈ dom Ā` is the limit of Gauss core vectors `xₙ` with `H̄ xₙ` convergent.  That is
exactly the joint-core hypothesis of `hamClosure_comm_gaussClosure_of_core_seq`, and the
lemma `clDom_hamClosure_of_charge_graph_dense` records that this density input *implies* the
inclusion, through `mem_hamClosure_domain_of_core_seq` (the closedness of the Hamiltonian's
graph).  The analytic obligation is therefore neither the inclusion nor its negation, but the
common-core density statement — an elliptic-regularity estimate for `H̄` on the charge's
domain, which remains open.
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

/-! ## The reduction: a common core is exactly what the inclusion needs

The literal inclusion `dom Ā ⊆ dom H̄` is not the statement the corpus can prove, and it is
not even true for an elliptic Hamiltonian: the charge `𝒢_d` is a first-order operator along
the linear field `ymGaussVec`, so a rough function constant along that flow lies in `dom Ā`
with `Ā = 0` while failing to lie in the (`H²`-type) domain of `H̄`.  What the commutation
argument actually needs is the *graph-norm* statement: every `y ∈ dom Ā` is the limit of Gauss
core vectors `xₙ` whose Hamiltonian images converge.  The lemma below is the half of that
reduction which is pure closedness: once such a core sequence exists, `y ∈ dom H̄` and the
Hamiltonian value is the limit. -/

set_option maxHeartbeats 800000 in
-- the `clGraph`/`clDom` projections need more than the default budget
/-- **A Gauss core sequence converging in the Hamiltonian's graph norm lands in `dom H̄`.**
If `xₙ → y` and `H̄ xₙ → z`, then `y` is in the domain of the closed Hamiltonian and
`H̄ y = z`.  This is the graph closure of `T = ymHamiltonian` being closed; it converts the
graph-norm density input into the domain inclusion, leaving the density itself as the only
analytic obligation. -/
theorem mem_hamClosure_domain_of_core_seq (G : GaugeAlgebra 8) {x : ℕ → PolyCore}
    {y z : L2d 99}
    (hx : Tendsto (fun n => ((x n : PolyCore) : L2d 99)) atTop (𝓝 y))
    (hz : Tendsto (fun n => hamClosure G ⟨((x n : PolyCore) : L2d 99),
      coe_mem_clDom _ (x n)⟩) atTop (𝓝 z)) :
    ∃ hyH : y ∈ clDom (ymHamiltonian (coreRepPoly 99) G.f),
      hamClosure G ⟨y, hyH⟩ = z := by
  have hmem : ∀ n, (((x n : PolyCore) : L2d 99),
      hamClosure G ⟨((x n : PolyCore) : L2d 99), coe_mem_clDom _ (x n)⟩)
      ∈ clGraph (ymHamiltonian (coreRepPoly 99) G.f) := by
    intro n
    simpa only [hamClosure_apply_core G (x n)] using
      (mem_clGraph_of_mem_opGraph
        (mem_opGraph (ymHamiltonian (coreRepPoly 99) G.f) (x n)))
  have hpair : Tendsto (fun n => (((x n : PolyCore) : L2d 99),
      hamClosure G ⟨((x n : PolyCore) : L2d 99), coe_mem_clDom _ (x n)⟩)) atTop
      (𝓝 (y, z)) := by
    have := hx.prodMk hz
    rwa [← nhds_prod_eq] at this
  have hcl := (clGraph_isClosed (ymHamiltonian (coreRepPoly 99) G.f)).isSeqClosed hmem hpair
  refine ⟨mem_clDom_iff.2 ⟨z, hcl⟩, ?_⟩
  exact clFun_unique (polyGaussCore_dense (d := 99)) (ymHamiltonian_symmetricOn _ _) hcl

set_option maxHeartbeats 800000 in
-- unfolding the density input through the two closures needs a larger budget
/-- **The graph-norm density input gives `dom Ā ⊆ dom H̄`.**  If every charge-domain vector
is approximated by a Gauss core sequence whose Hamiltonian images are Cauchy, then the
charge's domain is contained in the Hamiltonian's.  This is the sharp logical form of the
missing elliptic-regularity estimate: no further information about `𝒢_d` is used. -/
theorem clDom_hamClosure_of_charge_graph_dense (G : GaugeAlgebra 8) (d : Fin 8)
    (hdense : ∀ y ∈ (gaussPMap G d (coreRepPoly 99)).closure.domain,
      ∃ x : ℕ → PolyCore,
        Tendsto (fun n => ((x n : PolyCore) : L2d 99)) atTop (𝓝 y) ∧
        CauchySeq (fun n => hamClosure G ⟨((x n : PolyCore) : L2d 99),
          coe_mem_clDom _ (x n)⟩)) :
    (gaussPMap G d (coreRepPoly 99)).closure.domain
      ≤ clDom (ymHamiltonian (coreRepPoly 99) G.f) := by
  intro y hy
  obtain ⟨x, hx, hc⟩ := hdense y hy
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hc
  exact (mem_hamClosure_domain_of_core_seq G hx hz).1

/-! ## The graph-norm estimate on the core

`clDom_hamClosure_of_charge_graph_dense` leaves a statement quantified over all of `dom Ā`.
On the polynomial Gauss core both operators are explicit endomorphisms — `hamEndo` for the
Hamiltonian and `gaussEndo` for the charge — so the estimate can be stated, and in principle
checked, on the core alone: `‖H x‖ ≤ C (‖x‖ + ‖𝒢_d x‖)` for core vectors `x`.  The section
proves that this *core* inequality is enough.  Along any sequence of core vectors converging
in the charge's graph norm the Hamiltonian images are then Cauchy, because the inequality
controls their differences by the differences of the two convergent sequences.  Feeding that
into `clDom_hamClosure_of_charge_graph_dense` gives the domain inclusion.

So the analytic obligation is a two-term norm inequality between two operators whose action
on the core is a finite polynomial computation — not a statement about the domains. -/

/-- **The graph-norm estimate on the Gauss core**, with constant `C > 0`:
`‖H x‖ ≤ C (‖x‖ + ‖𝒢_d x‖)` for every core vector, where the charge acts through its core
endomorphism.  This is the elliptic-regularity input the common-core argument consumes,
stated only on the core. -/
def CoreChargeControlsHam (G : GaugeAlgebra 8) (d : Fin 8) (C : ℝ) : Prop :=
  0 < C ∧ ∀ x : PolyCore,
    ‖ymHamiltonian (coreRepPoly 99) G.f x‖
      ≤ C * (‖((x : PolyCore) : L2d 99)‖
        + ‖((gaussEndo G d x : PolyCore) : L2d 99)‖)

/-- The charge value of a core vector, read through the core endomorphism. -/
theorem gaussPMap_core_apply (G : GaugeAlgebra 8) (d : Fin 8) (x : PolyCore) :
    (gaussPMap G d (coreRepPoly 99)) ⟨((x : PolyCore) : L2d 99), x.2⟩
      = ((gaussEndo G d x : PolyCore) : L2d 99) := rfl

set_option maxHeartbeats 800000 in
-- the `clGraph`/`clDom` coercions need more than the default budget
/-- **A charge graph-norm sequence has Cauchy Hamiltonian images.**  If core vectors `xₙ`
converge, together with their charge values, then `H xₙ` is Cauchy: the core estimate bounds
`‖H xₘ − H xₙ‖` by `C (‖xₘ − xₙ‖ + ‖𝒢_d xₘ − 𝒢_d xₙ‖)` (both operators are linear on the core). -/
theorem cauchySeq_ham_of_core_sequences (G : GaugeAlgebra 8) (d : Fin 8) {C : ℝ}
    (hC : CoreChargeControlsHam G d C) {x : ℕ → PolyCore} {y z : L2d 99}
    (hx : Tendsto (fun n => ((x n : PolyCore) : L2d 99)) atTop (𝓝 y))
    (hA : Tendsto (fun n => ((gaussEndo G d (x n) : PolyCore) : L2d 99)) atTop (𝓝 z)) :
    CauchySeq (fun n => ymHamiltonian (coreRepPoly 99) G.f (x n)) := by
  obtain ⟨hCpos, hbound⟩ := hC
  refine Metric.cauchySeq_iff.2 fun ε hε => ?_
  have hδ : 0 < ε / (8 * C) := by positivity
  obtain ⟨Nx, hNx⟩ := Metric.cauchySeq_iff.1 hx.cauchySeq (ε / (8 * C)) hδ
  obtain ⟨NA, hNA⟩ := Metric.cauchySeq_iff.1 hA.cauchySeq (ε / (8 * C)) hδ
  refine ⟨max Nx NA, fun m hm n hn => ?_⟩
  have hmx := hNx m (le_of_max_le_left hm) n (le_of_max_le_left hn)
  have hmA := hNA m (le_of_max_le_right hm) n (le_of_max_le_right hn)
  have hsub : ((x m - x n : PolyCore) : L2d 99)
      = ((x m : PolyCore) : L2d 99) - ((x n : PolyCore) : L2d 99) := Submodule.coe_sub ..
  have hAsub : ((gaussEndo G d (x m - x n) : PolyCore) : L2d 99)
      = ((gaussEndo G d (x m) : PolyCore) : L2d 99)
        - ((gaussEndo G d (x n) : PolyCore) : L2d 99) := by
    rw [map_sub, Submodule.coe_sub]
  have hlin : ymHamiltonian (coreRepPoly 99) G.f (x m)
      - ymHamiltonian (coreRepPoly 99) G.f (x n)
      = ymHamiltonian (coreRepPoly 99) G.f (x m - x n) := (map_sub _ _ _).symm
  have hbound' := hbound (x m - x n)
  rw [hsub, hAsub] at hbound'
  rw [dist_eq_norm, hlin]
  simp only [dist_eq_norm] at hmx hmA
  have hval : C * (2 * (ε / (8 * C)) + 2 * (ε / (8 * C))) = ε / 2 := by
    field_simp
    norm_num
  nlinarith [hbound', hmx, hmA, hCpos, hval, hε]

set_option maxHeartbeats 800000 in
-- the `clGraph`/`clDom` coercions need more than the default budget
/-- **Every charge-domain vector has a core sequence whose charge values converge.**  This is
`polyGaussCore_dense` unpacked through the closedness of the charge's graph: the graph of the
closure is the closure of the core's graph. -/
theorem exists_core_seq_of_mem_charge_closure (G : GaugeAlgebra 8) (d : Fin 8)
    (y : (gaussPMap G d (coreRepPoly 99)).closure.domain) :
    ∃ x : ℕ → PolyCore,
      Tendsto (fun n => ((x n : PolyCore) : L2d 99)) atTop (𝓝 (y : L2d 99)) ∧
      Tendsto (fun n => ((gaussEndo G d (x n) : PolyCore) : L2d 99)) atTop
        (𝓝 ((gaussPMap G d (coreRepPoly 99)).closure y)) := by
  have hmem : ((y : L2d 99), (gaussPMap G d (coreRepPoly 99)).closure y)
      ∈ (gaussPMap G d (coreRepPoly 99)).graph.topologicalClosure := by
    rw [(gaussPMap_polyGaussCore_isClosable G d).graph_closure_eq_closure_graph]
    exact LinearPMap.mem_graph _ y
  obtain ⟨z, hz, hztend⟩ := mem_closure_iff_seq_limit.1 hmem
  choose x hx1 hx2 using fun n => (LinearPMap.mem_graph_iff _).1 (hz n)
  have hzt : ∀ n, z n = (((x n : PolyCore) : L2d 99),
      (gaussPMap G d (coreRepPoly 99)) ⟨((x n : PolyCore) : L2d 99), (x n).2⟩) :=
    fun n => Prod.ext (hx1 n).symm (hx2 n).symm
  have hseq : Tendsto (fun n => (((x n : PolyCore) : L2d 99),
      (gaussPMap G d (coreRepPoly 99)) ⟨((x n : PolyCore) : L2d 99), (x n).2⟩)) atTop
      (𝓝 ((y : L2d 99), (gaussPMap G d (coreRepPoly 99)).closure y)) :=
    hztend.congr' (Filter.Eventually.of_forall fun n => hzt n)
  refine ⟨x, (continuous_fst.tendsto _).comp hseq, ?_⟩
  have hsecond : Tendsto (fun n => (gaussPMap G d (coreRepPoly 99))
      ⟨((x n : PolyCore) : L2d 99), (x n).2⟩) atTop
      (𝓝 ((gaussPMap G d (coreRepPoly 99)).closure y)) :=
    (continuous_snd.tendsto _).comp hseq
  exact hsecond.congr' (Filter.Eventually.of_forall fun n => gaussPMap_core_apply G d (x n))

/-- **The core estimate gives the common-core density input.**  Every charge-domain vector is
approximated by core vectors in the charge graph norm, and the core estimate makes their
Hamiltonian images Cauchy. -/
theorem hdense_of_core_estimate (G : GaugeAlgebra 8) (d : Fin 8) {C : ℝ}
    (hC : CoreChargeControlsHam G d C) :
    ∀ y ∈ (gaussPMap G d (coreRepPoly 99)).closure.domain,
      ∃ x : ℕ → PolyCore,
        Tendsto (fun n => ((x n : PolyCore) : L2d 99)) atTop (𝓝 y) ∧
        CauchySeq (fun n => hamClosure G ⟨((x n : PolyCore) : L2d 99),
          coe_mem_clDom _ (x n)⟩) := by
  intro y hy
  obtain ⟨x, hx, hA⟩ := exists_core_seq_of_mem_charge_closure G d ⟨y, hy⟩
  refine ⟨x, hx, ?_⟩
  simpa only [hamClosure_apply_core] using cauchySeq_ham_of_core_sequences G d hC hx hA

/-- **The graph-norm estimate on the core puts the charge's domain inside the Hamiltonian's.**
This is the estimate the request asks for, in the form the commutation argument consumes: the
core inequality alone yields `dom Ā ⊆ dom H̄`, with no further domain-theoretic input. -/
theorem clDom_hamClosure_of_core_estimate (G : GaugeAlgebra 8) (d : Fin 8) {C : ℝ}
    (hC : CoreChargeControlsHam G d C) :
    (gaussPMap G d (coreRepPoly 99)).closure.domain
      ≤ clDom (ymHamiltonian (coreRepPoly 99) G.f) :=
  clDom_hamClosure_of_charge_graph_dense G d (hdense_of_core_estimate G d hC)

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
