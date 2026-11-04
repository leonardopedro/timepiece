import Mathlib
import BookProof.ChapterBrstHarmonicDecomposition

/-!
# The BRST harmonic decomposition for a closed densely defined charge

`ChapterBrstHarmonicDecomposition` proves the Hodge-type decomposition of the BRST complex —
`H = (ker Ω ⊓ ker Ω†) ⊕ closure (range Ω) ⊕ closure (range Ω†)`, and the identity that the
quotient (BRST) norm of a class is the norm of its harmonic representative — for a **bounded**
nilpotent charge `Ω`.  Its docstring records the unbounded case as the first thing it does not
do: the field-theoretic charge is a cubic differential operator, so the decomposition has to be
reproved for a closed, densely defined `Ω`.

This chapter does that.  The charge is now a partially defined linear map
`Om : H →ₗ.[ℂ] H` (Mathlib's `LinearPMap`), with three hypotheses:

* **`HasClosedGraph`** — `Om.graph` is closed in `H × H`.  Closedness is the extra input the
  unbounded case needs and a bounded `Ω` gets for free; it is what closes the physical subspace
  (`isClosed_physicalStates`), which in the bounded chapter was automatic from continuity.
* **`Dense (Om.domain)`** — density is exactly what makes the Hilbert adjoint a *function*:
  the vector representing `x ↦ ⟪Ω x, y⟫` is unique by `adjoint_unique` (the difference of two
  representatives is orthogonal to the domain, hence zero).  In the bounded chapter the adjoint
  was `ContinuousLinearMap.adjoint`; here it is built by hand from the representing vector,
  because no bounded adjoint exists.
* **`IsNilpotent`** — `Ω` maps its domain into itself and `Ω² = 0` there.  For a total map this
  is `∀ x, Ω (Ω x) = 0`; for a partial one the domain clause cannot be dropped, since `Ω x`
  need not be defined again.

## What is proved

The chapter mirrors the bounded one theorem for theorem, so the two can be read side by side:

* `physicalStates`, `mem_physicalStates` (`x ∈ ker Ω`), `isClosed_physicalStates`;
* `exactStates` (`closure (range Ω)`), `mem_exactStates_of_apply`, `isClosed_exactStates`, and
  **`exactStates_le_physicalStates`**: nilpotency puts the exact states inside the physical
  ones — the step that makes the cohomology `physicalStates ⧸ exactStates` exist;
* `adjointDomain`, `adjointFun`, `adjoint` — the Hilbert adjoint of the unbounded charge — and
  `adjoint_apply`, its defining relation;
* `adjointKernel`, **`range_orthogonal_eq_adjointKernel`**: `(range Ω)ᗮ = ker Ω†`, which is where
  density is used, and **`exactStates_orthogonal`**: `(closure (range Ω))ᗮ = ker Ω†`;
* `harmonicStates` (`ker Ω ⊓ ker Ω†`), `harmonicStates_eq`,
  **`sup_exact_harmonic`** (`exact ⊔ harmonic = physical`) and **`disjoint_exact_harmonic`**;
* `coexactStates`, `orthogonal_orthogonal_eq_self_of_isClosed`, `coexact_sup_physicalStates`,
  **`hodge_decomposition`** (`harmonic ⊔ exact ⊔ coexact = ⊤`) and the pairwise orthogonality
  lemmas `disjoint_exact_coexact`, `disjoint_harmonic_coexact`;
* in §7, the identification of the coexact sector with the adjoint's range closure —
  `adjoint_adjoint_of_isClosed`, `graph_adjoint`, `adjoint_adjoint_eq`, `adjoint_domain_dense`,
  `range_adjoint_orthogonal` and **`closure_range_adjoint_eq_coexact`**;
* `harmonicPart`, `sub_harmonicPart_mem_exact`, `harmonicPart_mem`,
  **`infDist_eq_norm_harmonicPart`** — the quotient norm is the norm of the harmonic
  representative, and the infimum is attained —, `harmonicPart_eq_of_sub_mem_exact` (the
  representative is a function of the cohomology class),
  `exists_harmonic_decomposition`, and `infDist_eq_norm_of_harmonic_decomposition` (the abstract
  form, independent of which projection produces the decomposition).

Nothing in the quotient-norm part needs closedness or density: the exact states are a closure,
hence complete, so the orthogonal projection onto them exists for *any* charge.  Closedness and
density are what make the physical sector closed and name the summands `ker Ω†`.

## The third summand is the adjoint's range (von Neumann)

In the bounded chapter the coexact sector was `closure (range Ω†)`, and its orthogonal complement
was `ker Ω` by `ContinuousLinearMap.orthogonal_range` applied twice (`Ω†† = Ω`).  Here the
coexact sector is defined as `(ker Ω)ᗮ`, which is the *same* space exactly because of von
Neumann's closed-range theorem,

  `closure (range Ω†) = (ker Ω)ᗮ`   (`closure_range_adjoint_eq_coexact`),

equivalently `Ω†† = Ω` for a closed densely defined `Ω` (`adjoint_adjoint_eq`).  Section 7 proves
this, so the naming of the third summand is complete in the unbounded case too, and the two
chapters can be read side by side after all.  The one inclusion that needs nothing is
`range_adjoint_le_coexact`; it is now sharpened to equality of closures.

The proof is the graph rotation.  `Submodule.adjoint` sends a submodule `g ≤ H × H` to the
rotation of its orthogonal complement inside `WithLp 2 (H × H)`, and its defining relation is
`(c, d) ∈ g.adjoint ↔ ∀ (a, b) ∈ g, ⟪a, d⟫ = ⟪b, c⟫` (`mem_adjoint_iff_pairing`); then

* `adjoint_adjoint_of_isClosed` — rotation is an involution on **closed** graphs.  Closedness of
  `Ω` enters only here: the proof projects `x ∉ g` onto `g` in the Hilbert product and rotates the
  normal direction, which violates the defining relation for `x`;
* `graph_adjoint` — `Ω†.graph = Ω.graph.adjoint`, where density of `Ω.domain` is what makes the
  representing vector of `x ↦ ⟪Ω x, y⟫` unique;
* hence `Ω†† = Ω` and `Ω†` is itself densely defined (`adjoint_domain_dense`) — a closed operator
  passes closedness and density to its adjoint, which is what lets `Ω†` be treated as a charge;
* finally `y ⊥ range Ω† ↔ (y, 0) ∈ Ω†.graph.adjoint = Ω.graph ↔ Ω y = 0`, which is
  `range_adjoint_orthogonal`, and a double orthogonal complement turns it into the identification.

Everything is `sorry`-free.
-/

noncomputable section

namespace BookProof.BrstUnbounded

open BookProof.BrstReducedTransfer
open scoped InnerProductSpace ComplexInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (Om : H →ₗ.[ℂ] H)

/-! ## 0. The hypotheses on the charge -/

/-- **The charge has a closed graph.**  A bounded charge satisfies this automatically; for a
field-theoretic one it is the closedness that lets the adjoint be defined and that closes the
kernel. -/
def HasClosedGraph : Prop := IsClosed (Om.graph : Set (H × H))

/-- **Nilpotency of a partial charge**: `Ω` preserves its domain and `Ω² = 0` there.  For a
total operator this is `∀ x, Ω (Ω x) = 0`; the domain clause is not removable, because `Ω x`
need not lie in the domain of `Ω`. -/
def IsNilpotent : Prop := ∀ x : Om.domain, ∃ (h : (Om x) ∈ Om.domain), Om ⟨Om x, h⟩ = 0

/-! ## 1. The physical (BRST-closed) states -/

/-- The **physical states** `ker Ω`.  Defined through the graph, so that closedness of the
operator becomes closedness of the subspace by a single preimage. -/
def physicalStates : Submodule ℂ H :=
  Om.graph.comap ((LinearMap.id : H →ₗ[ℂ] H).prod (0 : H →ₗ[ℂ] H))

omit [CompleteSpace H] in
theorem mem_physicalStates_iff_graph (x : H) :
    x ∈ physicalStates Om ↔ (x, (0 : H)) ∈ Om.graph := by
  simp [physicalStates]

omit [CompleteSpace H] in
/-- Membership in the physical states, unfolded: the state is in the domain and the charge
kills it. -/
theorem mem_physicalStates {x : H} :
    x ∈ physicalStates Om ↔ ∃ h : x ∈ Om.domain, Om ⟨x, h⟩ = 0 := by
  rw [mem_physicalStates_iff_graph]
  constructor
  · intro hx
    obtain ⟨y, hy, h0⟩ := (LinearPMap.mem_graph_iff (Om)).mp hx
    have hyx : (y : H) = x := hy
    refine ⟨hyx ▸ y.2, ?_⟩
    rw [show (⟨x, hyx ▸ y.2⟩ : Om.domain) = y from Subtype.ext hyx.symm]
    exact h0
  · rintro ⟨h, h0⟩
    exact (LinearPMap.mem_graph_iff (Om)).mpr ⟨⟨x, h⟩, rfl, h0⟩

omit [CompleteSpace H] in
/-- **The kernel of a closed operator is closed.**  For a bounded charge this is
`ContinuousLinearMap.isClosed_ker`; here it is closedness of the graph, pulled back along the
continuous embedding `x ↦ (x, 0)`.  This is the step the bounded chapter did not need. -/
theorem isClosed_physicalStates (hcl : HasClosedGraph Om) :
    IsClosed (physicalStates Om : Set H) := by
  have hcoe : (physicalStates Om : Set H)
      = (fun x : H => (x, (0 : H))) ⁻¹' (Om.graph : Set (H × H)) := by
    ext x
    exact mem_physicalStates_iff_graph Om x
  rw [hcoe]
  exact hcl.preimage (continuous_id.prodMk continuous_const)

/-! ## 2. The exact (pure gauge) states, and nilpotency -/

/-- The **exact states**: the closure of the range of the charge. -/
def exactStates : Submodule ℂ H := (LinearMap.range Om.toFun).topologicalClosure

omit [CompleteSpace H] in
theorem mem_exactStates_of_apply (x : Om.domain) : Om x ∈ exactStates Om :=
  Submodule.le_topologicalClosure _ ⟨x, rfl⟩

omit [CompleteSpace H] in
theorem isClosed_exactStates : IsClosed (exactStates Om : Set H) :=
  Submodule.isClosed_topologicalClosure _

instance : CompleteSpace (exactStates Om : Submodule ℂ H) :=
  (isClosed_exactStates Om).completeSpace_coe

omit [CompleteSpace H] in
/-- **Nilpotency puts the exact states inside the physical ones.**  A state in the range is
`Ω x`; nilpotency says `Ω (Ω x) = 0`, so it is closed, and the physical states are closed. -/
theorem exactStates_le_physicalStates (hcl : HasClosedGraph Om) (hnil : IsNilpotent Om) :
    exactStates Om ≤ physicalStates Om := by
  refine Submodule.topologicalClosure_minimal _ ?_ (isClosed_physicalStates Om hcl)
  rintro y ⟨x, rfl⟩
  exact (mem_physicalStates (Om := Om)).mpr (hnil x)

/-! ## 3. The Hilbert adjoint of a densely defined charge -/

/-- The domain of the adjoint: those `y` for which `x ↦ ⟪Ω x, y⟫` is the restriction of an
inner product functional.  Density of the domain makes the representing vector unique. -/
def adjointDomain : Submodule ℂ H where
  carrier := {y : H | ∃ z : H, ∀ x : Om.domain, ⟪(x : H), z⟫ = ⟪Om x, y⟫}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro y₁ y₂ ⟨z₁, h₁⟩ ⟨z₂, h₂⟩
    exact ⟨z₁ + z₂, fun x => by rw [inner_add_right, h₁ x, h₂ x, inner_add_right]⟩
  smul_mem' := by
    rintro c y ⟨z, h⟩
    exact ⟨c • z, fun x => by rw [inner_smul_right, h x, inner_smul_right]⟩

omit [CompleteSpace H] in
theorem mem_adjointDomain {y : H} :
    y ∈ adjointDomain Om ↔ ∃ z : H, ∀ x : Om.domain, ⟪(x : H), z⟫ = ⟪Om x, y⟫ :=
  Iff.rfl

omit [CompleteSpace H] in
/-- The orthogonal complement of a dense submodule is trivial.  This is the only place where
density of the domain is used. -/
theorem orthogonal_eq_bot_of_dense (K : Submodule ℂ H) (hK : Dense (K : Set H)) :
    Kᗮ = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Submodule.mem_orthogonal] at hz
  have hzero : ⟪z, z⟫ = 0 := by
    have htop : K.topologicalClosure = ⊤ :=
      Submodule.dense_iff_topologicalClosure_eq_top.mp hK
    have hall : ∀ y ∈ K.topologicalClosure, ⟪y, z⟫ = 0 :=
      (Submodule.orthogonal_closure' K z).mp hz
    rw [htop] at hall
    exact hall z Submodule.mem_top
  simpa using inner_self_eq_zero.mp hzero

omit [CompleteSpace H] in
/-- **Density makes the representing vector unique.**  Two vectors realizing the same functional
differ by a vector orthogonal to the whole (dense) domain, hence vanish. -/
theorem adjoint_unique (hdense : Dense (Om.domain : Set H)) {y z₁ z₂ : H}
    (h₁ : ∀ x : Om.domain, ⟪(x : H), z₁⟫ = ⟪Om x, y⟫)
    (h₂ : ∀ x : Om.domain, ⟪(x : H), z₂⟫ = ⟪Om x, y⟫) : z₁ = z₂ := by
  have hmem : z₁ - z₂ ∈ (Om.domain)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    have h1 := h₁ ⟨u, hu⟩
    have h2 := h₂ ⟨u, hu⟩
    rw [inner_sub_right, h1, h2]
    exact sub_self _
  rw [orthogonal_eq_bot_of_dense (Om.domain) hdense] at hmem
  exact sub_eq_zero.mp (by simpa using hmem)

omit [CompleteSpace H] in
/-- The representing vector exists and is unique on the adjoint domain. -/
theorem adjoint_existsUnique (hdense : Dense (Om.domain : Set H)) {y : H}
    (hy : y ∈ adjointDomain Om) :
    ∃! z : H, ∀ x : Om.domain, ⟪(x : H), z⟫ = ⟪Om x, y⟫ := by
  obtain ⟨z, hz⟩ := hy
  exact ⟨z, hz, fun z' hz' => adjoint_unique Om hdense hz' hz⟩

/-- The adjoint as a linear map on its domain, from the representing vector.  Linearity is
`adjoint_unique` applied to the sum resp. the scalar multiple of two witnesses. -/
noncomputable def adjointFun (hdense : Dense (Om.domain : Set H)) :
    adjointDomain Om →ₗ[ℂ] H where
  toFun y := Classical.choose y.2
  map_add' := by
    intro y₁ y₂
    have hbase : ((y₁ + y₂ : adjointDomain Om) : H) = (y₁ : H) + (y₂ : H) := rfl
    refine adjoint_unique Om hdense (Classical.choose_spec ((y₁ + y₂).2)) ?_
    intro x
    have h1 := Classical.choose_spec y₁.2 x
    have h2 := Classical.choose_spec y₂.2 x
    calc ⟪(x : H), Classical.choose y₁.2 + Classical.choose y₂.2⟫
        = ⟪(x : H), Classical.choose y₁.2⟫ + ⟪(x : H), Classical.choose y₂.2⟫ :=
          inner_add_right _ _ _
      _ = ⟪Om x, (y₁ : H)⟫ + ⟪Om x, (y₂ : H)⟫ := by rw [h1, h2]
      _ = ⟪Om x, (y₁ : H) + (y₂ : H)⟫ := (inner_add_right _ _ _).symm
      _ = ⟪Om x, ((y₁ + y₂ : adjointDomain Om) : H)⟫ := by rw [hbase]
  map_smul' := by
    intro c y
    have hbase : ((c • y : adjointDomain Om) : H) = c • (y : H) := rfl
    refine adjoint_unique Om hdense (Classical.choose_spec ((c • y).2)) ?_
    intro x
    have h1 := Classical.choose_spec y.2 x
    calc ⟪(x : H), c • Classical.choose y.2⟫ = c * ⟪(x : H), Classical.choose y.2⟫ := by
          rw [inner_smul_right]
      _ = c * ⟪Om x, (y : H)⟫ := by rw [h1]
      _ = ⟪Om x, c • (y : H)⟫ := by rw [inner_smul_right]
      _ = ⟪Om x, ((c • y : adjointDomain Om) : H)⟫ := by rw [hbase]

/-- **The Hilbert adjoint of a closed, densely defined charge**, as a partial linear map. -/
def adjoint (hdense : Dense (Om.domain : Set H)) : H →ₗ.[ℂ] H :=
  ⟨adjointDomain Om, adjointFun Om hdense⟩

omit [CompleteSpace H] in
/-- The defining relation of the adjoint. -/
theorem adjoint_apply (hdense : Dense (Om.domain : Set H))
    (y : (adjoint Om hdense).domain) (x : Om.domain) :
    ⟪(x : H), (adjoint Om hdense) y⟫ = ⟪Om x, (y : H)⟫ :=
  Classical.choose_spec y.2 x

/-- The **kernel of the adjoint**, as a subspace of `H`: the co-closed directions. -/
def adjointKernel (hdense : Dense (Om.domain : Set H)) : Submodule ℂ H :=
  (LinearMap.ker (adjoint Om hdense).toFun).map (adjoint Om hdense).domain.subtype

omit [CompleteSpace H] in
theorem mem_adjointKernel (hdense : Dense (Om.domain : Set H)) {y : H} :
    y ∈ adjointKernel Om hdense ↔
      ∃ (hy : y ∈ adjointDomain Om), adjointFun Om hdense ⟨y, hy⟩ = 0 := by
  rw [adjointKernel, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    rw [LinearMap.mem_ker] at hz
    refine ⟨hzy ▸ z.2, ?_⟩
    rw [show (⟨y, hzy ▸ z.2⟩ : adjointDomain Om) = z from Subtype.ext hzy.symm]
    exact hz
  · rintro ⟨hy, h0⟩
    exact ⟨⟨y, hy⟩, by rwa [LinearMap.mem_ker], rfl⟩

omit [CompleteSpace H] in
/-- The adjoint vanishes exactly on the vectors orthogonal to its own action. -/
theorem adjointFun_eq_zero_iff (hdense : Dense (Om.domain : Set H))
    {y : adjointDomain Om} :
    adjointFun Om hdense y = 0 ↔ ∀ x : Om.domain, ⟪Om x, (y : H)⟫ = 0 := by
  have hspec : ∀ x : Om.domain, ⟪(x : H), adjointFun Om hdense y⟫ = ⟪Om x, (y : H)⟫ :=
    fun x => Classical.choose_spec y.2 x
  constructor
  · intro h x
    calc ⟪Om x, (y : H)⟫ = ⟪(x : H), adjointFun Om hdense y⟫ := (hspec x).symm
      _ = ⟪(x : H), (0 : H)⟫ := by rw [h]
      _ = 0 := inner_zero_right _
  · intro h
    refine adjoint_unique Om hdense hspec ?_
    intro x
    rw [h x]
    simp

omit [CompleteSpace H] in
/-- **The orthogonal complement of the range is the kernel of the adjoint.**  The unbounded
analogue of `ContinuousLinearMap.orthogonal_range`; the inclusion `⊆` is where density of the
domain enters, because the representing vector produced there is `0`. -/
theorem range_orthogonal_eq_adjointKernel (hdense : Dense (Om.domain : Set H)) :
    (LinearMap.range Om.toFun)ᗮ = adjointKernel Om hdense := by
  ext y
  rw [Submodule.mem_orthogonal, mem_adjointKernel]
  constructor
  · intro h
    have hpos : y ∈ adjointDomain Om :=
      ⟨0, fun x => by simpa using (h (Om x) ⟨x, rfl⟩).symm⟩
    exact ⟨hpos, (adjointFun_eq_zero_iff Om hdense).mpr fun x => h (Om x) ⟨x, rfl⟩⟩
  · rintro ⟨hy, h0⟩ u ⟨x, rfl⟩
    exact (adjointFun_eq_zero_iff Om hdense).mp h0 x

omit [CompleteSpace H] in
/-- **`(closure (range Ω))ᗮ = ker Ω†`.**  The closure costs nothing: the orthogonal complement
of a closure is the orthogonal complement of the set. -/
theorem exactStates_orthogonal (hdense : Dense (Om.domain : Set H)) :
    (exactStates Om)ᗮ = adjointKernel Om hdense := by
  rw [exactStates, Submodule.orthogonal_closure]
  exact range_orthogonal_eq_adjointKernel Om hdense

/-! ## 4. The harmonic states and the decomposition of the physical sector -/

/-- The **harmonic (BRST-invariant) states** `ker Ω ⊓ ker Ω†`: closed *and* co-closed. -/
def harmonicStates (hdense : Dense (Om.domain : Set H)) : Submodule ℂ H :=
  physicalStates Om ⊓ adjointKernel Om hdense

omit [CompleteSpace H] in
/-- The harmonic states are the physical ones intersected with the orthogonal complement of the
exact ones — the form in which the projection argument uses them. -/
theorem harmonicStates_eq (hdense : Dense (Om.domain : Set H)) :
    harmonicStates Om hdense = physicalStates Om ⊓ (exactStates Om)ᗮ := by
  rw [harmonicStates, exactStates_orthogonal Om hdense]

/-- **Every closed state is a gauge part plus a harmonic part**:
`exact ⊔ harmonic = physical`.  Only `HasOrthogonalProjection` of the exact states is needed,
which they have because they are closed — no continuity of `Ω` enters. -/
theorem sup_exact_harmonic (hcl : HasClosedGraph Om) (hnil : IsNilpotent Om)
    (hdense : Dense (Om.domain : Set H)) :
    exactStates Om ⊔ harmonicStates Om hdense = physicalStates Om := by
  have hle : exactStates Om ≤ physicalStates Om := exactStates_le_physicalStates Om hcl hnil
  have h := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (K₁ := exactStates Om)
    (K₂ := physicalStates Om) hle
  rw [inf_comm, ← harmonicStates_eq] at h
  exact h

omit [CompleteSpace H] in
/-- The exact and harmonic summands are orthogonal, so the sum is direct. -/
theorem disjoint_exact_harmonic (hdense : Dense (Om.domain : Set H)) :
    Disjoint (exactStates Om) (harmonicStates Om hdense) := by
  have hle : harmonicStates Om hdense ≤ (exactStates Om)ᗮ := by
    rw [harmonicStates_eq]
    exact inf_le_right
  exact (exactStates Om).orthogonal_disjoint.mono_right hle

/-! ## 5. The coexact sector and the full Hodge decomposition -/

/-- The **coexact states**.  In the bounded chapter this is `closure (range Ω†)`, which coincides
with `(ker Ω)ᗮ` there; the identification is von Neumann's theorem, proved for this setting in
§7 as `closure_range_adjoint_eq_coexact`, so the sector is defined as `(ker Ω)ᗮ` — the space the
decomposition actually uses — without circularity. -/
def coexactStates : Submodule ℂ H := (physicalStates Om)ᗮ

/-- A closed submodule is its own double orthogonal complement. -/
theorem orthogonal_orthogonal_eq_self_of_isClosed (hcl : HasClosedGraph Om) :
    (coexactStates Om)ᗮ = physicalStates Om := by
  have hclos : IsClosed (physicalStates Om : Set H) := isClosed_physicalStates Om hcl
  have htop : (physicalStates Om).topologicalClosure = physicalStates Om :=
    le_antisymm (Submodule.topologicalClosure_minimal _ le_rfl hclos)
      (Submodule.le_topologicalClosure _)
  rw [coexactStates, Submodule.orthogonal_orthogonal_eq_closure, htop]

omit [CompleteSpace H] in
/-- **The range of the adjoint lies in the coexact sector**: the adjoint's range is orthogonal to
`ker Ω`.  This is the easy inclusion of von Neumann's theorem, and §7 upgrades it to an equality
of closures. -/
theorem range_adjoint_le_coexact (hdense : Dense (Om.domain : Set H)) :
    LinearMap.range (adjoint Om hdense).toFun ≤ coexactStates Om := by
  rintro y ⟨z, rfl⟩
  rw [coexactStates, Submodule.mem_orthogonal]
  intro v hv
  obtain ⟨hvD, hv0⟩ := (mem_physicalStates (Om := Om)).mp hv
  calc ⟪v, (adjoint Om hdense) z⟫ = ⟪Om ⟨v, hvD⟩, (z : H)⟫ :=
        adjoint_apply Om hdense z ⟨v, hvD⟩
    _ = ⟪(0 : H), (z : H)⟫ := by rw [hv0]
    _ = 0 := inner_zero_left _

/-- **The coexact states together with the physical ones fill the space.** -/
theorem coexact_sup_physicalStates (hcl : HasClosedGraph Om) :
    coexactStates Om ⊔ physicalStates Om = ⊤ := by
  haveI : CompleteSpace (physicalStates Om : Submodule ℂ H) :=
    (isClosed_physicalStates Om hcl).completeSpace_coe
  rw [coexactStates, sup_comm]
  exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

/-- **The Hodge decomposition of the BRST complex of a closed densely defined charge**:
`H = harmonic ⊕ closure (range Ω) ⊕ (ker Ω)ᗮ`, with pairwise orthogonal summands. -/
theorem hodge_decomposition (hcl : HasClosedGraph Om) (hnil : IsNilpotent Om)
    (hdense : Dense (Om.domain : Set H)) :
    harmonicStates Om hdense ⊔ exactStates Om ⊔ coexactStates Om = ⊤ := by
  rw [sup_comm (harmonicStates Om hdense) (exactStates Om),
    sup_exact_harmonic Om hcl hnil hdense,
    sup_comm (physicalStates Om) (coexactStates Om), coexact_sup_physicalStates Om hcl]

/-- The exact states are orthogonal to the coexact ones: they are closed, so lie in
`(coexact)ᗮ = ker Ω`. -/
theorem disjoint_exact_coexact (hcl : HasClosedGraph Om) (hnil : IsNilpotent Om) :
    Disjoint (exactStates Om) (coexactStates Om) := by
  have hle : exactStates Om ≤ (coexactStates Om)ᗮ := by
    rw [orthogonal_orthogonal_eq_self_of_isClosed Om hcl]
    exact exactStates_le_physicalStates Om hcl hnil
  exact (coexactStates Om).orthogonal_disjoint.symm.mono_left hle

omit [CompleteSpace H] in
/-- The harmonic states are orthogonal to the coexact ones, being closed. -/
theorem disjoint_harmonic_coexact (hdense : Dense (Om.domain : Set H)) :
    Disjoint (harmonicStates Om hdense) (coexactStates Om) := by
  have hle : harmonicStates Om hdense ≤ (coexactStates Om)ᗮ := by
    rw [coexactStates]
    exact ((harmonicStates_eq Om hdense).le.trans inf_le_left).trans
      (Submodule.le_orthogonal_orthogonal _)
  exact (coexactStates Om).orthogonal_disjoint.symm.mono_left hle

/-! ## 6. The harmonic representative and the quotient norm -/

/-- **The harmonic representative** of a state: the state minus its projection on the exact
directions. -/
def harmonicPart (x : H) : H := x - (exactStates Om).starProjection x

/-- The remainder is exact: it is the projection itself. -/
theorem sub_harmonicPart_mem_exact (x : H) : x - harmonicPart Om x ∈ exactStates Om := by
  simp only [harmonicPart, sub_sub_cancel]
  exact (exactStates Om).starProjection_apply_mem x

/-- The harmonic representative of a **closed** state is harmonic: it stays closed, since the
exact states are physical by nilpotency, and it is co-closed because the remainder lies in
`(exact)ᗮ = ker Ω†`. -/
theorem harmonicPart_mem (hcl : HasClosedGraph Om) (hnil : IsNilpotent Om)
    (hdense : Dense (Om.domain : Set H)) {x : H} (hx : x ∈ physicalStates Om) :
    harmonicPart Om x ∈ harmonicStates Om hdense := by
  have hle : exactStates Om ≤ physicalStates Om := exactStates_le_physicalStates Om hcl hnil
  refine ⟨?_, ?_⟩
  · exact (physicalStates Om).sub_mem hx (hle ((exactStates Om).starProjection_apply_mem x))
  · rw [← exactStates_orthogonal Om hdense]
    exact Submodule.sub_starProjection_mem_orthogonal (K := exactStates Om) x

/-- **The quotient (BRST) norm is the norm of the harmonic representative.**  The infimum
defining `Metric.infDist` is attained, so the harmonic norm is a genuine norm on the cohomology
and not an infimum over a set that never realizes it. -/
theorem infDist_eq_norm_harmonicPart (x : H) :
    Metric.infDist x (exactStates Om) = ‖harmonicPart Om x‖ := by
  rw [Metric.infDist_eq_iInf]
  simpa only [harmonicPart, dist_eq_norm, norm_sub_rev] using
    (Submodule.starProjection_minimal (U := exactStates Om) x).symm

/-- **The harmonic representative depends only on the cohomology class**: states differing by an
exact vector have the same harmonic part, so `‖harmonicPart ·‖` is a function of the class — and
with `infDist_eq_norm_harmonicPart` it *is* the quotient norm. -/
theorem harmonicPart_eq_of_sub_mem_exact {x y : H} (h : x - y ∈ exactStates Om) :
    harmonicPart Om x = harmonicPart Om y := by
  have hK : (x - (exactStates Om).starProjection x)
      - (y - (exactStates Om).starProjection y) ∈ exactStates Om := by
    have hmid : (exactStates Om).starProjection x - (exactStates Om).starProjection y
        ∈ exactStates Om :=
      (exactStates Om).sub_mem ((exactStates Om).starProjection_apply_mem x)
        ((exactStates Om).starProjection_apply_mem y)
    have heq : (x - (exactStates Om).starProjection x)
        - (y - (exactStates Om).starProjection y)
        = (x - y) - ((exactStates Om).starProjection x - (exactStates Om).starProjection y) := by
      abel
    rw [heq]
    exact (exactStates Om).sub_mem h hmid
  have hK' : (x - (exactStates Om).starProjection x)
      - (y - (exactStates Om).starProjection y) ∈ (exactStates Om)ᗮ :=
    Submodule.sub_mem _ (Submodule.sub_starProjection_mem_orthogonal (K := exactStates Om) x)
      (Submodule.sub_starProjection_mem_orthogonal (K := exactStates Om) y)
  have hzero : (x - (exactStates Om).starProjection x)
      - (y - (exactStates Om).starProjection y) = 0 := by
    have hmem : (x - (exactStates Om).starProjection x)
        - (y - (exactStates Om).starProjection y) ∈ (exactStates Om) ⊓ (exactStates Om)ᗮ :=
      ⟨hK, hK'⟩
    rw [(exactStates Om).orthogonal_disjoint.eq_bot] at hmem
    simpa using hmem
  simp only [harmonicPart] at hzero ⊢
  exact sub_eq_zero.mp hzero

/-- **The decomposition of a closed state into harmonic and exact parts, with the orthogonality
explicit.**  This is the Hodge decomposition of a single physical state, in the form in which
the quotient norm is read off it. -/
theorem exists_harmonic_decomposition (hcl : HasClosedGraph Om) (hnil : IsNilpotent Om)
    (hdense : Dense (Om.domain : Set H)) {x : H} (hx : x ∈ physicalStates Om) :
    ∃ h ∈ harmonicStates Om hdense, ∃ e ∈ exactStates Om,
      x = h + e ∧ ∀ y ∈ exactStates Om, ⟪y, h⟫ = 0 := by
  refine ⟨harmonicPart Om x, harmonicPart_mem Om hcl hnil hdense hx,
    (exactStates Om).starProjection x, (exactStates Om).starProjection_apply_mem x, ?_, ?_⟩
  · simp [harmonicPart]
  · intro y hy
    have h := Submodule.sub_starProjection_mem_orthogonal (K := exactStates Om) x
    rw [Submodule.mem_orthogonal] at h
    exact h y hy

/-- **The abstract form of the quotient-norm identity**: any orthogonal decomposition of a state
into a harmonic and an exact part realizes the distance to the exact states as the norm of the
harmonic part.  So `infDist_eq_norm_harmonicPart` does not depend on which projection produces
the decomposition. -/
theorem infDist_eq_norm_of_harmonic_decomposition {x h e : H}
    (hx : x = h + e) (he : e ∈ exactStates Om)
    (horth : ∀ y ∈ exactStates Om, ⟪y, h⟫ = 0) :
    Metric.infDist x (exactStates Om) = ‖h‖ := by
  have hproj : (exactStates Om).starProjection x = e := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero he ?_
    intro w hw
    rw [show x - e = h by rw [hx]; abel, inner_eq_zero_symm]
    exact horth w hw
  have hxe : x - e = h := by rw [hx]; abel
  rw [infDist_eq_norm_harmonicPart Om x, harmonicPart, hproj, hxe]

/-! ## 7. von Neumann's closed-range theorem

The third summand of the Hodge decomposition is `coexactStates Om = (ker Ω)ᗮ`.  The bounded
chapter could name it `closure (range Ω†)`, because for a bounded `Ω` the double adjoint is `Ω`
again (`ContinuousLinearMap.adjoint_adjoint`) and `(range Ω†)ᗮᗮ = range Ω†`.  Unbounded, the
identification `closure (range Ω†) = (ker Ω)ᗮ` is von Neumann's closed-range theorem, and it is
what this section proves.

Everything rests on a single device: **the graph of the adjoint is the rotated graph**.  Concretely,
Mathlib's `Submodule.adjoint` sends a submodule `g ≤ H × H` to

  `g.adjoint = {x | ∀ (a, b) ∈ g, ⟪b, x.1⟫ - ⟪a, x.2⟫ = 0}`   (`Submodule.mem_adjoint_iff`)

and `adjoint_graph_eq_graph_adjoint` says `T†.graph = T.graph.adjoint`.  The two facts we need are

* `adjoint_adjoint_of_isClosed` — `g.adjoint.adjoint = g` for a **closed** `g`, i.e. rotation is an
  involution on closed graphs.  This is the one place where closedness of `Ω` is essential and
  where the Hilbert structure of the product `WithLp 2 (H × H)` (Mathlib's `Submodule.adjoint`
  lives there) is used: the proof projects `x ∉ g` onto `g` and rotates the normal direction.
* `graph_adjoint` — `(Ω†).graph = Ω.graph.adjoint`, which uses density of `Ω.domain` for the
  uniqueness of the representing vector, not closedness.

Composing them gives `Ω†† = Ω` (hence density of `Ω†.domain`, which is what makes `Ω†` a
legitimate charge in its own right), and orthogonality then identifies the two sectors:
`y ⊥ range Ω†` iff `(y, 0) ∈ Ω†.graph.adjoint = Ω.graph`, i.e. iff `Ω y = 0`. -/

section VonNeumann

/-- A submodule of `H × H` pushed into the Hilbert product `WithLp 2 (H × H)`, where Mathlib's
`Submodule.adjoint` takes its orthogonal complement. -/
def pairSpace (g : Submodule ℂ (H × H)) : Submodule ℂ (WithLp 2 (H × H)) :=
  g.comap (WithLp.prodContinuousLinearEquiv 2 ℂ H H).toLinearMap

omit [CompleteSpace H] in
theorem mem_pairSpace {g : Submodule ℂ (H × H)} {x : WithLp 2 (H × H)} :
    x ∈ pairSpace g ↔ WithLp.ofLp x ∈ g := by
  simp [pairSpace]

omit [CompleteSpace H] in
theorem isClosed_pairSpace {g : Submodule ℂ (H × H)} (hg : IsClosed (g : Set (H × H))) :
    IsClosed (pairSpace g : Set (WithLp 2 (H × H))) :=
  hg.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ H H).continuous

omit [CompleteSpace H] in
/-- The orthogonal complement inside `WithLp 2 (H × H)`, written with the two coordinate
pairings: this is the form in which `Submodule.mem_adjoint_iff` uses it. -/
theorem mem_pairSpace_orthogonal {g : Submodule ℂ (H × H)} {x : WithLp 2 (H × H)} :
    x ∈ (pairSpace g)ᗮ ↔
      ∀ a b : H, (a, b) ∈ g → ⟪a, (WithLp.ofLp x).1⟫ + ⟪b, (WithLp.ofLp x).2⟫ = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h a b hab
    have hm : WithLp.toLp 2 (a, b) ∈ pairSpace g := by
      rw [mem_pairSpace]
      simpa using hab
    have := h _ hm
    rwa [WithLp.prod_inner_apply, WithLp.ofLp_toLp] at this
  · intro h y hy
    rw [mem_pairSpace] at hy
    rw [WithLp.prod_inner_apply]
    exact h _ _ hy

omit [CompleteSpace H] in
/-- `Submodule.mem_adjoint_iff` with the ordering of the two pairings made explicit: the adjoint
of `g` is the set of `(c, d)` whose second coordinate pairs against `g` the way the first does. -/
theorem mem_adjoint_iff_pairing (g : Submodule ℂ (H × H)) (c d : H) :
    (c, d) ∈ g.adjoint ↔ ∀ a b : H, (a, b) ∈ g → ⟪a, d⟫ = ⟪b, c⟫ := by
  rw [Submodule.mem_adjoint_iff]
  constructor
  · intro h a b hab
    have h0 := h a b hab
    rw [sub_eq_zero] at h0
    exact h0.symm
  · intro h a b hab
    rw [h a b hab, sub_self]

/-- **Rotation is an involution on closed submodules of `H × H`**: `g.adjoint.adjoint = g`.

The inclusion `g ≤ g.adjoint.adjoint` is algebra.  For the converse, take `x ∉ g` with `g`
closed and project `x` onto `g` inside `WithLp 2 (H × H)`: the normal `w = x − p` is orthogonal
to `g` and nonzero, and `⟪x, w⟫ = ‖w‖² ≠ 0`.  Reading the two coordinates `(u, v)` of `w`, the
rotated vector `(v, −u)` lies in `g.adjoint` and *violates* the defining relation for `x`, so
`x ∉ g.adjoint.adjoint`. -/
theorem adjoint_adjoint_of_isClosed (g : Submodule ℂ (H × H))
    (hg : IsClosed (g : Set (H × H))) :
    g.adjoint.adjoint = g := by
  refine le_antisymm ?_ ?_
  · intro x hx
    by_contra hxg
    have hsc : IsClosed (pairSpace g : Set (WithLp 2 (H × H))) := isClosed_pairSpace hg
    haveI : CompleteSpace (pairSpace g : Submodule ℂ (WithLp 2 (H × H))) := hsc.completeSpace_coe
    set xP : WithLp 2 (H × H) := WithLp.toLp 2 x with hxP
    have hxPg : xP ∉ pairSpace g := by
      rw [mem_pairSpace, hxP]
      simpa using hxg
    set w : WithLp 2 (H × H) := xP - (pairSpace g).starProjection xP with hw
    have hw_orth : w ∈ (pairSpace g)ᗮ :=
      Submodule.sub_starProjection_mem_orthogonal (K := pairSpace g) xP
    have hw_ne : w ≠ 0 := by
      intro h0
      apply hxPg
      have hxw : xP = (pairSpace g).starProjection xP := by
        rw [hw] at h0
        simpa using sub_eq_zero.mp h0
      rw [hxw]
      exact (pairSpace g).starProjection_apply_mem xP
    have hsp : ⟪(pairSpace g).starProjection xP, w⟫ = 0 :=
      (Submodule.mem_orthogonal _ _).mp hw_orth _ ((pairSpace g).starProjection_apply_mem xP)
    have hsplit : ⟪xP, w⟫ = ⟪w, w⟫ := by
      have hxw : xP = (pairSpace g).starProjection xP + w := by rw [hw]; abel
      nth_rewrite 1 [hxw]
      rw [inner_add_left, hsp, zero_add]
    have hw_inner : ⟪xP, w⟫ ≠ 0 := by
      rw [hsplit]
      exact inner_self_ne_zero.mpr hw_ne
    have horth := (mem_pairSpace_orthogonal).mp hw_orth
    set u : H := (WithLp.ofLp w).1 with hu
    set v : H := (WithLp.ofLp w).2 with hv
    have hinner : ⟪x.1, u⟫ + ⟪x.2, v⟫ ≠ 0 := by
      have h0 := hw_inner
      rwa [hxP, WithLp.prod_inner_apply] at h0
    have hmem : (v, -u) ∈ g.adjoint := by
      rw [mem_adjoint_iff_pairing]
      intro a b hab
      have h0 := horth a b hab
      rw [inner_neg_right]
      linear_combination -h0
    have hv' := (Submodule.mem_adjoint_iff g.adjoint x).mp hx v (-u) hmem
    rw [inner_neg_left] at hv'
    have hdiff : ⟪u, x.1⟫ + ⟪v, x.2⟫ = 0 := by linear_combination -hv'
    exact hinner (by simpa using congrArg star hdiff)
  · intro x hx
    rw [Submodule.mem_adjoint_iff]
    intro a b hab
    have h := (mem_adjoint_iff_pairing g a b).mp hab x.1 x.2 hx
    rw [sub_eq_zero, ← inner_conj_symm b x.1, ← inner_conj_symm a x.2, h]

omit [CompleteSpace H] in
/-- **The graph of the adjoint is the rotated graph**, `Ω†.graph = Ω.graph.adjoint`.  Both sides
encode the same relation: `(y, z)` is on the left exactly when `⟪x, z⟫ = ⟪Ω x, y⟫` for all
`x ∈ dom Ω`, which is `Submodule.mem_adjoint_iff` spelled out.  Density of `Ω.domain` is used
to know that `z` — the representing vector of the functional `x ↦ ⟪Ω x, y⟫` — is unique. -/
theorem graph_adjoint (hdense : Dense (Om.domain : Set H)) :
    (adjoint Om hdense).graph = Om.graph.adjoint := by
  ext x
  rw [LinearPMap.mem_graph_iff, Submodule.mem_adjoint_iff]
  constructor
  · rintro ⟨w, hw₁, hw₂⟩ a b hab
    obtain ⟨u, hu₁, hu₂⟩ := (LinearPMap.mem_graph_iff Om).mp hab
    have hu₁' : (u : H) = a := hu₁
    have hu₂' : Om u = b := hu₂
    rw [← hu₁', ← hu₂', ← hw₁, ← hw₂, adjoint_apply Om hdense w u, sub_self]
  · intro h
    have hm : ∀ v : Om.domain, ⟪(v : H), x.2⟫ = ⟪Om v, x.1⟫ := by
      intro v
      have hv := h (v : H) (Om v) (LinearPMap.mem_graph Om v)
      rw [sub_eq_zero] at hv
      exact hv.symm
    refine ⟨⟨x.1, ⟨x.2, hm⟩⟩, rfl, ?_⟩
    exact adjoint_unique Om hdense (fun v => adjoint_apply Om hdense ⟨x.1, ⟨x.2, hm⟩⟩ v) hm

/-- **`Ω†† = Ω`** for a closed densely defined charge — von Neumann's theorem, i.e. the statement
that a closed operator is determined by its graph rotation twice. -/
theorem adjoint_adjoint_eq (hcl : HasClosedGraph Om) (hdense : Dense (Om.domain : Set H))
    (hdense' : Dense ((adjoint Om hdense).domain : Set H)) :
    adjoint (adjoint Om hdense) hdense' = Om := by
  refine LinearPMap.eq_of_eq_graph ?_
  rw [graph_adjoint (adjoint Om hdense) hdense', graph_adjoint Om hdense,
    adjoint_adjoint_of_isClosed Om.graph hcl]

/-- A submodule whose orthogonal complement vanishes is dense.  The density criterion
`Submodule.orthogonal_eq_bot_iff` is stated for submodules that admit an orthogonal projection,
i.e. closed ones, so it is applied to `K.topologicalClosure`. -/
theorem dense_of_orthogonal_eq_bot {K : Submodule ℂ H} (h : Kᗮ = ⊥) : Dense (K : Set H) := by
  haveI : CompleteSpace (K.topologicalClosure : Submodule ℂ H) :=
    (Submodule.isClosed_topologicalClosure K).completeSpace_coe
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    ← Submodule.orthogonal_eq_bot_iff (K := K.topologicalClosure), Submodule.orthogonal_closure]
  exact h

/-- **The adjoint of a closed densely defined operator is densely defined.**  If `w ⊥ Ω†.domain`
then `(0, w) ∈ Ω†.graph.adjoint = Ω.graph`, so `w = Ω 0 = 0`: the rotated graph has no vertical
lines.  This is what lets `Ω†` be treated as a charge in its own right. -/
theorem adjoint_domain_dense (hcl : HasClosedGraph Om) (hdense : Dense (Om.domain : Set H)) :
    Dense ((adjoint Om hdense).domain : Set H) := by
  refine dense_of_orthogonal_eq_bot (K := (adjoint Om hdense).domain) ?_
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  have hmem : ((0 : H), w) ∈ (adjoint Om hdense).graph.adjoint := by
    rw [Submodule.mem_adjoint_iff]
    intro a b hab
    obtain ⟨u, hu, _⟩ := (LinearPMap.mem_graph_iff (adjoint Om hdense)).mp hab
    have hu' : (u : H) = a := hu
    have hz := (Submodule.mem_orthogonal _ _).mp hw (u : H) u.2
    rw [inner_zero_right, zero_sub, neg_eq_zero, ← hu']
    exact hz
  have hg : ((0 : H), w) ∈ (Om.graph.adjoint).adjoint := by
    rwa [← graph_adjoint Om hdense]
  rw [adjoint_adjoint_of_isClosed Om.graph hcl] at hg
  obtain ⟨h, h1, h2⟩ := (LinearPMap.mem_graph_iff Om).mp hg
  have h2' : Om h = w := h2
  have hz : (h : Om.domain) = 0 := Subtype.ext (by simpa using h1)
  rw [← h2', hz]
  simp

/-- **`(range Ω†)ᗮ = ker Ω`.**  A state is orthogonal to the adjoint's range exactly when the
functional `z ↦ ⟪Ω† z, y⟫` vanishes, which is the statement `(y, 0) ∈ Ω†.graph.adjoint`; by the
rotated-graph description and rotation being an involution on the closed graph of `Ω`, that is
exactly `(y, 0) ∈ Ω.graph`, i.e. `y ∈ ker Ω`. -/
theorem range_adjoint_orthogonal (hcl : HasClosedGraph Om) (hdense : Dense (Om.domain : Set H)) :
    (LinearMap.range (adjoint Om hdense).toFun)ᗮ = physicalStates Om := by
  ext y
  rw [Submodule.mem_orthogonal, mem_physicalStates]
  constructor
  · intro h
    have hmem : (y, (0 : H)) ∈ (adjoint Om hdense).graph.adjoint := by
      rw [Submodule.mem_adjoint_iff]
      intro a b hab
      obtain ⟨u, hu₁, hu₂⟩ := (LinearPMap.mem_graph_iff (adjoint Om hdense)).mp hab
      have hu₁' : (u : H) = a := hu₁
      have hu₂' : (adjoint Om hdense) u = b := hu₂
      have hz := h _ ⟨u, rfl⟩
      rw [← hu₁', ← hu₂', inner_zero_right, sub_zero]
      exact hz
    have hg : (y, (0 : H)) ∈ (Om.graph.adjoint).adjoint := by
      rwa [← graph_adjoint Om hdense]
    rw [adjoint_adjoint_of_isClosed Om.graph hcl] at hg
    obtain ⟨h, h1, h2⟩ := (LinearPMap.mem_graph_iff Om).mp hg
    have h1' : (h : H) = y := h1
    have h2' : Om h = 0 := h2
    have hmem' : y ∈ Om.domain := h1' ▸ h.2
    refine ⟨hmem', ?_⟩
    have he : (⟨y, hmem'⟩ : Om.domain) = h := Subtype.ext h1'.symm
    rw [he, h2']
  · rintro ⟨hy, h0⟩ z ⟨u, rfl⟩
    have key : ⟪y, (adjoint Om hdense) u⟫ = 0 := by
      rw [adjoint_apply Om hdense u ⟨y, hy⟩, h0, inner_zero_left]
    exact (by simpa using congrArg star key)

/-- **von Neumann's closed-range identification**: the closure of the adjoint's range is the
orthogonal complement of the charge's kernel.  This is the missing half of the naming of the
coexact sector: `coexactStates Om` was *defined* as `(ker Ω)ᗮ`, and it does equal
`closure (range Ω†)`. -/
theorem closure_range_adjoint_eq_coexact (hcl : HasClosedGraph Om)
    (hdense : Dense (Om.domain : Set H)) :
    (LinearMap.range (adjoint Om hdense).toFun).topologicalClosure = coexactStates Om := by
  rw [coexactStates, ← range_adjoint_orthogonal Om hcl hdense,
    Submodule.orthogonal_orthogonal_eq_closure]

/-- The same identity in the form `closure (range Ω†) = (ker Ω)ᗮ`, and with the double orthogonal
complement written out: the coexact sector is exactly the adjoint's range closure. -/
theorem exactStates_adjoint_eq_coexact (hcl : HasClosedGraph Om)
    (hdense : Dense (Om.domain : Set H)) :
    exactStates (adjoint Om hdense) = coexactStates Om :=
  closure_range_adjoint_eq_coexact Om hcl hdense

end VonNeumann

end BookProof.BrstUnbounded
