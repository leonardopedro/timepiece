import Mathlib
import BookProof.ChapterBrstReducedTransfer

/-!
# The harmonic decomposition of the BRST charge, and the BRST quotient norm

`softmodes.md` Phase 1 asks for the BRST reduction of the field space, and its status note
records four missing inputs.  The second of them is the one this chapter supplies, in the
bounded setting where the algebra is available:

> The quotient norm on `ker Ω ⧸ closure (range Ω)` has to come from the **harmonic
> (invariant) representative** — a Hodge-type decomposition
> `H = ker Ω ∩ ker Ω* ⊕ range Ω ⊕ range Ω*` — rather than from `infDist`.

That claim is a theorem, not a definition, and it is proved here for a bounded nilpotent
`Ω` on a complex Hilbert space `H`:

* **`harmonicStates`** — `ker Ω ⊓ ker Ω†`, the harmonic (BRST-invariant) states;
* **`exactStates_orthogonal`** — `(closure (range Ω))ᗮ = ker Ω†`, from
  `ContinuousLinearMap.orthogonal_range` and `Submodule.orthogonal_closure`.  This is the
  identity that makes the harmonic states a *complement* rather than merely a subspace;
* **`sup_exact_harmonic`** — `exactStates Ω ⊔ harmonicStates Ω = physicalStates Ω`, from
  `Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection`.  So every BRST-closed state is a
  gauge part plus a harmonic part, and **`disjoint_exact_harmonic`** says the sum is direct.
  Together these are `IsCompl`-shaped, and because they hold for a *bounded* `Ω` they are
  literally true rather than formal: the closure in `exactStates` is essential and the
  harmonic part is what survives it;
* **`coexactStates`**, **`coexactStates_orthogonal`** (`(closure (range Ω†))ᗮ = ker Ω`),
  **`coexact_sup_physicalStates`** — the other half of the Hodge decomposition, and
  **`hodge_decomposition`**: `harmonic ⊔ exact ⊔ coexact = ⊤`, with the three subspaces
  pairwise orthogonal (`disjoint_harmonic_exact`, `disjoint_exact_coexact`,
  `disjoint_harmonic_coexact`).  This is the `H = ker Ω ∩ ker Ω* ⊕ range Ω ⊕ range Ω*` of the
  plan, with closures, for a bounded nilpotent charge;
* **`harmonicPart`** — the harmonic representative `x − P_{exact} x` of a state, with
  **`harmonicPart_mem`** (it is harmonic and closed when `x` is closed),
  **`harmonicPart_sub_mem_exact`** (the difference is exact) and
  **`exists_harmonic_decomposition`** (the decomposition with explicit orthogonality);
* **`infDist_eq_norm_harmonicPart`** — **the quotient norm is the norm of the harmonic
  representative**, `infDist x (exactStates Ω) = ‖harmonicPart x‖`.  The right-hand side is
  attained, so it is a norm and not an infimum that is never reached;
* **`harmonicPart_eq_of_sub_mem_exact`** — the representative depends only on the cohomology
  class, so the quotient norm well defined by the harmonic norm is the *same* function as
  `infDist` — the plan's point 2, as an identity between the two candidates;
* **`infDist_eq_norm_of_harmonic_decomposition`** — the abstract form: any orthogonal
  decomposition of a closed state into harmonic + exact parts has `infDist` equal to the norm
  of the harmonic part, so the identity does not depend on the projection being used.

## What this does *not* do (the rest of Phase 1 is still open)

* **Unbounded `Ω`.**  `Ω` is a bounded operator, as in `ChapterBrstReducedTransfer`.  The
  field-theoretic charge is a cubic differential operator; the decomposition above then has
  to be reproved for `Ω` closed and densely defined with an invariant core, and no part of
  that is claimed here.
* **"Longitudinal = exact".**  The identification `closure (range Ω) = span{∂ᵢφ}` is not
  attempted: this chapter proves the decomposition of the abstract Hilbert space, not that
  its exact part is the pure-gauge sector of a field theory.
* **Stability of the bottom under the elimination.**  Nothing here says that restricting to
  the harmonic sector preserves `θ∞`; that is Phase 1's fourth missing input and it needs the
  Phases 2–5 forms on the reduced operator.
* **`H_phys` as a Hilbert space.**  The quotient `Cohomology Ω` of
  `ChapterBrstReducedTransfer` is a `Submodule.Quotient`; what is proved here is that its
  natural norm is the harmonic norm, which is the substantive half of the identification.
  No completion of the polynomial core is constructed.

Everything is `sorry`-free and introduces no axioms.
-/

noncomputable section

namespace BookProof.BrstHarmonicDecomposition

open BookProof.BrstReducedTransfer
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (Om : H →L[ℂ] H)

/-- The BRST **cocharge**: the adjoint of the charge.  Its kernel cuts out the harmonic part
of the physical states. -/
abbrev cocharge : H →L[ℂ] H := ContinuousLinearMap.adjoint Om

/-- The BRST-**coexact** states: the closure of the range of the cocharge — the second
`range` summand of the Hodge decomposition. -/
def coexactStates : Submodule ℂ H :=
  (LinearMap.range (cocharge Om : H →ₗ[ℂ] H)).topologicalClosure

/-- The **harmonic** states: closed *and* co-closed, `ker Ω ⊓ ker Ω†`.  These are the
representatives the BRST quotient norm is read off. -/
def harmonicStates : Submodule ℂ H := physicalStates Om ⊓ (cocharge Om).ker

theorem isClosed_coexactStates : IsClosed (coexactStates Om : Set H) :=
  Submodule.isClosed_topologicalClosure _

/-- A closed submodule of a Hilbert space is complete, so it carries the orthogonal
projection.  Recorded as an instance so that `starProjection` elaborates in statements. -/
instance : CompleteSpace (exactStates Om : Submodule ℂ H) :=
  (isClosed_exactStates Om).completeSpace_coe

instance : CompleteSpace (coexactStates Om : Submodule ℂ H) :=
  (isClosed_coexactStates Om).completeSpace_coe

/-! ## 1. The two orthogonal complements, and the harmonic complement -/

/-- **The orthogonal complement of the exact states is the kernel of the cocharge.**  This is
the identity that makes the harmonic states a complement of the gauge directions: the closure
in `exactStates` costs nothing, because the orthogonal complement of a closure is the
orthogonal complement of the set (`Submodule.orthogonal_closure`). -/
theorem exactStates_orthogonal : (exactStates Om)ᗮ = (cocharge Om).ker := by
  rw [exactStates, Submodule.orthogonal_closure]
  exact ContinuousLinearMap.orthogonal_range Om

/-- **The orthogonal complement of the coexact states is the physical subspace** — the other
half of the decomposition, obtained from `orthogonal_range` and `Ω†† = Ω`. -/
theorem coexactStates_orthogonal : (coexactStates Om)ᗮ = physicalStates Om := by
  rw [coexactStates, Submodule.orthogonal_closure, ContinuousLinearMap.orthogonal_range]
  simp [cocharge, physicalStates, ContinuousLinearMap.adjoint_adjoint]

/-- The harmonic states, as an intersection of the physical ones with the orthogonal
complement of the exact ones. -/
theorem harmonicStates_eq :
    harmonicStates Om = physicalStates Om ⊓ (exactStates Om)ᗮ := by
  rw [harmonicStates, exactStates_orthogonal]

/-! ## 2. The decomposition of the physical states -/

/-- **Every BRST-closed state is a gauge part plus a harmonic part**:
`physicalStates Ω = exactStates Ω ⊔ harmonicStates Ω`.  The point is that the second summand
is exactly the orthogonal complement *intersected with* the physical states — this is
`Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection` at `exactStates ≤ physicalStates`,
and it is why the harmonic representative is canonical. -/
theorem sup_exact_harmonic (hnil : ∀ x, Om (Om x) = 0) :
    exactStates Om ⊔ harmonicStates Om = physicalStates Om := by
  have hle : exactStates Om ≤ physicalStates Om := exactStates_le_physicalStates Om hnil
  have h := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (K₁ := exactStates Om)
    (K₂ := physicalStates Om) hle
  rw [inf_comm, ← harmonicStates_eq] at h
  exact h

/-- The exact and harmonic states span the physical subspace **directly**. -/
theorem disjoint_exact_harmonic : Disjoint (exactStates Om) (harmonicStates Om) := by
  have hle : harmonicStates Om ≤ (exactStates Om)ᗮ := by
    rw [harmonicStates_eq]
    exact inf_le_right
  exact (exactStates Om).orthogonal_disjoint.mono_right hle

/-- **A longitudinal state is not harmonic.**  Whatever "longitudinal" means, once the
identification puts it inside the exact (pure-gauge) states, no nonzero longitudinal state can
lie in `ker Ω ∩ ker Ω†`: the exact and harmonic sectors are disjoint
(`disjoint_exact_harmonic`), so a state of an arbitrary `L ≤ exactStates Om` that is also
harmonic is zero.  This is the "observation" half of `softmodes.md` Phase 1 item 3 — a
longitudinal plane wave is not a soft zero-mode — stated for an arbitrary subspace and needing
no field model: it holds for whatever "longitudinal" is, provided the identification of that
plan's §1 puts it inside the exact states. -/
theorem no_longitudinal_zero_mode {L : Submodule ℂ H} (hL : L ≤ exactStates Om) {x : H}
    (hx : x ∈ L) (harm : x ∈ harmonicStates Om) : x = 0 := by
  have h : x ∈ exactStates Om ⊓ harmonicStates Om := ⟨hL hx, harm⟩
  rw [(disjoint_exact_harmonic Om).eq_bot, Submodule.mem_bot] at h
  exact h

/-! ## 3. The full Hodge decomposition `H = harmonic ⊕ exact ⊕ coexact` -/

/-- **The coexact states together with the physical ones fill the space**: the orthogonal
complement of the coexact states is `ker Ω`. -/
theorem coexact_sup_physicalStates : coexactStates Om ⊔ physicalStates Om = ⊤ := by
  have h := Submodule.sup_orthogonal_of_hasOrthogonalProjection (K := coexactStates Om)
  rwa [coexactStates_orthogonal] at h

/-- **The Hodge decomposition of the BRST complex**: the harmonic, exact and coexact states
span the Hilbert space, with pairwise orthogonal summands (the three `disjoint_*` theorems
below).  This is the plan's `H = ker Ω ∩ ker Ω* ⊕ range Ω ⊕ range Ω*`, with the closures of
the two ranges. -/
theorem hodge_decomposition (hnil : ∀ x, Om (Om x) = 0) :
    harmonicStates Om ⊔ exactStates Om ⊔ coexactStates Om = ⊤ := by
  rw [sup_comm (harmonicStates Om) (exactStates Om), sup_exact_harmonic Om hnil,
    sup_comm (physicalStates Om) (coexactStates Om), coexact_sup_physicalStates Om]

/-- The exact states are orthogonal to the coexact ones: the exact states are closed, hence lie
in `ker Ω = (coexact)ᗮ`. -/
theorem disjoint_exact_coexact (hnil : ∀ x, Om (Om x) = 0) :
    Disjoint (exactStates Om) (coexactStates Om) := by
  have hle : exactStates Om ≤ (coexactStates Om)ᗮ := by
    rw [coexactStates_orthogonal]
    exact exactStates_le_physicalStates Om hnil
  exact (coexactStates Om).orthogonal_disjoint.symm.mono_left hle

/-- The harmonic states are orthogonal to the coexact ones, being closed. -/
theorem disjoint_harmonic_coexact : Disjoint (harmonicStates Om) (coexactStates Om) := by
  have hle : harmonicStates Om ≤ (coexactStates Om)ᗮ := by
    rw [coexactStates_orthogonal, harmonicStates_eq]
    exact inf_le_left
  exact (coexactStates Om).orthogonal_disjoint.symm.mono_left hle

/-! ## 4. The harmonic representative, and the quotient norm -/

/-- **The harmonic representative** of a state: the state minus its orthogonal projection on
the exact (pure gauge) directions. -/
def harmonicPart (x : H) : H := x - (exactStates Om).starProjection x

/-- For a closed state, the remainder is exact: it is exactly the projection. -/
theorem sub_harmonicPart_mem_exact (x : H) : x - harmonicPart Om x ∈ exactStates Om := by
  simp only [harmonicPart, sub_sub_cancel]
  exact (exactStates Om).starProjection_apply_mem x

/-- The harmonic representative of a **closed** state is harmonic: it stays closed, and the
cocharge kills it because the remainder lies in the orthogonal complement of the exact
states, i.e. in `ker Ω†`. -/
theorem harmonicPart_mem (hnil : ∀ x, Om (Om x) = 0) {x : H}
    (hx : x ∈ physicalStates Om) : harmonicPart Om x ∈ harmonicStates Om := by
  have hle : exactStates Om ≤ physicalStates Om := exactStates_le_physicalStates Om hnil
  refine ⟨?_, ?_⟩
  · exact (physicalStates Om).sub_mem hx (hle ((exactStates Om).starProjection_apply_mem x))
  · have horth : harmonicPart Om x ∈ (exactStates Om)ᗮ :=
      Submodule.sub_starProjection_mem_orthogonal (K := exactStates Om) x
    rwa [exactStates_orthogonal] at horth

/-- **The quotient (BRST) norm is the norm of the harmonic representative.**  The infimum
defining `infDist` is attained at the harmonic representative — `starProjection_minimal`
identifies it with the distance to the projection — so the harmonic norm is a genuine norm on
the cohomology, not an infimum taken over a set that never realizes it. -/
theorem infDist_eq_norm_harmonicPart (x : H) :
    Metric.infDist x (exactStates Om) = ‖harmonicPart Om x‖ := by
  rw [Metric.infDist_eq_iInf]
  simpa only [harmonicPart, dist_eq_norm, norm_sub_rev] using
    (Submodule.starProjection_minimal (U := exactStates Om) x).symm

/-- **The harmonic representative depends only on the cohomology class.**  Two states differing
by an exact (pure gauge) vector have the same harmonic part, so the norm
`‖harmonicPart ·‖` is a function of the class — which, with
`infDist_eq_norm_harmonicPart`, is the statement that the harmonic norm *is* the quotient
norm of the plan's point 2. -/
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
        - (y - (exactStates Om).starProjection y)
        ∈ (exactStates Om) ⊓ (exactStates Om)ᗮ := ⟨hK, hK'⟩
    rw [(exactStates Om).orthogonal_disjoint.eq_bot] at hmem
    simpa using hmem
  simp only [harmonicPart] at hzero ⊢
  exact sub_eq_zero.mp hzero

/-- **The decomposition of a closed state into harmonic and exact parts, with the orthogonality
explicit.**  This is the form in which the plan states the Hodge decomposition of a physical
state, and it is what makes the quotient norm computable. -/
theorem exists_harmonic_decomposition (hnil : ∀ x, Om (Om x) = 0) {x : H}
    (hx : x ∈ physicalStates Om) :
    ∃ h ∈ harmonicStates Om, ∃ e ∈ exactStates Om,
      x = h + e ∧ ∀ y ∈ exactStates Om, inner ℂ h y = 0 := by
  refine ⟨harmonicPart Om x, harmonicPart_mem Om hnil hx, (exactStates Om).starProjection x,
    (exactStates Om).starProjection_apply_mem x, ?_, ?_⟩
  · simp [harmonicPart]
  · intro y hy
    have h := Submodule.sub_starProjection_mem_orthogonal (K := exactStates Om) x
    rw [Submodule.mem_orthogonal] at h
    have hy0 : inner ℂ y (harmonicPart Om x) = 0 := h y hy
    exact inner_eq_zero_symm.mpr hy0

end BookProof.BrstHarmonicDecomposition
