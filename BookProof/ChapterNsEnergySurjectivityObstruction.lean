import Mathlib
import BookProof.ChapterNsKoopman

/-!
# The surjectivity hypothesis of the NS mainstream leg cannot hold on the Gauss–polynomial core

`BookProof.NsKoopman.nsKoopman_esa_of_energy_comparison` concludes essential self-adjointness of
the mainstream Navier–Stokes Koopman generator from a named hypothesis

`hsurj : ∀ f : L2d d, ∃ x : polyGaussCore, nsEnergyOp x + x = f`,

the surjectivity of `N_E + 1` (Leray energy `N_E = mulOp(1 + ‖u‖²)`) **from the Gauss–polynomial
core itself**.  The work order of `CONSOLIDATED_PLAN.md` lists proving this surjectivity as the
open input of the NS mainstream leg.  This module proves that, in every dimension `d ≥ 1`, the
hypothesis is **false**:

* `countable_span_ne_top` — in an infinite-dimensional complete normed space, the linear span of
  a countable family is never the whole space (Baire category);
* `not_finiteDimensional_L2d` — `L²(ℝᵈ)` is infinite-dimensional for `d ≥ 1` (the injective
  Gauss–polynomial map `pgMap` embeds the infinite-dimensional polynomial ring);
* `polyGaussCore_ne_top` — hence the Gauss–polynomial core is a proper subspace of `L²(ℝᵈ)`;
* **`not_nsEnergy_surjective`** — `N_E + 1` maps the core into the core, so it is not onto
  `L²(ℝᵈ)`: the hypothesis `hsurj` of `nsKoopman_esa_of_energy_comparison` is unsatisfiable for
  `d ≥ 1`, and that theorem is vacuous as stated.

The surjectivity input must therefore be taken on a domain larger than the Gauss core (for
instance the maximal domain of the multiplication operator), together with a separate core
argument — it cannot be supplied on `polyGaussCore`.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.NsEnergySurjectivityObstruction

open MvPolynomial
open BookProof.HermiteProductCore BookProof.NsKoopman

noncomputable section

/-- **Baire.**  In an infinite-dimensional complete normed space over `ℂ`, the span of a
countable family is a proper subspace. -/
theorem countable_span_ne_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (hinf : ¬ FiniteDimensional ℂ E) {ι : Type*} [Countable ι] (b : ι → E) :
    Submodule.span ℂ (Set.range b) ≠ ⊤ := by
  intro htop
  set W : Finset ι → Submodule ℂ E := fun s => Submodule.span ℂ (b '' (s : Set ι)) with hW
  have hfin : ∀ s, FiniteDimensional ℂ (W s) := fun s =>
    FiniteDimensional.span_of_finite ℂ ((s.finite_toSet).image b)
  have hclosed : ∀ s, IsClosed ((W s : Submodule ℂ E) : Set E) := fun s =>
    haveI := hfin s; Submodule.closed_of_finiteDimensional _
  have hcover : (⋃ s : Finset ι, ((W s : Submodule ℂ E) : Set E)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : x ∈ Submodule.span ℂ (Set.range b) := by rw [htop]; trivial
    obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hx
    refine Set.mem_iUnion.2 ⟨c.support, ?_⟩
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨i, hi, rfl⟩
  obtain ⟨s, hs⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  have htop' : W s = ⊤ := Submodule.eq_top_of_nonempty_interior' _ hs
  haveI := hfin s
  apply hinf
  rw [htop'] at this
  exact LinearEquiv.finiteDimensional (Submodule.topEquiv)

/-- `L²(ℝᵈ)` is infinite-dimensional for `d ≥ 1`. -/
theorem not_finiteDimensional_L2d {d : ℕ} (hd : 0 < d) : ¬ FiniteDimensional ℂ (L2d d) := by
  intro hfd
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  haveI : Module.Finite ℂ (MvPolynomial (Fin d) ℂ) :=
    Module.Finite.of_injective (pgMap (d := d)) pgMap_injective
  have := Module.Finite.finite_basis (MvPolynomial.basisMonomials (Fin d) ℂ)
  exact not_finite (Fin d →₀ ℕ)

/-- **The Gauss–polynomial core is a proper subspace of `L²(ℝᵈ)`** for `d ≥ 1`. -/
theorem polyGaussCore_ne_top {d : ℕ} (hd : 0 < d) : polyGaussCore (d := d) ≠ ⊤ := by
  intro htop
  apply countable_span_ne_top (not_finiteDimensional_L2d hd)
    (fun m : Fin d →₀ ℕ => pgMap (d := d) (MvPolynomial.basisMonomials (Fin d) ℂ m))
  rw [eq_top_iff, ← htop]
  rintro _ ⟨p, rfl⟩
  have hp : p ∈ Submodule.span ℂ (Set.range (MvPolynomial.basisMonomials (Fin d) ℂ)) := by
    rw [Module.Basis.span_eq]; trivial
  have := Submodule.mem_map_of_mem (f := pgMap (d := d)) hp
  rwa [Submodule.map_span, ← Set.range_comp] at this

/-- **The surjectivity hypothesis of the NS mainstream leg is false on the Gauss–polynomial
core**: for `d ≥ 1`, `N_E + 1` (Leray energy `N_E = mulOp(1 + ‖u‖²)`) does not map
`polyGaussCore` onto `L²(ℝᵈ)`.  Consequently the hypothesis `hsurj` of
`BookProof.NsKoopman.nsKoopman_esa_of_energy_comparison` can never be met. -/
theorem not_nsEnergy_surjective {d : ℕ} (hd : 0 < d) :
    ¬ ∀ f : L2d d, ∃ x : polyGaussCore (d := d), nsEnergyOp (d := d) x + (x : L2d d) = f := by
  intro hsurj
  apply polyGaussCore_ne_top hd
  rw [eq_top_iff]
  intro f _
  obtain ⟨x, rfl⟩ := hsurj f
  refine Submodule.add_mem _ ?_ x.2
  simp only [nsEnergyOp, LinearMap.comp_apply, Submodule.coe_subtype]
  exact Submodule.coe_mem _

end

end BookProof.NsEnergySurjectivityObstruction
