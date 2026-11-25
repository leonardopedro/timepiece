import Mathlib

/-!
# Chapter FiniteRankObstructions — the two U1 counterchecks as formal examples

`softmodes.md` U1 records two checks that must be built into the mass-gap argument so no
later theorem silently asks for an impossible norm limit, and U6 step 2 asks for them as
small formal examples.  This module supplies them.

1. **A finite-rank reconstruction of an infinite-dimensional unitary flow has whole-space
   error at least `1`.**  `finiteRank_isometry_norm_sub_ge_one` tests a nonzero vector in
   the kernel of the finite-rank map: the isometry preserves its norm, so the operator
   norm of the difference is at least `1`.  Consequently seed-wise convergence of a
   Krylov reconstruction says nothing about a vanishing worst-case flow error.

2. **Whole-space norm convergence of finite-rank reconstructions forces compactness.**
   `finiteRank_isCompactOperator` (a finite-dimensional range is compact) composed with
   Mathlib's `isCompactOperator_of_tendsto` gives `isCompactOperator_of_tendsto_finiteRank`.
   Hence `not_tendsto_finiteRank_to_isometry`: an isometry on an infinite-dimensional
   space (in particular the identity) is not a norm limit of finite-rank operators.  The
   resolvent `R_g` of the unreduced 99-coordinate model must therefore not be assumed
   compact to make `e_R → 0`; a finite positive error suffices for the U5 witness.

No Hamiltonian, resolvent or numerical data is used.  Everything is operator algebra and
one compactness fact; axioms are `propext`, `Classical.choice`, `Quot.sound` only.
-/

noncomputable section

namespace BookProof.FiniteRankObstructions

open Filter Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! ## Check 1 — the kernel vector and the norm-one floor -/

omit [LocallyCompactSpace 𝕜] in
/-- A finite-rank operator on an infinite-dimensional space has a nontrivial kernel.
    If it were injective, `FiniteDimensional.of_injective` would make the domain finite
    dimensional from the finite-dimensional range — a contradiction. -/
theorem finiteRank_has_kernel (hInf : ¬ FiniteDimensional 𝕜 E) (F : E →L[𝕜] E)
    (hFin : FiniteDimensional 𝕜 F.range) : ∃ z : E, z ≠ 0 ∧ F z = 0 := by
  by_contra h
  push_neg at h
  have hinj : Function.Injective F := by
    intro x y hxy
    have hz : F (x - y) = 0 := by simp [hxy]
    by_cases hdiff : x - y = 0
    · exact sub_eq_zero.mp hdiff
    · exact False.elim (h (x - y) hdiff hz)
  letI : FiniteDimensional 𝕜 E :=
    FiniteDimensional.of_injective (F.rangeRestrict : E →ₗ[𝕜] F.range) (by
      intro x y hxy
      apply hinj
      exact congrArg Subtype.val hxy)
  exact hInf inferInstance

omit [LocallyCompactSpace 𝕜] in
/-- **U1 check 1.**  For an isometric `U` and a finite-rank `F` on an infinite-dimensional
    space, `1 ≤ ‖U − F‖`.  The inequality is read at a kernel vector of `F`. -/
theorem finiteRank_isometry_norm_sub_ge_one (hInf : ¬ FiniteDimensional 𝕜 E)
    (U : E →L[𝕜] E) (hU : ∀ x : E, ‖U x‖ = ‖x‖)
    (F : E →L[𝕜] E) (hFin : FiniteDimensional 𝕜 F.range) :
    1 ≤ ‖U - F‖ := by
  rcases finiteRank_has_kernel hInf F hFin with ⟨z, hz0, hFz⟩
  have hle := (U - F).le_opNorm z
  rw [ContinuousLinearMap.sub_apply, hFz, sub_zero, hU] at hle
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  nlinarith

omit [LocallyCompactSpace 𝕜] in
/-- The special case of a finite-rank reconstruction of the identity flow. -/
theorem finiteRank_identity_norm_sub_ge_one (hInf : ¬ FiniteDimensional 𝕜 E)
    (F : E →L[𝕜] E) (hFin : FiniteDimensional 𝕜 F.range) :
    1 ≤ ‖1 - F‖ := by
  exact finiteRank_isometry_norm_sub_ge_one hInf 1 (by simp) F hFin

/-! ## Check 2 — a norm limit of finite-rank operators is compact -/

/-- A continuous linear map with finite-dimensional range is a compact operator: the
    image of the unit ball lies in a compact ball of the finite-dimensional range. -/
theorem finiteRank_isCompactOperator (F : E →L[𝕜] E)
    (hFin : FiniteDimensional 𝕜 F.range) : IsCompactOperator (F : E → E) := by
  letI : ProperSpace F.range := FiniteDimensional.proper 𝕜 F.range
  let K : Set E := (fun y : F.range => (y : E)) '' Metric.closedBall (0 : F.range) ‖F‖
  refine ⟨K, ?_, ?_⟩
  · exact (ProperSpace.isCompact_closedBall (0 : F.range) ‖F‖).image continuous_subtype_val
  · refine Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : E) zero_lt_one) ?_
    intro x hx
    refine ⟨⟨F x, ⟨x, rfl⟩⟩, ?_, rfl⟩
    have hx' : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hFx : ‖F x‖ ≤ ‖F‖ := by
      calc
        ‖F x‖ ≤ ‖F‖ * ‖x‖ := F.le_opNorm x
        _ ≤ ‖F‖ * 1 := mul_le_mul_of_nonneg_left hx' (norm_nonneg F)
        _ = ‖F‖ := by ring
    simpa [Metric.mem_closedBall, dist_eq_norm] using hFx

variable {ι : Type*} {l : Filter ι} [l.NeBot]

/-- A norm limit of finite-rank operators is compact, by Mathlib's closedness of the
    compact operators.  So `e_R → 0` for finite-rank reconstructions of `R_g` *is* the
    assertion that `R_g` is compact. -/
theorem isCompactOperator_of_tendsto_finiteRank [CompleteSpace E]
    (H : ι → E →L[𝕜] E) (R : E →L[𝕜] E)
    (hH : ∀ i, FiniteDimensional 𝕜 (H i).range) (hlim : Tendsto H l (𝓝 R)) :
    IsCompactOperator (R : E → E) := by
  exact isCompactOperator_of_tendsto hlim
    (Filter.Eventually.of_forall fun i => finiteRank_isCompactOperator (H i) (hH i))

omit [LocallyCompactSpace 𝕜] in
/-- **U1 check 2, negative form.**  An isometry on an infinite-dimensional space is not a
    norm limit of finite-rank operators: the limit would be compact, while check 1 gives a
    uniform distance `≥ 1` from every finite-rank map. -/
theorem not_tendsto_finiteRank_to_isometry (hInf : ¬ FiniteDimensional 𝕜 E)
    (U : E →L[𝕜] E) (hU : ∀ x : E, ‖U x‖ = ‖x‖)
    (H : ι → E →L[𝕜] E) (hH : ∀ i, FiniteDimensional 𝕜 (H i).range) :
    ¬ Tendsto H l (𝓝 U) := by
  intro hlim
  have hsub : Tendsto (fun i => H i - U) l (𝓝 (U - U)) := hlim.sub tendsto_const_nhds
  have hsub0 : Tendsto (fun i => H i - U) l (𝓝 0) := by simpa using hsub
  have hnorm : Tendsto (fun i => ‖H i - U‖) l (𝓝 0) := by simpa using hsub0.norm
  have hev : ∀ᶠ i in l, ‖H i - U‖ < 1 := hnorm.eventually (Iio_mem_nhds (by norm_num))
  rcases hev.exists with ⟨i, hi⟩
  have hge := finiteRank_isometry_norm_sub_ge_one hInf U hU (H i) (hH i)
  rw [norm_sub_rev] at hge
  linarith

omit [LocallyCompactSpace 𝕜] in
/-- The identity special case: whole-space norm convergence of finite-rank
    reconstructions of the identity flow is impossible. -/
theorem not_tendsto_finiteRank_to_identity (hInf : ¬ FiniteDimensional 𝕜 E)
    (H : ι → E →L[𝕜] E) (hH : ∀ i, FiniteDimensional 𝕜 (H i).range) :
    ¬ Tendsto H l (𝓝 (1 : E →L[𝕜] E)) := by
  exact not_tendsto_finiteRank_to_isometry hInf 1 (by simp) H hH

end BookProof.FiniteRankObstructions
