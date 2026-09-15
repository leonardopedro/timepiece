import Mathlib
import BookProof.ChapterBrstTruncationLeakage
import BookProof.ChapterStoneGenerator

/-!
# BRST leakage of the truncated dynamics for an **unbounded** Hamiltonian

`CONSOLIDATED_PLAN.md` §12.2 **Gap 5** asks for a bound on the physical-subspace (BRST)
leakage `‖Ω ψ(t)‖` of the *truncated* dynamics in terms of the truncation.
`BookProof/ChapterBrstTruncationLeakage.lean` closes it for **bounded** generators and
records the unbounded field-theoretic Hamiltonian as the remaining boundary.  This module
removes that restriction: the exact generator is an arbitrary unbounded self-adjoint
operator `T` (the bundled `UnboundedSelfAdjoint` of `BookProof.ChapterStoneResolvent`,
whose flow `e^{-itT} = T.stoneU t` is the one Stone's theorem produces), and the truncated
generator is the compression `P T P` to a **finite-dimensional** retained subspace — which
is exactly the finite-`m` object the SIRK/Hashimoto solver integrates.

## What is proved

* **Duhamel against an unbounded exact generator.**
  `hasDerivAt_duhamel_stone` differentiates `u ↦ e^{-i(t-u)T} e^{-iuB} x` when the truncated
  orbit stays in the domain of `T`; the derivative is `e^{-i(t-u)T}(-i)(B - T)` applied to
  the orbit, so only the *defect* `T - B` along the orbit enters.  The step that replaces
  the bounded-generator product rule is `hasDerivAt_isometry_apply`, an elementary
  strong-continuity lemma: an isometric, strongly continuous family `U h` applied to a
  differentiable curve vanishing at `0` is differentiable, with derivative `U 0` of the
  curve's derivative.
* **The flow error.**  `norm_flow_sub_stoneU_le` — `‖e^{-itB}x - e^{-itT}x‖ ≤ K t` whenever
  `‖T y - B y‖ ≤ K` along the truncated orbit `y = e^{-isB}x`, `s ∈ [0, t]`.  No
  boundedness, no relative bound, no analytic-vector hypothesis: unitarity of both groups
  is what keeps the rate linear in `t`.
* **The leakage bound.**  `leakage_le` — for a bounded observable `Ω` commuting with the
  exact group, `‖Ω(e^{-itB}x)‖ ≤ ‖Ωx‖ + ‖Ω‖ K t`, and `leakage_le_of_physical` for a
  physical initial state `Ωx = 0`.  The exact dynamics does not leak
  (`norm_omega_stoneU_eq`): all of the leakage comes from the truncation.
* **The truncation instance.**  For a finite-dimensional subspace `V ≤ T.domain` with
  orthogonal projection `P`, the compression `truncGen = P T P` is a *bounded* self-adjoint
  operator (`truncGen_isSelfAdjoint`) — finite-dimensionality is what makes `T P` bounded —
  its flow keeps a retained state retained (`flow_truncGen_mem`, by ODE uniqueness), and the
  defect along the orbit is exactly the discarded off-diagonal block `(1 - P) T P`
  (`truncDefect`).  Hence
  * **`norm_flow_truncGen_sub_stoneU_le`** — `‖e^{-itPTP}x - e^{-itT}x‖ ≤ ‖(1-P)TP‖ ‖x‖ t`,
    the finite-`m` flow error for an unbounded Hamiltonian, and
  * **`truncation_leakage_le`** — `‖Ω(e^{-itPTP}x)‖ ≤ ‖Ωx‖ + ‖Ω‖ ‖(1-P)TP‖ ‖x‖ t`,
    with `truncation_leakage_le_of_physical` for a physical retained state.

  Both vanish with the discarded block, so a retained subspace that is nearly invariant
  under the unbounded Hamiltonian leaks nearly nothing.
* **Restarts.**  `restartGen` is the sequence of compressions the restarted cycle uses — a
  fresh retained subspace each cycle — and **`restart_leakage_le`** accumulates the bound
  linearly in the number of cycles:
  `‖Ω (leakageIter (restartGen …) τ x n)‖ ≤ ‖Ωx‖ + n ‖Ω‖ D ‖x‖ τ` whenever every discarded
  block satisfies `‖(1 - Pᵢ)TPᵢ‖ ≤ D` and the restarted state is retained in the new
  subspace at each restart (which is what re-seeding the Krylov cycle provides).

## Honest boundary

`Ω` is a bounded observable and is assumed to commute with the *group* `e^{-itT}` (the
correct unbounded form of "commutes with `H`"); nilpotency `Ω² = 0` is not needed.  The
retained subspace is finite-dimensional and inside the domain — the finite-`m` Krylov
subspace of the numerics.  All the bounds are stated for `t ≥ 0` (unlike the bounded-
generator module, which reflects the generators to reach negative times; reflecting an
unbounded generator would require rebuilding its group).  Nothing about floating-point
arithmetic (§12.2 Gap 6) is claimed.
-/

open NormedSpace Filter Topology
open scoped InnerProductSpace

namespace BookProof.BrstUnboundedLeakage

open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## A strong-continuity product rule -/

omit [CompleteSpace H] in
/-- If `U` is a family of isometries with `U 0 = id`, strongly continuous at `0`, and `f` is
differentiable at `0` with `f 0 = 0`, then `h ↦ U h (f h)` is differentiable at `0` with the
same derivative.  This replaces the product rule when `U` is only *strongly* continuous —
the situation for the unitary group of an unbounded generator. -/
theorem hasDerivAt_isometry_apply {U : ℝ → H →L[ℂ] H} {f : ℝ → H} {f' : H}
    (hiso : ∀ (h : ℝ) (y : H), ‖U h y‖ = ‖y‖) (hU0 : ∀ y : H, U 0 y = y)
    (hcont : ∀ y : H, Tendsto (fun h : ℝ => U h y) (𝓝 0) (𝓝 y))
    (hf : HasDerivAt f f' 0) (hf0 : f 0 = 0) :
    HasDerivAt (fun h : ℝ => U h (f h)) f' 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hc2 : 0 < c / 2 := by linarith
  -- the curve's own error term
  have h1 : ∀ᶠ h : ℝ in 𝓝 0, ‖f (0 + h) - f 0 - h • f'‖ ≤ (c / 2) * ‖h‖ := by
    have := (hasDerivAt_iff_isLittleO_nhds_zero.mp hf)
    exact (Asymptotics.isLittleO_iff.mp this) hc2
  -- the strong-continuity error term
  have h2 : ∀ᶠ h : ℝ in 𝓝 0, ‖U h f' - f'‖ ≤ c / 2 := by
    have hten := hcont f'
    have : ∀ᶠ h : ℝ in 𝓝 0, U h f' ∈ Metric.closedBall f' (c / 2) :=
      hten (Metric.closedBall_mem_nhds f' hc2)
    filter_upwards [this] with h hh
    simpa [Metric.mem_closedBall, dist_eq_norm] using hh
  filter_upwards [h1, h2] with h hh1 hh2
  rw [zero_add] at hh1
  simp only [zero_add]
  have hsplit : U h (f h) - U 0 (f 0) - h • f'
      = U h (f h - f 0 - h • f') + h • (U h f' - f') := by
    have hU0f : U 0 (f 0) = 0 := by rw [hU0, hf0]
    have hlin : U h (f h - f 0 - h • f') = U h (f h) - U h (f 0) - h • U h f' := by
      simp [map_sub, ContinuousLinearMap.map_smul_of_tower]
    rw [hlin, hU0f, hf0]
    simp only [map_zero, smul_sub]
    abel
  rw [hsplit]
  have hb1 : ‖U h (f h - f 0 - h • f')‖ ≤ (c / 2) * ‖h‖ := by
    rw [hiso]; exact hh1
  have hb2 : ‖h • (U h f' - f')‖ ≤ ‖h‖ * (c / 2) := by
    rw [norm_smul, Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hh2 (norm_nonneg _)
  calc ‖U h (f h - f 0 - h • f') + h • (U h f' - f')‖
      ≤ ‖U h (f h - f 0 - h • f')‖ + ‖h • (U h f' - f')‖ := norm_add_le _ _
    _ ≤ (c / 2) * ‖h‖ + ‖h‖ * (c / 2) := add_le_add hb1 hb2
    _ = c * ‖h‖ := by ring
    _ = c * ‖(id : ℝ → ℝ) h‖ := rfl

/-! ## The flow of a bounded generator -/

/-- The derivative of the bounded flow: `d/du e^{-iuB}x = -i B e^{-iuB}x`. -/
theorem hasDerivAt_flow (B : H →L[ℂ] H) (x : H) (u : ℝ) :
    HasDerivAt (fun v : ℝ => flow B v x) ((-Complex.I) • B (flow B u x)) u := by
  set Z : H →L[ℂ] H := (-Complex.I) • B with hZ
  have h1 : HasDerivAt (fun v : ℝ => exp (v • Z)) (exp (u • Z) * Z) u :=
    hasDerivAt_exp_smul_const Z u
  have hev : HasFDerivAt (fun S : H →L[ℂ] H => S x)
      ((ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ) (exp (u • Z)) :=
    ((ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ).hasFDerivAt
  have h2 := hev.comp_hasDerivAt u h1
  have hcomm : exp (u • Z) * Z = Z * exp (u • Z) := ((Commute.refl Z).smul_left u).exp_left.eq
  rw [hcomm] at h2
  have h3 : HasDerivAt (fun v : ℝ => (exp (v • Z)) x) ((Z * exp (u • Z)) x) u := by
    simpa [Function.comp_def] using h2
  exact h3

theorem flow_apply_flow (B : H →L[ℂ] H) (s u : ℝ) (x : H) :
    flow B u (flow B s x) = flow B (u + s) x := by
  have hc : Commute (u • ((-Complex.I) • B)) (s • ((-Complex.I) • B)) :=
    ((Commute.refl ((-Complex.I) • B)).smul_left u).smul_right s
  have hball : ∀ z : H →L[ℂ] H,
      z ∈ Metric.eball (0 : H →L[ℂ] H) (expSeries ℂ (H →L[ℂ] H)).radius := by
    intro z
    rw [expSeries_radius_eq_top ℂ (H →L[ℂ] H)]
    exact Metric.mem_eball.mpr (edist_lt_top z (0 : H →L[ℂ] H))
  have h : exp (u • ((-Complex.I) • B)) * exp (s • ((-Complex.I) • B))
      = exp ((u + s) • ((-Complex.I) • B)) := by
    rw [← exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hc (hball _) (hball _), ← add_smul]
  calc flow B u (flow B s x)
      = (exp (u • ((-Complex.I) • B)) * exp (s • ((-Complex.I) • B))) x := rfl
    _ = flow B (u + s) x := by rw [h]; rfl

/-! ## Duhamel against the unbounded group -/

variable (T : UnboundedSelfAdjoint H)

/-- The Duhamel derivative with an **unbounded** exact generator: the derivative of
`u ↦ e^{-i(t-u)T} e^{-iuB} x`, along an orbit that stays in the domain of `T`. -/
theorem hasDerivAt_duhamel_stone (B : H →L[ℂ] H) (t : ℝ) (x : H)
    (hdom : ∀ s : ℝ, flow B s x ∈ T.domain) (s : ℝ) :
    HasDerivAt (fun u : ℝ => T.stoneU (t - u) (flow B u x))
      (T.stoneU (t - s) ((-Complex.I) • (B (flow B s x) - T.op ⟨flow B s x, hdom s⟩))) s := by
  set y : H := flow B s x with hy
  have hyd : y ∈ T.domain := hdom s
  -- the local curve `k h = e^{ihT} e^{-ihB} y`
  set k : ℝ → H := fun h => T.stoneU (-h) (flow B h y) with hk
  -- piece 1: the truncated increment, transported by the (isometric) group
  have hg1 : HasDerivAt (fun h : ℝ => T.stoneU (-h) (flow B h y - y))
      ((-Complex.I) • B y) 0 := by
    refine hasDerivAt_isometry_apply (U := fun h : ℝ => T.stoneU (-h))
      (fun h z => T.norm_stoneU_apply (-h) z) (fun z => by simp) (fun z => ?_) ?_ (by simp)
    · have hcont : Continuous fun h : ℝ => T.stoneU (-h) z :=
        (T.continuous_stoneU_apply z).comp continuous_neg
      have := hcont.tendsto (0 : ℝ)
      simpa using this
    · have h0 := hasDerivAt_flow B y 0
      simpa using h0.sub_const y
  -- piece 2: the exact group applied to the (fixed) state
  have hg2 : HasDerivAt (fun h : ℝ => T.stoneU (-h) y) (Complex.I • T.op ⟨y, hyd⟩) 0 := by
    have h1 : HasDerivAt (fun r : ℝ => T.stoneU r y) ((-Complex.I) • T.op ⟨y, hyd⟩) (0 - 0) := by
      simpa using T.hasDerivAt_stoneU_zero ⟨y, hyd⟩
    have h2 := HasDerivAt.comp_const_sub (0 : ℝ) (0 : ℝ) h1
    have h3 : HasDerivAt (fun h : ℝ => T.stoneU (0 - h) y)
        (-((-Complex.I) • T.op ⟨y, hyd⟩)) 0 := h2
    have hfun : (fun h : ℝ => T.stoneU (0 - h) y) = fun h : ℝ => T.stoneU (-h) y := by
      funext h; rw [zero_sub]
    have hval : -((-Complex.I) • T.op ⟨y, hyd⟩) = Complex.I • T.op ⟨y, hyd⟩ := by
      rw [neg_smul, neg_neg]
    rw [hfun, hval] at h3
    exact h3
  have hkderiv : HasDerivAt k ((-Complex.I) • (B y - T.op ⟨y, hyd⟩)) 0 := by
    have hsum : HasDerivAt (fun h : ℝ => T.stoneU (-h) (flow B h y - y) + T.stoneU (-h) y)
        ((-Complex.I) • B y + Complex.I • T.op ⟨y, hyd⟩) 0 := hg1.add hg2
    have hfun : ∀ h : ℝ, T.stoneU (-h) (flow B h y - y) + T.stoneU (-h) y = k h := by
      intro h
      rw [hk]
      simp [map_sub]
    have hval : (-Complex.I) • B y + Complex.I • T.op ⟨y, hyd⟩
        = (-Complex.I) • (B y - T.op ⟨y, hyd⟩) := by
      simp [sub_eq_add_neg]
    rw [hval] at hsum
    exact hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun h => (hfun h).symm)
  -- transport: the global curve is `e^{-i(t-s)T}` applied to the local one, shifted
  have hk0 : HasDerivAt k ((-Complex.I) • (B y - T.op ⟨y, hyd⟩)) (s - s) := by
    simpa using hkderiv
  have hshift : HasDerivAt (fun u : ℝ => k (u - s)) ((-Complex.I) • (B y - T.op ⟨y, hyd⟩)) s :=
    HasDerivAt.comp_sub_const s s hk0
  have hcomp := ((T.stoneU (t - s)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hshift
  have hfun : (fun u : ℝ => T.stoneU (t - s) (k (u - s)))
      = fun u : ℝ => T.stoneU (t - u) (flow B u x) := by
    funext u
    change T.stoneU (t - s) (T.stoneU (-(u - s)) (flow B (u - s) y)) = _
    rw [T.stoneU_apply_stoneU, hy, flow_apply_flow]
    have e1 : (t - s) + -(u - s) = t - u := by ring
    have e2 : (u - s) + s = u := by ring
    rw [e1, e2]
  have hcomp' : HasDerivAt (fun u : ℝ => T.stoneU (t - s) (k (u - s)))
      (T.stoneU (t - s) ((-Complex.I) • (B y - T.op ⟨y, hyd⟩))) s := by
    simpa [Function.comp_def] using hcomp
  rw [hfun] at hcomp'
  exact hcomp'

/-- **The Duhamel estimate against an unbounded generator.**  If the defect `T - B` is at
most `K` along the truncated orbit, the truncated flow and the exact unitary group differ
by at most `K t`. -/
theorem norm_flow_sub_stoneU_le {B : H →L[ℂ] H} (t : ℝ) (ht : 0 ≤ t) (x : H)
    (hdom : ∀ s : ℝ, flow B s x ∈ T.domain) (K : ℝ)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖T.op ⟨flow B s x, hdom s⟩ - B (flow B s x)‖ ≤ K) :
    ‖flow B t x - T.stoneU t x‖ ≤ K * t := by
  set g : ℝ → H := fun u => T.stoneU (t - u) (flow B u x) with hg
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) t,
      HasDerivWithinAt g
        (T.stoneU (t - s) ((-Complex.I) • (B (flow B s x) - T.op ⟨flow B s x, hdom s⟩)))
        (Set.Icc 0 t) s :=
    fun s _ => (hasDerivAt_duhamel_stone T B t x hdom s).hasDerivWithinAt
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) t,
      ‖T.stoneU (t - s) ((-Complex.I) • (B (flow B s x) - T.op ⟨flow B s x, hdom s⟩))‖ ≤ K := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) t := ⟨hs.1, hs.2.le⟩
    rw [T.norm_stoneU_apply, norm_smul]
    have hnorm : ‖B (flow B s x) - T.op ⟨flow B s x, hdom s⟩‖
        = ‖T.op ⟨flow B s x, hdom s⟩ - B (flow B s x)‖ := norm_sub_rev _ _
    simp only [norm_neg, Complex.norm_I, one_mul, hnorm]
    exact hK s hs'
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound t
    (Set.right_mem_Icc.mpr ht)
  have hgt : g t = flow B t x := by
    simp only [hg, sub_self, UnboundedSelfAdjoint.stoneU_zero, ContinuousLinearMap.one_apply]
  have hg0 : g 0 = T.stoneU t x := by
    simp only [hg, sub_zero, flow_apply_zero]
  rw [hgt, hg0] at hmvt
  simpa using hmvt

/-! ## The leakage bound -/

/-- **The exact dynamics does not leak**: a bounded observable commuting with the exact
unitary group has constant content along the exact orbit. -/
theorem norm_omega_stoneU_eq {Om : H →L[ℂ] H}
    (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y)) (t : ℝ) (x : H) :
    ‖Om (T.stoneU t x)‖ = ‖Om x‖ := by
  rw [hcomm, T.norm_stoneU_apply]

/-- **The BRST leakage bound for an unbounded Hamiltonian.**  All of the leakage comes from
the defect of the truncated generator along the orbit. -/
theorem leakage_le {B Om : H →L[ℂ] H}
    (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y))
    (t : ℝ) (ht : 0 ≤ t) (x : H) (hdom : ∀ s : ℝ, flow B s x ∈ T.domain) (K : ℝ)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖T.op ⟨flow B s x, hdom s⟩ - B (flow B s x)‖ ≤ K) :
    ‖Om (flow B t x)‖ ≤ ‖Om x‖ + ‖Om‖ * (K * t) := by
  have hdiff := norm_flow_sub_stoneU_le T t ht x hdom K hK
  have hsplit : Om (flow B t x)
      = Om (T.stoneU t x) + Om (flow B t x - T.stoneU t x) := by
    rw [map_sub]; abel
  have h1 : ‖Om (T.stoneU t x)‖ = ‖Om x‖ := norm_omega_stoneU_eq T hcomm t x
  calc ‖Om (flow B t x)‖
      ≤ ‖Om (T.stoneU t x)‖ + ‖Om (flow B t x - T.stoneU t x)‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ ‖Om x‖ + ‖Om‖ * (K * t) := by
        rw [h1]
        gcongr
        exact (Om.le_opNorm _).trans (by gcongr)

/-- The leakage bound for a physical initial state. -/
theorem leakage_le_of_physical {B Om : H →L[ℂ] H}
    (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y))
    (t : ℝ) (ht : 0 ≤ t) (x : H) (hdom : ∀ s : ℝ, flow B s x ∈ T.domain) (K : ℝ)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖T.op ⟨flow B s x, hdom s⟩ - B (flow B s x)‖ ≤ K)
    (hOm : Om x = 0) :
    ‖Om (flow B t x)‖ ≤ ‖Om‖ * (K * t) := by
  simpa [hOm] using leakage_le T hcomm t ht x hdom K hK

end BookProof.BrstUnboundedLeakage
