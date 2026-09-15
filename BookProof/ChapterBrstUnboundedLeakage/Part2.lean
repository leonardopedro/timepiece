import Mathlib
import BookProof.ChapterBrstTruncationLeakage
import BookProof.ChapterStoneGenerator
import BookProof.ChapterBrstUnboundedLeakage.Part1

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

variable (T : UnboundedSelfAdjoint H)
/-! ## The finite-dimensional truncation -/

section Truncation

variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

/-- The orthogonal projection onto the retained subspace, as an operator on `H`. -/
noncomputable def projOp : H →L[ℂ] H := V.starProjection

/-- `T P`: the unbounded operator applied to the retained part.  Bounded because the
retained subspace is finite-dimensional. -/
noncomputable def opProj : H →L[ℂ] H :=
  (LinearMap.toContinuousLinearMap (T.op.comp (Submodule.inclusion hV))) ∘L
    (V.orthogonalProjection)

/-- The truncated (compressed) generator `P T P` — a *bounded* self-adjoint operator. -/
noncomputable def truncGen : H →L[ℂ] H := projOp V ∘L opProj T V hV

/-- The discarded off-diagonal block `(1 - P) T P`. -/
noncomputable def truncDefect : H →L[ℂ] H := (1 - projOp V) ∘L opProj T V hV

omit [CompleteSpace H] in
theorem projOp_apply_mem (x : H) : projOp V x ∈ V := V.starProjection_apply_mem x

omit [CompleteSpace H] in
theorem projOp_eq_self_of_mem {x : H} (hx : x ∈ V) : projOp V x = x :=
  Submodule.starProjection_eq_self_iff.mpr hx

omit [CompleteSpace H] in
theorem projOp_idempotent : IsIdempotentElem (projOp V) := V.isIdempotentElem_starProjection

omit [CompleteSpace H] in
theorem projOp_inner (x y : H) : ⟪projOp V x, y⟫_ℂ = ⟪x, projOp V y⟫_ℂ :=
  V.starProjection_isSymmetric x y

omit [CompleteSpace H] in
theorem opProj_apply (x : H) : opProj T V hV x = T.op ⟨projOp V x, hV (projOp_apply_mem V x)⟩ :=
  rfl

omit [CompleteSpace H] in
theorem opProj_apply_of_mem {x : H} (hx : x ∈ V) :
    opProj T V hV x = T.op ⟨x, hV hx⟩ := by
  have hsub : (⟨projOp V x, hV (projOp_apply_mem V x)⟩ : T.domain) = ⟨x, hV hx⟩ :=
    Subtype.ext (projOp_eq_self_of_mem V hx)
  rw [opProj_apply, hsub]

theorem truncGen_isSelfAdjoint : IsSelfAdjoint (truncGen T V hV) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  have hx : (projOp V x) ∈ V := projOp_apply_mem V x
  have hy : (projOp V y) ∈ V := projOp_apply_mem V y
  have hstep :
      ⟪T.op ⟨projOp V x, hV hx⟩, (projOp V y : H)⟫_ℂ
        = ⟪(projOp V x : H), T.op ⟨projOp V y, hV hy⟩⟫_ℂ :=
    T.symmetric ⟨projOp V x, hV hx⟩ ⟨projOp V y, hV hy⟩
  have hl : ⟪truncGen T V hV x, y⟫_ℂ = ⟪T.op ⟨projOp V x, hV hx⟩, (projOp V y : H)⟫_ℂ := by
    have : truncGen T V hV x = projOp V (T.op ⟨projOp V x, hV hx⟩) := rfl
    rw [this, projOp_inner]
  have hr : ⟪x, truncGen T V hV y⟫_ℂ = ⟪(projOp V x : H), T.op ⟨projOp V y, hV hy⟩⟫_ℂ := by
    have : truncGen T V hV y = projOp V (T.op ⟨projOp V y, hV hy⟩) := rfl
    rw [this, ← projOp_inner]
  have hgoal : ⟪truncGen T V hV x, y⟫_ℂ = ⟪x, truncGen T V hV y⟫_ℂ := by
    rw [hl, hr, hstep]
  exact hgoal

omit [CompleteSpace H] in
theorem proj_mul_truncGen : projOp V * truncGen T V hV = truncGen T V hV := by
  ext x
  simp [truncGen, ContinuousLinearMap.mul_apply,
    projOp_eq_self_of_mem V (projOp_apply_mem V _)]

/-- The truncated flow keeps a retained state inside the retained subspace (ODE
uniqueness). -/
theorem flow_mem_of_proj {P B : H →L[ℂ] H} (hPB : P * B = B)
    (t : ℝ) {x : H} (hx : P x = x) : P (flow B t x) = flow B t x := by
  set Z : H →L[ℂ] H := (-Complex.I) • B with hZ
  have hPZ : P * Z = Z := by rw [hZ, mul_smul_comm, hPB]
  set f : ℝ → H := fun u => (exp (u • Z)) x with hf
  have hfderiv : ∀ u : ℝ, HasDerivAt f (Z (f u)) u := by
    intro u
    have h1 : HasDerivAt (fun v : ℝ => exp (v • Z)) (exp (u • Z) * Z) u :=
      hasDerivAt_exp_smul_const Z u
    have hev : HasFDerivAt (fun S : H →L[ℂ] H => S x)
        ((ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ) (exp (u • Z)) :=
      ((ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ).hasFDerivAt
    have h2 := hev.comp_hasDerivAt u h1
    have hcomm : exp (u • Z) * Z = Z * exp (u • Z) := ((Commute.refl Z).smul_left u).exp_left.eq
    simpa [hf, Function.comp_def, hcomm, ContinuousLinearMap.mul_apply] using h2
  set d : ℝ → H := fun u => P (f u) - f u with hd
  have hPfderiv : ∀ u : ℝ, HasDerivAt (fun v => P (f v)) (Z (f u)) u := by
    intro u
    have h := (P.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt u (hfderiv u)
    have hPZ' : P (Z (f u)) = Z (f u) := by
      have := congrArg (fun S : H →L[ℂ] H => S (f u)) hPZ
      simpa [ContinuousLinearMap.mul_apply] using this
    simpa [Function.comp_def, hPZ'] using h
  have hdderiv : ∀ u : ℝ, HasDerivAt d 0 u := by
    intro u
    simpa [hd] using (hPfderiv u).sub (hfderiv u)
  have hconst : d t = d 0 :=
    is_const_of_deriv_eq_zero (fun u => (hdderiv u).differentiableAt)
      (fun u => (hdderiv u).deriv) t 0
  have h0 : d 0 = 0 := by simp [hd, hf, hx]
  have hzero : d t = 0 := by rw [hconst, h0]
  have := sub_eq_zero.mp hzero
  simpa [hd, hf, flow, hZ] using this

theorem flow_truncGen_mem (t : ℝ) {x : H} (hx : x ∈ V) : flow (truncGen T V hV) t x ∈ V := by
  have hx' : projOp V x = x := projOp_eq_self_of_mem V hx
  have h := flow_mem_of_proj (proj_mul_truncGen T V hV) t hx'
  rw [← h]
  exact projOp_apply_mem V _

theorem flow_truncGen_mem_domain (t : ℝ) {x : H} (hx : x ∈ V) :
    flow (truncGen T V hV) t x ∈ T.domain :=
  hV (flow_truncGen_mem T V hV t hx)

omit [CompleteSpace H] in
/-- Along a retained orbit the defect of the compressed generator is exactly the discarded
block `(1 - P) T P`. -/
theorem defect_eq_truncDefect {y : H} (hy : y ∈ V) :
    T.op ⟨y, hV hy⟩ - truncGen T V hV y = truncDefect T V hV y := by
  have h1 : opProj T V hV y = T.op ⟨y, hV hy⟩ := opProj_apply_of_mem T V hV hy
  simp [truncDefect, truncGen, ContinuousLinearMap.sub_apply, h1]

/-- The defect along a retained orbit, in the form the Duhamel estimate consumes. -/
theorem defect_orbit_le {x : H} (hx : x ∈ V) (s : ℝ) :
    ‖T.op ⟨flow (truncGen T V hV) s x, flow_truncGen_mem_domain T V hV s hx⟩
        - truncGen T V hV (flow (truncGen T V hV) s x)‖ ≤ ‖truncDefect T V hV‖ * ‖x‖ := by
  have hsa : IsSelfAdjoint (truncGen T V hV) := truncGen_isSelfAdjoint T V hV
  have hmem : flow (truncGen T V hV) s x ∈ V := flow_truncGen_mem T V hV s hx
  rw [defect_eq_truncDefect T V hV hmem]
  calc ‖truncDefect T V hV (flow (truncGen T V hV) s x)‖
      ≤ ‖truncDefect T V hV‖ * ‖flow (truncGen T V hV) s x‖ := (truncDefect T V hV).le_opNorm _
    _ = ‖truncDefect T V hV‖ * ‖x‖ := by rw [norm_flow_apply hsa]

/-- **The finite-`m` flow error for an unbounded Hamiltonian.**  The compressed flow tracks
the exact unitary group with an error controlled by the discarded off-diagonal block. -/
theorem norm_flow_truncGen_sub_stoneU_le (t : ℝ) (ht : 0 ≤ t) {x : H} (hx : x ∈ V) :
    ‖flow (truncGen T V hV) t x - T.stoneU t x‖ ≤ ‖truncDefect T V hV‖ * ‖x‖ * t := by
  have h := norm_flow_sub_stoneU_le T (B := truncGen T V hV) t ht x
    (fun s => flow_truncGen_mem_domain T V hV s hx) (‖truncDefect T V hV‖ * ‖x‖)
    (fun s _ => defect_orbit_le T V hV hx s)
  exact h

/-- **The BRST leakage of the truncated dynamics, unbounded Hamiltonian.** -/
theorem truncation_leakage_le {Om : H →L[ℂ] H}
    (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y))
    (t : ℝ) (ht : 0 ≤ t) {x : H} (hx : x ∈ V) :
    ‖Om (flow (truncGen T V hV) t x)‖
      ≤ ‖Om x‖ + ‖Om‖ * (‖truncDefect T V hV‖ * ‖x‖ * t) := by
  have h := leakage_le T (B := truncGen T V hV) hcomm t ht x
    (fun s => flow_truncGen_mem_domain T V hV s hx) (‖truncDefect T V hV‖ * ‖x‖)
    (fun s _ => defect_orbit_le T V hV hx s)
  simpa [mul_assoc] using h

/-- The leakage bound for a physical retained state: what the truncation creates is bounded
by the discarded block alone. -/
theorem truncation_leakage_le_of_physical {Om : H →L[ℂ] H}
    (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y))
    (t : ℝ) (ht : 0 ≤ t) {x : H} (hx : x ∈ V) (hOm : Om x = 0) :
    ‖Om (flow (truncGen T V hV) t x)‖ ≤ ‖Om‖ * (‖truncDefect T V hV‖ * ‖x‖ * t) := by
  simpa [hOm] using truncation_leakage_le T V hV hcomm t ht hx

end Truncation

/-! ## Restarts -/

section Restart

variable (Vs : ℕ → Submodule ℂ H) [∀ i, FiniteDimensional ℂ (Vs i)] (hVs : ∀ i, Vs i ≤ T.domain)

/-- The restarted truncated generators: cycle `i` is integrated with the compression of `T`
to the `i`-th retained subspace. -/
noncomputable def restartGen (i : ℕ) : H →L[ℂ] H := truncGen T (Vs i) (hVs i)

theorem restartGen_isSelfAdjoint (i : ℕ) : IsSelfAdjoint (restartGen T Vs hVs i) :=
  truncGen_isSelfAdjoint T (Vs i) (hVs i)

theorem norm_restartIter (τ : ℝ) (x : H) (n : ℕ) :
    ‖leakageIter (restartGen T Vs hVs) τ x n‖ = ‖x‖ :=
  norm_leakageIter (fun i => restartGen_isSelfAdjoint T Vs hVs i) τ x n

/-- **Accumulated leakage over restarts, unbounded Hamiltonian.**  With a fresh truncation
each cycle — and the restarted state retained in the new subspace, which is what the
re-seeding of the Krylov cycle provides — the leakage grows at most linearly in the number
of cycles, at the rate set by the discarded blocks. -/
theorem restart_leakage_le {Om : H →L[ℂ] H}
    (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y))
    (τ : ℝ) (hτ : 0 ≤ τ) (x : H) (D : ℝ)
    (hret : ∀ i, leakageIter (restartGen T Vs hVs) τ x i ∈ Vs i)
    (hD : ∀ i, ‖truncDefect T (Vs i) (hVs i)‖ ≤ D) :
    ∀ n : ℕ, ‖Om (leakageIter (restartGen T Vs hVs) τ x n)‖
      ≤ ‖Om x‖ + n * (‖Om‖ * (D * ‖x‖ * τ))
  | 0 => by simp
  | n + 1 => by
      have hxn : ‖leakageIter (restartGen T Vs hVs) τ x n‖ = ‖x‖ :=
        norm_restartIter T Vs hVs τ x n
      have hstep := truncation_leakage_le T (Vs n) (hVs n) (Om := Om) hcomm τ hτ (hret n)
      have hmono : ‖Om‖ * (‖truncDefect T (Vs n) (hVs n)‖
            * ‖leakageIter (restartGen T Vs hVs) τ x n‖ * τ)
          ≤ ‖Om‖ * (D * ‖x‖ * τ) := by
        rw [hxn]
        gcongr
        exact hD n
      have hsucc : ‖Om (leakageIter (restartGen T Vs hVs) τ x (n + 1))‖
          ≤ ‖Om (leakageIter (restartGen T Vs hVs) τ x n)‖ + ‖Om‖ * (D * ‖x‖ * τ) := by
        rw [leakageIter_succ]
        exact hstep.trans (by gcongr)
      have hind := restart_leakage_le hcomm τ hτ x D hret hD n
      have hcast : ((n : ℝ) + 1) * (‖Om‖ * (D * ‖x‖ * τ))
          = (n : ℝ) * (‖Om‖ * (D * ‖x‖ * τ)) + ‖Om‖ * (D * ‖x‖ * τ) := by ring
      push_cast
      rw [hcast]
      linarith

end Restart

end BookProof.BrstUnboundedLeakage
