# Reusable theorems from prove2me — frozen search for the offline Lean specialist

*Search run 2026-09-17 by the workspace agent against prove2me API `0.10.4`, default environment `Mathlib 0df444a (Lean v4.33.1)` (`0df444a360eaa60ab8c11dca51a86af692955474`).*

> **This file is the only record of the prove2me catalogue that the specialist can see.** The specialist works inside `../timepiece` with Lean `v4.28.0` and Mathlib only — no network, no prove2me access, no workspace. Every statement below is the **verbatim `formal_statement` as stored on the platform** (which elaborates at Lean `v4.33.1`), so it is a source to transcribe, not to import.

## How to use this file

1. These theorems are **already proved and machine-verified on prove2me**. They cannot be `import`ed into timepiece: a Lean `import` binds one toolchain, and the platform is `v4.33.1` while timepiece is `v4.28.0`.
2. To use one, **state it as a named hypothesis** of the timepiece theorem that needs it — a `Prop`-valued binder, or a structure field in the style of `FarisLavine`'s hypotheses — with the platform name and id in a comment. Do **not** introduce a silent `axiom`; the platform node is the external witness, and the project's axiom gate (`axiom_gate.lean`, `Audits/`) must keep listing anything assumed.
3. Restate against the `4.28.0` Mathlib API where it drifted. A `Mathlib-only` row can be restated directly; a `needs platform-local definitions` row must be abstracted first (re-declare the minimal notion — a form, a kernel, a coercivity predicate — and state the result over it).
4. The rows are grouped by the route item they serve, matching the plan items in `CONSOLIDATED_PLAN.md` (“Cross-platform reuse” and the two “Plan items” sections).
5. The portability verdict is against **timepiece's own Mathlib (`v4.28.0`)**, verified by `#check` on the `v4.28.0` toolchain — not against the `v4.33.1` Mathlib of the platform. A row marked `needs defs (4.28 gap)` uses an identifier that does not exist here (or denotes something else) and so is *not* a direct transcription.
6. Seven `Mathlib-only` rows are **already transcribed** in-repo as named hypotheses, for the NS / QG Faris–Lavine route: `BookProof/ChapterProve2meReuse.lean` (`BookProof.Prove2meReuse`) carries one `Prop` per theorem plus the bundle `RouteHypotheses`, and projects them onto the route-facing names `ns_convolution_symmetric`, `ns_convolution_compact`, `ns_friedrichs_lower_bound`, `lagrangian_det_add_two`, `qg_compact_spectral_edge`, `qg_high_part_finiteDimensional`, `qg_gribov_negative_direction`. The three `4.28 gap` rows are listed there as deferred, so nothing is lost and no `axiom` is introduced.

## Summary

| route item | theorem | author | portability |
| :-- | :-- | :-- | :-- |
| 1 | `BookProof.ChapterMajoranaProp76.fourierTransform_isNote4Unitary` | leonardopedro | needs defs |
| 1/3 | `FourierFA.parseval` | raver1975 | needs defs |
| 1/3 | `FourierFA.parseval_norm` | raver1975 | needs defs |
| 3 | `FourierFA.dft_conv` | raver1975 | needs defs |
| 3 | `ChebotarevDFT.dft_conv` | raver1975 | needs defs |
| 1–3 | `QFS.formHs_ball_ne_top_of_L2inclusion` | dbenbenn | needs defs |
| 1–3 | `QFS.formHs_congr_ae` | dbenbenn | needs defs |
| 1–3 | `QFS.localPoincare_visible_on` | dbenbenn | needs defs |
| 1–3 | `QFS.chain_estimate` | dbenbenn | needs defs |
| 1–3 | `QFS.cutoff_le_one` | dbenbenn | needs defs |
| 1–3 | `QFS.lintegral_stepG_eq` | dbenbenn | needs defs |
| 1–3 | `QFS.limsup_lintegral_stepG_le` | dbenbenn | needs defs |
| 1–3 | `QFS.path_props_long` | dbenbenn | needs defs |
| 3 | `MeasureTheory.L2.convolutionCLM_isSymmetric_of_conj_neg` | Claude | Mathlib-only |
| 3 | `MeasureTheory.L2.exists_convolutionCLM_isCompactOperator_of_compactSpace` | Claude | Mathlib-only |
| 4 | `VectorSpaceOpt.coercive_selfadjoint_bijective` | wenxinzhang | needs defs |
| 4 (adjacent) | `VectorSpaceOpt.cg_directions_conjugate_until_stop` | wenxinzhang | needs defs |
| 4 / §5 | `posDef_quadratic_form_lower_bound` | olivier | Mathlib-only |
| 4 (adjacent) | `Bochner.fourierTransform_nonneg` | carlok | needs defs (4.28 gap) |
| 4 / §3 | `AsaiLargeSieve.schur_row_bound_of_quasiOrthogonal` | raver1975 | needs defs |
| 4 / §3 | `AsaiLargeSieve.largeSieve_of_schur` | raver1975 | needs defs |
| 4 | `NavierStokes.hasDerivAt_heatFlow` | korbonits | needs defs |
| 4 | `NavierStokes.heatFlow_heatFlow` | korbonits | needs defs |
| 4 | `NavierStokes.integral_heatKernel_mul_heatKernel` | korbonits | needs defs |
| 4 | `NavierStokes.norm_heatFlow_le` | korbonits | needs defs |
| §6 | `singular_value_zero_le_spectral_norm` | Aphrodite | needs defs (4.28 gap) |
| §6 | `spectral_norm_le_singular_value_zero` | Aphrodite | needs defs (4.28 gap) |
| §6 (adjacent) | `Diaz.det_add_two` | carlok | Mathlib-only |
| §6 (adjacent) | `Diaz.det_pencil_eq_conic` | carlok | needs defs |
| QG | `ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker` | Claude | Mathlib-only |
| QG | `ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal` | Claude | Mathlib-only |
| QG (adjacent) | `GribovRegion.exists_neg_quadratic_form_of_traceless` | Lucas | Mathlib-only |

## The theorems

### `BookProof.ChapterMajoranaProp76.fourierTransform_isNote4Unitary`

* **platform id** `2cdf5458-531e-46ef-a4e3-e76ff33a66c8` · **status** Proved · **author** leonardopedro · **route item** 1
* **what it buys.** The L² Fourier transform is a unitary (`IsNote4Unitary`) — the Plancherel counterpart of the spatial transform. Ours already, but it is the *shape* to mirror on `L²(ℝ_p^d × ℝ_u^m)`.
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem BookProof.ChapterMajoranaProp76.fourierTransform_isNote4Unitary :
    IsNote4Unitary ℂ (Lp.fourierTransformₗᵢ E F : Lp F 2 volume → Lp F 2 volume) := by sorry
```

### `FourierFA.parseval`

* **platform id** `6d1c2ef4-b7e4-4ab6-b014-79508ad3b873` · **status** Proved · **author** raver1975 · **route item** 1/3
* **what it buys.** Parseval/Plancherel for the finite abelian group DFT (the discrete-mode picture of the spatial transform).
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem FourierFA.parseval(f g : G → ℂ) :
    ∑ ψ : AddChar G ℂ, dft f ψ * conj (dft g ψ)
      = (Fintype.card G : ℂ) * ∑ x, f x * conj (g x) := by sorry
```

### `FourierFA.parseval_norm`

* **platform id** `a9442a65-0b95-4748-94f8-fde2df506b1c` · **status** Proved · **author** raver1975 · **route item** 1/3
* **what it buys.** Norm form of the same Parseval identity.
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem FourierFA.parseval_norm(f : G → ℂ) :
    ∑ ψ : AddChar G ℂ, ‖dft f ψ‖ ^ 2 = (Fintype.card G : ℝ) * ∑ x, ‖f x‖ ^ 2 := by sorry
```

### `FourierFA.dft_conv`

* **platform id** `246ac8f1-e1e9-4e34-a2b6-8cf4790046e5` · **status** Proved · **author** raver1975 · **route item** 3
* **what it buys.** The DFT turns convolution into pointwise product — the discrete shadow of ‘local products become momentum convolutions’.
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem FourierFA.dft_conv(f g : G → ℂ) (ψ : AddChar G ℂ) :
    dft (conv f g) ψ = dft f ψ * dft g ψ := by sorry
```

### `ChebotarevDFT.dft_conv`

* **platform id** `34ead44a-6a60-48b0-98f0-ca9b89440fa3` · **status** Proved · **author** raver1975 · **route item** 3
* **what it buys.** Same convolution theorem, independent formalization (cross-check).
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem ChebotarevDFT.dft_conv(f g : ZMod p → ℂ) (k : ZMod p) : 𝓕 (conv f g) k = 𝓕 f k * 𝓕 g k := by sorry
```

### `QFS.formHs_ball_ne_top_of_L2inclusion`

* **platform id** `76bd738e-f79c-480a-b1e4-85142ab89c3f` · **status** Proved · **author** dbenbenn · **route item** 1–3
* **what it buys.** The `H^s` form-domain ball has finite measure once `L²` is included — the formal content of the finite energy/momentum cutoff (residual (iii)).
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem QFS.formHs_ball_ne_top_of_L2inclusion {d : ℕ} (hd : 0 < d) {α Λ : ℝ}
    (hα : 0 < α) (hα2 : α < 2)
    {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k)
    {C C' : ℝ≥0∞} (hC : C ≠ ∞) (hC' : C' ≠ ∞)
    {w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hincl : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, Measurable g →
      (Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ENNReal.ofReal ((g p.2 - g p.1) ^ 2) * k p.1 p.2) →
      formHs Set.univ α g ≤ C * form Set.univ k g
        + C' * ∫⁻ x, ENNReal.ofReal (2 * g x ^ 2) * w x)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      k p.1 p.2)
    {x₀ : EuclideanSpace ℝ (Fin d)} {R R' : ℝ} (hRR : R < R')
    (hL2 : ∫⁻ x in ball x₀ R', ENNReal.ofReal (f x ^ 2) ≠ ∞)
    (hL2w : ∫⁻ x in ball x₀ R', ENNReal.ofReal (f x ^ 2) * w x ≠ ∞)
    (hHk : form (ball x₀ R') k f ≠ ∞) :
    formHs (ball x₀ R) α f ≠ ∞ := by sorry
```

### `QFS.formHs_congr_ae`

* **platform id** `e918a7b3-696e-40a4-974e-94492e96e4b8` · **status** Proved · **author** dbenbenn · **route item** 1–3
* **what it buys.** The `H^s` form is a.e.-invariant (well-definedness of the form domain).
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem QFS.formHs_congr_ae {Ω : Set (EuclideanSpace ℝ (Fin d))} (α : ℝ)
    {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hfg : ∀ᵐ x ∂(volume.restrict Ω), f x = g x) : formHs Ω α f = formHs Ω α g := by sorry
```

### `QFS.localPoincare_visible_on`

* **platform id** `be2ce877-e0f2-4b84-b04f-5d34be97a875` · **status** Proved · **author** dbenbenn · **route item** 1–3
* **what it buys.** A local Poincaré inequality for the form — the coercivity input that makes the cutoff comparison bounded below.
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem QFS.localPoincare_visible_on {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α c₀ : ℝ} (hα : 0 ≤ α) (hd : 0 < d)
    (hc₀ : 0 ≤ c₀) {U : Set (EuclideanSpace ℝ (Fin d))} (hUm : MeasurableSet U)
    {P : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))} (hPm : MeasurableSet P)
    (hU : ∀ p ∈ P, p.1 ≠ p.2 → ENNReal.ofReal (c₀ * ‖p.1 - p.2‖ ^ d) ≤
      volume (U ∩ closedBall (midCentre v ϑ p.1 p.2) ‖p.1 - p.2‖))
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) :
    ENNReal.ofReal c₀ * ∫⁻ p in P,
        ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α))
      ≤ ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
          (∫⁻ s, ∫⁻ z in {z | z - s ∈ cone v ϑ},
            U.indicator (fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2)) z *
              ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)))
        + ENNReal.ofReal (chainConst_prime d ϑ α) * unitBallVol d *
          (∫⁻ t, ∫⁻ z in {z | z - t ∈ cone v ϑ},
            U.indicator (fun z => ENNReal.ofReal (2 * (f t - f z) ^ 2)) z *
              ENNReal.ofReal (‖z - t‖ ^ (-(d : ℝ) - α))) := by sorry
```

### `QFS.chain_estimate`

* **platform id** `afb8611d-7c36-4184-82b0-abaae77cb01a` · **status** Proved · **author** dbenbenn · **route item** 1–3
* **what it buys.** Chaining estimate gluing local Poincaré bounds — the `H^s` embedding argument behind the Faris–Lavine domain.
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem QFS.chain_estimate {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {α Λ R₀ lam : ℝ} {ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hω : DiscreteKernelBounds Γ α Λ R₀ (lattice d) ω) (hα : 0 < α) (hlam : 1 ≤ lam)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) {x y : EuclideanSpace ℝ (Fin d)}
    (w : (latticeGraph Γ).Walk x y)
    (hb : ∀ D ∈ w.darts, ‖D.toProd.1 - D.toProd.2‖ ≤ lam * ‖x - y‖ ∧
      R₀ < ‖D.toProd.1 - D.toProd.2‖) :
    ENNReal.ofReal ((f x - f y) ^ 2) * jumpKernel d α x y
      ≤ ENNReal.ofReal ((w.length : ℝ) * lam ^ ((d : ℝ) + α) * Λ) *
        (w.darts.map (fun D => ENNReal.ofReal ((f D.toProd.1 - f D.toProd.2) ^ 2)
          * ω D.toProd.1 D.toProd.2)).sum := by sorry
```

### `QFS.cutoff_le_one`

* **platform id** `7a4504f6-f445-46ca-9226-7e2bf1306f32` · **status** Proved · **author** dbenbenn · **route item** 1–3
* **what it buys.** The cutoff is ≤ 1 (the sharp bound needed to keep `c` uniform).
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
lemma QFS.cutoff_le_one (x₀ : EuclideanSpace ℝ (Fin d)) (R R' : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : cutoff x₀ R R' x ≤ 1 := by sorry
```

### `QFS.lintegral_stepG_eq`

* **platform id** `af5ea30d-5b21-4aea-b858-5c2c06c3564a` · **status** Proved · **author** dbenbenn · **route item** 1–3
* **what it buys.** Layer-cake/step-function identity used to bound the form.
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem QFS.lintegral_stepG_eq {h : ℝ} (hh : 0 < h) (S : Set (EuclideanSpace ℝ (Fin d))) (R₀ : ℝ)
    (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫⁻ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d), stepG d h S R₀ k f p
      = ∫⁻ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
          discreteC d h S R₀ (discreteKernel d k h) (cubeAvg d h f)
            (stepIndex d h p.1, stepIndex d h p.2) := by sorry
```

### `QFS.limsup_lintegral_stepG_le`

* **platform id** `93993aa6-4879-4580-b485-26e70515ad8e` · **status** Proved · **author** dbenbenn · **route item** 1–3
* **what it buys.** The limsup form of the same bound (cutoff removal).
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem QFS.limsup_lintegral_stepG_le {α Λ R R' : ℝ} (hα : 0 ≤ α)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : ∀ a b, k a b ≤ ENNReal.ofReal Λ * jumpKernel d α a b)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => k p.1 p.2)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hfm : Measurable f)
    (hf : LocallyIntegrable f volume) (hd : 0 < d)
    {x₀ : EuclideanSpace ℝ (Fin d)}
    (hn : ℕ → ℝ) (hpos : ∀ n, 0 < hn n) (hlim : Filter.Tendsto hn Filter.atTop (nhds 0))
    (hsmall : ∀ n, Real.sqrt d * (hn n / 2) ≤ R' - R)
    (hfinite : formHs (ball x₀ R') α f ≠ ⊤) :
    Filter.limsup (fun n => ∫⁻ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
        stepG d (hn n) (ball x₀ R) (3 * Real.sqrt d * hn n) k f p) Filter.atTop
      ≤ form (ball x₀ R) k f := by sorry
```

### `QFS.path_props_long`

* **platform id** `e3144bf5-1d58-4c54-bdb3-db48a4e03f8e` · **status** Proved · **author** dbenbenn · **route item** 1–3
* **what it buys.** Path properties of the chaining argument (supporting lemma).
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem QFS.path_props_long (hd : 1 ≤ d) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) (R₀ : ℝ) :
    PathPropsLongHolds d ϑ R₀ := by sorry
```

### `MeasureTheory.L2.convolutionCLM_isSymmetric_of_conj_neg`

* **platform id** `f7acdc05-a79d-5e62-9e62-4744e92d9ee6` · **status** Proved · **author** Claude · **route item** 3
* **what it buys.** The convolution operator is symmetric when the kernel satisfies `f (-x) = conj (f x)` — symmetry/self-adjointness of `Û_i(q)`.
* **portability.** Mathlib-only — can be restated directly on the 4.28 API.
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem MeasureTheory.L2.convolutionCLM_isSymmetric_of_conj_neg
    (G : Type*) [MeasurableSpace G] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure] [MeasureTheory.IsFiniteMeasure μ]
    (f : C(G, ℂ)) (hf : ∀ x, f (-x) = star (f x))
    (T : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ)
    (hT : ∀ φ : MeasureTheory.Lp ℂ 2 μ, (T φ : G → ℂ) =ᵐ[μ]
      ((f : G → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (φ : G → ℂ))) :
    LinearMap.IsSymmetric (T : MeasureTheory.Lp ℂ 2 μ →ₗ[ℂ] MeasureTheory.Lp ℂ 2 μ) := by sorry
```

### `MeasureTheory.L2.exists_convolutionCLM_isCompactOperator_of_compactSpace`

* **platform id** `b4b789f8-1e81-5087-ba89-9a6b3bef55f0` · **status** Proved · **author** Claude · **route item** 3
* **what it buys.** Convolution with a continuous kernel on a compact group is compact — compactness of the convolution mode operator.
* **portability.** Mathlib-only — can be restated directly on the 4.28 API.
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem MeasureTheory.L2.exists_convolutionCLM_isCompactOperator_of_compactSpace
    (G : Type*) [MeasurableSpace G] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure] [MeasureTheory.IsFiniteMeasure μ]
    (f : C(G, ℂ)) (hf : ∀ x, f (-x) = star (f x)) :
    ∃ T : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ,
      (∀ φ : MeasureTheory.Lp ℂ 2 μ, (T φ : G → ℂ) =ᵐ[μ]
        ((f : G → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (φ : G → ℂ))) ∧
      IsCompactOperator T ∧ LinearMap.IsSymmetric (T : MeasureTheory.Lp ℂ 2 μ →ₗ[ℂ] MeasureTheory.Lp ℂ 2 μ) := by sorry
```

### `VectorSpaceOpt.coercive_selfadjoint_bijective`

* **platform id** `35241842-a11f-40ab-9014-feca9c844c94` · **status** Proved · **author** wenxinzhang · **route item** 4
* **what it buys.** A coercive real self-adjoint bounded operator is bijective — the bounded-cutoff surrogate for hypothesis (3) (`N + 1` onto).
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
namespace VectorSpaceOpt

/-- The operator-invertibility fact recorded as Chapter 10, Problem 10. -/
theorem coercive_selfadjoint_bijective
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Q : H →L[ℝ] H) (m M : ℝ) (hm : 0 < m)
    (hself : IsRealSelfAdjoint Q) (hbounds : IsCoerciveBetween Q m M) :
    Function.Bijective Q := by
  sorry

end VectorSpaceOpt
```

### `VectorSpaceOpt.cg_directions_conjugate_until_stop`

* **platform id** `f5cf73cd-2599-4ef0-880e-5e2ccda7ccbc` · **status** Proved · **author** wenxinzhang · **route item** 4 (adjacent)
* **what it buys.** Coercive self-adjoint operator ⇒ conjugacy invariant of the CG iterates (secondary; useful if the comparison is realized numerically).
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
namespace VectorSpaceOpt

/-- The conjugacy invariant proved in §10.8 before the convergence estimate. -/
theorem cg_directions_conjugate_until_stop
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Q : H →L[ℝ] H) (b x₀ : H) (m M : ℝ) (hm : 0 < m)
    (hself : IsRealSelfAdjoint Q) (hbounds : IsCoerciveBetween Q m M) :
    ∀ n : ℕ,
      (∀ k ≤ n, (conjugateGradientIterate Q b x₀ k).p ≠ 0) →
      ∀ i j, i < j → j ≤ n →
        ⟪(conjugateGradientIterate Q b x₀ i).p,
          Q ((conjugateGradientIterate Q b x₀ j).p)⟫ = 0 := by
  sorry

end VectorSpaceOpt
```

### `posDef_quadratic_form_lower_bound`

* **platform id** `0fc6dadb-9da8-4557-815b-127c310e3ef3` · **status** Proved · **author** olivier · **route item** 4 / §5
* **what it buys.** A positive-definite matrix has a positive form lower bound `c‖x‖² ≤ ⟨x, M x⟩` — the fibrewise `PosSymOp.pos` input for Friedrichs.
* **portability.** Mathlib-only — can be restated directly on the 4.28 API.
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem posDef_quadratic_form_lower_bound {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (M *ᵥ x) := by sorry
```

### `Bochner.fourierTransform_nonneg`

* **platform id** `5c399c24-e6b3-41f4-bdf8-bdef8ebcdbdb` · **status** Proved · **author** carlok · **route item** 4 (adjacent)
* **what it buys.** Bochner: a positive-definite function has non-negative Fourier transform — positivity of the viscous (Fourier-multiplier) symbol.
* **portability.** Needs defs (4.28 gap): the statement's hypothesis `IsPositiveDefinite` **does not exist** in timepiece's Mathlib (`#check @IsPositiveDefinite` → `unknown identifier`). Restate by first defining the positive-definiteness predicate locally (or replacing it with a kernel/`∀ x, 0 ≤ …` form), then state and prove the Bochner inequality over that; the platform node is not a direct transcription.
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
namespace Bochner

theorem fourierTransform_nonneg
    (f : ℝ → ℂ) (hf_cont : Continuous f) (hf_int : Integrable f (volume : Measure ℝ))
    (hf_pd : IsPositiveDefinite f) (ξ : ℝ) :
    0 ≤ fourierTransform f ξ := by sorry

end Bochner
```

### `AsaiLargeSieve.schur_row_bound_of_quasiOrthogonal`

* **platform id** `20165988-4656-4936-9f94-acd5e9c37d23` · **status** Proved · **author** raver1975 · **route item** 4 / §3
* **what it buys.** Row-sum Schur bound from quasi-orthogonality — the particle-number-independent bound on the advection kernel.
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem AsaiLargeSieve.schur_row_bound_of_quasiOrthogonal(S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ) (D e : ℝ)
    (hD : 0 ≤ D) (h : QuasiOrthogonal S lam N D e) :
    ∀ m ∈ Finset.range N, ∑ n ∈ Finset.range N, ‖gram S lam m n‖ ≤ D + e * N := by sorry
```

### `AsaiLargeSieve.largeSieve_of_schur`

* **platform id** `f1277cdd-5b0b-43d0-b499-6117be780d1a` · **status** Proved · **author** raver1975 · **route item** 4 / §3
* **what it buys.** The row-sum (Schur) test implies the large-sieve inequality — the abstract `dΓ`/kernel bound in the project's Schur gate.
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem AsaiLargeSieve.largeSieve_of_schur(S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ) (K : ℝ)
    (hK : ∀ m ∈ Finset.range N, ∑ n ∈ Finset.range N, ‖gram S lam m n‖ ≤ K) :
    LargeSieve S lam N K := by sorry
```

### `NavierStokes.hasDerivAt_heatFlow`

* **platform id** `d70bd03f-33f6-4201-b813-840824ca07d9` · **status** Proved · **author** korbonits · **route item** 4
* **what it buys.** `∂_t heatFlow = ν Δ heatFlow` — the viscous semigroup generator (the classical model of `H_visc` on the cutoff).
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
namespace NavierStokes
theorem hasDerivAt_heatFlow {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) {f : Vec 3 → Vec 3}
    (hf : AEStronglyMeasurable f volume) {M : ℝ} (hM : ∀ y, ‖f y‖ ≤ M) (x : Vec 3) :
    HasDerivAt (fun s => heatFlow ν s f x) (ν • Δ (heatFlow ν t f) x) t := by sorry
end NavierStokes
```

### `NavierStokes.heatFlow_heatFlow`

* **platform id** `57f597e6-85a2-4bc4-932a-55ee1da2b25d` · **status** Proved · **author** korbonits · **route item** 4
* **what it buys.** The heat flow is a semigroup, `heatFlow s ∘ heatFlow t = heatFlow (s+t)`.
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
namespace NavierStokes
theorem heatFlow_heatFlow {ν : ℝ} (hν : 0 < ν) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {f : Vec 3 → Vec 3}
    (hf : AEStronglyMeasurable f volume) {M : ℝ} (hM : ∀ y, ‖f y‖ ≤ M) (x : Vec 3) :
    heatFlow ν s (heatFlow ν t f) x = heatFlow ν (s + t) f x := by sorry
end NavierStokes
```

### `NavierStokes.integral_heatKernel_mul_heatKernel`

* **platform id** `b4d521f5-61d7-493a-8031-cad3adb8444b` · **status** Proved · **author** korbonits · **route item** 4
* **what it buys.** Heat-kernel convolution identity (the convolution algebra for viscosity).
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
namespace NavierStokes
theorem integral_heatKernel_mul_heatKernel {ν : ℝ} (hν : 0 < ν) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (w : Vec 3) :
    ∫ y, heatKernel ν s (w - y) * heatKernel ν t y = heatKernel ν (s + t) w := by sorry
end NavierStokes
```

### `NavierStokes.norm_heatFlow_le`

* **platform id** `88931298-072a-4967-8cad-f09e15b5d75d` · **status** Proved · **author** korbonits · **route item** 4
* **what it buys.** Contraction bound `‖heatFlow ν t f‖ ≤ M` — the dissipative `L^∞` bound.
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
namespace NavierStokes
theorem norm_heatFlow_le {ν : ℝ} (hν : 0 < ν) (t : ℝ) {f : Vec 3 → Vec 3} {M : ℝ}
    (hM : ∀ y, ‖f y‖ ≤ M) (x : Vec 3) : ‖heatFlow ν t f x‖ ≤ M := by sorry
end NavierStokes
```

### `singular_value_zero_le_spectral_norm`

* **platform id** `dc5ff0e0-72e0-4a4b-85e1-95bd8ba76d14` · **status** Proved · **author** Aphrodite · **route item** §6
* **what it buys.** `σ₀(Y) ≤ ‖Y‖` (largest singular value bounds the operator norm).
* **portability.** Needs defs (4.28 gap): `Matrix.singularValues` **does not exist** in timepiece's Mathlib (`unknown constant`), and the `spectralNorm` that does exist is the `Algebra`-norm `spectralNorm 𝕜 x : ℝ` — *not* the matrix operator norm of the platform statement. Restate after defining the singular values / operator norm locally.
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem singular_value_zero_le_spectral_norm :
    ∀ {n₁ n₂ : ℕ} (Y : Matrix (Fin n₁) (Fin n₂) ℝ),
      (Matrix.toEuclideanLin Y).singularValues 0 ≤ spectralNorm Y := by sorry
```

### `spectral_norm_le_singular_value_zero`

* **platform id** `1243cf8d-48bd-44aa-bee7-f997599e2467` · **status** Proved · **author** Aphrodite · **route item** §6
* **what it buys.** `‖Y‖ ≤ σ₀(Y)` — with the previous, `‖Y‖ = σ₀(Y)`; the norm input to `σ_min(1+A) ≥ 1 − ‖A‖ > 0` in §6.1.
* **portability.** Needs defs (4.28 gap): same two obstacles as the preceding row (`Matrix.singularValues` absent; `spectralNorm` here is a different notion).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem spectral_norm_le_singular_value_zero :
    ∀ {n₁ n₂ : ℕ} (Y : Matrix (Fin n₁) (Fin n₂) ℝ),
      spectralNorm Y ≤ (Matrix.toEuclideanLin Y).singularValues 0 := by sorry
```

### `Diaz.det_add_two`

* **platform id** `47ddec80-bd8c-47cb-a891-32d7f12de9b3` · **status** Proved · **author** carlok · **route item** §6 (adjacent)
* **what it buys.** `det(X+Y)` for `2×2` in terms of traces — the small-case template for the `detPoly` expansion of §6.1 (our 3×3 case is the target).
* **portability.** Mathlib-only — can be restated directly on the 4.28 API.
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem Diaz.det_add_two {R : Type*} [CommRing R] (X Y : Matrix (Fin 2) (Fin 2) R) :
    (X + Y).det = X.det + Y.det + Matrix.trace X * Matrix.trace Y - Matrix.trace (X * Y) := by sorry
```

### `Diaz.det_pencil_eq_conic`

* **platform id** `f93dad25-84e2-4727-8b3a-cf2dd8103815` · **status** Proved · **author** carlok · **route item** §6 (adjacent)
* **what it buys.** A determinant pencil is a conic — determinant-as-polynomial technique, adjacent to `volumePoly`.
* **portability.** Needs platform-local definitions (re-declare a minimal abstraction and state the result over it).
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem Diaz.det_pencil_eq_conic {K : Subfield ℂ} {u : ℂ} (hT : Transcendental K u) (hu0 : u ≠ 0)
    (hρ : u * conj u ∈ K) (A B C : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ i j, A i j ∈ K) (hB : ∀ i j, B i j ∈ K) (hC : ∀ i j, C i j ∈ K)
    (hdet : (A + u • B + (conj u) • C).det = 0) :
    ∃ c : ℂ, c ∈ K ∧ ∀ x y z : ℂ,
      (x • A + y • B + z • C).det = c * (y * z - (u * conj u) * x ^ 2) := by sorry
```

### `ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker`

* **platform id** `9b157d55-6fac-50a1-a424-4b346c1ec0da` · **status** Proved · **author** Claude · **route item** QG
* **what it buys.** For compact symmetric `T`, the orthogonal of the span of the non-zero eigenspaces is `ker T` — the compact-symmetric spectral decomposition consumed by the band/Ritz ladder.
* **portability.** Mathlib-only — can be restated directly on the 4.28 API.
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
    (⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ)ᗮ = LinearMap.ker (T : E →ₗ[𝕜] E) := by sorry
```

### `ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal`

* **platform id** `2126e74d-67bb-5b87-90d7-98ffb1eda8fd` · **status** Proved · **author** Claude · **route item** QG
* **what it buys.** The high-part finite-dimensionality refinement of the same spectral decomposition (Ritz truncation).
* **portability.** Mathlib-only — can be restated directly on the 4.28 API.
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
theorem ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (X : Submodule 𝕜 E)
    (hX : ∀ r : ℝ, 0 < r → X ⊓ (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥ ∨ X ≤ (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ) :
    X ≤ LinearMap.ker (T : E →ₗ[𝕜] E) ∨ FiniteDimensional 𝕜 ↥X := by sorry
```

### `GribovRegion.exists_neg_quadratic_form_of_traceless`

* **platform id** `a883b692-5447-48b6-8920-15e669d3954e` · **status** Proved · **author** Lucas · **route item** QG (adjacent)
* **what it buys.** A traceless Hermitian matrix has a negative direction — a Gribov-region fact adjacent to the QG quadratic form.
* **portability.** Mathlib-only — can be restated directly on the 4.28 API.
* **statement as stored on prove2me (Lean 4.33.1):**

```lean
namespace GribovRegion

open scoped Matrix

theorem exists_neg_quadratic_form_of_traceless {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsHermitian) (htr : M.trace = 0) (hne : M ≠ 0) :
    ∃ w : Fin n → ℝ, w ⬝ᵥ M *ᵥ w < 0 := by sorry

end GribovRegion
```

## Anti-reuse — `Proved` badges that must NOT be cited

Both are marked `Proved` and both are worthless for this plan. Recorded so the trap is not rediscovered.

### `navier_stokes_global_regularity` — do not cite

* platform id `af8cbeaf-d12a-474b-b532-438ed7d965b9` · author tianyipeng
```lean
import Mathlib

theorem navier_stokes_global_regularity :
    ∀ u₀ : (Fin 3 → ℝ) → (Fin 3 → ℝ),
      ContDiff ℝ ⊤ u₀ →
      (∀ x : Fin 3 → ℝ,
        ∑ i : Fin 3, fderiv ℝ (fun y => u₀ y i) x (Pi.basisFun ℝ (Fin 3) i) = 0) →
      ∃ u : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ),
        (∀ t : ℝ, ContDiff ℝ ⊤ (u t)) ∧ u 0 = u₀ := by
  sorry
```

### `sum_of_squares_r_function` — do not cite

* platform id `b897f82b-1660-4f86-9ae0-fef9a03f25c2` · author tianyipeng
```lean
import Mathlib

theorem sum_of_squares_r_function (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    {v : Fin k → ℤ | ∑ i, v i ^ 2 = n}.ncard > 0 → True := by
  sorry
```

* `navier_stokes_global_regularity` never states the momentum equation — it only asserts the existence of *some* smooth `u` with `u 0 = u₀`, so it says nothing about Navier–Stokes.
* `sum_of_squares_r_function` has conclusion literally `True`.

## Leaf-name triage — checked and *not* needed

A pipeline stub can share its leaf name with another user's `Proved` node and still be no reuse
candidate, because timepiece's **own** Mathlib (`v4.28.0`) already proves the fact. One such hit is
recorded so it is not re-investigated.

### `QFS.abs_coord_le_norm` — do not cite (already in timepiece's Mathlib)

* platform id `9fed8780-d3ea-4228-820b-252f6afb439a` · status Proved · author dbenbenn ·
  leaf-matches `BookProof.HermiteQuadraticEsa.abs_coord_le_norm`

```lean
lemma QFS.abs_coord_le_norm (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |x i| ≤ ‖x‖ := by sorry
```

* **Verdict.**  Nothing to transcribe.  `EuclideanSpace ℝ (Fin d)` is `PiLp 2 (fun _ : Fin d => ℝ)`,
  so the statement is `PiLp.norm_apply_le`
  (`Mathlib/Analysis/Normed/Lp/PiLp.lean`, module `Mathlib`) composed with `Real.norm_eq_abs`;
  verified in this repository by

```lean
import Mathlib
example (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |x i| ≤ ‖x‖ :=
  by simpa using PiLp.norm_apply_le (p := 2) x i
```

* The leaf match is a naming coincidence on a generic one-liner; the platform node is **not** an
  instrument for the route, and no `import Theorems.Thm_…` reduction is owed for it.

## What was *not* found

* No platform theorem states **Faris–Lavine**, an **essential self-adjointness criterion**, a **Friedrichs extension**, **second quantization / `dΓ`**, a **Fock-space** construction, or a **Kato–Rellich** bound. Those instruments remain the project's own (`ChapterFarisLavineCore`, `ChapterQgOuterFockFarisLavine`, …); nothing on the platform duplicates them.
* No platform theorem asserts **global regularity of the Navier–Stokes equation** (see the anti-reuse section), nor **any mass gap**.
