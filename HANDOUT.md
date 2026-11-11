# HANDOUT — paused work on the flow of `H` (multiplier model)

Written 2026-11-08 while the user asked to pause. Everything needed to restart is below.

## 1. Snapshot

- Repo: `/home/leo/Projects/timepiece`, branch `main`, HEAD `0018f95`
  ("Flow of H: no gap means no norm convergence, and strong convergence gets a rate"), **pushed**
  (`0b2cb7e..0018f95`).
- Working tree: only `.gitignore` modified (`+/math28/`). That edit is **not** mine and was already
  there at the start of this session — leave it alone or let the user decide.
- **No Lean file has been edited for the paused tasks.** The two new results below are designed but
  not written, so `MultiplierSelfAdjoint.lean` is exactly as committed. Nothing is half-applied.

## 2. What is already done (commit `0018f95`, pushed)

In `BookProof/OSReconstruction/MultiplierSelfAdjoint.lean` (2482 lines):

| result | name | ~line |
|---|---|---|
| submodule equality `ker H = range P` | `kerHamiltonianMulModel_eq_range_limitProjection`, `range_limitProjection_subset_domain`, `kerHamiltonianMulModel` | 1839–1967 |
| no gap ⇒ no operator-norm convergence | `not_tendsto_opNorm_flowOfHCLM_of_noGap` (+ `norm_expFlow_sub_limitMulL2_ge`, `norm_flowOfHCLM_sub_limitProjection_eq`) | 2320–2440 |
| quantified strong convergence | `norm_flowOfHCLM_sub_limitProjection_lt_of_time`, `exists_time_norm_flowOfHCLM_sub_limitProjection_lt` | 2270–2318 |
| two-scale estimate / tail | `norm_expFlow_sub_limitMulL2_le_two_scale`, `norm_flowOfHCLM_sub_limitProjection_le_two_scale`, `tailMul`, `tailMul_coeFn`, `tendsto_norm_tailMul`, `exists_tailMul_norm_lt` | 2100–2269 |

Verification already run on this content: module build clean, `lake build BookProof` 8902 jobs
success, `sorry` count 0, `#print axioms` on the new theorems gives only `propext`,
`Classical.choice`, `Quot.sound`. `softmodes.md` (2026-11-08 entry) and the module docstring bullets
are updated.

## 3. The two paused tasks

Both are new results the user asked for while the session was ending:

- **Task D** — "Prove the two-scale rate is sharp: exhibit a density and vector where the bound is
  attained."
- **Task E** — "Formalize the impossibility of a uniform rate over the unit ball without a gap."

Insert both **before `theorem limitProjection_isOrthogonalProjectionOntoDensity` (line 2463)**, as
one new section after the existing "Without a gap the operator norm does not converge" header
block (which ends ~line 2440). Add a section header `/-! ### Sharpness of the rate, and the absence
of a uniform one ... -/`.

The existing bound being sharpened (line 2150) is

```
‖expFlow D.f D.hf D.hpos τ u - limitMulL2 D u‖
  ≤ Real.exp (-(τ * δ)) * ‖u‖ + ‖tailMul D δ u‖
```

and its flow-side form (line 2185) is the same with `‖D.U y‖` in place of `‖u‖` and `D.U y` in the
tail. `limitMulL2 D = mulL2 (kernelIndicator D)` is multiplication by `1_{f = 0}`.

### Task D — sharpness

Idea: if the density is **exactly** the split `δ` on the support of the vector, the tail vanishes
and the gapped term is tight, so the inequality is an equality — for every `τ ≥ 0`.  Then exhibit
the barrier density `δ·1_[0,1]` on `volume` over `ℝ` with the indicator vector as a concrete
witness.

Proof plan: show the difference *equals* `Real.exp (-(τ * δ)) • u` as an `Lp` element
(`Lp.ext` + `filter_upwards` over `expFlow_coeFn`, `limitMulL2_coeFn`, `Lp.coeFn_sub`,
`Lp.coeFn_smul`, and the support hypothesis), then `norm_smul`.

Names and statements to add (all in the `BookProof.OSReconstruction` namespace, `variable {X}
[MeasurableSpace X] {ν : Measure X}` in scope):

```lean
theorem memLp_kernelIndicator_of_measurable {f : X → ℝ} (hf : Measurable f) :
    MemLp (fun x => if f x = 0 then (1 : ℝ) else 0) (⊤ : ℝ≥0∞) ν

noncomputable def kernelWeight {f : X → ℝ} (hf : Measurable f) : Lp ℝ (⊤ : ℝ≥0∞) ν :=
  (memLp_kernelIndicator_of_measurable hf).toLp _

theorem kernelWeight_coeFn {f : X → ℝ} (hf : Measurable f) :
    (kernelWeight hf : X → ℝ) =ᵐ[ν] fun x => if f x = 0 then (1 : ℝ) else 0

theorem limitMulL2_eq_mulL2_kernelWeight (D : MulModel X ν Λ T) :
    limitMulL2 D = mulL2 (kernelWeight D.hf)
  -- ContinuousLinearMap.ext, Lp.ext, rw [limitMulL2_coeFn, mulL2_coeFn, kernelWeight_coeFn]

theorem norm_expFlow_sub_mulL2_kernel_eq_of_eq_on_support {f : X → ℝ} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂ν, 0 ≤ f x) {δ τ : ℝ} (hδ : 0 < δ) (hτ : 0 ≤ τ) (u : Lp ℝ 2 ν)
    (hu : ∀ᵐ x ∂ν, (u : X → ℝ) x ≠ 0 → f x = δ) :
    ‖expFlow f hf hpos τ u - mulL2 (kernelWeight hf) u‖ = Real.exp (-(τ * δ)) * ‖u‖

theorem norm_expFlow_sub_limitMulL2_eq_of_eq_on_support (D : MulModel X ν Λ T) {δ τ : ℝ}
    (hδ : 0 < δ) (hτ : 0 ≤ τ) (u : Lp ℝ 2 ν)
    (hu : ∀ᵐ x ∂ν, (u : X → ℝ) x ≠ 0 → D.f x = δ) :
    ‖expFlow D.f D.hf D.hpos τ u - limitMulL2 D u‖ = Real.exp (-(τ * δ)) * ‖u‖
  -- rw [limitMulL2_eq_mulL2_kernelWeight]; exact <the general lemma>

theorem tailMul_eq_zero_of_eq_on_support (D : MulModel X ν Λ T) {δ : ℝ} (hδ : 0 < δ)
    (u : Lp ℝ 2 ν) (hu : ∀ᵐ x ∂ν, (u : X → ℝ) x ≠ 0 → D.f x = δ) :
    tailMul D δ u = 0

theorem norm_expFlow_sub_limitMulL2_eq_two_scale_of_eq_on_support (D : MulModel X ν Λ T)
    {δ τ : ℝ} (hδ : 0 < δ) (hτ : 0 ≤ τ) (u : Lp ℝ 2 ν)
    (hu : ∀ᵐ x ∂ν, (u : X → ℝ) x ≠ 0 → D.f x = δ) :
    ‖expFlow D.f D.hf D.hpos τ u - limitMulL2 D u‖
      = Real.exp (-(τ * δ)) * ‖u‖ + ‖tailMul D δ u‖

theorem norm_flowOfHCLM_sub_limitProjection_eq_two_scale (D : MulModel X ν Λ T) {δ τ : ℝ}
    (hδ : 0 < δ) (hτ : 0 ≤ τ) (y : Hphys Λ)
    (hy : ∀ᵐ x ∂ν, (D.U y : X → ℝ) x ≠ 0 → D.f x = δ) :
    ‖flowOfHCLM D τ y - limitProjection D y‖
      = Real.exp (-(τ * δ)) * ‖y‖ + ‖tailMul D δ (D.U y)‖
```

Concrete witness (barrier density; put it under a `/-! #### A density and a vector where the bound
is attained -/` header, still inside the namespace):

```lean
def barrierDensity (δ : ℝ) : ℝ → ℝ := Set.indicator (Set.Icc (0 : ℝ) 1) fun _ => δ

theorem measurable_barrierDensity (δ : ℝ) : Measurable (barrierDensity δ) :=
  measurable_const.indicator measurableSet_Icc          -- `Measurable.indicator`

theorem barrierDensity_nonneg {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ barrierDensity δ x

theorem memLp_barrierIndicator :
    MemLp (Set.indicator (Set.Icc (0 : ℝ) 1) fun _ => (1 : ℝ)) 2 (volume : Measure ℝ) := by
  refine memLp_indicator_const 2 measurableSet_Icc (1 : ℝ) (Or.inr ?_)
  rw [Real.volume_Icc]; simp                            -- only `≠ ∞` is needed, not `≠ 0`

noncomputable def barrierVector : Lp ℝ 2 (volume : Measure ℝ) :=
  memLp_barrierIndicator.toLp _

theorem barrierVector_coeFn : (barrierVector : ℝ → ℝ) =ᵐ[volume]
    Set.indicator (Set.Icc (0 : ℝ) 1) fun _ => (1 : ℝ) :=
  MemLp.coeFn_toLp _

theorem barrier_sharp {δ : ℝ} (hδ : 0 < δ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖expFlow (barrierDensity δ) (measurable_barrierDensity δ) (barrierDensity_nonneg hδ.le) τ
        barrierVector - mulL2 (kernelWeight (measurable_barrierDensity δ)) barrierVector‖
      = Real.exp (-(τ * δ)) * ‖barrierVector‖
```

`barrier_sharp` is `norm_expFlow_sub_mulL2_kernel_eq_of_eq_on_support (ν := volume) ...` with the
support hypothesis discharged by `filter_upwards [barrierVector_coeFn]`, splitting on
`x ∈ Icc 0 1`: inside use `Set.indicator_of_mem`, outside rewrite with
`Set.indicator_of_notMem` to get `barrierVector x = 0` and `exact absurd hx hne`.

Why this is the right sharpness statement: the two-scale RHS reduces to `e^{−τδ}‖u‖` because
`{0 < f < δ} = ∅` for this density, so the *estimate itself* becomes the identity — the gapped rate
is the truth whenever the density is constant at the split, and the no-gap regime is exactly where
the tail term is unavoidable. Say this in the section docstring.

### Task E — no uniform rate on the unit ball

Idea: a bound on the unit ball is a bound on the operator norm, so a rate function `r τ → 0` that
dominates the unit ball would give `‖S_τ − P‖ → 0`, contradicting `not_tendsto_opNorm_...`.

```lean
theorem opNorm_le_of_unit_ball_bound (D : MulModel X ν Λ T) {r τ : ℝ} (hr : 0 ≤ r)
    (h : ∀ y : Hphys Λ, ‖y‖ ≤ 1 →
      ‖(flowOfHCLM D τ - limitProjection D) y‖ ≤ r) :
    ‖flowOfHCLM D τ - limitProjection D‖ ≤ r

theorem not_exists_uniform_rate_of_noGap (D : MulModel X ν Λ T)
    (hno : ∀ δ : ℝ, 0 < δ → ∃ s : Set X, MeasurableSet s ∧ ν s ≠ 0 ∧ ν s ≠ ∞ ∧
      ∀ x ∈ s, 0 < D.f x ∧ D.f x < δ) :
    ¬ ∃ r : ℝ → ℝ, Tendsto r atTop (𝓝 0) ∧
      ∀ (τ : ℝ), 0 ≤ τ → ∀ y : Hphys Λ, ‖y‖ ≤ 1 →
        ‖(flowOfHCLM D τ - limitProjection D) y‖ ≤ r τ
```

Proof of the first: `ContinuousLinearMap.opNorm_le_bound _ hr`, split `y = 0`; for `y ≠ 0` apply
`h` to the unit vector `(‖y‖⁻¹ : ℝ) • y`, rewrite `map_smul`, `norm_smul`, `Real.norm_eq_abs`,
`abs_of_pos (inv_pos.2 hypos)`, multiply the resulting `‖y‖⁻¹ * ‖S y‖ ≤ r` by `‖y‖ ≥ 0`, and use
`mul_inv_cancel_left₀ hypos.ne'`.  Note `r τ ≥ 0` comes from `h τ hτ 0 (by simp)`.

Proof of the second: `rintro ⟨r, hr, hbound⟩`, then `apply not_tendsto_opNorm_flowOfHCLM_of_noGap D
hno` and squeeze `‖S τ‖` between `0` and `r τ` with
`tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr` and
`filter_upwards [eventually_ge_atTop (0 : ℝ)]`.  (`squeeze_zero` uses `∀`, this one accepts
`∀ᶠ`, which is what the `τ ≥ 0` hypothesis needs.)

### Then

1. Add two bullets to the module docstring list (near lines 77–110) and extend the 2026-11-08
   `softmodes.md` entry with paragraphs for sharpness and the uniform-rate impossibility.
2. `export PATH="/home/leo/.elan/bin:$PATH"; lake build BookProof.OSReconstruction.MultiplierSelfAdjoint`
   then `lake build BookProof` (expect 8902 jobs).  No `sorry`, no new `axiom`; `#print axioms` the
   new theorems (should stay at `propext`, `Classical.choice`, `Quot.sound`).
3. Commit only `BookProof/OSReconstruction/MultiplierSelfAdjoint.lean` and `softmodes.md`
   (HEREDOC message, attribution footer per repo convention; previous messages are long-form
   paragraphs).  Push only if the user asks.

## 4. Pitfalls that cost time last round

- `read_files` / `str_replace` resolve against the **unfer** project root, not this repo — use
  absolute paths (`/home/leo/Projects/timepiece/...`) or `run_terminal_command` with `cd`.
- `↑(limitProjection D)` (LinearMap coercion) vs `limitProjection D` (CLM): defeq but not
  `rw`-matchable. Use `exact`/`calc`, or introduce `have hy' : y = limitProjection D z := hz.symm`.
- `↑(resolventMulModel D hlam)` has the same problem.
- `rw [h]` rewrites **all** occurrences, including both sides of an equation — use `conv_lhs` or
  reorder (`rw [ha, hay]`, not `[hay, ha]`).
- `mul_inv_cancel₀ a : a * a⁻¹ = 1`; for `a⁻¹ * a` use `inv_mul_cancel₀`.
- `field_simp` needs the nonzero hypothesis in context; `mul_inv_cancel_left₀` is usually shorter.
- A docstring must sit immediately before its declaration (`unexpected token '/--'` otherwise); I
  twice closed a section doc with `-/ -/`.
- The repo warns on lines over 100 characters (`BookProof.lean:3623` already does, in an untouched
  file). Check new code with `awk 'length > 100'`.
- Both `MemLp.toLp` proofs are not defeq-equal, so `kernelIndicator D` and `kernelWeight D.hf` are
  only equal **propositionally** — that is why `limitMulL2_eq_mulL2_kernelWeight` exists.
- `Lp.coeFn_zero` needs explicit `(E := ℝ) (p := 2) (μ := ν)` if inference fails; ae hypotheses
  passed to `filter_upwards` arrive as pointwise equalities at `x`, which is what makes them
  `rw`-able.

## 5. The mass-gap question (asked, answered in prose, not formalized)

The user's inference was: YM in the Hamiltonian nested Fock space is well defined and equivalent to
the 4D Euclidean theory "so there should be operator norm convergence"; combined with
no-gap ⇒ no norm convergence, that would give a mass gap.

The answer given: the implication runs the other way, and nothing in the corpus supplies the
premise.

- For a self-adjoint `H ≥ 0` with kernel projection `P`, `‖e^{−τH} − P‖ = sup_{λ ∈ σ(H), λ>0}
  e^{−τλ}`.  So **norm convergence ⇔ a gap** (or `σ(H) ⊆ {0}`).  `not_tendsto_opNorm_...` is the
  contrapositive, i.e. exactly "norm convergence would imply a gap".
- Well-definedness plus OS/reflection-positivity reconstruction gives a strongly continuous
  contraction semigroup and **strong** convergence `e^{−τH} → P`; it does not give uniform
  (operator-norm) convergence, and in 1+3 dimensions there is no reason it should.
- Therefore assuming norm convergence for YM *is* assuming a mass gap: the argument is circular, and
  a proof of operator-norm convergence would be a proof of the Millennium statement, not a
  corollary of well-definedness.
- The theorem is also a model theorem (multiplication by `f` on `L²(ν)`), where the gap is a gap of
  the essential range of `f` above its zero set — the toy version of "mass gap ⇔ uniform
  exponential return".  The `barrier_sharp` result above makes the complementary point: where a
  gap exists the uniform rate is attained, so the no-gap hypothesis is doing real work.

## 6. The Lean corpus bundle

`YANG_MILLS_MASS_GAP_LEAN.md` (repo root, 41544 lines, 2118305 bytes ≈ 520k–690k tokens, below the
user's 1M ceiling) contains, verbatim and with a path/module/line/byte banner for each,
118 files: everything under `BookProof/Qym/`, every `*Yang*`, `*Brst*`, `*MassGap*` and `*Gap*`
file, plus the nested-Fock framework (`ChapterQuadraticFockEsa`,
`Toolbox/ChapterFockFieldPerturbation`, `Toolbox/ChapterFockSecondQuantization`,
`ChapterGradedFock`, `RequestProject/NestedFock`).  The header documents the exact regeneration
command.

Excluded on purpose: generic Fock toolbox chapters (NS/QG/MCMC), the `math/OAI` series, and files
that only mention Yang–Mills in passing.  If the user wants those too, the remaining budget to 1M
tokens is roughly 1.3 MB at 3 chars/token — enough for the whole `*Fock*` set (adds ~1.44 MB) but
not for that plus everything else; re-measure before regenerating.

## 7. Files touched by this pause

- `HANDOUT.md` (this file) — new, uncommitted.
- `YANG_MILLS_MASS_GAP_LEAN.md` — new, uncommitted (generated, 2.1 MB).
- `.gitignore` — modified before this session (`+/math28/`), untouched by me.
