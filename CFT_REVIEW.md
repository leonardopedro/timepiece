# Review of `cft.md`: machine-checked claims and assessment

`cft.md` asks two questions and gives two answers:

* **A.** Can Bałaban's renormalisation group, combined with the Timepiece certified spectral
  pipeline (SIRK / Temple / `dΓ` lift), prove the mass gap?
* **B.** What constructive-QFT properties can the artificial gap `H_μ = H + μN` be used to prove?

The Lean proofs are in the following files, namespace `CftCheck`:

* `RequestProject/ArtificialGap.lean`: Temple's inequality and the basic properties of `H + μN`
  (bounded operators).
* `RequestProject/NestedFock.lean`: the conditional form of claim A, and claim B redone in the
  **nested Fock space**, where the outer number operator `N` is not the number operator of the
  physical (inner) Fock space (bounded operators).
* `RequestProject/Unbounded.lean`: SIRK's shift-invert operator `(H - σ)⁻¹` for an **unbounded**
  `H`, and Temple / Step 3 for unbounded `H` (Section 4).
* `RequestProject/HeatSemigroup.lean`: construction of the Euclidean transfer operators
  `exp(-τH)` for an **unbounded** semibounded self-adjoint `H`, and existence and uniqueness of
  solutions of `dψ/dτ = -Hψ` (Section 5).
* `RequestProject/SelfAdjointResolvent.lean`: every self-adjoint (`H† = H`) operator bounded
  below, and the closure of every essentially self-adjoint operator bounded below, has a bounded
  shift-invert operator, so Section 5 applies to it.
* `RequestProject/UnboundedPhysics.lean`: claims A and B redone for unbounded `H` and `N`
  (Section 6).
* `RequestProject/Existence.lean`: summary existence theorems for A and B (Section 6).
* `RequestProject/UnboundedExample.lean`: a concrete unbounded operator (`diag(k)` on `ℓ²(ℕ)`)
  that satisfies the hypotheses, so the unbounded results are not vacuous.
* `RequestProject/UnitaryGroup.lean`: construction of the real-time unitary group `exp(itH)` of
  an **unbounded** self-adjoint `H` bounded below, and existence and uniqueness of solutions of
  the Schrödinger equation `dψ/dt = iHψ` (Section 6b).
* `RequestProject/HeisenbergUnbounded.lean`: the Heisenberg-invariance statement of claim B for
  unbounded `H` and `N` (Section 6b).
* `RequestProject/HeisenbergExample.lean`: a concrete unbounded instance (`H = N = diag(k)` on
  `ℓ²(ℕ)`) that satisfies all hypotheses of Section 6b.

All files build with no `sorry` and use only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). **Scope:** the first two files use bounded operators because
there `e^{-τH}` is the operator exponential, which Mathlib only has for bounded operators. The
later files remove this restriction for the Euclidean (real-exponential) part of A and B: the
transfer operators `e^{-τH}` and `e^{-τ(H+μN)}` are constructed for unbounded self-adjoint
operators bounded below, from SIRK's bounded shift-invert operator (Sections 5 and 6). Nothing in
these files is a statement about the Yang–Mills operator itself; that would need it to be
constructed first.

**What "prove claim A / claim B" can mean here.** Claim A's conclusion ("the synthesis yields a
rigorous proof of the mass gap") is a version of the Millennium problem and cannot be proved
here. Its steps can be proved in conditional form, and that is done below. The proof also shows
that Step 3's hypothesis already contains the gap. Claim B's formulas are proved. Its stronger
statement, exponential clustering of the physical theory at rate `μ`, is refuted in the nested
setting by a theorem and a concrete model.

---

## 1. Claim A: Bałaban + Timepiece

| Lean name | Statement | Corresponds to |
|---|---|---|
| `temple_lower_bound` | If the spectrum avoids `(λ₀, β)` (`Re⟪(H-β)x,(H-λ₀)x⟫ ≥ 0`), then `θ - η²/(β-θ) ≤ λ₀`. | §1 Temple formula |
| `temple_bound_degenerates` | For fixed `η ≠ 0`, `θ - η²/(β-θ) → -∞` as `β ↓ θ`. | §1 "spectral squeeze" |
| `temple_enclosure` | If also `λ₀` is the bottom of `H` and `β - θ ≥ c > 0`, then `θ - η²/c ≤ λ₀ ≤ θ`. | Step 3 enclosure |
| `temple_enclosure_converges` | If `β - θ_m ≥ c > 0` uniformly and `η_m → 0`, then `θ_m → λ₀`. | Step 3 "monotone shrinking" |
| `separation_input_is_gap` | Under the separation hypothesis, every eigenvalue `e > λ₀` has `e ≥ β`. | — |
| `step3_hypothesis_implies_gap` | Under Step 3's hypotheses, every eigenvalue `e > λ₀` has `e - λ₀ ≥ c`. | Step 3 is circular |
| `second_quantized_edge` | A sum of `n` operators, each `≥ μ`, is `≥ nμ` (the algebraic content of `dΓ(h) ≥ μN`). | Step 4 `dΓ` lift |

**Verdict on A.**

* The diagnosis is correct and proved: Temple's bound is only as good as the separation input
  `β`, and it degenerates as `β - θ → 0`.
* The conditional pipeline is proved: given a uniform separation `c`, the enclosure shrinks to
  the ground energy as residuals go to zero.
* **But the hypothesis is the gap.** `step3_hypothesis_implies_gap` shows that the assumption of
  Step 3 (`β - θ ≥ CΛ_QCD`) already gives a gap `≥ CΛ_QCD` above the ground state, without
  using Temple's inequality or numerics. So the synthesis moves the open problem into the
  hypothesis. Bałaban's published results (ultraviolet stability in finite volume) do not supply
  such a spectral bound.
* Not formalised (assessment): converting Bałaban's Euclidean lattice RG into a Hamiltonian
  (reflection positivity at each scale); uniformity in volume and number of RG steps; and the
  fact that the interacting effective Hamiltonian is not of the form `dΓ(h)`, so Step 4 applies
  only through the perturbative extensions.

## 2. Claim B: the artificial gap in the nested Fock space

### 2.1 Correction to the previous review

The previous review used `truncated_correlation_vanishes` to argue that observables commuting
with `N` "cannot excite the vacuum", so the clustering in answer B is vacuous. **That is only true
for the outer vacuum `Ω`**, which spans `ker N`. In the nested construction:

* the outer number operator `N` counts outer quanta;
* the physical (inner) Fock space sits inside the one-outer-quantum sector `N = 1`;
* the physical inner vacuum `ω` is a vector of that sector, orthogonal to `Ω`.

Observables that commute with the outer `N` act on each outer sector separately. Inside the
sector `N = 1` they can be any operator on the inner Fock space, so they **can** excite `ω`.
This is now proved:

| Lean name | Statement |
|---|---|
| `number_preserving_excites_inner_vacuum` | If `ω, φ` lie in the sector `N = 1`, `φ ⊥ ω`, `φ ≠ 0`, `‖ω‖ = 1`, then `O = |φ⟩⟨ω|` and `A = |ω⟩⟨φ|` commute with `N`, `Oω = φ` is not a multiple of `ω`, and `⟪ω, A O ω⟫ - ⟪ω, A ω⟫⟪ω, O ω⟫ = ‖φ‖² ≠ 0`. |

So the user's remark is correct. The objection "μ-independent observables have no truncated
correlations" does not apply to the inner vacuum.

### 2.2 What the shift does to physical correlations

The relevant question is then what `μ` does to correlations in the inner vacuum `ω`, or more
generally in any sector of fixed outer number. The answer is exact:

| Lean name | Statement |
|---|---|
| `shifted_transfer_on_sector` | If `[H,N] = 0` and `Nψ = nψ`: `e^{-τ(H+μN)}ψ = e^{-τμn} e^{-τH}ψ`. |
| `shifted_correlation_factorizes` | `⟪χ, e^{-τ(H+μN)}ψ⟫ = e^{-τμn} ⟪χ, e^{-τH}ψ⟫` for every `χ` (this includes outer creation/annihilation operators, which do not commute with `N`). |
| `shifted_normalized_correlation_invariant` | For `ψ` in sector `n`, `[B,N] = 0` and any `A`: `⟪ψ, A U_μ B ψ⟫ / ⟪ψ, U_μ ψ⟫ = ⟪ψ, A U_0 B ψ⟫ / ⟪ψ, U_0 ψ⟫`, where `U_μ = e^{-τ(H+μN)}`. |
| `inner_vacuum_shifted_correlation` | If `Hω = 0`, `Hφ = eφ` (both in sector 1): the unnormalised correlation is `e^{-τ(μ+e)}‖φ‖²`, and the normalised truncated correlation is `e^{-τe}‖φ‖²` for every `μ`. |
| `inner_vacuum_no_rate_mu_clustering` | In that setting, if `e < μ`, the normalised truncated correlation in `ω` is **not** bounded by `C e^{-μτ}` for any `C`. |
| `toy_nested_model` | A concrete 3-dimensional model (outer vacuum `Ω`, inner vacuum `ω`, one inner excitation `φ` of energy `e ≥ 0`) satisfies every hypothesis of the artificial-gap construction (`H ≥ 0`, `N ≥ 1` on `Ω^⊥`, `Ω` spans `ker N`, `[H,N] = 0`, `HΩ = NΩ = 0`). In it a number-preserving observable excites `ω`, and for `μ > e` there is no rate-`μ` clustering in `ω`. |

The toy model shows that the hypotheses are consistent, so the general theorems are not vacuous.

### 2.3 Verdict on B

* **Proved, as stated in answer B:** coercivity `⟨ψ, H_μψ⟩ ≥ μ‖ψ‖²` on `Ω^⊥`, the resolvent
  bound `1/μ`, the transfer-matrix contraction `‖e^{-aH_μ}‖_{Ω^⊥} ≤ e^{-aμ}`, vacuum invariance,
  and μ-independence of the Heisenberg dynamics of observables commuting with `N`
  (`ArtificialGap.lean`).
* **Corrected (nested Fock space):** these observables can excite the inner vacuum, so their
  correlations in `ω` are not trivial.
* **Refuted, as a statement about the physical theory:** the gap `μ` isolates the *outer*
  vacuum `Ω`, not the physical vacuum `ω`. On the sector containing `ω`, the whole effect of the
  shift is the scalar factor `e^{-μτ}` (`shifted_transfer_on_sector`). This factor cancels in
  normalised correlations (`shifted_normalized_correlation_invariant`). So the decay of physical
  correlations in `ω` is governed by `H` alone, and it is not `e^{-μτ}` in general
  (`inner_vacuum_no_rate_mu_clustering`, `toy_nested_model`). The exact μ-independence that makes
  the regulator "trivially removable" (point 1) is the same fact that makes it give no
  information about clustering in the physical vacuum (points 2 and 5). The `e^{-μτ}` decay of
  correlations taken with respect to `Ω` is an explicit prefactor
  (`shifted_correlation_factorizes`). It is not a property of the physical dynamics.
* **Consequences for the other points (assessment, not formalised):**
  * Point 2 (polymer damping in Bałaban's expansion): any damping `e^{-naμ}` gained this way is
    an overall factor that has to be divided out again in normalised expectations. It does not
    improve the convergence of the physical cluster expansion.
  * Point 3 (resolvent / SIRK bounds): the `1/μ` bound controls `H + μN` on `Ω^⊥`. Restricted to
    the physical sector it is `(H + μ)^{-1}`, an ordinary shifted resolvent. It gives no
    separation input `β` for `H` above `ω` in Temple's inequality.
  * Point 4 (Haag–Ruelle): this needs an isolated mass shell of the physical energy–momentum
    operators above `ω`. Isolating `Ω` does not provide one.
  * Point 5 (temporal into spatial decay): the needed input is a gap of the physical generator
    above `ω` together with Lorentz covariance. The shift supplies neither.

## 4. Unbounded Hamiltonians and shift-invert (`Unbounded.lean`)

An unbounded `H` is a partially defined linear map `H : E →ₗ.[ℂ] E` with domain `D(H)`.
`IsShiftInvert H σ R` says that the bounded operator `R` is `(H - σ)⁻¹`: `R` maps `E` into
`D(H)`, `(H - σ)R = 1` on `E`, and `R(H - σ) = 1` on `D(H)`.

| Lean name | Statement |
|---|---|
| `shiftInvert_eigen_of_eigen` | If `y ∈ D(H)`, `Hy = l y` and `l ≠ σ`, then `Ry = (l - σ)⁻¹ y`. |
| `eigen_of_shiftInvert_eigen` | If `Rx = ν x` with `ν ≠ 0`, then `x ∈ D(H)` and `Hx = (σ + 1/ν) x`. |
| `temple_lower_bound_unbounded` | Temple's inequality for trial vectors `ψ ∈ D(H)`, under the separation hypothesis on `D(H)`. |
| `temple_enclosure_converges_unbounded` | Step 3's shrinking enclosure, for unbounded `H`. |
| `separation_input_is_gap_unbounded`, `step3_hypothesis_implies_gap_unbounded` | Step 3's separation hypothesis already gives every eigenvalue `e > l₀` the bound `e - l₀ ≥ c`, for unbounded `H`. |
| `shifted_shiftInvert_on_sector` | Suppose `H_μ = H + μN` on `D(H) ∩ D(N)` (`N` may be unbounded too) and `ψ` is in the sector `N = n` (more precisely, `N(R₀ψ) = n R₀ψ`). Then the shift-invert operator of `H_μ` at `z` agrees on `ψ` with the shift-invert operator of `H` at `z - μn`. |

**What this changes.** The user's point is correct: SIRK, and the certified bounds it produces,
make sense for an unbounded `H` because they only use the bounded operator `(H - σ)⁻¹`. The
first two theorems show that its eigenpairs correspond exactly to eigenpairs of `H`. **What it
does not change.** The two structural conclusions do not depend on boundedness:

* Step 3 of A: the separation input is still the gap (`step3_hypothesis_implies_gap_unbounded`).
  Shift-invert makes the numerics well defined. It does not supply `β`.
* Point 3 of B: on the sector of the physical vacuum, the shift-invert operator of `H + μN` is
  just a shift-invert operator of `H` with the shift moved by `μn`
  (`shifted_shiftInvert_on_sector`). So the regulator changes which shift SIRK uses there. It
  gives no separation input above `ω`.

The statements about `e^{-τ(H+μN)}` in Section 2 were proved there only for bounded `H`. They
are now proved for unbounded `H` and `N` in Sections 5 and 6.

## 5. The transfer operators `e^{-τH}` for unbounded `H` (`HeatSemigroup.lean`, `SelfAdjointResolvent.lean`)

`IsSemibounded H m σ R` says: `H` is symmetric on its domain, `Re⟪x, Hx⟫ ≥ m‖x‖²`, `σ < m`, and
`R` is the bounded shift-invert operator `(H - σ)⁻¹` (`IsShiftInvert`). This is exactly a
self-adjoint operator bounded below by `m`, together with its SIRK resolvent:

| Lean name | Statement |
|---|---|
| `IsSelfAdjoint.exists_isSemibounded` | If `H† = H` (Mathlib's adjoint of a partially defined operator) and `Re⟪x, Hx⟫ ≥ m‖x‖²`, then for every `σ < m` there is a bounded `R = (H - σ)⁻¹` with `IsSemibounded H m σ R`. |
| `exists_isSemibounded_closure` | The same for the closure of an **essentially self-adjoint** operator bounded below (the lower bound passes to the closure, `lower_bound_closure`). |
| `exists_isSemibounded_of_closed` | The criterion behind both: closed, symmetric, bounded below, and no nonzero vector orthogonal to the range of `H - σ`. |
| `IsSemibounded.exists_shift` | A resolvent at one shift `σ < m` gives one at every shift `σ' < m`. |

**Construction.** `R` is a bounded self-adjoint operator with spectrum in `[0, 1/(m-σ)]`
(`isSelfAdjoint_R`, `spectrum_R_subset`), injective with dense range. Since
`H = σ + R⁻¹`, the transfer operator is defined by the continuous functional calculus of the
bounded `R`:

`heatSG σ R τ = e^{-τσ} · f_τ(R)`, `f_τ(r) = e^{-τ/r}` for `r > 0`, `f_τ(0) = 0` (`τ > 0`),

and `heatSG σ R 0 = 1`. The function `f_τ` is continuous (`continuous_heatFun`), so this is
well defined even though `0` can be in the spectrum of `R` (exactly when `H` is unbounded).

| Lean name | Statement |
|---|---|
| `heatSG_add`, `heatSG_zero` | Semigroup law `e^{-(s+t)H} = e^{-sH} e^{-tH}` for `s, t ≥ 0`, and `e^{0·H} = 1`. |
| `isSelfAdjoint_heatSG`, `norm_heatSG_le` | `e^{-τH}` is self-adjoint and `‖e^{-τH}‖ ≤ e^{-mτ}`. |
| `heatSG_mem_domain`, `H_heatSG` | `e^{-τH}` maps `D(H)` into `D(H)` and commutes with `H` there. |
| `continuousOn_heatSG`, `tendsto_heatSG_zero` | Strong continuity: `τ ↦ e^{-τH}x` is continuous on `[0, ∞)` for every `x`. |
| `tendsto_heatSG_gen` | The generator is `-H`: `(e^{-hH}x - x)/h → -Hx` as `h → 0⁺`, for `x ∈ D(H)`. |
| `heatSG_isHeatSolution` | **Existence:** for `x ∈ D(H)`, `ψ(τ) = e^{-τH}x` stays in `D(H)`, is continuous, and has right derivative `-Hψ(τ)` at every `τ ≥ 0`. |
| `IsHeatSolution.norm_sq_le` | Energy estimate: if `Re⟪ψ, Hψ⟫ ≥ c‖ψ‖²` along a solution, then `‖ψ(τ)‖² ≤ ‖ψ(0)‖² e^{-2cτ}`. |
| `IsHeatSolution.unique`, `IsHeatSolution.eq_heatSG` | **Uniqueness:** for `H` bounded below, every solution of `dψ/dτ = -Hψ` is `ψ(τ) = e^{-τH}ψ(0)`. |
| `heatSG_unique` | `e^{-τH}` depends only on `H`, not on the shift or resolvent used to build it. |
| `heatSG_eigen` | `Hx = λx` implies `e^{-τH}x = e^{-τλ}x`. |
| `euclidean_evolution_exists` (`Existence.lean`) | Summary: for `H† = H` bounded below, the semigroup `e^{-τH}` exists with all the properties above. |

**Non-vacuity.** `UnboundedExample.lean` builds `H = diag(k)` on `ℓ²(ℕ)` from
`R = diag(1/(k+1))`, proves `IsSemibounded H 0 (-1) R` (`diagH_isSemibounded`), proves that `H`
is unbounded (`diagH_unbounded`: no `C` with `‖Hx‖ ≤ C‖x‖`), and applies the existence and
uniqueness theorems to it (`diagH_heat_exists`).

The real-time unitary group `e^{itH}` is not obtained this way: the function `r ↦ e^{it/r}` is
not continuous at `r = 0`, so the continuous functional calculus of `R` does not give it directly
when `H` is unbounded. It is constructed in Section 6b, and the Heisenberg-dynamics statement of
claim B is proved there for unbounded operators.

## 6. Claims A and B for unbounded `H` and `N` (`UnboundedPhysics.lean`, `Existence.lean`)

**Claim B.** `H`, `N` and `Hμ` are partially defined operators, `Hμ = H + μN` on
`D(H) ∩ D(N)`, and `H`, `Hμ` are semibounded. A sector is a closed subspace `V` on which `N = n`
and which is preserved by the shift-invert operator of `H`; this is the standard meaning of
"`H` commutes with `N`" for unbounded operators.

| Lean name | Statement |
|---|---|
| `heat_shifted_on_sector` | On the sector, `e^{-τ(H+μN)}ψ = e^{-τμn} e^{-τH}ψ`. |
| `heat_shifted_correlation_factorizes` | `⟪χ, e^{-τ(H+μN)}ψ⟫ = e^{-τμn}⟪χ, e^{-τH}ψ⟫` for `ψ` in the sector and every `χ`. |
| `heat_shifted_normalized_correlation_invariant` | Normalised correlations `⟪ψ, A e^{-τ(H+μN)} Bψ⟫ / ⟪ψ, e^{-τ(H+μN)}ψ⟫` do not depend on `μ`. |
| `heat_inner_vacuum_shifted_correlation` | With `Hω = 0`, `Hφ = eφ` in the sector: unnormalised correlation `e^{-τ(μn+e)}‖φ‖²`, normalised truncated correlation `e^{-τe}‖φ‖²`. |
| `heat_inner_vacuum_no_rate_mu_clustering` | If `e < μ` the normalised truncated correlation in `ω` is not `O(e^{-μτ})`. |
| `shifted_coercive_unbounded`, `shifted_resolvent_bound_unbounded` | `Re⟪y, Hμy⟫ ≥ μ‖y‖²` and `‖Hμy‖ ≥ μ‖y‖` on `D(H) ∩ D(N) ∩ Ω^⊥`. |
| `shifted_heat_contraction` | `e^{-τHμ}Ω = Ω` and `‖e^{-τHμ}x‖ ≤ e^{-μτ}‖x‖` for `x ⊥ Ω`. |
| `artificial_gap_theory_exists` (`Existence.lean`) | **Existence for B:** if `Hμ` is self-adjoint with domain `D(H) ∩ D(N)`, `H ≥ 0`, `N ≥ 0`, `N ≥ 1` on `Ω^⊥`, `HΩ = NΩ = 0`, then the Euclidean evolution `e^{-τHμ}` exists: a semigroup of self-adjoint contractions, solutions of `dψ/dτ = -Hμψ` exist for every initial value in the domain and are unique, `Ω` is invariant, and `e^{-τHμ}` decays like `e^{-μτ}` on `Ω^⊥`. |

So the artificial gap does give an existence result, as pointed out in the follow-up request. For unbounded
`H` and `N`, the shifted Euclidean dynamics exists, is unique, and has the uniform decay
`e^{-μτ}` on `Ω^⊥`. The conclusions of Section 2 do not change: the shift acts as the scalar
`e^{-τμn}` on each sector, so normalised physical correlations are `μ`-independent and their
decay in the inner vacuum is not `e^{-μτ}` in general.

**Claim A.**

| Lean name | Statement |
|---|---|
| `temple_enclosure_unbounded` | Temple enclosure `θ - η²/c ≤ l₀ ≤ θ` for trial vectors in `D(H)`. |
| `second_quantized_edge_unbounded` | `dΓ` lift for unbounded summands on their common domain. |
| `heatSG_contraction_orth` | A gap `Re⟪x, Kx⟫ ≥ c‖x‖²` on `D(K) ∩ Ω^⊥`, with `KΩ = 0`, gives `‖e^{-τK}x‖ ≤ e^{-cτ}‖x‖` on `Ω^⊥`. |
| `gap_of_heatSG_decay` | Conversely, decay `‖e^{-τK}x‖ ≤ e^{-gτ}‖x‖` on `Ω^⊥` at one `τ > 0` forces every eigenvalue with eigenvector `⊥ Ω` to be `≥ g`. |
| `transfer_decay_iff_gap` (`Existence.lean`) | For `H† = H`, `H ≥ 0`, `HΩ = 0`: the transfer operator exists, fixes `Ω`, and both directions above hold. |

So for an unbounded self-adjoint Hamiltonian, the Euclidean transfer operator (the object
Bałaban's renormalisation group works with) exists, and its exponential decay on `Ω^⊥` carries
the same information as the Hamiltonian gap. Together with
`step3_hypothesis_implies_gap_unbounded`, this confirms the verdict on A for unbounded `H`: the
separation input of Step 3 is the gap, whether it is stated for `H` or for the transfer
operator.

## 6b. Real-time dynamics and Heisenberg invariance for unbounded `H` and `N` (`UnitaryGroup.lean`, `HeisenbergUnbounded.lean`, `HeisenbergExample.lean`)

**The unitary group.** For `IsSemibounded H m σ R` (`H` self-adjoint, bounded below, with
resolvent `R = (H - σ)⁻¹`), `H - σ = R⁻¹`. The function `r ↦ r e^{it/r}` (value `0` at `r = 0`) is
continuous, so `(r ↦ r e^{it/r})(R)` is defined by the continuous functional calculus of `R`.
`exp(it R⁻¹)` is the strong limit of the bounded operators `e^{it/max(R, 1/(n+1))}`. It is the
unique contraction with `exp(itR⁻¹) R = (r ↦ r e^{it/r})(R)`, and
`unitaryGroup σ R t = e^{itσ} exp(itR⁻¹)`. This is the spectral-theorem input that Section 5 was
missing. It is built from the resolvent, the same route as the spectral theorem for unbounded
operators in `BookProof` (`ChapterUnboundedSpectralModel`). It is formalised directly in this project.

`IsUnitaryGroupOf H U` means: `U 0 = 1`, and for every `x ∈ D(H)`, `t ↦ U t x` stays in `D(H)` and
solves `dψ/dt = iHψ` (`IsSchrodingerSolution`).

| Lean name | Statement |
|---|---|
| `unitaryGroup_isUnitaryGroupOf` | **Existence:** `exp(itH)` maps `D(H)` into `D(H)`, and `t ↦ exp(itH) x` solves `dψ/dt = iHψ` for `x ∈ D(H)`. |
| `unitaryGroup_zero`, `unitaryGroup_add`, `unitaryGroup_neg_mul`, `unitaryGroup_mul_neg` | `exp(i0H) = 1`, `exp(i(s+t)H) = exp(isH) exp(itH)`, inverse `exp(-itH)`. |
| `norm_unitaryGroup_apply`, `continuous_unitaryGroup_apply` | `exp(itH)` is an isometry, and `t ↦ exp(itH) x` is continuous for every `x`. |
| `unitaryGroup_commute`, `unitaryGroup_apply_mem` | `exp(itH)` commutes with every bounded operator commuting with `R`, and preserves every closed subspace preserved by `R`. |
| `IsSchrodingerSolution.unique` | **Uniqueness:** for symmetric `H`, two solutions of `dψ/dt = iHψ` with the same initial value agree (the norm of their difference is conserved). |
| `IsUnitaryGroupOf.unique`, `IsUnitaryGroupOf.eq_unitaryGroup` | A symmetric, densely defined `H` generates at most one unitary group, so `exp(itH)` depends only on `H`. |
| `unitary_evolution_exists` (`HeisenbergUnbounded.lean`) | Summary: for `H† = H` bounded below there is exactly one unitary group generated by `H`; it is a strongly continuous one-parameter group of isometries. |

**Heisenberg invariance.** Hypotheses: `H` as above, `N` closed with eigenvectors spanning a
dense subspace (a number operator), `[H, N] = 0` in the usual sense for unbounded operators (the
resolvent `R` of `H` maps `D(N)` into `D(N)` and commutes with `N` there), `Hμ = H + μN` on
`D(H) ∩ D(N)` symmetric, and `O` bounded with `[O, N] = 0` (`O` maps `D(N)` into `D(N)` and
`NO = ON` there).

| Lean name | Statement |
|---|---|
| `sector_dynamics` | For `v` in the eigenspace `N = n`: `exp(it(H+μN)) v = e^{itμn} exp(itH) v`. |
| `heisenberg_shift_invariant_unbounded` | For every unitary group `U` generated by `H` and `Uμ` generated by `Hμ`: `Uμ t O Uμ(-t) = U t O U(-t)`, i.e. `e^{it(H+μN)} O e^{-it(H+μN)} = e^{itH} O e^{-itH}`. |
| `heisenberg_shift_invariant_selfAdjoint` | If moreover `Hμ† = Hμ` is bounded below, both unitary groups exist and the identity holds. |
| `heisenberg_unbounded_example` | On `ℓ²(ℕ)`, `H = N = diag(k)` (unbounded), `Hμ = (1+μ)H`, `O = diag(1/(k+1))` satisfy every hypothesis. |

So `heisenberg_shift_invariant` now holds for unbounded `H` and `N`. Its role in claim B is the
same as before: the shift `μN` drops out of the Heisenberg dynamics of number-preserving
observables. **Scope.** "`N` has a dense set of eigenvectors" is the case of a number operator.
The general case of strongly commuting `H`, `N` with continuous spectrum would need the joint
functional calculus, and it is not formalised here.

## 7. Bottom line

* **A:** the diagnosis and the conditional pipeline are proved. The hypothesis of Step 3 is
  shown formally to already imply the mass gap, so the synthesis does not prove it.
* **B:** the formulas are proved. In the nested Fock space, number-preserving observables do
  excite the inner vacuum (this corrects the previous review). But the shift acts on each outer
  sector as a scalar, so it leaves normalised physical correlations unchanged. It therefore
  cannot provide the clustering that constructive QFT needs from a mass gap. This is shown by a
  general theorem and a concrete model.
* **Unbounded operators:** none of the Euclidean statements needs a bounded Hamiltonian. For
  self-adjoint (or essentially self-adjoint) operators bounded below, `e^{-τH}` and
  `e^{-τ(H+μN)}` are constructed from SIRK's shift-invert operator, the evolution equation
  `dψ/dτ = -Hψ` has unique solutions, and the conclusions on A and B hold unchanged. For B this
  gives a genuine existence result for the regulated theory (`artificial_gap_theory_exists`);
  it does not change the physical predictions or how they are computed.
* **Real-time dynamics:** the unitary group `e^{itH}` of an unbounded self-adjoint `H` bounded
  below is constructed and characterised by the Schrödinger equation (existence and
  uniqueness). The Heisenberg-invariance statement of claim B
  (`heisenberg_shift_invariant_unbounded`) holds for unbounded `H` and number operator `N`.
