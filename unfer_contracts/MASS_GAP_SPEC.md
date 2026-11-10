# MASS_GAP_SPEC — the proof-facing seam of the certified mass gap

*Spec of record for `fock_sirk::mass_gap_spec` and the sector-solve seam
`fock_sirk::certified_mass_gap_parity`. This is the non-Lean part of the
`MASS_GAP_CERTIFIED.md` §4–§5 formalization: the numerical code is converted
into a form proofs can be written about — pure, dependency-free functions with
exact contracts, a runtime-enforced precondition seam, and NDJSON certificates
consumable by the nanoda/lean4export pipeline (S29/S31). The Lean4 parts are
out of scope here (LLM-Lean4-specialist).*

**Hamiltonian of record: the 3D gauge-fixed QYM Hamiltonian, not the lattice.**
The mass-gap observable lives on `qcd_ym_hamiltonian(g)` — the nested-Fock
realization of the Cadabra-derived `H_final = ½π² + ½B²` with
`B = (A₀ − A₁) + ½g·A₀A₁` (`unfer_contracts/docs/yang_mills_hamiltonian.cdb`,
vendored here; the Cadabra2 derivation, not Rust). All numerical
approximations are SIRK–Hashimoto solves (`solve_forward_sirk_with_opts`).

> **The `.cdb` files are reference text only — never run them.** They are
> Cadabra2 notebook derivations vendored so the specialist can *read* the
> algebra (the derivation of `H_final = ½π² + ½B²` and the `B` definition).
> The specialist has no Cadabra2 and must not execute them; the operative
> content (the final Hamiltonian and its `B` field) is stated inline in this
> spec and in `docs/qg_starobinsky_hamiltonian.cdb` / `docs/qg_starobinsky_vielbein_hamiltonian.cdb`
> for the QG fibers. Treat the `.cdb` bytes as un-runnable algebra, exactly
> like a `.tex` source.
The sector symmetry is the exact `Z₂` **reflection** `R: (A₀, A₁) → (−A₁, −A₀)`
(occupation parity is *not* a symmetry at `g > 0`, where `B²` carries
3-operator products): the R-even sector contains the vacuum start, the R-odd
sector the `(|1₀⟩ + |1₁⟩)/√2` one-quantum start.

## 1. The theorem of record (T6)

For the gauge-fixed QYM Hamiltonian `H` and its Galerkin/Krylov truncation
`H_m` (the whitened projection `h_proj` the kernel actually diagonalizes), let
`θᵉ₀`, `θᵒ₀` be the computed **lowest Ritz values** of the R-even and R-odd
sector solves, with certified widths `δᵉ`, `δᵒ`:

```
λ₁(H_m) − λ₀(H_m) ≥ θᵒ₀ − θᵉ₀ − (δᵒ + δᵉ)                      (T6)
```

The width is the sum of three explicit, machine-checkable terms (§4.4):

```
δˢ = ‖rˢ‖  (T2: a-posteriori Rayleigh–Ritz residual, Parlett)
   + c(nˢ)·u·‖Ĝˢ‖  (T1/T3: eigendecomposition backward error, c(n) = n³,
                    u = 2⁻⁵³, ‖Ĝˢ‖ = spectral norm of the matrix diagonalized)
   + h_Oˢ  (T5: directed-rounding enclosure of the measured value,
            h_O = 4u·max(|θ|, 1))
```

**Honesty boundary:** the certificate is a theorem about the truncated
gauge-fixed object `H_m` — the object the numerics actually computes — not the
continuum Millennium mass gap. The continuum passage needs one additional
(gap-preserving) convergence theorem, explicitly out of scope.

**Conditionality (2026-11-10 audit — this line was unconditional before).**
(T6) requires `θᵒ₀` to lie within `δᵒ` of the **odd sector's ground**, and no
term of the width witnesses that. Parlett's bound (`‖r‖`) places *some*
eigenvalue of the sector within `δᵒ`; it does not say which, and a Krylov start
orthogonal to the ground keeps its whole chain orthogonal to it, so the solve
converges to an *excited* sector level with `δᵒ → 0`. Measured on the truncated
gauge-fixed QYM (`g = 0`, inner occupation `N ≤ 6`, `m = 14`, odd start built
orthogonal to the odd ground, overlap `7.5e-16`):

```
θᵉ₀ = −1.304851   (sector ground −1.304851, δᵉ = 1.4e-5)
θᵒ₀ = −0.778457   (sector ground −1.114924, δᵒ = 1.2e-7)
(T6) gives lo = +0.526380      true sector gap = 0.189928
```

Every stated precondition holds and `lo` exceeds the gap by `0.34`, so `lo` is
an **estimate**, not a lower bound, and `gap_certified_positive(lo)` is not a
proof. Consequences for the formalization: keep `rfl`-level arithmetic on
`(θ, δ)` (that part is exact), but do **not** instantiate the gap theorem from
`θ, δ` alone — the Lean instance needs the ground-resolution witness as an
explicit hypothesis. A valid form exists (§6a): exclude the second eigenvalue
from a certified explicit spectrum and use Kato–Temple.

## 2. Code → math mapping

| Math | Code | Where |
| :--- | :--- | :--- |
| `u = 2⁻⁵³` | `UNIT_ROUNDOFF` | `mass_gap_spec` / `certificate` |
| `c(n) = n³` | `backward_error_const(rank)` | `mass_gap_spec` |
| `δ = ‖r‖ + c(n)u‖Ĝ‖ + h_O` | `certified_width(residual, rank, g_norm, theta)` | `mass_gap_spec` |
| `|θ − λ| ≤ ‖Hψ − θψ‖/‖ψ‖` | `parlett_bound(residual_norm, psi_norm)` | `mass_gap_spec` |
| `θ = ⟨ψ,Hψ⟩/⟨ψ,ψ⟩` | `rayleigh_quotient(psi_h_psi, psi_psi)` | `mass_gap_spec` |
| `[θ−δ, θ+δ] ∋ x` | `interval_contains(value, delta, x)` | `mass_gap_spec` |
| T6 lower bound | `certified_gap_lower_bound(θᵒ, θᵉ, δᵒ, δᵉ)` | `mass_gap_spec` |
| gap interval | `gap_interval(θᵒ, θᵉ, δᵒ, δᵉ) → (lo, hi)` | `mass_gap_spec` |
| stopping rule `lo > 0` | `gap_certified_positive(lo)` | `mass_gap_spec` |
| sector purity witness | `parities_disjoint(max_overlap, tol)` | `mass_gap_spec` |
| per-Ritz certificate | `certified_ritz_values(res)` → `Vec<Certificate>` | `certificate.rs` |
| T6 assembly | `certified_mass_gap(even, odd)` → `GapCertificate` | `certificate.rs` |
| NDJSON emitter | `emit_gap_certificate_ndjson(gap)` | `certificate.rs` |
| **seam** (solve + preconditions + assembly) | `certified_mass_gap_parity(h, v_e, v_o, shifts, opts)` | `forward_sirk.rs` |

## 3. Preconditions of T6 and where they are enforced

1. **Sector purity**: the reflection `R: (A₀,A₁) → (−A₁,−A₀)` is an exact
   `Z₂` symmetry of the gauge-fixed H for **all** `g` (it leaves
   `B = (A₀−A₁) + ½g·A₀A₁` invariant); the starts `v_e = |Ω⟩` (R-even) and
   `v_o = (a†₀ + a†₁)|Ω⟩/√2` (R-odd) are pure-sector; the two Krylov chains
   are disjoint and the Ritz sets independent.
   *Runtime witness:* `parities_disjoint(max_chain_overlap, 1e-8)` inside
   `certified_mass_gap_parity` (`debug_assert`). *Numerical witness:*
   `qym_gauge_fixed_reflection_symmetry_sector_purity`.
2. **Ground selection**: `θˢ₀` is the lowest Ritz value of sector `s` — the
   solver returns the sorted spectrum (`ForwardSirkResult::ritz_values`).
   This selects the lowest value **of the solve's own subspace**; it is not the
   sector ground unless precondition 3 holds.
3. **Ground resolution** (the hypothesis of (T6), and it is *not* checkable
   from the certificate): `θᵒ₀` is within `δᵒ` of the odd sector's ground. A
   residual measures "converged", not "lowest" — see the counterexample in
   §1. Obtainable from an exclusion argument instead (§6a).
4. **Enclosure validity**: `δˢ` bounds `|θˢ − λˢ|` **for the eigenvalue matched
   to the Ritz pair** — residual measured cancellation-free from the stored
   Gram (`ritz_abs_residuals`), roundoff and enclosure per §4.4. *Pinned by:*
   `mass_gap_spec::tests::parlett_bound_holds_on_explicit_matrix` and
   `certified_width_matches_certificate_delta`. Matching to the *ground* is
   precondition 3, not this one.
5. **NO vacuum-sector identification** — deliberately dropped for the
   gauge-fixed H: `⟨0|H|0⟩ = 0` (normal ordering) but the ground is a
   pair-squeezed state below it (`E₀ < 0`, deepening with `g`; at strong
   coupling the truncated ground even flips reflection-odd). The seam
   therefore certifies the **enclosure** of the exact truncated gap by the
   sector-ground-difference interval, not a strict `lo > 0` stopping rule.
   (The lattice-era `even_sector_is_vacuum` predicate is retained as a
   generic contract only.)

## 4. The numerically-pinned claims (the gauge-fixed formalization)

`fock_sirk/tests/qym_mass_gap.rs` (10 tests) executes the formalization on
`qcd_ym_hamiltonian(g)` + SIRK–Hashimoto:

| Claim | Test | Measured |
| :--- | :--- | :--- |
| nested-Fock structure (⟨0|H|0⟩=0, Hermitian, ⟨vac|H|1,1⟩=−1, non-abelian terms at g>0) | `qym_gauge_fixed_hamiltonian_nested_fock_structure` | ✓ |
| R-reflection exact + R-pure chains disjoint (all g) | `qym_gauge_fixed_reflection_symmetry_sector_purity` | ✓ ‖[H,R]‖ = 0 |
| low window alternates R-parity at g=1 (E₀ even, E₁ odd) | `qym_gauge_fixed_low_window_reflection_alternation` | ✓ |
| **gapped at g>0**: E₁−E₀ = 0.091 stable across N≤6/N≤8; SIRK Ritz values bound the exact levels from above | `qym_gauge_fixed_spectral_gap_positive_stable` | ✓ |
| **gapless abelian limit**: g=0 truncated gap shrinks with depth (0.34→0.19→0.12 at N≤4/6/8); R-sector grounds coincide at every m | `qym_gauge_fixed_abelian_limit_gapless` | ✓ |
| gap grows with g (0.030 at g=0.5, 0.091 at g=1, 1.24 at g=2, N≤8) | `qym_gauge_fixed_gap_grows_with_coupling` | ✓ |
| one-particle ground is squeezed, not the Fock vacuum (E₀<0 under ⟨0|H|0⟩=0; R-odd at strong coupling) — a one-particle diagnostic; the nested-Fock ground stays the outer vacuum (S45) | `qym_gauge_fixed_one_particle_ground_sector_structure` | ✓ |
| SIRK sector Ritz values tighten with m | `qym_gauge_fixed_sirk_ritz_monotone_stable_in_m` | ✓ |
| certified interval encloses the exact truncated gap | `qym_gauge_fixed_certified_enclosure_of_exact_gap` | ✓ |
| seam = manual assembly; spec predicates fire | `qym_gauge_fixed_proof_facing_seam_agrees_manual_assembly` | ✓ |

**Refinement found by the numerics (corrects the lattice-era wording):** the
continuum gauge-fixed H's gap is its own — `≈ 0.09` at `g = 1`, growing with
`g` — **not** the lattice's `g²/2` (an electric-lattice result: the lattice
electric term `(g²/2)Σn` gaps the one-quantum sector, while the gauge-fixed
H's quartic `½B²` confines the `(A₀−A₁)` mode). The plan's `lo > 0` stopping
rule, reachable on the lattice at `m = 4`, is not honestly reachable on the
gauge-fixed H at the solved `m` (the deeply squeezed ground makes the Krylov
residuals large), so the certified statement here is the **enclosure of the
exact truncated gap** by the sector-ground-difference interval, cross-checked
against the exact `N ≤ 8` diagonalization of the truncated model.

## 5. Truncation-depth stability (replaces the lattice finite-size study)

The lattice's `l ∈ {2,3,4}` finite-size / Richardson study does not carry
over (the gauge-fixed H has no lattice size parameter). Its honest
replacement is the **truncation-depth study**: at `g = 1` the exact truncated
gap is stable across `N ≤ 6` and `N ≤ 8` (`0.0911` vs `0.0912` — the confining
quartic converges), while at `g = 0` it shrinks with depth (`0.336 → 0.190 →
0.122` — the gapless free-Maxwell limit). This depth-stability is the order
parameter separating gapped from gapless.

## 6. Certified table (gauge-fixed)

`fock_sirk/tests/qcd_mass_gap_certified.rs` (4 tests) instantiates the T6
assembly on the gauge-fixed H: the certified window `[lo, hi]` encloses the
exact truncated gap `E₁ − E₀` for `g ∈ {1, 2}` across truncations, and the
NDJSON emitter produces well-formed sector certificates whose
`certified_positive` flag truthfully reflects `lo > 0` of the emitted numbers
(the pinned Lean4 T6 instance in `../timepiece/GapCertificate/` remains the
historical lattice instantiation; regenerating it for the gauge-fixed numbers
is an LLM-Lean4-specialist item).

The fourth test,
`the_certified_gap_lower_bound_needs_the_sector_ground`, drives SIRK on the
bounded `P_N H P_N` (`QuantumState::restrict_inner` +
`fock_sirk::solve_forward_sirk_truncated`) against the exact parity-resolved
spectrum, and pins two facts: (i) at the **gapless control** `g = 0`, `N ≤ 6`,
`m = 14` the (T6) expression is *positive* (`lo = +0.189913` against an exact
`0.189928`), so positivity is a property of the finite basis and never evidence
of a continuum gap — no coupling has to be found, `g = 0` already does it; and
(ii) the §1 counterexample, `lo = +0.526380` against a true gap of `0.189928`,
with every documented precondition holding.

### 6a. The valid form: exclusion + Kato–Temple

(T6)'s missing hypothesis is obtainable without any new physics input:

* `certificate::certify_spectrum` — an **exclusion witness** for an explicit
  `n × n` Hermitian matrix. Every computed eigenpair gets a Parlett interval;
  touching intervals merge into disjoint clusters, and since the matrix has `n`
  eigenvalues and each interval holds at least one, every cluster holds exactly
  its own multiplicity. So a cluster's lower edge is rigorous and
  `second_eigenvalue_lower_bound()` is a rigorous `λ₂` bound (`None` for a
  degenerate ground, where no witness can exist).
* `mass_gap_spec::temple_lower_bound(θ, r, β)`: `λ₁ ≥ θ − r²/(β − θ)`, valid
  when `θ < β ≤ λ₂` and `r < β − θ`. The second condition is the ground
  witness: in the two-level model it holds exactly when the start has more
  than 50% ground overlap, which is what rejects the §1 counterexample.
* `mass_gap_spec::certified_gap_lower_bound_with_exclusion(θᵒ₀, rᵒ, β, θᵉ₀)`:
  `λ₁ − λ₀ ≥ temple − θᵉ₀`. The even side needs no hypothesis (Rayleigh gives
  `λ₀ ≤ θᵉ₀`), and neither sector's residual enters as a width any more.

Measured at `g = 0`, `N ≤ 6`, `m = 14`: `θᵒ₀ = −1.114923508`, `rᵒ = 4.586e-7`,
`β = −0.778457120`, certified gap `0.189927960` against an exact `0.189927963`
— a **valid** positive gap for `H_N`, `3e-9` below the exact value where the
Parlett-width assembly gave `0.189913148`. Scope: `H_N` only. The witness is a
dense `n × n` matrix (`n = 80` for the odd block at `N ≤ 6`), unusable at
production truncations, and the unbounded `H` still has no lowest eigenvalue
for any of this to bound. The continuum mass gap remains unproven.

### 6b. The campaign verdicts, and two traps (2026-11-10b)

`fock_sirk/tests/mass_gap_exclusion_campaign.rs` runs the campaign grid
(`g ∈ {0, 0.5, 1, 2, 3}`, `N ∈ {6, 8}`, `m = 12`) through the §6a assembly, with
`β ≤ λ₂` from `certify_spectrum` on an explicitly built reflection sector, and
every bound checked against the exact spectrum of the same `H_N`.

With the Ritz pair from the truncated SIRK solve, 3 of 10 rows certify. With the
pair from matvec-only Lanczos on the *same* `H_N` (`certificate::lanczos_ritz`,
40 steps, same sector starts), **6 of 10 rows certify**, and each bound equals the
exact truncated gap to the last printed digit:

| `g` | `N≤` | `θᵉ₀` | `θᵒ₀` | `rᵒ` | certified | exact |
|---|---|---|---|---|---|---|
| 0 | 6 | −1.114923508 | −1.114923508 | 2.0e-15 | **0.189927963** | 0.189927963 |
| 0 | 8 | −1.304851471 | −1.304851471 | 7.3e-15 | **0.122434177** | 0.122434177 |
| 0.5 | 6 | −1.343008908 | −1.307966783 | 5.4e-15 | **0.035042125** | 0.035042125 |
| 1 | 6 | −2.024960357 | −1.933887157 | 1.5e-14 | **0.091073200** | 0.091073200 |
| 1 | 8 | −2.743629504 | −2.652468280 | 1.6e-14 | **0.091161224** | 0.091161224 |
| 2 | 6 | −5.217666264 | −4.367552423 | 2.2e-14 | **0.850113842** | 0.850113842 |

The other four rows are the cells where the odd ground sits *below* the even one
inside `H_N`, so `θᵒ₀ − θᵉ₀` is the **negative of the truncated gap**, to machine
precision:

| `g` | `N≤` | λ₀(even) | λ₁(odd) | `H_N` gap (even − odd) | T6 bound |
|---|---|---|---|---|---|
| 0.5 | 8 | −1.545550924 | −1.576008527 | 0.030457603 | −0.030457603 |
| 2 | 8 | −6.511130065 | −7.754776632 | 1.243646566 | −1.243646566 |
| 3 | 6 | −9.214246967 | −9.236287521 | 0.022040554 | −0.022040554 |
| 3 | 8 | −13.610338101 | −14.566593782 | 0.956255682 | −0.956255682 |

T6's orientation (odd above even) does not hold in those cells at all — so
there is no gap *in that direction* there, and no accuracy can make the
expression positive. But it is not a ceiling on the grid: Temple's inequality is
sector-local, and nothing in it prefers the odd sector.

#### The other orientation, the sectors exchanged (2026-11-10c)

Exchanging the roles certifies the other quantity, `λ₀(even) − λ₁(odd)`:

```text
  λ₀(even) ≥ temple(θᵉ₀, rᵉ, β_even)      λ₁(odd) ≤ θᵒ₀   (Rayleigh–Ritz)
  ⟹ λ₀(even) − λ₁(odd) ≥ temple(θᵉ₀, rᵉ, β_even) − θᵒ₀
```

The odd side then needs **no witness at all**, and the only extra work is one
more `certify_spectrum` pass, on the even block, for `β_even ≤ λ₂(even)`:

| `g` | `N≤` | `θᵉ₀` | `rᵉ` | `λ₂(even)` | `β(even)` | certified⇄ | exact⇄ |
|---|---|---|---|---|---|---|---|
| 0.5 | 8 | −1.545550924 | 6.6e-6 | −1.445385952 | −1.445386066 | **0.030457603** | 0.030457603 |
| 2 | 8 | −6.511130065 | 2.8e-10 | −5.396349662 | −5.396350050 | **1.243646566** | 1.243646566 |
| 3 | 6 | −9.214246967 | 3.2e-14 | −5.126287367 | −5.126287397 | **0.022040554** | 0.022040554 |
| 3 | 8 | −13.610338101 | 1.3e-11 | −11.921429604 | −11.921430269 | **0.956255682** | 0.956255682 |

All four certify, each bound equal to the exact gap to the last printed digit:
**10 of 10 grid cells now carry a certified gap**, with the sector that owns the
ground reported beside it rather than assumed. In T6's own cells the swapped
bound is exactly the negative of the same number (`−0.189927963` at `g = 0,
N ≤ 6`), so the orientations are complements; the test asserts that each
certifies exactly the cells whose ordering matches it.

Two limits on that reading. It is **not ten rows of one theorem**: the paper's
statement is certified on 6 cells, the exchanged one on 4. And in a crossing cell
the bound is the gap of `H_N` only because no odd level lies between the two
grounds — asserted per cell (`λ₂(odd) > λ₀(even)`) — which is what makes the two
sector grounds the two lowest levels of the truncation. A truncated ground that
is *odd* is the finite-`N` artifact to flag: the continuum vacuum is even, so a
crossing cell says `N` is too small, not that the theory has no gap.

The `g = 0` rows are the **control**: they certify a positive gap on a theory
with no continuum gap, which is the sharpest statement of what a truncation
certificate can and cannot mean. And `θᵉ₀` is consumed only as an upper bound on
`λ₀`: the even side needs no witness, only a better `θᵉ₀`.

Two findings worth keeping:

* **The truncated chain stagnates, and `m` does not fix it.** At `g = 1, N ≤ 6`
  the even excess over `λ₀` is `3.71e-1` at `m = 12`, `3.97e-1` at `m = 24` and
  `3.99e-1` at `m = 40`, with the residual flat at `~8e-1`: the forward chain's
  span stops growing, so extra shifts buy nothing. The SIRK rows remain *valid*,
  merely loose — this is a property of the truncated solve, not of the
  certificate.
* **Lanczos belongs on the even side** for the same reason: 40 matvecs reach
  `r ≤ 3e-11` at every cell (usually `1e-14`) where 40 SIRK steps leave `~8e-1`.

#### One count-free `λ₂` bound measured, and why the family cannot reach the window

`certificate::MatchingExclusion` is the tightest count-free witness the crate
can build: colour the sparsity graph's edges into **matchings** `V = Σ_c V_c`
(greedy edge colouring, `C ≤ max degree`), so each `V_c` is a disjoint union of
`2×2` blocks `[[0,v],[v,0]]` and `λ_min(V_c) = −max |H_e|` in closed form; Weyl
class by class gives `λ₂ ≥ d₂ − Σ_c max |H_e|`. That trades the Frobenius split's
`√(#edges)` for `#classes`, so the slack is degree-bounded rather than
`√n`-bounded:

| `N≤` | `n` | classes | colouring slack | `‖V‖_F` | `β` colouring | `β` diagonal |
|---|---|---|---|---|---|---|
| 6 | 80 | 13 | 42.7 | 34.5 | −41.74 | −33.49 |
| 8 | 200 | 17 | 92.6 | 86.4 | −91.64 | −85.39 |
| 12 | 1820 | 28 | 313.5 | 553.8 | −312.49 | −552.78 |

At the two smaller sizes the colouring is *looser* than one Frobenius term
(charging each class's largest entry beats the `l2` norm of ~600 edges only once
the graph is dense enough); by `N ≤ 12` it is 1.8× tighter — the first
count-free bound whose slack does not explode with `n`. It is still nowhere near
a witness, and the obstacle is structural, not a matter of a cleverer split:
`d₂ = 1` while `θ ≈ −2.8 … −1.9`, so the entire off-diagonal budget is
`d₂ − θ < 4`, whereas any splitting bound charges at least one entry per class
against a degree of 13–28. Fewer, larger classes would mean needing `λ_min` of a
large block — the eigenvalue problem again. So the measured answer is: no `λ₂`
witness in the splitting family, at any `N`. The untried route is the count
itself without a full diagonalization — inertia of a sparse factorization of
`H − βI`.

#### `(n₀+n₁)` parity is not the reflection sector

The first version of the sweep classified states by `(n₀+n₁) % 2` and certified
`0.322254` at `g = 2, N ≤ 6` against a true gap of `0.044450` — a soundness
violation the exact check caught. `R` flips modes 0↔1 times `(−1)^(n₀+n₁)`, so
for `n₀ ≠ n₁` its eigenvectors are the ± *combinations*
`(|n₀,n₁⟩ ± (−1)^(n₀+n₁)|n₁,n₀⟩)/√2`, not the states themselves; and at `g > 0`
the `(n₀+n₁)` parity is not even `H`-invariant, because `B²` carries the
three-operator products `A₀²A₁` and `A₀A₁²`, which change that parity. The
corrected construction pairs each `R`-orbit and asserts
`‖(I − P_sector) H u‖ < 1e-9‖Hu‖` for every sector vector — an explicit residual,
because subtracting `Σdot²` from `‖Hu‖²` cancels catastrophically and reports a
spurious `2e-8` leak on an exactly invariant sector.

#### The `g = 0`-only parity-block helper refuses a nonzero coupling

`truncated_parity_block` in `qcd_mass_gap_certified.rs` filters by
`(n₀+n₁) % 2`, which at `g = 0` *is* a reflection sector (both parities are
preserved by the quadratic `H`). It now takes the coupling and refuses to run at
`g ≠ 0`, a `#[should_panic]` test pins the refusal, and the `H`-invariance of the
returned block is measured (`‖(1−P) H P‖_F < 1e-10`). Never reuse it at `g > 0`:
a `β` read from a non-invariant block is not a `λ₂` witness, and that is exactly
how this run's `0.322254` violation would have entered as a "result".
