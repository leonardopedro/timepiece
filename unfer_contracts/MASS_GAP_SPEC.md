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
60 steps, same sector starts), **6 of 10 rows certify at `N ≤ 8` and 10 of 15 at
`N ≤ 10`**, and each bound equals the
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
| 3 | 8 | −13.610338101 | 8.8e-14 | −11.921429604 | −11.921430269 | **0.956255682** | 0.956255682 |
| 1 | 10 | −3.340446626 | 6.7e-11 | −2.614147195 | −2.614149342 | **0.273337089** | 0.273337089 |

All five crossing cells certify (the grid was widened to `N ≤ 10`), each bound
equal to the exact gap to the last printed digit, so **15 of 15 grid cells now carry a certified gap** with the sector that owns the ground reported beside it rather than assumed. In T6's own cells the swapped
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

#### The crossing set is not monotone in `N`

A crossing cell is not "`N` too small": the crossings at `g = 1` are `N ≤ 8` no,
`N ≤ 10` yes, `N ≤ 12` no, `N ≤ 14` yes, `N ≤ 16` yes, and at `g = 2` `N ≤ 8` yes,
`N ≤ 10` no. The parity of the truncated ground therefore oscillates with depth
and must not be read as the vacuum's parity; only the sector-local statements
survive. On the 15-cell grid the unusable-in-T6's-orientation cells are
`(g, N) = (0.5, 8), (1, 10), (2, 8), (3, 6), (3, 8)`.

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
witness in the splitting family, at any `N`. The count itself *is* reachable
without a diagonalization: see below.

#### The count without a diagonalization

`certificate::inertia_below` gets the count from Sylvester's law of inertia
(`H − βI = L D Lᵀ`, so negative pivots = eigenvalues below `β`), carrying an
error bound beside every entry and using a pivot's sign only when
`|value| > error`. Sparse, with a selectable fill-reducing ordering
(`Ordering::ReverseCuthillMckee` or `Ordering::NestedDissection`) and 1×1
symmetric pivoting. The campaign then brackets the gap with no dense step:
`temple(θᵒ₀, rᵒ, β_odd) − θᵉ₀ ≤ λ₁(odd) − λ₀(even) ≤ θᵒ₀ − temple(θᵉ₀, rᵉ, β_even)`.

| `N≤` | sector `n` | fill | count(β) | lower = upper | exact | secs |
|---|---|---|---|---|---|---|
| 6 | 80 | 27 | 1/1 | 0.091073200 | 0.091073200 | 0.00 |
| 8 | 200 | 49 | 1/1 | 0.091161224 | 0.091161224 | 0.02 |
| 10 | 420 | 78 | 1/1 | −0.273337089 | −0.273337089 | 0.07 |
| 12 | 784 | 116 | 1/1 | 0.273346184 | — | 0.15 |
| 14 | 1344 | 164 | 1/1 | −0.112820857 | — | 0.36 |
| 16 | 2160 | 223 | 1/1 | −0.060551502 | — | 0.97 |

The dense `O(n³)` is therefore *not* the price of the witness: the count is
decided through `N ≤ 16` in under a second, and it equals the exact gap where the
dense route can still run (`N ≤ 10`). The margin must be probed over a ladder
(`1e-9 … 1e-2`): at a `1e-9` margin the shift is that close to an eigenvalue, one
pivot is undecidable at the last index, and the counter refuses — a refusal, not
a wrong count.

The campaign's own 15 rows now run on the count instead of `certify_spectrum`:
`β` is a bisection on the count (start at `θ + r`, grow until the count says `λ₂`
has been passed, then 30 bisections back down to the largest deciding `β`, which
minimises Temple's `r²/(β − θ)`). The verdicts come out **identical** to the
dense-`β` run, with the same bounds to the printed digits — SIRK 4 certified /
5 valid-but-not-positive / 6 refused, Lanczos 10 / 5 / 0, and 5 more in the
exchanged orientation, **15 of 15**. `O(n³)` is nowhere on the certification
path; the dense spectrum survives only as the oracle each bound is checked
against.

#### Where the count stops, and what stops it (2026-11-10d)

Driven past its range (odd sector, `g = 1`, `β = θ₀ + 0.5`, both orderings on the
same matrix):

| `N≤` | `n` | fill RCM | fill ND | secs RCM | secs ND |
|---|---|---|---|---|---|
| 6 | 80 | 18 | 16 | 0.00 | 0.00 |
| 10 | 420 | 58 | 52 | 0.00 | 0.00 |
| 14 | 1344 | 138 | 108 | 0.03 | 0.01 |
| 16 | 2160 | 192 | 172 | 0.09 | 0.05 |
| 18 | 3300 | 258 | 226 | 0.27 | 0.15 |
| 20 | 4840 | 337 | 315 | 0.76 | 0.37 |
| 22 | 6864 | 429 | 395 | 1.95 | 0.99 |
| 24 | 9464 | 534 | 485 | 4.75 | 2.24 |

**Fill is not the limit.** The fill is 534 on `n = 9464` at the top of the grid
(5.6 % of the dimension), and both orderings decide there.

**The matrix is not the limit either.** The same elimination in plain `f64`, no
bounds at all, decides every size in the table: smallest pivot `6.162, 7.147,
7.491` at `N ≤ 18, 20, 22`, one eigenvalue below `β` each time, matching the dense
count. What failed was the *bound*: traced per step the pivots stayed in
`10…38`, multipliers below `0.6`, no value above `1e2`, while the tracked error
climbed `1e-14 → 1e-6 → 1.96e3` and reached `4.1e16` at `N ≤ 22`. One `f64` per
entry let each step charge `u ≈ 1.1e-16` of its own value, and the elimination
multiplies that charge along the fill.

**The fix is arithmetic.** `certificate::Bounded` now carries its value as an
unevaluated sum of two `f64`s (`hi + lo`), renormalized through the exact
transforms (`two_sum`, `quick_two_sum`, `two_prod` via `fma`); each operation
folds in only the `8u²·|value|` its renormalization can leave, so one step
injects `u² ≈ 1.2e-32`. The interval bookkeeping and the rule `|value| − error`
are unchanged — a count is still refused unless every pivot's sign is certain.
The same trace at `N ≤ 22` now ends at `7.6e-15` against pivots of `10…38`, and
the worst bound-to-pivot ratio in the grid is `4.7e-10`. The extra flops do not
show: the elimination is `BTreeMap`-bound, so `N ≤ 22` costs 1.95 s where the
one-term value cost 2.16 s.

**Nothing in the grid refuses now, and the reach runs to `N ≤ 32`.** The ignored
reach test (`the_count_reaches_past_the_grid`) decides `N ≤ 26 / 28 / 30`
(`n = 21760`, fill 961 RCM / 927 ND) with both orderings counting the same
inertia — RCM `1.6e-9 / 1.2e-6 / 2.0e-2` bound-to-pivot, nested dissection
`1.2e-22 / 3.5e-21 / 2.9e-19`, at 85.5 s / 19.3 s at `N ≤ 30`. The ignored wall
test (`the_count_refuses_past_the_reach`) pins the end: nested dissection decides
`N ≤ 33` (`n = 31161`, fill 1212, 52 s, ratio `8.0e-13`) and refuses `N ≤ 34`
after 85 s, giving up 725 pivots from the end where the trailing separator's own
relative errors already run to `1e15`; RCM refuses `N ≤ 32` after 216 s (last
deciding size 30) and `N ≤ 36` costs 329 s to refuse. So the reach now differs by
ordering (`30` RCM / `33` nested dissection), what ends it is the same
accumulated rounding, and it is not the clock: the bound arrives with the
elimination nearly finished.

**Two ranges — at the campaign's `β`.** `below == 1` only through `N ≤ 30`, so
that is the certified `λ₂`-witness range *at that threshold*; at `N ≤ 32 / 33`
the counter still decides but reports three and four eigenvalues below `β`,
because the 60-step Ritz value put `β` above `λ₂` as well as above `λ₁`. A `2×2`
block-pivot fallback (for a trailing block in which no diagonal has a decidable
sign; inertia from the determinant and the trace) now counts `[[0,1],[1,0]]`
instead of refusing, but it did not move the wall: at `N ≤ 34` at the loose `β`
no determinantal sign was decidable either and the refusal landed on the same
index `34159`.

**The wall was the shift, not the block (2026-11-11).** Every refusal in the table
above used `β = θ₀ + 0.5` with `θ₀` from 60 Lanczos steps, and 60 steps is
unconverged on these blocks — the residual is `0.05` (odd `N ≤ 20`), `0.58` (even
`N ≤ 20`) and `2.60` (odd `N ≤ 30`) — so `θ₀` was a loose upper bound on `λ₁`
(`−11.8546` against the converged `−13.6716` at `N ≤ 34`) and the count was asked
to factor `H + 11.35·I`: `1.8` above the ground instead of `0.5`. Doubling the
step count until the Ritz *residual* is below `1e-9` (`converged_ground`, which
asserts rather than falling back) every size that refused now decides, in both
blocks, with `below == 1` — a genuine `λ₂` witness: odd `N ≤ 34` (fill 1298,
`9.0e-13`, 70 s, `3.8e-19`), odd `N ≤ 36` (`n = 43320`, fill 1494, 129 s,
`8.0e-18`), even `N ≤ 36` (`n = 48070`, fill 1604, 172 s, `5.2e-15`), odd
`N ≤ 38` (`n = 53200`, `θ₀ = −15.447014`, 320 steps, 230 s, `2.0e-17`), even
`N ≤ 38` (`n = 58730`, `θ₀ = −15.447425`, 295 s, `9.1e-18` — near-degenerate
with the odd ground, `4.1e-4` apart), odd `N ≤ 40` (`n = 64680`,
`θ₀ = −16.341870`, 394 s, fill 2080, `8.8e-17`), odd `N ≤ 42` (`n = 77924`,
`θ₀ = −17.237774`, 620 s, fill 2309, `5.0e-14`) and odd `N ≤ 44` (`n = 93104`,
`θ₀ = −18.138131`, 978 s, fill 2675, `1.5e-14`) and odd `N ≤ 46`
(`n = 110400`, `θ₀ = −19.039563`, 1552 s, fill 3120, `5.8e-14`); the even
block under its **own** `β` reports `below == 1` from `N ≤ 20`
(`n = 5786`, `θ₀ = −7.512462`, fill 358) up through `N ≤ 40`
(`n = 71071`, fill 2218, 479 s, `6.4e-17`), `N ≤ 42` (`n = 85261`, fill 2460,
795 s, `1.3e-14`) and `N ≤ 44` (`n = 101476`, `θ₀ = −18.137463`, 1214 s, fill
2958, `8.4e-15`). So the reach is `46` in the odd block and `44` in the even
one and **the ladder has not stopped, it has become expensive** — the last rows
keep fourteen orders of headroom to the refusal rule — with the witness range at
least that rather than `30`, and the `562 s` even refusal was that matrix at the
*odd* threshold. What grows is the price: in the odd block the count alone goes
`70 → 129 → 230 → 394 → 620 → 978 → 1552 s` (~1.6× a shell) with fill
`1960 → 2080 → 2309 → 2675 → 3120`, the even curve runs
`295 → 479 → 795 → 1214 s` with fill `1960 → 2218 → 2460 → 2958`, so the next
odd shell is ~`2400 s` and is unrun rather than unwalled. The ordering split
survives the correction and is now pinned
rather than bracketed: RCM decides `N ≤ 32` at its own converged `β` (fill 1141,
`θ₀ = −12.777793`, residual `7.6e-13`, ratio `2.6e-2`, 198 s) and refuses
`N ≤ 34` (asserted by `the_converged_shift_does_not_rescue_rcm_at_34`, which
hands RCM the same `θ₀ = −13.671622` at residual `9.0e-13` and requires `None`
back), so RCM's reach is bracketed to `(32, 34]`, and the even block at `N ≤ 30`
decides under RCM only at ratio `1.8e-2` against nested dissection's `5.3e-18`.

**Ordering: smaller fill, and two sizes of reach.** Nested dissection cuts the
fill by 6–27 % on the grid (18→16, 93→68, 258→226, 534→485) and is 2–2.5× faster
at the top. Past the grid its fill advantage fades (652 vs 653 at `N ≤ 26`, 961
vs 927 at `N ≤ 30`), so fill is asserted only on the campaign's own sizes; its
*bound* advantage does not fade, which is why it is the ordering that reaches
furthest (`N ≤ 44` where RCM stops at `32`). Pivoting on relative accuracy instead of magnitude does not move the
wall (measured), and neither do `2×2` block pivots. **Symmetric equilibration is a measured no-op**: `D(H − βI)D`
with `D = diag(2ᵏ)` is an exact congruence (the count must come out identical,
and does, at every size), and the bound-to-pivot ratios are identical to the
printed digits (`4.689e-10 → 4.689e-10` at `N ≤ 24`, `1.248e-6 → 1.248e-6` at
`N ≤ 28`). The growth is in the update chain's rounding, not the matrix's
scaling.

**Recorded because it was measuring a mangled matrix.** The permutation check on
the nested-dissection order is a `debug_assert`, so release runs never saw that
the recursive cut dropped the component it had just walked — `60 of 80` vertices
were missing from the order already at `N ≤ 6`, and the previous revision of this
section measured nested dissection on that truncated matrix (its `N ≤ 16`
refusal was an artifact). The component is now ordered with the others and
`nested_dissection_orders_every_vertex_of_a_split_graph` checks the permutation
in release.

**And one harness bug, since it capped the measurement silently.** Reaching past
`N ≤ 30` first failed in the basis builder: `fock_state` normalized by
`scale_and_add(1/‖ψ‖ − 1)`, and the creation chain returns `‖ψ‖ = √(n!)`, which
passes `2⁵³` at occupation 30 (`√(30!) ≈ 1.6e16`) — there the coefficient rounds
to exactly `−1` and the state is annihilated. Every `N` the harness could build
was capped at 30 without an error; the amplitudes are now divided out directly.

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
