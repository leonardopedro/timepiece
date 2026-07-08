# Summary of changes for run 5e4df198-c2f9-4696-8620-3fec23294d0e
Continued executing `FORMALIZATION_ROADMAP.md`. The single remaining open (optional) queue item was **N14 / F3.5 — the Misra–Gries heavy-hitter bound** (targeted at `BookProof/ChapterF4.lean`); it is now fully implemented and proved, completing the last outstanding roadmap deliverable. (The only `sorry`s left in the project are in `RiemannProof/`, which the roadmap explicitly places out of scope.)

What was added to `BookProof/ChapterF4.lean` — a self-contained, executable formalization of the Misra–Gries streaming frequency-estimation algorithm and its two-sided guarantee:
- `mgSupport`, `mgStep`, `mgRun`: the active-counter count, one processing step (increment if tracked; else open a new counter if fewer than `k` are active; else decrement all counters and record a decrement round), and the run over a stream (`List`).
- `mgSum_decrement`: a full decrement lowers the total by exactly the number of active counters.
- `mgStep_support_le` / `mgRun_support_le`: at most `k` counters are ever active.
- `mgRun_sum`: the conservation invariant `(∑ counters) + (k+1)·(#decrement rounds) = N`.
- `mgRun_decrement_le`: the decrement budget `k·d ≤ N`.
- `mgRun_undercount` (`f̂ ≤ f`) and `mgRun_error_le` (`f ≤ f̂ + d`).
- `misraGries_bound` (the F3.5 headline): the heavy-hitter guarantee `f − N/k ≤ f̂ ≤ f`, stated in truncated-subtraction-free form as `f̂ ≤ f ∧ f ≤ f̂ + N/k`, where `f = xs.count x`, `f̂ = (mgRun k xs).1 x`, `N = xs.length`.

Verification: `lake build` on all default targets is green (8123 jobs). Every new declaration is `sorry`-free and `axiom`-free (`misraGries_bound` checked with the axiom checker: only `propext`, `Classical.choice`, `Quot.sound`); a grep confirms no `sorry`/`admit`/`axiom` in `ChapterF4.lean`, and the `BookProof` library remains fully `sorry`-free. Documentation was updated: `BookProof/ChapterF4.lean` docstring, `BookProof/STATUS.md` (new Wave 41 entry), and `ARISTOTLE_SUMMARY.md` (new top entry, per the explicit request). All changes are committed and pushed.

# Summary of changes — F3.5 (Misra–Gries) completion

Continued `FORMALIZATION_ROADMAP.md`. The single remaining open (optional) queue
item was **N14 / F3.5 — the Misra–Gries heavy-hitter bound** (target
`BookProof/ChapterF4.lean`, §8 Phase 4). It is now fully implemented and proved;
this was the last outstanding roadmap deliverable. (All other `sorry`s in the
project remain confined to `RiemannProof/`, which the roadmap explicitly places
out of scope.)

**F3.5 (new content in `BookProof/ChapterF4.lean`).** A self-contained,
executable formalization of the Misra–Gries frequency-estimation algorithm and
its two-sided guarantee:
- `mgSupport`, `mgStep`, `mgRun` — the counter-support size, one processing step
  (increment if tracked; else open a new counter if fewer than `k` are active;
  else decrement every counter and record a decrement round), and the run of the
  algorithm over a stream (a `List`).
- `mgSum_decrement` — decrementing every counter reduces the total by exactly the
  number of active counters (stated additively over `ℕ`).
- `mgStep_support_le` / `mgRun_support_le` — the invariant that at most `k`
  counters are ever active.
- `mgRun_sum` — the master conservation invariant
  `(∑ counters) + (k+1)·(#decrement rounds) = N` (stream length).
- `mgRun_decrement_le` — the decrement budget `k·d ≤ N`.
- `mgRun_undercount` — the estimate never exceeds the true frequency (`f̂ ≤ f`).
- `mgRun_error_le` — the error is bounded by the number of decrement rounds
  (`f ≤ f̂ + d`).
- `misraGries_bound` (**F3.5 headline**) — the heavy-hitter guarantee
  `f - N/k ≤ f̂ ≤ f`, stated in the truncated-subtraction-free form
  `f̂ ≤ f ∧ f ≤ f̂ + N/k` with `f = xs.count x`, `f̂ = (mgRun k xs).1 x`,
  `N = xs.length`.

The file docstring's deliverable list was extended with an F3.5 bullet.

**Verification.** `lake build` on all default targets is green (8123 jobs). Every
new declaration is `sorry`-free and `axiom`-free (`misraGries_bound` checked with
the axiom checker: only `propext`, `Classical.choice`, `Quot.sound`); a grep
confirms no `sorry`/`admit`/`axiom` in `ChapterF4.lean`. The `BookProof` library
remains fully `sorry`-free. All changes are committed and pushed.

---

# Summary of changes for run 5d334a3d-01a2-46a8-8e96-be6f227b5114
Executed `FORMALIZATION_ROADMAP.md`. The only work still open in the roadmap was the two flagship residues — N13 (Hashimoto Shift-invert Rational Krylov) and N14 (Quantum Flow Matching); both are now complete, and the HYGIENE block was confirmed already satisfied (the seven keeper modules are registered in `BookProof.lean` and the broken `ChapterSphericalBessel2.lean` is absent).

N13 residue (in `BookProof/ChapterH1.lean` and `BookProof/ChapterH2.lean`):
- H1.3 — `phiOp1` (operator φ₁-function) and `duhamel_phiOp1` (the exponential-integrator Duhamel identity `∫₀^δ e^{(δ−s)·A}g ds = δ·phiOp1(δ·A)g`).
- H1.5 — `psi` (ψ_{k,γ}(x)=φ_k(γ−x⁻¹), Def 2.4), `psi_resolvent`, and `resolvent_eigenvector` (the spectral bridge for φ_k(A)=ψ_{k,γ}(X)).
- H1.7 — `resolvent_shift_repr` (`X_j = (1+h(m−j)·X_m)⁻¹·X_m`, the rational-Krylov generating step of eq. 11).
- H2.2 — `sirk_compression` (`Vᴴ X V = H K⁻¹`, eq. 10).
- H2.3 — `sirk_error_bound_of_crouzeix` (the (13)+(14) SIRK error bound, conditional on two named Crouzeix-inequality applications supplied as hypotheses — no axiom).
- H2.4 — `sirk_advantage_factor` (`e^{−hm}·B ≤ B`, the Remark 4.2 decay advantage).

N14 residue (new `BookProof/ChapterF4.lean`, registered in `BookProof.lean`):
- F3.1 — `countSketch`, `countSketch_add`, and `countSketch_unbiased` (Count-Sketch inner-product unbiasedness for Rademacher signs).
- F3.2 — `observable_matrix_entry` (the trace identity `Tr(Eᴴ Wᴴ P_a W) = conj(W_{a,r})·W_{a,s}`).
- F3.3 — `hermitian_flow_unitary` and `hermitian_flow_preserves_normSq` (the reduced flow e^{−itH} is unitary and norm-preserving).
- F3.4 — `pseudoInverse_left_inverse` (`(ΦᵀΦ)⁻¹Φᵀ·Φ = I`).
The optional/low-priority F3.5 (Misra–Gries) is noted as future work.

Verification: `lake build` on all default targets is green (8123 jobs). Every new declaration is sorry-free and axiom-free (only `propext`, `Classical.choice`, `Quot.sound`, spot-checked with the axiom checker on `duhamel_phiOp1`, `sirk_error_bound_of_crouzeix`, and `countSketch_unbiased`); a source scan confirms no `sorry`/`admit`/`axiom` in the new code. The `BookProof` library remains fully sorry-free. The only remaining `sorry`s in the project are in `RiemannProof/` (the Riemann Hypothesis chapter), which the roadmap explicitly places out of scope. Documentation was updated (`BookProof/STATUS.md` Wave 40, the roadmap status header, and `ARISTOTLE_SUMMARY.md`). All changes are committed and pushed.

# Summary of changes for the Wave 40 run (N13 + N14 residues)

Executed `FORMALIZATION_ROADMAP.md`. The remaining open work in the roadmap was
the N13 (Hashimoto SIRK) and N14 (QFM) residues; both are now complete, and the
HYGIENE block was verified already satisfied (keeper modules registered in
`BookProof.lean`, `ChapterSphericalBessel2.lean` absent).

**N13 residue (`BookProof/ChapterH1.lean`, `BookProof/ChapterH2.lean`).**
- H1.3: `phiOp1` + `duhamel_phiOp1` (exponential-integrator Duhamel identity).
- H1.5: `psi`, `psi_resolvent`, `resolvent_eigenvector` (Def 2.4 spectral bridge).
- H1.7: `resolvent_shift_repr` (rational-Krylov generating step, eq. 11).
- H2.2: `sirk_compression` (`Vᴴ X V = H K⁻¹`, eq. 10).
- H2.3: `sirk_error_bound_of_crouzeix` (SIRK error bound (13)+(14), conditional on
  the two named Crouzeix applications — no axiom).
- H2.4: `sirk_advantage_factor` (`e^{−hm}·B ≤ B`, Remark 4.2).

**N14 residue (new `BookProof/ChapterF4.lean`, registered in `BookProof.lean`).**
- F3.1: `countSketch`, `countSketch_add`, `countSketch_unbiased` (Count-Sketch
  unbiasedness for Rademacher signs).
- F3.2: `observable_matrix_entry` (trace identity `Tr(Eᴴ Wᴴ P_a W) = conj(W_{a,r})·W_{a,s}`).
- F3.3: `hermitian_flow_unitary`, `hermitian_flow_preserves_normSq`.
- F3.4: `pseudoInverse_left_inverse` (`(ΦᵀΦ)⁻¹Φᵀ·Φ = I`).
- F3.5 (Misra–Gries) was optional/low-priority; left as future work.

All new declarations are `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`, spot-checked with `lean_verify`).
`lake build` on all default targets is green (8123 jobs). BookProof remains fully
`sorry`-free. The only remaining `sorry`s in the project are in `RiemannProof/`
(the Riemann Hypothesis chapter), which the roadmap explicitly places out of
scope. See `BookProof/STATUS.md` Wave 40 for details.

# Summary of changes for run 2c67c6af-fbb5-48fd-85f3-0c347cc354e3
Completed the next step of the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) as **Wave 63**, extending the previous spherical Bessel work one order further to `j₆`.

**New module** `BookProof/ChapterSphericalBessel6.lean` (registered in `BookProof.lean`), covering the §A.5 "Hankel–Majorana Transform" subsection. Building on the earlier `j₀…j₅` closed forms and derivatives, it proves:
- `sj6` / `deriv_sj6` — the closed form `j₆(r) = (10395/r⁷ − 4725/r⁵ + 210/r³ − 1/r) sin r − (10395/r⁶ − 1260/r⁴ + 21/r²) cos r` and its first derivative;
- `sbessel_six_eq` — the Rayleigh formula reproduces the closed form, `sbessel 6 r = j₆(r)`;
- `sj6_satisfies_ode` — `j₆` solves the l = 6 spherical Bessel ODE `r² j'' + 2 r j' + (r² − 42) j = 0`;
- `sbessel_recurrence_456` — the three-term recurrence at l = 5: `j₄ + j₆ = (11/r)·j₅`;
- `deriv_recurrence_sj5` — the differentiation law `d/dr j₅ = j₄ − 6/r j₅`.

With this addition the seven lowest spherical Bessel functions `j₀…j₆` are all shown to arise from the Rayleigh formula, satisfy their defining second-order ODEs, and obey both the three-term and first-derivative recurrences.

**Verification.** Each identity was checked numerically first (against the standard recurrence). The full `lake build` is green (8141 jobs); the new module is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`), confirmed by a `sorry` grep and the axiom checker on the headline theorems. The three heavy proofs use a locally-scoped, commented `maxHeartbeats` (needed because the `j₆` closed form carries terms up to `r⁻⁸`); no new linter warnings remain. `BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md` were both updated with a Wave 63 entry. All work is committed and pushed.

# Summary of changes — Wave 63
Completed the next step of the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) as **Wave 63**, extending the spherical Bessel function work of the previous waves one order further to `j₆`.

**New module** `BookProof/ChapterSphericalBessel6.lean` (registered in `BookProof.lean`), covering the §A.5 "Hankel–Majorana Transform" subsection. Building on the earlier `j₀…j₅` closed forms and derivatives, it proves:
- `sj6` / `deriv_sj6` — the closed form `j₆(r) = (10395/r⁷ − 4725/r⁵ + 210/r³ − 1/r) sin r − (10395/r⁶ − 1260/r⁴ + 21/r²) cos r` and its first derivative;
- `sbessel_six_eq` — the Rayleigh formula reproduces the closed form, `sbessel 6 r = j₆(r)`;
- `sj6_satisfies_ode` — `j₆` solves the l = 6 spherical Bessel ODE `r² j'' + 2 r j' + (r² − 42) j = 0`;
- `sbessel_recurrence_456` — the three-term recurrence at l = 5: `j₄ + j₆ = (11/r)·j₅`;
- `deriv_recurrence_sj5` — the differentiation law `d/dr j₅ = j₄ − 6/r j₅`.

With this addition the seven lowest spherical Bessel functions `j₀…j₆` are all shown to arise from the Rayleigh formula, satisfy their defining second-order ODEs, and obey both the three-term and first-derivative recurrences.

**Verification.** Each identity was checked numerically first (against the standard three-term recurrence). The full `lake build` is green (8141 jobs); the new module is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`), confirmed by a `sorry` grep and the axiom checker on the headline theorems (`sbessel_six_eq`, `sj6_satisfies_ode`). `BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md` were both updated with a Wave 63 entry. All work is committed and pushed.

# Summary of changes for run 2d58541c-07b4-4a6e-b992-891af330f111
Completed the next step of the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) as **Wave 62**, extending the spherical Bessel function work of the previous waves one order further to `j₅`.

**New module** `BookProof/ChapterSphericalBessel5.lean` (registered in `BookProof.lean`), covering the §A.5 "Hankel–Majorana Transform" subsection. Building on the earlier `j₀…j₄` closed forms and derivatives, it proves:
- `sj5` / `deriv_sj5` — the closed form `j₅(r) = (945/r⁶ − 420/r⁴ + 15/r²) sin r − (945/r⁵ − 105/r³ + 1/r) cos r` and its first derivative;
- `sbessel_five_eq` — the Rayleigh formula reproduces the closed form, `sbessel 5 r = j₅(r)`;
- `sj5_satisfies_ode` — `j₅` solves the l = 5 spherical Bessel ODE `r² j'' + 2 r j' + (r² − 30) j = 0`;
- `sbessel_recurrence_345` — the three-term recurrence at l = 4: `j₃ + j₅ = (9/r)·j₄`;
- `deriv_recurrence_sj4` — the differentiation law `d/dr j₄ = j₃ − 5/r j₄`.

With this addition the six lowest spherical Bessel functions `j₀…j₅` are all shown to arise from the Rayleigh formula, satisfy their defining second-order ODEs, and obey both the three-term and first-derivative recurrences.

**Verification.** Each identity was checked numerically first. The full `lake build` is green (8140 jobs); the new module is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`), confirmed by a `sorry` grep and the axiom checker on the headline theorems. `BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md` were both updated with a Wave 62 entry. All work is committed and pushed.

# Summary of changes — Wave 62
Continued the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) as **Wave 62**, extending the spherical Bessel function work of Waves 58–61 one order further to `j₅`.

**New module** `BookProof/ChapterSphericalBessel5.lean` (registered in `BookProof.lean`), covering the §A.5 "Hankel–Majorana Transform" subsection (Definitions 65–71). Building on the earlier `j₀…j₄` closed forms and derivatives, it proves:
- `sj5` / `deriv_sj5` — the closed form `j₅(r) = (945/r⁶ − 420/r⁴ + 15/r²) sin r − (945/r⁵ − 105/r³ + 1/r) cos r` and its first derivative;
- `sbessel_five_eq` — the Rayleigh formula reproduces the closed form, `sbessel 5 r = j₅(r)`;
- `sj5_satisfies_ode` — `j₅` solves the l = 5 spherical Bessel ODE `r² j'' + 2 r j' + (r² − 30) j = 0`;
- `sbessel_recurrence_345` — the three-term recurrence at l = 4: `j₃ + j₅ = (9/r)·j₄`;
- `deriv_recurrence_sj4` — the differentiation law `d/dr j₄ = j₃ − 5/r j₄`.

With this addition the six lowest spherical Bessel functions `j₀, j₁, j₂, j₃, j₄, j₅` are all shown to arise from the Rayleigh formula, satisfy their defining second-order ODEs, and obey both the three-term and first-derivative recurrences.

**Verification.** Every identity was checked numerically before formalization. The full `lake build` is green (8140 jobs); the new module is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`), confirmed by a `sorry` grep and the axiom checker on the headline theorems. `BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md` were both updated with a Wave 62 entry. All work is committed and pushed.

# Summary of changes for run 0da57b2b-c9a5-48d6-b046-044b9fb8c929
Continued the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) as **Wave 61**, extending the spherical Bessel function work of the previous waves one order further to `j₄`.

**New module** `BookProof/ChapterSphericalBessel4.lean` (registered in `BookProof.lean`), covering the §A.5 "Hankel–Majorana Transform" subsection (Definitions 65–71). Building on the earlier `j₀…j₃` closed forms and derivatives, it proves:
- `sj4` / `deriv_sj4` — the closed form `j₄(r) = (105/r⁵ − 45/r³ + 1/r) sin r − (105/r⁴ − 10/r²) cos r` and its first derivative;
- `sbessel_four_eq` — the Rayleigh formula reproduces the closed form, `sbessel 4 r = j₄(r)`;
- `sj4_satisfies_ode` — `j₄` solves the l = 4 spherical Bessel ODE `r² j'' + 2 r j' + (r² − 20) j = 0`;
- `sbessel_recurrence_234` — the three-term recurrence at l = 3: `j₂ + j₄ = (7/r)·j₃`;
- `deriv_recurrence_sj3` — the differentiation law `d/dr j₃ = j₂ − 4/r j₃`.

With this addition the five lowest spherical Bessel functions `j₀, j₁, j₂, j₃, j₄` are all shown to arise from the Rayleigh formula, satisfy their defining second-order ODEs, and obey both the three-term and first-derivative recurrences.

**Verification.** Every identity was checked numerically before formalization. The full `lake build` is green (8139 jobs); the new module is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`), confirmed by a `sorry` grep and the axiom checker on all headline theorems.

`BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md` were both updated with a Wave 61 entry. All work is committed and pushed.

# Summary of changes — Wave 61
Continued the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) as **Wave 61**, extending the spherical Bessel function work of Waves 58–60 one order further to `j₄`.

**New module** `BookProof/ChapterSphericalBessel4.lean` (registered in `BookProof.lean`), covering the §A.5 "Hankel–Majorana Transform" subsection (Definitions 65–71). It reuses the earlier closed forms/derivatives and proves:
- `sj4` / `deriv_sj4` — the closed form `j₄(r) = (105/r⁵ − 45/r³ + 1/r) sin r − (105/r⁴ − 10/r²) cos r` and its first derivative;
- `sbessel_four_eq` — the Rayleigh formula reproduces the closed form, `sbessel 4 r = j₄(r)`;
- `sj4_satisfies_ode` — `j₄` solves the l = 4 spherical Bessel ODE `r² j'' + 2 r j' + (r² − 20) j = 0`;
- `sbessel_recurrence_234` — the three-term recurrence at l = 3: `j₂(r) + j₄(r) = (7/r)·j₃(r)`;
- `deriv_recurrence_sj3` — the differentiation law `d/dr j₃ = j₂ − 4/r j₃`.

With Waves 58–61 the five lowest spherical Bessel functions `j₀, j₁, j₂, j₃, j₄` are shown to arise from the Rayleigh formula, satisfy their defining second-order ODEs, and obey both the three-term and first-derivative recurrences.

**Verification.** Each identity was checked numerically before formalization. The full `lake build` is green (8139 jobs); the new module is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`, no external hypotheses), confirmed by a `sorry` grep and the axiom checker on all headline theorems.

`BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md` were both updated with a Wave 61 entry. All work is committed and pushed.

# Summary of changes for run 42a25b7b-af17-4523-9309-45e21072f29c
Continued the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) as **Wave 60**, extending the spherical Bessel function work of Waves 58–59.

**New module** `BookProof/ChapterSphericalBessel3.lean` (registered in `BookProof.lean`), covering the §A.5 "Hankel–Majorana Transform" subsection (Definitions 65–71). It reuses the earlier closed forms/derivatives and proves:
- `sj3` / `deriv_sj3` — the closed form `j₃(r) = (15/r⁴ − 6/r²) sin r − (15/r³ − 1/r) cos r` and its first derivative;
- `sbessel_three_eq` — the Rayleigh formula reproduces the closed form, `sbessel 3 r = j₃(r)`;
- `sj3_satisfies_ode` — `j₃` solves the l = 3 spherical Bessel ODE `r² j'' + 2 r j' + (r² − 12) j = 0`;
- `sbessel_recurrence_123` — the three-term recurrence at l = 2: `j₁(r) + j₃(r) = (5/r)·j₂(r)`;
- `deriv_recurrence_sj1` / `deriv_recurrence_sj2` — the differentiation law `d/dr jₗ = jₗ₋₁ − (l+1)/r jₗ` at l = 1, 2.

With Waves 58–60 the four lowest spherical Bessel functions `j₀, j₁, j₂, j₃` are shown to arise from the Rayleigh formula, satisfy their defining second-order ODEs, and obey both the three-term and first-derivative recurrences.

**Verification.** Each identity was checked numerically before formalization. The full `lake build` is green (8138 jobs); the new module is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`, no external hypotheses), confirmed by a `sorry` grep and the axiom checker on all headline theorems. I also cleaned up the machine-found proofs (removed dangling semicolons, split over-long lines) so the file is warning-free.

`BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md` were both updated with a Wave 60 entry. All work is committed and pushed.

# Summary of changes — Wave 60
Executed the next step of the standing roadmap directive (mine the next
self-contained mathematical content from `book.tex`) as **Wave 60**, and updated
`ARISTOTLE_SUMMARY.md` as requested.

**What I did.** Extended the classical analytic characterisation of the spherical
Bessel functions of the first kind `jₗ` (the `book.tex` §A.5 subsection
*"Hankel–Majorana Transform"*, Definitions 65–71) one order beyond Waves 58–59.
The new module `BookProof/ChapterSphericalBessel3.lean` (registered in
`BookProof.lean`) reuses the earlier closed forms/derivatives and proves:

- `sj3` / `deriv_sj3` — the closed form
  `j₃(r) = (15/r⁴ − 6/r²) sin r − (15/r³ − 1/r) cos r` and its first derivative;
- `sbessel_three_eq` — the Rayleigh formula reproduces the closed form,
  `sbessel 3 r = j₃(r)` (assembled from Wave 59's `sbessel_two_eq` via one more
  Rayleigh iterate);
- `sj3_satisfies_ode` — `j₃` solves the `l = 3` spherical Bessel ODE
  `r² j'' + 2 r j' + (r² − 12) j = 0`;
- `sbessel_recurrence_123` — the three-term recurrence at `l = 2`:
  `j₁(r) + j₃(r) = (5/r) · j₂(r)`;
- `deriv_recurrence_sj1` / `deriv_recurrence_sj2` — the differentiation law
  `d/dr jₗ = jₗ₋₁ − (l+1)/r jₗ` at `l = 1, 2`.

With Waves 58–60 the four lowest spherical Bessel functions `j₀, j₁, j₂, j₃` are
shown to arise from the Rayleigh formula, satisfy their defining second-order
ODEs, and obey both the three-term and first-derivative recurrences.

**Verification.** Each new identity was first checked numerically, then
formalized. The full build is green (8138 jobs); the new module is `sorry`-free
and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`; no
`native_decide`, no external hypotheses), confirmed by a `sorry` grep and the
axiom checker on all headline theorems. Wave 60 entries were added to
`BookProof/STATUS.md` and prepended here. All work is committed and pushed.

# Summary of changes for run 4f0309eb-35a5-486b-98aa-cc9129ed5053
Executed the next step of the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) as **Wave 59**, and updated `ARISTOTLE_SUMMARY.md` as requested.

**What I did.** Completed the classical analytic characterisation of the spherical Bessel functions of the first kind `jₗ` begun in Wave 58 (the `book.tex` §A.5 subsection *"Hankel–Majorana Transform"*, Definitions 65–71). The new module `BookProof/ChapterSphericalBessel2.lean` (registered in `BookProof.lean`) reuses the Wave 58 closed forms `sj0`/`sj1`/`sj2` and proves:

- `deriv_sj1` / `deriv_sj2` — the first derivatives of the closed forms `j₁(r) = sin r / r² − cos r / r` and `j₂(r) = (3/r³ − 1/r) sin r − (3/r²) cos r`;
- `sj1_satisfies_ode` — `j₁` solves the `l = 1` spherical Bessel ODE `r² j'' + 2 r j' + (r² − 2) j = 0`;
- `sj2_satisfies_ode` — `j₂` solves the `l = 2` spherical Bessel ODE `r² j'' + 2 r j' + (r² − 6) j = 0`;
- `sbessel_recurrence_012` — the classical three-term recurrence `jₗ₋₁ + jₗ₊₁ = (2l+1)/r · jₗ` at `l = 1`: `j₀(r) + j₂(r) = (3/r) · j₁(r)`.

Together with Wave 58's `sj0_satisfies_ode` and `rayleigh_raise_01`, the three lowest spherical Bessel functions are now shown to satisfy their defining ODEs and the recurrence relations that generate the family.

**Verification.** The three claims were first checked numerically, then formalized. The full build is green (8137 jobs); the new module is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`, no external hypotheses), confirmed by a `sorry` grep and the axiom checker on all headline theorems. Wave 59 entries were added to `BookProof/STATUS.md` and prepended to `ARISTOTLE_SUMMARY.md`. All work is committed and pushed.

# Summary of changes — Wave 59
Executed the next step of the standing roadmap directive (mine the next
self-contained mathematical content from `book.tex`) as **Wave 59**, and updated
`ARISTOTLE_SUMMARY.md` as requested.

**What I did.** Completed the classical analytic characterisation of the
**spherical Bessel functions of the first kind** `jₗ` begun in Wave 58 (the
`book.tex` §A.5 subsection *"Hankel–Majorana Transform"*, Definitions 65–71). The
new module `BookProof/ChapterSphericalBessel2.lean` (registered in
`BookProof.lean`) reuses the Wave 58 closed forms `sj0`/`sj1`/`sj2` and proves:

- `deriv_sj1` / `deriv_sj2` — the first derivatives of the closed forms
  `j₁(r) = sin r / r² − cos r / r` and
  `j₂(r) = (3/r³ − 1/r) sin r − (3/r²) cos r`;
- `sj1_satisfies_ode` — `j₁` solves the `l = 1` spherical Bessel ODE
  `r² j'' + 2 r j' + (r² − 2) j = 0`;
- `sj2_satisfies_ode` — `j₂` solves the `l = 2` spherical Bessel ODE
  `r² j'' + 2 r j' + (r² − 6) j = 0`;
- `sbessel_recurrence_012` — the classical three-term recurrence
  `jₗ₋₁ + jₗ₊₁ = (2l+1)/r · jₗ` at `l = 1`: `j₀(r) + j₂(r) = (3/r) · j₁(r)`.

**Verification.** The full `lake build` is green (8137 jobs). The new module is
`sorry`-free and `axiom`-free — confirmed by a `sorry` grep and by the axiom
checker on `sj1_satisfies_ode`, `sj2_satisfies_ode`, and `sbessel_recurrence_012`
(only `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`, no
`axiom`, no external hypotheses). The three claims (both ODEs and the recurrence)
were first checked numerically before formalizing. Matching Wave 59 entries were
added to `BookProof/STATUS.md` and prepended here. All work committed and pushed.

# Summary of changes for run 84ccc86f-d487-4655-b162-e6a65fa3ed07
Executed the next step of the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) as **Wave 58**, and updated `ARISTOTLE_SUMMARY.md` as requested.

**What I did.** Formalized the analytic backbone of the `book.tex` §A.5 subsection *"Hankel–Majorana Transform"* (Definitions 65–71): the **spherical Bessel functions of the first kind** `jₗ`, defined by the **Rayleigh formula** `jₗ(r) = rˡ (-(1/r) d/dr)ˡ (sin r / r)`. These special functions are absent from Mathlib (only the Legendre *symbol* exists — no spherical Bessel functions, spherical harmonics, or Legendre polynomials), so the new module `BookProof/ChapterSphericalBessel.lean` (registered in `BookProof.lean`) builds the core from scratch:

- `rayleighOp` — the Rayleigh operator `T f (r) = -(1/r)·f'(r)`;
- `sbesselBase` / `sbessel` — the generator `j₀ = sin r / r` and the general `jₗ(r) = rˡ (Tˡ (sin r / r))(r)` (Definition 67);
- `sj0` / `sj1` / `sj2` — the closed forms `j₀ = sin r / r`, `j₁ = sin r / r² − cos r / r`, `j₂ = (3/r³ − 1/r) sin r − (3/r²) cos r`;
- `deriv_sbesselBase` — `d/dr (sin r / r) = cos r / r − sin r / r²`;
- `sbessel_zero` / `sbessel_one_eq` / `sbessel_two_eq` — the Rayleigh formula reproduces the three closed forms (l = 1, 2 via first/second derivatives);
- `rayleigh_raise_01` — the raising relation `j₁ = −(d/dr) j₀`;
- `sj0_satisfies_ode` — `j₀ = sin r / r` solves the l = 0 spherical Bessel ODE `r² j'' + 2 r j' + r² j = 0`.

**Verification.** The full `lake build` is green (8136 jobs). The new module is `sorry`-free and `axiom`-free — confirmed by a `sorry` grep and by the axiom checker on the headline results `sbessel_two_eq` and `sj0_satisfies_ode` (only `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`, no `axiom`, no external hypotheses). Proofs were cleaned of leftover `grind`/multi-goal artifacts and the module compiles warning-free. Matching Wave 58 entries were added to `BookProof/STATUS.md` and prepended to `ARISTOTLE_SUMMARY.md`. All work committed and pushed.

# Summary of changes — Wave 58
Executed the next step of the standing roadmap directive (mine the next
self-contained mathematical content from `book.tex`) as **Wave 58**, and updated
`ARISTOTLE_SUMMARY.md` as requested.

**New work.** Formalized the analytic backbone of the `book.tex` §A.5 subsection
*"Hankel–Majorana Transform"* (line ~5805, Definitions 65–71): the **spherical
Bessel functions of the first kind** `jₗ`, defined (Definition 67) by the
**Rayleigh formula** `jₗ(r) = rˡ (-(1/r) d/dr)ˡ (sin r / r)`.  These special
functions are **absent from Mathlib** (only the Legendre *symbol* exists; there
are no spherical Bessel functions, spherical harmonics, or Legendre
polynomials), so the new module `BookProof/ChapterSphericalBessel.lean`
(registered in `BookProof.lean`) builds the self-contained core from scratch:

- `rayleighOp` — the Rayleigh differential operator `T f (r) = -(1/r) · f'(r)`;
- `sbesselBase` / `sbessel` — the generator `j₀(r) = sin r / r` and the general
  spherical Bessel function `jₗ(r) = rˡ (Tˡ (sin r / r))(r)` (Definition 67);
- `sj0` / `sj1` / `sj2` — the classical closed forms `j₀ = sin r / r`,
  `j₁ = sin r / r² − cos r / r`, `j₂ = (3/r³ − 1/r) sin r − (3/r²) cos r`;
- `deriv_sbesselBase` — `d/dr (sin r / r) = cos r / r − sin r / r²`;
- `sbessel_zero` / `sbessel_one_eq` / `sbessel_two_eq` — the Rayleigh formula
  reproduces the three closed forms (the `l = 1, 2` cases via the first/second
  derivatives, with `Filter.EventuallyEq.deriv_eq` on the punctured line);
- `rayleigh_raise_01` — the raising relation `j₁ = −(d/dr) j₀`;
- `sj0_satisfies_ode` — `j₀(r) = sin r / r` solves the `l = 0` spherical Bessel
  ODE `r² j'' + 2 r j' + r² j = 0`.

The surrounding representation-theoretic modelling (unitarity of the full
Hankel–Majorana transform, spherical-harmonic expansions, Clebsch–Gordan
assembly) is left as prose.

**Verification.** Full `lake build` is green (8136 jobs). The module is
`sorry`-free and `axiom`-free — confirmed by a `sorry` grep and by the axiom
checker on the headline declarations `sbessel_two_eq` and `sj0_satisfies_ode`
(only `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`, no
`axiom`, no external hypotheses).  Added a matching Wave 58 entry to
`BookProof/STATUS.md` and prepended this Wave 58 section to
`ARISTOTLE_SUMMARY.md`.  All work committed and pushed.

# Summary of changes for run 5bb8dec8-ed3c-4860-92f7-3102ef2b71cf
Executed the next step of the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) as **Wave 57**, and updated `ARISTOTLE_SUMMARY.md` as requested.

**New work.** Formalized the finite-dimensional algebraic core of the `book.tex` §A.5 subsection *"Spinor frame and CPT theorem"*. There the author states that the most general mass in the Hamiltonian `iH` covariant under the connected component of the Lorentz group is `iH = ∂⃗·γ⃗ γ⁰ + i γ⁰ m₁ + γ⁰γ⁵ m₂`, invariant under parity–time reversal ("essentially the CPT theorem"). Working in the concrete 4×4 Majorana model of §A.3 (`BookProof/ChapterA3.lean`), the plane-wave form (`∂ⱼ ↦ i kⱼ`) is the matrix `D(k,m₁,m₂) = i (Σⱼ kⱼ γ^{j+1}γ⁰) + i m₁ γ⁰ + m₂ γ⁰γ⁵`. New module `BookProof/ChapterCPTHamiltonian.lean` (registered in `BookProof.lean`) establishes:
- the five building-block matrices `γ^{j+1}γ⁰`, `iγ⁰`, `γ⁰γ⁵` are each casts of explicit integer matrices;
- they are mutually anticommuting involutions with squares `+1,+1,+1,-1,-1` (Clifford relations reduced to the §A.3 integer model, closed by `decide`);
- the kinetic blocks are Hermitian, the two mass blocks anti-Hermitian;
- `diracHamOp_conjTranspose`: `iH` is anti-Hermitian (`Dᴴ = -D`), i.e. the Hamiltonian `H` is self-adjoint;
- `diracHamOp_sq`: the relativistic mass-shell / dispersion relation `D² = -(k₀²+k₁²+k₂²+m₁²+m₂²) • 1`, so the eigenvalues of `H` are `±√(k⃗²+m₁²+m₂²)` — `m₁, m₂` are exactly the covariant mass parameters. The surrounding physical modelling is left as prose.

**Verification.** Full `lake build` is green (8135 jobs). The module is `sorry`-free and `axiom`-free — confirmed by a `sorry` grep and by the axiom checker on the two headline declarations `diracHamOp_conjTranspose` and `diracHamOp_sq` (only `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`, no `axiom`, no external hypotheses). Added a matching Wave 57 entry to `BookProof/STATUS.md` and prepended a Wave 57 section to `ARISTOTLE_SUMMARY.md`. All work committed and pushed.

# Summary of changes — Wave 57
Executed the next step of the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) as **Wave 57**.

**New work.** Formalized the finite-dimensional algebraic core of the `book.tex` §A.5 subsection *"Spinor frame and CPT theorem"* (line ~6453). There the author states that, in space coordinates, the most general mass in the Hamiltonian `iH` covariant under the connected component of the Lorentz group is `iH = ∂⃗·γ⃗ γ⁰ + i γ⁰ m₁ + γ⁰γ⁵ m₂`, and that this operator is invariant under a parity–time reversal ("this is essentially the CPT theorem"). Working in the concrete `4×4` Majorana model of §A.3 (`BookProof/ChapterA3.lean`), the plane-wave form of that operator (`∂ⱼ ↦ i kⱼ`) is the `4×4` complex matrix `D(k,m₁,m₂) = i (Σⱼ kⱼ γ^{j+1}γ⁰) + i m₁ γ⁰ + m₂ γ⁰γ⁵`. New module `BookProof/ChapterCPTHamiltonian.lean` (registered in `BookProof.lean`) proves:
- `Kin` / `MassA` / `MassB` and `Kin_eq_cast` / `MassA_eq_cast` / `MassB_eq_cast` — the five building-block matrices `γ^{j+1}γ⁰` (`j : Fin 3`), `iγ⁰`, `γ⁰γ⁵` are each the cast of an explicit integer matrix;
- `Kin_sq` (`=1`), `Kin_anticomm`, `MassA_sq` / `MassB_sq` (`=-1`), `MassA_MassB_anticomm`, `Kin_MassA_anticomm`, `Kin_MassB_anticomm` — the five matrices are mutually anticommuting involutions with squares `+1,+1,+1,-1,-1` (Clifford relations reduced to the §A.3 integer model and closed by `decide`);
- `Kin_conjTranspose` / `MassA_conjTranspose` / `MassB_conjTranspose` — the kinetic blocks are Hermitian and the two mass blocks anti-Hermitian;
- `diracHamOp_conjTranspose` — `iH` is anti-Hermitian (`Dᴴ = -D`), i.e. the Hamiltonian `H` is self-adjoint;
- `diracHamOp_sq` — the relativistic mass-shell / dispersion relation `D² = -(k₀²+k₁²+k₂²+m₁²+m₂²) • 1`, so the eigenvalues of `H` are `±√(k⃗²+m₁²+m₂²)`: `m₁, m₂` are exactly the covariant mass parameters.

The surrounding physical modelling (spinor frames, the `Pin(3,1)` principal homogeneous space, field reparametrizations) is left as prose.

**Verification.** Full `lake build` is green (8135 jobs). The module is `sorry`-free and `axiom`-free — verified via the axiom checker on the two headline declarations `diracHamOp_conjTranspose` and `diracHamOp_sq` (only `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`, no `axiom`, no external hypotheses). Added a matching Wave 57 entry to `BookProof/STATUS.md` and prepended this Wave 57 section to `ARISTOTLE_SUMMARY.md` as requested. All work committed and pushed.

# Summary of changes for run 1efe807a-29c3-45d9-8f3a-93605308f572
Executed the next step of the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) as **Wave 56**.

**New work.** Formalized the finite-dimensional algebraic core of the `book.tex` chapter *"On the physical parity transformation and antiparticles"*. The chapter's central thesis — that at the quantum level all fields are real representations (self-adjoint operators), so CP and P coincide and the (generalized) parity transformation is order four, which forces the Lorentz double cover to be `Pin(3,1)` rather than `Pin(1,3)` — rests on a handful of concrete linear-algebra facts. New module `BookProof/ChapterParity.lean` (registered in `BookProof.lean`), reusing the concrete 4×4 Dirac model in `BookProof/ChapterA3.lean`, proves:
- `field_hermitian_decomp` (with `hermPart`/`antihermPart` and their `IsHermitian` proofs) — "any non-Hermitian field decomposes into a sum of two Hermitian fields": every square complex matrix `X = A + iB` with `A = ½(X+Xᴴ)`, `B = (2i)⁻¹(X−Xᴴ)` Hermitian;
- the Higgs (generalized) parity `iσ₂` is order four: `pauli2_sq` (`σ₂²=1`), `higgsParity_sq` (`(iσ₂)²=−1`), `higgsParity_pow_four`, `higgsParity_order_four`;
- the Majorana fermion parity `iγ⁰` is order four with `(iγ⁰)²=−1` (`mgamma0_sq`, `fermionParity_order_four`) versus the naive Dirac `(γ⁰)²=+1` (`dgamma0_sq`) — the `−1` being the invariant selecting `Pin(3,1)`;
- the eight `SU(3)` Gell-Mann matrices realize the ℤ₂ outer automorphism under complex conjugation with sign pattern `ε=(+,−,+,+,−,+,−,+)` (`gellMann_conj`), and the chapter's gluon parity sign `s^a=−ε^a` (`gellMann_parity_sign`).

The surrounding physical modelling is left as prose.

**Verification.** Full `lake build` is green (8134 jobs). The module is `sorry`-free and `axiom`-free — verified via the axiom checker on the headline declarations (only `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`, no `axiom`, no external hypotheses). Added a matching Wave 56 entry to `BookProof/STATUS.md` and prepended a Wave 56 section to `ARISTOTLE_SUMMARY.md` as requested. All work committed and pushed.

# Summary of changes — Wave 56
Executed the next step of the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) as **Wave 56**.

**New work.** Formalized the finite-dimensional algebraic core of the `book.tex` chapter **"On the physical parity transformation and antiparticles"** (line ~7522). The chapter's central thesis — that at the quantum level all fields are *real representations* (self-adjoint operators), so CP and P coincide and the (generalized) parity transformation is **order four**, which forces the Lorentz double cover to be `Pin(3,1)` rather than `Pin(1,3)` — rests on a handful of concrete linear-algebra facts. New module `BookProof/ChapterParity.lean` (registered in `BookProof.lean`), reusing the concrete `4×4` Dirac model `BookProof.ChapterA3.mgamma`/`dgamma`, proves:
- `field_hermitian_decomp` (with `hermPart`/`antihermPart` and their `IsHermitian` proofs) — *"any non-Hermitian field can always be decomposed into a sum of two Hermitian fields"*: every square complex matrix `X = A + iB` with `A = ½(X+Xᴴ)`, `B = (2i)⁻¹(X−Xᴴ)` Hermitian;
- the Higgs (generalized) parity `iσ₂` is order four: `pauli2_sq` (`σ₂²=1`), `higgsParity_sq` (`(iσ₂)²=−1`), `higgsParity_pow_four` (`(iσ₂)⁴=1`), `higgsParity_order_four`;
- the Majorana fermion parity `iγ⁰` is order four with `(iγ⁰)²=−1` (`mgamma0_sq`, `fermionParity_order_four`) versus the naive Dirac `(γ⁰)²=+1` (`dgamma0_sq`) — the `−1` is the invariant selecting `Pin(3,1)` over `Pin(1,3)`;
- the eight `SU(3)` Gell-Mann matrices realize the `ℤ₂` outer automorphism under complex conjugation with sign pattern `ε=(+,−,+,+,−,+,−,+)` (`gellMann_conj`), and the chapter's gluon parity sign is `s^a=−ε^a`, i.e. `s^{1,3,4,6,8}=−1`, `s^{2,5,7}=+1` (`gellMann_parity_sign`).

The surrounding physical modelling (canonical quantization of a real Hilbert space, the Standard-Model Lagrangian, path-integral measures) is left as prose.

**Verification.** Full `lake build` is green (8134 jobs). The module is `sorry`-free and `axiom`-free — verified via `lean_verify` on the headline declarations, which depend only on `propext`, `Classical.choice`, `Quot.sound` (no `native_decide`, no `axiom`, no `EXTERNAL` hypothesis). Added a Wave 56 entry to `BookProof/STATUS.md` and prepended this matching section to `ARISTOTLE_SUMMARY.md`. All work committed and pushed.

# Summary of changes for run 3bded584-b260-499f-8722-079a7793f95e
Executed the next step of the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) as **Wave 55**.

**New work.** Formalized the algebraic core of **Proposition 73** of `book.tex` §A.5 ("Application to the momentum of Majorana spinor fields"). The book proves the Majorana–Fourier transform `𝓕_M = S ∘ 𝓕_P^Θ` is unitary by reducing to the claim that the explicit 2×2 block "boost mixing" matrix `S = [[c, −s·A],[s·A, c]]` is orthogonal/unitary, where `c = √((E+m)/(2E))`, `s = √((E−m)/(2E))` are the boost half-angle coefficients (`E = √(q²+m²)`, `q = |p⃗|`, `m ≥ 0`) and `A = (n̂·γ⃗)γ⁰` is the Dirac spatial slash of the unit momentum direction. The development reuses the existing concrete 4×4 Dirac model in `BookProof/ChapterA3.lean`.

New module `BookProof/ChapterMajoranaFourier.lean` (registered in `BookProof.lean`) proves:
- the boost half-angle identities `c²+s²=1`, `c²−s²=m/E`, `2cs=q/E`;
- `γ⁰` is Hermitian and spatial `γⁱ` anti-Hermitian, with spatial Clifford relations `(γⁱ)²=−1`, `γⁱγʲ=−γʲγⁱ`;
- `A = n̸γ⁰` is a Hermitian involution (`Aᴴ=A`, `A²=1`), the unit-vector slash squaring to `−1`;
- the abstract block-unitarity lemma (Hermitian involution + `c²+s²=1` ⇒ `SᴴS=1`);
- the headline `majoranaFourier_boostBlock_unitary`: the concrete Prop-73 boost mixing matrix is unitary.

The surrounding analytic content (the integral operators and their L²-unitarity) is left as prose.

**Verification.** Full `lake build` is green (8133 jobs). The module is `sorry`-free and `axiom`-free — verified via `#print axioms majoranaFourier_boostBlock_unitary`, which depends only on `propext`, `Classical.choice`, `Quot.sound` (no `native_decide`, no `axiom`, no `EXTERNAL` hypothesis). Added a Wave 55 entry to `BookProof/STATUS.md` and prepended a matching section to `ARISTOTLE_SUMMARY.md` as requested. All work committed and pushed.

# Summary of changes — Wave 55
Continued the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) with **Wave 55**.

**New work.** Formalized the algebraic core of **Proposition 73** of `book.tex` §A.5 (*"Application to the momentum of Majorana spinor fields"*, line ~5900): the book proves the **Majorana–Fourier transform** `𝓕_M = S ∘ 𝓕_P^Θ` is unitary by reducing to the claim that the explicit `2×2` block "boost mixing" matrix `S = [[c, −s·A],[s·A, c]]` is orthogonal/unitary. Here `c = √((E+m)/(2E))`, `s = √((E−m)/(2E))` are the boost half-angle coefficients (`E = √(q²+m²)` the energy, `q = |p⃗|`, `m ≥ 0` the mass), and `A = (n̂·γ⃗) γ⁰` is the Dirac spatial slash of the unit momentum direction. The proof reuses the existing concrete `4×4` Dirac model `BookProof.ChapterA3.dgamma`.

New module `BookProof/ChapterMajoranaFourier.lean` (registered in `BookProof.lean`) proves, sorry-free and axiom-free (no `native_decide`):
- the boost half-angle identities `c² + s² = 1`, `c² − s² = m/E`, `2cs = q/E` (`boost_sq_add`, `boost_sq_sub`, `boost_two_mul`);
- Hermiticity of the Dirac matrices: `γ⁰` Hermitian, spatial `γⁱ` anti-Hermitian (`dgamma_conjTranspose`), plus the spatial Clifford relations `(γⁱ)² = −1` and `γⁱγʲ = −γʲγⁱ` (`dgamma_spatial_sq`, `dgamma_spatial_anticomm`);
- `A = n̸ γ⁰` is a Hermitian involution (`Aop_conjTranspose`, `Aop_sq`), where the unit-vector slash squares to `−1` (`nslash_sq`);
- the abstract block-unitarity lemma `boostBlock_unitary` (Hermitian involution + `c²+s²=1` ⇒ `Sᴴ S = 1`);
- the headline `majoranaFourier_boostBlock_unitary`: the concrete Prop-73 boost mixing matrix is unitary.

The surrounding analytic content (the integral operators `𝓕_P`, `𝓕_M` and their `L²`-unitarity) is left as prose.

**Verification.** Full `lake build` is green (8133 jobs); the module is confirmed `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, via `#print axioms majoranaFourier_boostBlock_unitary`). Added a Wave 55 entry to `BookProof/STATUS.md` and prepended this section to `ARISTOTLE_SUMMARY.md`. All work committed and pushed.

# Summary of changes for run e15221d3-4483-4244-8cef-69616962ffd8
Continued the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) with **Wave 54**.

**New work.** Formalized the section *"6. Free field parametrization for finite sample spaces and the spin-statistics theorem"* (`book.tex` line ~1816). The book parametrizes a finite sample space `ℤ₂` by a fermionic Fock space and, for the product `ℤ₂ × ℤ₂`, requires a graded tensor product so the two fermionic modes **anticommute** — the algebra underlying spin–statistics. Extending the single-mode ghost CAR of Wave 53, I built the two-mode fermionic Fock space `ℂ⁴ ≅ ℂ² ⊗ ℂ²` via the Jordan–Wigner realization `b₁ = a ⊗ I`, `b₂ = Z ⊗ a` (parity string `Z = diag(1,-1)`) as explicit 4×4 complex matrices.

New module `BookProof/ChapterSpinStatistics.lean` (registered in `BookProof.lean`) proves, sorry-free and axiom-free:
- explicit creation-operator matrices (`fermiCreate1_eq`, `fermiCreate2_eq`, each the conjugate-transpose adjoint of its annihilation operator);
- the diagonal CAR `{bᵢ, bᵢ†} = 1` (`fermi_CAR₁`, `fermi_CAR₂`);
- the off-diagonal CAR `{b₁, b₂†} = 0`, `{b₂, b₁†} = 0` (`fermi_CAR_cross`, `fermi_CAR_cross'`);
- fermionic statistics `{b₁, b₂} = 0`, `{b₁†, b₂†} = 0` (`fermiAnticomm_annih`, `fermiAnticomm_create`);
- per-mode nilpotency `bᵢ² = 0`, `bᵢ†² = 0` (Pauli exclusion);
- number operators `Nᵢ = bᵢ† bᵢ` with Hermiticity, idempotence, commutativity `N₁N₂ = N₂N₁`, and the total number `N₁ + N₂ = diag(0,1,1,2)`.

The representation-theoretic spin–statistics claim itself is left as prose.

**Verification.** Full `lake build` is green (8132 jobs); the module is confirmed `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, checked via the axiom tracer). Added a Wave 54 entry to `BookProof/STATUS.md` and prepended a matching section to `ARISTOTLE_SUMMARY.md` as requested. All work committed and pushed.

# Summary of changes — Wave 54
Executed the next step of the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) as **Wave 54**.

**New work.** Formalized the section *"6. Free field parametrization for finite sample spaces and the spin-statistics theorem"* (`book.tex` line ~1816). The book parametrizes a finite sample space `ℤ₂` by a fermionic Fock space and, for the product `ℤ₂ × ℤ₂`, requires a graded tensor product so that the two fermionic modes **anticommute** (rather than producing spurious products of creation operators) — the algebraic content behind the spin–statistics correspondence. Extending the single-mode ghost CAR of Wave 53, this builds the **two-mode** fermionic Fock space `ℂ⁴ ≅ ℂ² ⊗ ℂ²` via the Jordan–Wigner realization `b₁ = a ⊗ I`, `b₂ = Z ⊗ a` (parity string `Z = diag(1,-1)`), realized as explicit `4×4` complex matrices.

**New module** `BookProof/ChapterSpinStatistics.lean` (registered in `BookProof.lean`) proves:
- `fermiCreate1_eq`, `fermiCreate2_eq` — explicit matrix form of the creation operators `b₁†`, `b₂†` (each the conjugate-transpose adjoint of its annihilation operator);
- `fermi_CAR₁`, `fermi_CAR₂` — the diagonal CAR `{bᵢ, bᵢ†} = 1`;
- `fermi_CAR_cross`, `fermi_CAR_cross'` — the off-diagonal CAR `{b₁, b₂†} = 0`, `{b₂, b₁†} = 0` (distinct modes canonically anticommute);
- `fermiAnticomm_annih`, `fermiAnticomm_create` — the fermionic statistics `{b₁, b₂} = 0`, `{b₁†, b₂†} = 0` (so `b₁ b₂ = − b₂ b₁`);
- `fermiAnnih₁_sq`, `fermiAnnih₂_sq`, `fermiCreate₁_sq`, `fermiCreate₂_sq` — per-mode nilpotency `bᵢ² = 0`, `bᵢ†² = 0` (Pauli exclusion);
- `fermiNumber₁_eq`, `fermiNumber₂_eq` — the number operators `Nᵢ = bᵢ† bᵢ` (`diag(0,0,1,1)`, `diag(0,1,0,1)`), with `fermiNumber₁_hermitian`/`fermiNumber₂_hermitian` and `fermiNumber₁_idem`/`fermiNumber₂_idem` (Hermitian projections, eigenvalues `0,1`), `fermiNumber_commute` (`N₁ N₂ = N₂ N₁`), and `fermiTotalNumber_eq` (`N = N₁ + N₂ = diag(0,1,1,2)`).

The representation-theoretic spin–statistics claim (fermionic vs. bosonic representability of symmetry transformations) is left as prose.

**Verification.** Full `lake build` is green (8132 jobs); the module is confirmed `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified via `lean_verify`). Added a Wave 54 entry to `BookProof/STATUS.md` and prepended this section to `ARISTOTLE_SUMMARY.md`.

---

# Summary of changes for run 398e31ba-db94-4a74-97be-2d20897b690b
Executed the next step of the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) as **Wave 53**.

**New work.** Formalized the fermionic **BRST ghost-field algebra** of the section *"Free field parametrization in Navier–Stokes equations"* (`book.tex` line ~4134), where the incompressibility (divergence) constraint of Navier–Stokes is implemented à la BRST through a single fermionic ghost `ψ`. Using the explicit realization the book writes down (`ψ†{a}(…,j)=a(…,1)δ_{j0}`, `ψ{a}(…,j)=a(…,0)δ_{j1}`), realized on the two-dimensional occupation space `ℂ²` as the 2×2 matrices `ψ = !![0,0;1,0]`, `ψ† = ψᴴ = !![0,1;0,0]`.

**New module** `BookProof/ChapterNavierStokes.lean` (registered in `BookProof.lean`) proves:
- `ghostCreate_eq`, `ghostCreate_eq_conjTranspose` — explicit form of `ψ†` and that it is the conjugate-transpose (adjoint) of `ψ`;
- `ghost_CAR` — the canonical anticommutation relation `ψψ† + ψ†ψ = 1` (the book's `{ψ,ψ†}=1`);
- `ghostAnnih_sq`, `ghostCreate_sq`, `ghostAnticomm_annih`, `ghostAnticomm_create` — nilpotency `ψ²=0`, `ψ†²=0` (fermionic Pauli exclusion) and the paired anticommutators;
- `ghostNumber_eq`, `ghostNumber_hermitian`, `ghostNumber_idem` — the number operator `N = ψ†ψ = !![1,0;0,0]` is Hermitian and idempotent (occupation eigenvalues 0, 1);
- `ghost_annih_create_eq`, `ghostNumber_resolution` — `ψψ† = !![0,0;0,1]` and the identity resolution `N + ψψ† = 1`.

The surrounding field-theoretic construction (full graded Lie superalgebra, essential self-adjointness of the polynomial Hamiltonian, existence/uniqueness) is physical modelling left as prose.

**Verification.** Full `lake build` is green (8131 jobs); the module is confirmed `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified on the headline results). 

**Docs.** Added a Wave 53 entry to `BookProof/STATUS.md` and prepended a matching Wave 53 section to `ARISTOTLE_SUMMARY.md` (as requested). All work is committed and pushed.

# Summary of changes — Wave 53: Book "Free field parametrization … Navier–Stokes", *Navier–Stokes* section: the BRST ghost-field CAR algebra `{ψ, ψ†} = 1` (`ChapterNavierStokes`)

Continued the standing roadmap directive (mine the next self-contained
mathematical content from `book.tex`) with a new wave (Wave 53), then updated the
status docs.

**What I did.** Formalized the fermionic **ghost field** of the section *"Free
field parametrization in Navier–Stokes equations"* (`book.tex` line ~4134). There
the divergence (incompressibility) constraint of the Navier–Stokes equations is
implemented à la BRST through a single fermionic ghost `ψ` (with BRST charge
`Ω = ∫ u_{j,j} ψ†`), governed by the canonical anticommutation relation
`{ψ, ψ†} = ψψ† + ψ†ψ = 1`, using the explicit realization the book writes down:
`ψ†{a}(…,j) = a(…,1) δ_{j0}` and `ψ{a}(…,j) = a(…,0) δ_{j1}`. On the
two-dimensional occupation space `ℂ²` (`j = 0`: no ghost, `j = 1`: one ghost)
these are the `2×2` matrices `ψ = !![0,0;1,0]` and `ψ† = ψᴴ = !![0,1;0,0]`.

**New module** `BookProof/ChapterNavierStokes.lean` (registered in
`BookProof.lean`):
- `ghostCreate_eq` — explicit matrix form of `ψ†`;
- `ghostCreate_eq_conjTranspose` — `ψ†` is the conjugate-transpose (adjoint) of
  `ψ`, so the CAR pair is a genuine operator/adjoint pair;
- `ghost_CAR` — the canonical anticommutation relation `ψψ† + ψ†ψ = 1`
  (the book's `{ψ, ψ†} = 1`);
- `ghostAnnih_sq` / `ghostCreate_sq` — nilpotency `ψ² = 0`, `ψ†² = 0` (fermionic
  Pauli exclusion), with the paired `{ψ,ψ} = 0`, `{ψ†,ψ†} = 0`;
- `ghostNumber_eq`, `ghostNumber_hermitian`, `ghostNumber_idem` — the number
  operator `N = ψ†ψ = !![1,0;0,0]` is Hermitian and idempotent (eigenvalues
  `0, 1`, the fermionic occupation numbers);
- `ghost_annih_create_eq`, `ghostNumber_resolution` — `ψψ† = !![0,0;0,1]` and the
  resolution of the identity `N + ψψ† = 1` into the two occupation sectors.

The surrounding field-theoretic construction (the full graded Lie superalgebra,
essential self-adjointness of the polynomial Navier–Stokes Hamiltonian, and the
existence/uniqueness claim) is physical modelling left as prose.

**Verification.** Full `lake build` is green (8131 jobs). The module is confirmed
`sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`,
verified via `lean_verify` on the headline results). Added a Wave 53 entry to
`BookProof/STATUS.md` and prepended this matching section to
`ARISTOTLE_SUMMARY.md` (as requested). All work is committed and pushed.

---

# Summary of changes for run dbd9874a-904b-44b8-89d1-9d9a5d571912
Continued the standing roadmap directive (mine the next self-contained mathematical content from `book.tex`) with a new wave (Wave 52).

**What I did.** Formalized the section *"Holomorphic fields"* (`book.tex` line ~4105), where the field-theory Hamiltonian is *defined by the Cauchy–Riemann equations*. The book states the distributional (Weyl-lemma) version — a locally-integrable function whose Cauchy–Riemann equations hold weakly is a.e. equal to an analytic function — which relies on elliptic regularity not available in the library. I formalized the classical (strong-derivative) core it rests on: a complex function that is real-differentiable on an open domain and satisfies the Cauchy–Riemann equations there is complex analytic (holomorphic), so it is its own analytic representative.

**New module** `BookProof/ChapterHolomorphic.lean` (registered in `BookProof.lean`), over an open `s ⊆ ℂ`:
- `cauchyRiemann_analyticOn` — operator form (`∂f/∂y = i · ∂f/∂x`) ⇒ analytic;
- `cauchyRiemann_partial_analyticOn` — classical partial-derivative form (`u_x = v_y`, `u_y = -v_x`, with `f = u + i v`) ⇒ analytic;
- `analyticOn_cauchyRiemann` — the converse (holomorphic ⇒ Cauchy–Riemann);
- `cauchyRiemann_iff_analyticOn` — the resulting characterization;
- `cauchyRiemann_contDiffOn` — the smoothness payoff (`C^∞`).

The docstring is explicit that the classical version is formalized (not the stronger distributional Weyl-lemma statement).

**Verification.** Full `lake build` is green (8130 jobs). The module is confirmed `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`), verified on the headline results. Added a Wave 52 entry to `BookProof/STATUS.md` and prepended a matching section to `ARISTOTLE_SUMMARY.md` (as explicitly requested in the new prompt). All work is committed and pushed.

# Summary of changes — Wave 52: Book "Free field parametrization … Navier–Stokes", *Holomorphic fields*: Cauchy–Riemann ⇒ holomorphic (`ChapterHolomorphic`)

Executed the next `FORMALIZATION_ROADMAP.md` step (the standing directive to mine
the next self-contained mathematical content from `book.tex`) and updated the
status docs.

**New work (Wave 52).** Formalized the self-contained mathematical claim of the
section *"Holomorphic fields"* (`book.tex` line ~4105), where the field theory's
Hamiltonian is *defined by the Cauchy–Riemann equations*. The book states the
distributional (Weyl-lemma) version — a locally-integrable function whose
Cauchy–Riemann equations hold weakly is a.e. equal to an analytic function; that
elliptic-regularity statement is not in Mathlib. This pass formalizes the
classical (strong-derivative) core it rests on: a complex function that is
real-differentiable on an open domain and satisfies the Cauchy–Riemann equations
there is complex analytic (holomorphic), hence its own analytic representative.

New module `BookProof/ChapterHolomorphic.lean` (registered in `BookProof.lean`),
all `sorry`-free and `axiom`-free. Over an open `s ⊆ ℂ`:
- `cauchyRiemann_analyticOn` — operator form (`fderiv ℝ f z I = I • fderiv ℝ f z 1`,
  i.e. `∂f/∂y = i · ∂f/∂x`) ⇒ `AnalyticOn ℂ f s`;
- `cauchyRiemann_partial_analyticOn` — the classical partial-derivative form
  `u_x = v_y`, `u_y = -v_x` (writing `f = u + i v`) ⇒ analyticity;
- `analyticOn_cauchyRiemann` — the converse (holomorphic ⇒ Cauchy–Riemann);
- `cauchyRiemann_iff_analyticOn` — the resulting characterization;
- `cauchyRiemann_contDiffOn` — the smoothness payoff (`C^∞`).

**Verification.** Full `lake build` is green (8130 jobs); the module is confirmed
`sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`,
verified via `lean_verify` on the headline results). Added a Wave 52 entry to
`BookProof/STATUS.md` and prepended this section to `ARISTOTLE_SUMMARY.md`. All
work is committed and pushed.

# Summary of changes for run 79d62767-170e-4f05-86e1-15c971f8ee84
Executed the next `FORMALIZATION_ROADMAP.md` step (mine the next self-contained mathematical content from `book.tex`) and updated the status docs.

**New work (Wave 51).** Formalized the self-contained, finite-dimensional core of the `book.tex` section *"3. Any conditional probability measure in a standard measure space is parametrized by a unitary operator"* (Chapter *"Wave-function parametrization of a probability measure"*, book line ~1392): the claim that a joint probability density `p(x,y)` can be written as `|𝒰(y,x,0)|²` for a unitary `𝒰` built by Gram–Schmidt with a chosen column equal to the wave-function `Ψ` (`|Ψ|²=p`), together with its converse. The abstract L²/Hilbert-basis form already existed (`ChapterB.unit_vector_extends`); this pass adds the concrete matrix form.

New module `BookProof/ChapterJointUnitary.lean` (registered in `BookProof.lean`), all `sorry`-free and `axiom`-free. Over a finite index type:
- `exists_unitary_column` — Gram–Schmidt crux: every unit vector `v` (`∑ᵢ ‖v i‖² = 1`) is the `i₀`-th column of some unitary matrix (via extension to an orthonormal basis of `EuclideanSpace ℂ ι`);
- `exists_unitary_of_prob` — every finite probability distribution `p` is the squared modulus of a column of a unitary matrix (using `v i = √(p i)`);
- `exists_unitary_joint` — the book's two-space form: every joint distribution `p(x,y)` on a finite `X × Y` is `|U|²` along a column of a unitary matrix indexed by `X × Y`;
- `sqAbs_isProb_of_frobenius_one` + `frobenius_eq_trace` — the converse: any matrix `B` with `∑_{i,j} ‖B i j‖² = 1` (i.e. `tr(Bᴴ B) = 1`) makes `(i,j) ↦ ‖B i j‖²` a genuine probability distribution.

**Verification.** Full `lake build` is green (8129 jobs); the module is confirmed `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified on the headlines). Added a Wave 51 entry to `BookProof/STATUS.md` and prepended a matching section to `ARISTOTLE_SUMMARY.md` as requested. All work is committed and pushed.

# Summary of changes — Wave 51: Book §3 "Any conditional probability measure is parametrized by a unitary operator": the finite-dimensional matrix version (`ChapterJointUnitary`)

Executed the next `FORMALIZATION_ROADMAP.md` step (mine the next self-contained
mathematical content from `book.tex`) and updated the status docs.

**Starting point.** The roadmap queue N1–N14 and mining Waves 46–50 were
complete; `BookProof` was `sorry`/`axiom`-free and the build green. The
standing directive is to mine the next self-contained content from `book.tex`.

**What I did.** Formalized the self-contained, finite-dimensional core of the
`book.tex` section *"3. Any conditional probability measure in a standard measure
space is parametrized by a unitary operator"* (Chapter *"Wave-function
parametrization of a probability measure"*, book line ~1392): the book's claim
that a joint probability density `p(x,y)` can be written as `p(x,y)=|𝒰(y,x,0)|²`
for a unitary `𝒰` built "through the Gram–Schmidt process" so that a chosen column
of `𝒰` reproduces the wave-function `Ψ` with `|Ψ|²=p`, together with its converse.
The abstract `L²`/Hilbert-basis form already exists (`ChapterB.unit_vector_extends`);
this pass adds the concrete matrix form of the Gram–Schmidt construction.

New module `BookProof/ChapterJointUnitary.lean` (registered in `BookProof.lean`),
all `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, verified via `lean_verify` on the headlines); full `lake build`
green (8129 jobs). Over a finite index type:
- `exists_unitary_column` — the Gram–Schmidt crux: every unit vector `v`
  (`∑ᵢ ‖v i‖² = 1`) is the `i₀`-th column of some unitary matrix (extend `v` to
  an orthonormal basis of `EuclideanSpace ℂ ι`; its coordinate matrix is unitary
  with `i₀`-column `v`);
- `exists_unitary_of_prob` — every finite probability distribution `p` is the
  squared modulus `|·|²` of a column of a unitary matrix (via `v i = √(p i)`);
- `exists_unitary_joint` — the book's exact two-space statement: every joint
  distribution `p(x,y)` on a finite `X × Y` is `|U|²` along a column of a unitary
  matrix indexed by `X × Y`;
- `sqAbs_isProb_of_frobenius_one` + `frobenius_eq_trace` — the converse: any
  matrix `B` with `∑_{i,j} ‖B i j‖² = 1` (i.e. `tr(Bᴴ B) = 1`) makes
  `(i,j) ↦ ‖B i j‖²` a genuine probability distribution.

**Verification.** Full `lake build` is green (8129 jobs); the module is
`sorry`-free and `axiom`-free. Updated `BookProof/STATUS.md` with a Wave 51
entry and prepended this section to `ARISTOTLE_SUMMARY.md`. All work committed
and pushed.

# Summary of changes for run 323a669d-1c34-4af8-8f56-28e7cdf77c19
Executed the next `FORMALIZATION_ROADMAP.md` step (mine the next self-contained mathematical content from `book.tex`) and updated the status docs.

**New work (Wave 50).** Formalized the self-contained claim of the `book.tex` section *"11. Conditions for the classical limit of Quantum Mechanics"* (Chapter *"Wave-function parametrization of a probability measure"*): that step, polynomial, and smooth functions are dense in the `L²` measure, and that any bounded function on a compact domain can be `L²`-approximated by such calculable functions.

New module `BookProof/ChapterClassicalLimit.lean` (registered in `BookProof.lean`), all `sorry`-free and `axiom`-free. Over a compact `s ⊆ ℝ` with any finite, weakly-regular Borel measure `μ`:
- `simpleFunc_dense_L2` — step / simple functions dense in `L²`;
- `continuousMap_denseRange_L2` — continuous functions dense in `L²`;
- `polynomialFunctions_val_denseRange` — Stone–Weierstrass: polynomials dense in `C(s, ℝ)`;
- `polynomial_denseRange_L2` — polynomial (hence also smooth) functions dense in `L²`, by composition;
- headline `exists_polynomial_approx_L2` — for every `F ∈ L²(μ)` and `ε > 0` there is a polynomial `q` with `‖q|ₛ − F‖₂ < ε`.

**Verification.** Full `lake build` is green (8128 jobs); the module is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed on the headline). Updated `BookProof/STATUS.md` with a Wave 50 entry and prepended a matching section to `ARISTOTLE_SUMMARY.md`. All work is committed and pushed.

# Summary of changes — Wave 50: Book "Conditions for the classical limit of Quantum Mechanics": calculable functions are dense in `L²` (`ChapterClassicalLimit`)

Executed the next `FORMALIZATION_ROADMAP.md` step (mine the next self-contained
mathematical content from `book.tex`) and updated the status docs.

**Starting point.** The roadmap queue N1–N14 and the recent mining Waves 46–49
were complete; `BookProof` was `sorry`/`axiom`-free and the build was green.
The roadmap's standing "Beyond N13/N14" directive is to mine the next
self-contained content from `book.tex`.

**What I did.** Formalized the self-contained claim of the `book.tex` section
*"11. Conditions for the classical limit of Quantum Mechanics"* (Chapter
*"Wave-function parametrization of a probability measure"*, line ~2081):
*"step, polynomial or smooth functions are dense in the `L²` measure"*, and that
any bounded function on a compact domain can be `L²`-approximated by such
calculable functions.

New module `BookProof/ChapterClassicalLimit.lean` (registered in
`BookProof.lean`), all `sorry`-free and `axiom`-free. Working over a compact
`s ⊆ ℝ` with any finite, weakly-regular Borel measure `μ`:
- `simpleFunc_dense_L2` (step / simple functions dense in `L²`);
- `continuousMap_denseRange_L2` (continuous functions dense in `L²`);
- `polynomialFunctions_val_denseRange` (Stone–Weierstrass: polynomials dense in
  `C(s, ℝ)`);
- `polynomial_denseRange_L2` (polynomial — hence also smooth — functions dense in
  `L²`, by composition);
- headline `exists_polynomial_approx_L2` (for every `F ∈ L²(μ)` and `ε > 0` a
  polynomial `q` with `‖q|ₛ − F‖₂ < ε`).

**Verification.** Full `lake build` is green (8128 jobs); the module is
`sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`,
confirmed via `lean_verify` on the headline). All work is committed and pushed.

**Docs updated.** Added a Wave 50 entry to `BookProof/STATUS.md` and prepended
this section to `ARISTOTLE_SUMMARY.md`.

# Summary of changes for run b81e6f04-0771-4a23-a49a-7991144e3542
Executed the next `FORMALIZATION_ROADMAP.md` step and updated the summary docs.

**Next step done (Wave 49).** Following the roadmap's standing directive to mine the next self-contained mathematical content from `book.tex`, I formalized the linear-algebra core of the section *"Time translation is a stochastic process if and only if it is deterministic"* (Chapter *"Reconstructing the classical trajectory of any isolated quantum system"*). This is the book's claim that a Wigner symmetry `U` induces a well-defined group action on the post-collapse probability distributions **iff** `U` is *deterministic* (each column has at most one nonzero entry).

New module `BookProof/ChapterReconstruct.lean` (registered in `BookProof.lean`), all `sorry`-free and `axiom`-free:
- `IsDeterministicCol`/`IsDeterministic` and the off-diagonal Born sum `offDiag`;
- `offDiag_eq` (the full-bilinear-product-minus-diagonal identity);
- `offDiag_of_isDeterministicCol` (forward) and `isDeterministicCol_of_offDiag` (backward, via the polarization witnesses `Ψ = δ_{·m} + zδ_{·l}`, `z ∈ {1, i}`, the rigorous form of the book's real witness);
- headlines `offDiag_eq_zero_iff` (per column) and `offDiag_eq_zero_iff_isDeterministic` (global);
- `offDiag_unit_iff` (the book's exact unit-state form).

**Verification.** Full `lake build` is green (8127 jobs); the module is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed on the headline). Only cosmetic long-line style warnings remain, consistent with the rest of the library.

**Docs updated.** Added a Wave 49 entry to `BookProof/STATUS.md` and prepended a matching section to `ARISTOTLE_SUMMARY.md`. All work is committed and pushed.

# Summary of changes — Wave 49: Book "Reconstructing the classical trajectory": a symmetry acts on probability distributions iff it is deterministic (`ChapterReconstruct`)

Executed the next `FORMALIZATION_ROADMAP.md` step and updated the status docs.

**Starting point.** The roadmap queue N1–N14 and the recent mining Waves 46–48
were complete; `BookProof` was `sorry`/`axiom`-free and the build was green. The
roadmap's standing "Beyond N13/N14" note directs mining the next self-contained
content from `book.tex`.

**What I did.** Formalized the self-contained linear-algebra core of the
`book.tex` section *"Time translation is a stochastic process if and only if it
is deterministic"* (Chapter *"Reconstructing the classical trajectory of any
isolated quantum system"*, line ~2613) in a new module
`BookProof/ChapterReconstruct.lean` (registered in `BookProof.lean`). The book's
main result there is that a Wigner symmetry `U` induces a well-defined group
action on the (post-collapse) probability distributions **iff** `U` is
*deterministic* — each column of `U` has at most one nonzero entry. Deliverables
(all proved, no `sorry`/`axiom`/`EXTERNAL`):
- `IsDeterministicCol`/`IsDeterministic` definitions and the `offDiag`
  off-diagonal Born sum `S_a(Ψ) = ∑_{k≠b} conj(U k a)·Ψ k·conj(Ψ b)·U b a`;
- `offDiag_eq`: the full-bilinear-product-minus-diagonal identity for `S_a`;
- `offDiag_of_isDeterministicCol` (forward direction) and
  `isDeterministicCol_of_offDiag` (backward direction via the polarization
  witnesses `Ψ = δ_{·m} + zδ_{·l}`, `z ∈ {1, i}` — the rigorous form of the
  book's real witness);
- headlines `offDiag_eq_zero_iff` (per column) and
  `offDiag_eq_zero_iff_isDeterministic` (global): the Born-rule map is a
  well-defined action on distributions iff `U` is deterministic;
- `offDiag_unit_iff`: the book's exact unit-state (pure-density-matrix) form.
No unitarity hypothesis is needed for this algebraic equivalence.

**Verification.** Full `lake build` is green (8127 jobs); the module is
`sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`,
confirmed via the theorem checker on `offDiag_eq_zero_iff_isDeterministic`). Only
cosmetic long-line style warnings remain (consistent with the rest of the
library).

**Documentation.** Added a Wave 49 entry to `BookProof/STATUS.md` and prepended
this section to `ARISTOTLE_SUMMARY.md`. All work is committed and pushed.

---

# Summary of changes for run f47bb112-1319-470e-93eb-8516db60498c
Executed the next `FORMALIZATION_ROADMAP.md` step and updated `ARISTOTLE_SUMMARY.md`.

**Starting point.** The roadmap queue N1–N14, the Wave-46 Gleason sanity check, and the Wave-47 Entropy `n!/nⁿ` nugget were already complete; `BookProof` was `sorry`/`axiom`-free and the build was green. The roadmap's standing "Beyond N13/N14" note directs mining the next self-contained content from `book.tex`.

**What I did.** Formalized the `book.tex` sections *"Euler's formula for a phase-space with 4 states"* and *"Euler's formula for a generic phase-space"* (Chapter *"Wave-function collapse versus Euler's formula"*) in a new module `BookProof/ChapterE2.lean` (registered in `BookProof.lean`). The existing `BookProof/ChapterE.lean` had only covered the 2-state clock; this pass formalizes the `n`-state / countable stick-breaking Born parametrization `P(1)=c₁²`, `P(2)=(s₁c₂)²`, `P(3)=(s₁s₂c₃)²`, …. Deliverables (all proved, no `sorry`/`axiom`/`EXTERNAL`):
- `stick`/`remainder`/`bornProb` definitions plus basic identities (`stick_eq`, `remainder_succ`, `remainder_zero`, `stick_nonneg`, `remainder_nonneg`, `remainder_le_one`);
- `sum_stick_add_remainder`: the telescoping normalization `(∑_{n<N} stick θ n) + remainder θ N = 1`;
- `bornProb_nonneg` + `bornProb_sum_eq_one`: the `n`-state Born family is a genuine probability distribution;
- `cos_sq_surjective`: conditional probabilities `cos²(θ)` are arbitrary over `[0,1]`;
- headline `exists_angles_realize`: *every* probability distribution on `n` states is realized by the Born rule of some wave-function (the book's claim), via the stick-breaking construction `cos²θ_k = q_k / R_k`.

**Verification.** Full `lake build` is green (8126 jobs); the module is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via the theorem checker on the two headlines). The heavy headline proof carries a local `set_option maxHeartbeats 1000000` so it elaborates under the default build limit. Only cosmetic style-linter warnings remain.

**Documentation.** Added a Wave 48 entry to `BookProof/STATUS.md` and prepended a matching section to `ARISTOTLE_SUMMARY.md`. The out-of-scope `RiemannProof/RcpEuler.lean` sorries are unchanged. All work is committed and pushed.

# Summary of changes — Book "Wave-function collapse versus Euler's formula": the generic-phase-space (stick-breaking) Born parametrization (`ChapterE2`)

Executed the next `FORMALIZATION_ROADMAP.md` step and updated `ARISTOTLE_SUMMARY.md` as requested.

**Starting point.** The roadmap queue N1–N14 (both flagship packages), the
Wave-46 Gleason sanity check, and the Wave-47 Entropy `n!/nⁿ` nugget were already
complete, `BookProof` was `sorry`/`axiom`-free, and the build was green.  The
roadmap's standing "Beyond N13/N14" note flags that `book.tex` still has
unformalized chapters to mine, so this pass formalizes the next self-contained
mathematical content.

**What I did.** Formalized the `book.tex` sections *"Euler's formula for a
phase-space with 4 states"* and *"Euler's formula for a generic phase-space"*
(Chapter *"Wave-function collapse versus Euler's formula"*, line ~3565) in a new
module `BookProof/ChapterE2.lean` (registered in `BookProof.lean`).  The existing
`BookProof/ChapterE.lean` had only covered the 2-state clock (E.1–E.4); this pass
formalizes the `n`-state / countable generalization.  The book parametrizes a
real normalized wave-function by Euler angles via `vₙ = cos(θₙ) lₙ + sin(θₙ) vₙ₊₁`,
yielding the *stick-breaking* Born probabilities `P(1)=c₁²`, `P(2)=(s₁c₂)²`,
`P(3)=(s₁s₂c₃)²`, ….  Deliverables (all proved):
- `stick`, `remainder`, `bornProb` definitions and basic identities;
- `sum_stick_add_remainder`: the telescoping normalization
  `(∑_{n<N} stick θ n) + remainder θ N = 1`;
- `bornProb_nonneg` and `bornProb_sum_eq_one`: the `n`-state Born family is a
  genuine probability distribution;
- `cos_sq_surjective`: the conditional probabilities `cos²(θ)` are arbitrary over
  `[0,1]`;
- headline `exists_angles_realize`: *every* probability distribution on `n`
  states is realized by the Born rule of some wave-function (the book's claim
  "any probability distribution can be reproduced by the Born rule for some
  wave-function"), via the stick-breaking construction `cos²θ_k = q_k / R_k`.

**Verification.** The full `lake build` is green (8126 jobs); the module is
`sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`,
confirmed via `lean_verify` on the two headlines); no `EXTERNAL` hypothesis and
no `axiom`.  (The headline proof carries a local `set_option maxHeartbeats
1000000` so it elaborates under the default build limit.)

**Documentation.** Added a Wave 48 entry to `BookProof/STATUS.md` and prepended
this section to `ARISTOTLE_SUMMARY.md`.  The out-of-scope
`RiemannProof/RcpEuler.lean` sorries are unchanged.  All work is committed and
pushed.

# Summary of changes for run 891ff3a5-ce81-4c36-9d74-8af81ffb80c1
Executed the next `FORMALIZATION_ROADMAP.md` step and updated `ARISTOTLE_SUMMARY.md` as requested.

**Starting point.** I confirmed the roadmap queue N1–N14 (both flagship packages, Hashimoto SIRK and QFM) plus the earlier Gleason sanity check were already complete, `BookProof` was `sorry`/`axiom`-free, and the build was green. The roadmap's standing "Beyond N13/N14" note flags that `book.tex` still has unformalized chapters to mine, so this pass formalizes the next self-contained numbered claim.

**What I did.** Formalized the mathematical content of the `book.tex` chapter *"Entropy and an irreversible deterministic time-evolution coexist"* (§"Irreversible deterministic time-evolution") in a new module `BookProof/ChapterEntropy.lean` (registered in `BookProof.lean`). The chapter partitions the rescaled joint sample square into `n²` cells and asserts that the probability a uniformly random discrete self-map of the `n` index cells is invertible (a bijection) is `n!/nⁿ ~ √(2πn) e^{-n}`, which tends to `0` — its arrow-of-time mechanism. Deliverables (all proved):
- `card_selfMaps` / `card_bijections`: an `n`-element index set has `nⁿ` self-maps and `n!` bijections;
- `invertibleProb` with `invertibleProb_eq` (`= (n! : ℝ)/nⁿ`), and `invertibleProb_nonneg` / `invertibleProb_le_one` (a genuine probability in `[0,1]`);
- headline `invertibleProb_tendsto_zero` (it tends to `0`);
- `invertibleProb_isEquivalent_stirling` (the book's Stirling asymptotic `n!/nⁿ ~ √(2πn) e^{-n}`);
- `exists_injective_not_surjective` (successor map on `ℕ`: injective "non-singular" yet not surjective "not invertible").

**Verification.** The full `lake build` is green (8125 jobs); the module is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via the theorem checker); no `EXTERNAL` hypothesis and no `axiom`.

**Documentation.** Added a Wave 47 entry to `BookProof/STATUS.md` and prepended a new section to `ARISTOTLE_SUMMARY.md`. The out-of-scope `RiemannProof/RcpEuler.lean` sorries are unchanged. All work is committed and pushed.

# Summary of changes — Book "Entropy and irreversible time-evolution": the invertibility probability `n!/nⁿ` (`ChapterEntropy`)

Executed the next `FORMALIZATION_ROADMAP.md` step and updated this file as requested.

**Context.** The whole roadmap queue N1–N14 (both flagship packages, Hashimoto SIRK and QFM) plus the Wave-46 Gleason sanity check were already complete and `lake build` was green. The roadmap's standing "Beyond N13/N14" note flags that `book.tex` still has unformalized chapters to mine. This pass formalizes the next self-contained numbered claim: the chapter *"Entropy and an irreversible deterministic time-evolution coexist"* (`book.tex` line ~9474, §"Irreversible deterministic time-evolution").

**New module `BookProof/ChapterEntropy.lean`** (registered in `BookProof.lean`), all `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified via `lean_verify` on the headlines); full `lake build` green (8125 jobs). No `EXTERNAL` hypothesis, no `axiom`.

The book partitions the rescaled joint sample square `[0,1]×[0,1]` into `n²` cells and states that the probability that a uniformly random discrete self-map of the `n` index cells is invertible (a bijection) is `n!/nⁿ ~ √(2πn) e^{-n}`, which tends to `0` — so a randomly sampled time-evolution is almost surely non-invertible (irreversible), the book's arrow-of-time mechanism. Deliverables:
- `card_selfMaps` / `card_bijections`: an `n`-element index set has `nⁿ` self-maps and `n!` bijections.
- `invertibleProb` (ratio of the two counts) with `invertibleProb_eq` (`= (n! : ℝ)/nⁿ`), and `invertibleProb_nonneg` / `invertibleProb_le_one` (a genuine probability in `[0,1]`, via `Nat.factorial_le_pow`).
- headline `invertibleProb_tendsto_zero` (it tends to `0`, from `tendsto_factorial_div_pow_self_atTop`).
- `invertibleProb_isEquivalent_stirling` (the book's Stirling asymptotic `n!/nⁿ ~ √(2πn) e^{-n}`, from `Stirling.factorial_isEquivalent_stirling` divided by `nⁿ`).
- `exists_injective_not_surjective` (successor map on `ℕ`: injective "non-singular" yet not surjective "not invertible" — a concrete irreversible-dynamics witness).

**Documentation.** Added a Wave 47 entry to `BookProof/STATUS.md` and this section to `ARISTOTLE_SUMMARY.md`. The out-of-scope `RiemannProof/RcpEuler.lean` sorries are unchanged. All work is committed and pushed.

# Summary of changes for run 0a559911-9e42-47a4-8bc3-a4fc460b560f
Executed the next `FORMALIZATION_ROADMAP.md` step and updated `ARISTOTLE_SUMMARY.md` as requested.

**Starting point.** I first confirmed the current state: the full roadmap queue N1–N14 (including both flagship packages — Hashimoto SIRK and QFM) was already complete, and `lake build` was green. I verified there were no remaining open queue items and that the previously-pending §0 S7 hygiene item (the `../unfer` cross-reference docstrings on `born_conditioning` and `prodEquiv` in `ChapterU.lean`) was in fact already present, so no edit was needed there.

**What I did — the next open item.** The remaining previously-unimplemented deliverable explicitly flagged in the roadmap (Chapter B remark, "worth adding as a sanity check") is the concrete 2-dimensional real **Gleason contrast** from `book.tex` §4. I formalized it as a new module `BookProof/ChapterB4.lean` (registered in `BookProof.lean`), `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified with the theorem checker on the headlines). The full project builds cleanly (8124 jobs), with no `EXTERNAL` hypothesis and no `axiom`.

Fixing the two non-commuting real projections `P₁ = [[1,0],[0,0]]` and `P₂ = ½[[1,1],[1,1]]`, with a pure state defined as a rank-one projector `v vᵀ` (unit `v`) and a density matrix defined as Hermitian, positive-semidefinite, unit-trace:
- `pure_state_satisfies_P1` / `pure_state_satisfies_P2`: a pure state realizes each Born constraint `tr(ρ P) = ½` individually;
- headline `no_pure_state_satisfies_both`: no pure state realizes both `tr(ρ P₁) = ½` and `tr(ρ P₂) = ½` at once;
- `mixed_state_satisfies_both`, `mixed_state_isDensityMatrix`, `mixed_state_not_pure`: the mixed state `ρ = ½ I` satisfies both constraints and is a genuine (non-pure) density matrix.

This captures the book's point that a wave-function (pure state) cannot match the Born data of two non-commuting projections simultaneously, whereas Gleason's mixed-state density matrix can.

**Documentation.** Added a Wave 46 entry to `BookProof/STATUS.md` and prepended a new section to `ARISTOTLE_SUMMARY.md`. The out-of-scope `RiemannProof/RcpEuler.lean` sorries are unchanged. All work is committed and pushed.

# Summary of changes — Book §4 Gleason contrast (`ChapterB4`)
Executed the next `FORMALIZATION_ROADMAP.md` step and updated `ARISTOTLE_SUMMARY.md` as requested.

**Context.** The entire roadmap queue N1–N14 was already complete (both flagship packages, Hashimoto SIRK and QFM, landed in prior waves). The next remaining, previously-unimplemented item explicitly flagged in `FORMALIZATION_ROADMAP.md` (Chapter B remark, "worth adding as a sanity check") is the concrete `2`-dimensional real **Gleason contrast** from `book.tex` §4 (line ~1637). This pass formalizes it.

**New module `BookProof/ChapterB4.lean`** (registered in `BookProof.lean`), all `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified via `lean_verify` on the headlines); full `lake build` green (8124 jobs). No `EXTERNAL` hypothesis, no `axiom`.

Fix the two non-commuting real projections `P₁ = [[1,0],[0,0]]` and `P₂ = ½[[1,1],[1,1]]`. A **pure state** is a rank-one projector `v vᵀ` for a real unit vector `v` (`IsPureState`); a **density matrix** is Hermitian, positive-semidefinite, unit-trace (`IsDensityMatrix`); the Born value of projection `P` in state `ρ` is `tr(ρ P)`.
- `pure_state_satisfies_P1` / `pure_state_satisfies_P2`: a pure state (namely `P₂`, resp. `P₁`, each shown pure via `P2_isPureState` / `P1_isPureState`) individually realizes each Born constraint `= ½`.
- **headline `no_pure_state_satisfies_both`**: no pure state realizes both `tr(ρ P₁) = ½` and `tr(ρ P₂) = ½` simultaneously.
- `mixed_state_satisfies_both` + `mixed_state_isDensityMatrix` + `mixed_state_not_pure`: the genuinely mixed state `ρ = ½ I` does satisfy both constraints and is a legitimate (Gleason) density matrix, yet is not pure.

This captures the book's point: the wave-function (pure states) cannot match the Born data of two non-commuting projections at once, whereas Gleason's mixed-state density matrix can. Separately confirmed the §0 S7 hygiene item (the `../unfer` cross-reference docstrings on `born_conditioning` and `prodEquiv` in `ChapterU.lean`) is already present, so no edit was needed there. A Wave 46 entry was added to `BookProof/STATUS.md`. The out-of-scope `RiemannProof/RcpEuler.lean` sorries are unchanged. All work is committed and pushed.

# Summary of changes for run 44b696f5-29f9-45bd-82b2-997b47ea4216
Executed the next `FORMALIZATION_ROADMAP.md` step — the last recorded open item of the two flagship packages — and updated `ARISTOTLE_SUMMARY.md`.

**What was done.** The remaining open work across N13/N14 (per the previous summary/`BookProof/STATUS.md`) was the concrete `p̂ = −i ∂` / `x̂` integration-by-parts *function-space* model underlying the QFM package's deliverables F2.1 and F2.2 (whose purely algebraic cores were already in `BookProof/ChapterF5.lean`). This pass supplies that concrete model.

**New module `BookProof/ChapterF7.lean`** (registered in `BookProof.lean`), `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified on the headline theorems); the full `lake build` is green (8123 jobs). No `EXTERNAL` hypothesis, no `axiom`.

The domain is the Schwartz space `𝓢(ℝ, ℂ)` with the sesquilinear L² pairing `⟪f, g⟫ = ∫ conj(f x)·g x`:
- `l2pair` with integrability helper and full (conjugate-)bilinearity; `IsL2Symmetric T` = Hermiticity on the dense Schwartz domain.
- Position / real-multiplication operators (`mulOp`): `mulOp_l2Symmetric`, `position_l2Symmetric`.
- Momentum (`−i Ψ′`): `momentum_l2Symmetric`, whose analytic heart is `schwartz_integration_by_parts` (`∫ conj(f′) g = −∫ conj(f) g′`), proved from Mathlib's `integral_deriv_mul_eq_sub` with vanishing boundary terms (Schwartz decay) and Schwartz-product integrability.
- F2.1 concretely: `anticomm_l2Symmetric` ⇒ `continuityHamiltonian_l2Symmetric` (the continuity Hamiltonian `H = ½(p̂ v(x̂) + v(x̂) p̂)` is Hermitian).
- F2.2 concretely: `i_comm_l2Symmetric` + `kinetic_l2Symmetric` (`K = ½ p̂·p̂`) ⇒ `conservativeHamiltonian_l2Symmetric` (the conservative Hamiltonian `H^c = i[K, V(x̂)]` is Hermitian).

With this pass both flagship packages (Hashimoto SIRK and QFM) are complete, including the previously-deferred concrete `x̂`/`p̂` model. Added a Wave 45 entry to `BookProof/STATUS.md` and a new top section to `ARISTOTLE_SUMMARY.md`. The out-of-scope `RiemannProof/RcpEuler.lean` sorries are unchanged. All work is committed and pushed.

# Summary of changes — N14 QFM concrete `x̂`/`p̂` model (F2.1/F2.2), `ChapterF7`
Executed the next `FORMALIZATION_ROADMAP.md` step — the last recorded open item
of the two flagship packages — then updated `ARISTOTLE_SUMMARY.md` as requested.

**What the pass did.** The remaining open work across N13/N14 (per the previous
`ARISTOTLE_SUMMARY.md` / `BookProof/STATUS.md` wave-44 note) was the concrete
`p̂ = −i ∂` / `x̂` integration-by-parts *function-space* model underlying N14's
QFM deliverables **F2.1** and **F2.2** — the algebraic cores of which were
already in `ChapterF5`. This pass supplies that concrete model.

**New module `BookProof/ChapterF7.lean`** (registered in `BookProof.lean`) —
`sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`,
verified via `lean_verify` on the headline theorems); full `lake build` green
(8123 jobs). **No `EXTERNAL` hypothesis, no `axiom`.**

The domain is the Schwartz space `𝓢(ℝ, ℂ)` with the sesquilinear `L²` pairing
`⟪f, g⟫ = ∫ conj (f x) · g x`:
- **`l2pair`** with integrability helper `l2pair_integrable` and full
  (conjugate-)bilinearity (`l2pair_add/sub/smul_left/right`); `IsL2Symmetric T`
  = Hermiticity on the dense Schwartz domain.
- **Position / real multiplication** `mulOp v` (via `SchwartzMap.bilinLeftCLM`):
  `mulOp_l2Symmetric` (multiplication by any real temperate-growth function is
  `L²`-symmetric, since `conj (v x) = v x`); `position_l2Symmetric`.
- **Momentum** `momentum` (`−i Ψ′`, via `SchwartzMap.derivCLM`):
  `momentum_l2Symmetric`, whose analytic heart is the integration-by-parts
  lemma `schwartz_integration_by_parts` (`∫ conj(f′) g = −∫ conj(f) g′`), proved
  from `integral_deriv_mul_eq_sub` with vanishing boundary terms (Schwartz decay
  at `±∞`) and Schwartz-product integrability.
- **F2.1 concretely**: `anticomm_l2Symmetric` ⇒ `continuityHamiltonian_l2Symmetric`
  (the symmetrized continuity Hamiltonian `H = ½(p̂ v(x̂) + v(x̂) p̂)` is Hermitian).
- **F2.2 concretely**: `i_comm_l2Symmetric` + `kinetic_l2Symmetric` (`K = ½ p̂·p̂`)
  ⇒ `conservativeHamiltonian_l2Symmetric` (the conservative continuity
  Hamiltonian `H^c = i[K, V(x̂)]` is Hermitian).

With this pass **both flagship packages N13 (Hashimoto SIRK) and N14 (QFM) are
complete**, including the previously-deferred concrete `x̂`/`p̂` model. A Wave 45
entry was added to `BookProof/STATUS.md`. The out-of-scope `RiemannProof/`
sorries are unchanged. All work is committed and pushed.

# Summary of changes for run 75c5ea0b-3b77-4639-80bb-66b931d6ff96
Executed the next `FORMALIZATION_ROADMAP.md` steps, completing the N13 (Hashimoto Shift-invert Rational Krylov) work package, then updated `ARISTOTLE_SUMMARY.md`.

**New module `BookProof/ChapterH4.lean`** (registered in `BookProof.lean`), landing the four remaining N13 deliverables — all `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`); full `lake build` green (8122 jobs). The two deep analytic inputs (Crouzeix's inequality; the deferred `e^{−hm}` deformation of the source Theorem 5) are introduced as named hypotheses with citation docstrings, never axioms.

- **H1.5** — operator φ-function via the resolvent (Definition 2.4): the scalar function `psi k γ w := φ_k(γ − w⁻¹)` and its spectral-consistency identity `psi_shift_eq_phi`.
- **H2.2** — the SIRK compression `compress V X := V∗ X V` (exactly the paper's `Hₘ Kₘ⁻¹`, eq. 10) with the full transfer chain `compress_X_comp_V`, `compress_pow` (`Xⁿ∘V = V∘Bⁿ`), `compress_transfer`, `compress_inv_transfer`, yielding the load-bearing identity `r(Xₘ)v = Vₘ r(HₘKₘ⁻¹) Vₘ∗ v`.
- **H2.3** — the SIRK convergence headline (Theorem 4.1): `sirk_error_bound` (triangle-inequality core `≤ 2C·D·‖v‖`, conditional on the two named Crouzeix bounds) and `sirk_error_bound_decay` (the eq.-(12) form `≤ 2C·e^{−hm}·Dmin·‖v‖`).
- **H2.4** — the existing-methods comparison (Remark 4.2): `sia_error_bound` (SIA bound (15)) and `sirk_le_sia` (the `e^{−hm}` advantage of SIRK over SIA).

With this pass the N13 (Hashimoto SIRK) package is complete (H1.1–H2.4). Documentation: added a Wave 44 entry to `BookProof/STATUS.md` and a new top section to `ARISTOTLE_SUMMARY.md`. The remaining open item across the two flagship packages is the concrete function-space (`p̂ = −i ∂` / `x̂` integration-by-parts) model underlying N14's F2.1/F2.2, whose algebraic cores are already done in `ChapterF5`. The out-of-scope `RiemannProof/` sorries are unchanged. All work is committed and pushed.

# Summary of changes — N13 SIRK completed (H1.5 + H2.2 + H2.3 + H2.4, `ChapterH4`)
Executed the next `FORMALIZATION_ROADMAP.md` steps, landing the four remaining N13 (Hashimoto Shift-invert Rational Krylov) deliverables, then updated `ARISTOTLE_SUMMARY.md` as requested.

**New deliverables — N13 H1.5, H2.2, H2.3, H2.4 (Hashimoto SIRK, source `Hashimoto.md`).** Added one new module, `BookProof/ChapterH4.lean` (registered in `BookProof.lean`), all `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`), with **no `axiom`**. The full project `lake build` is green (8122 jobs). The two genuinely deep analytic inputs (Crouzeix's inequality and the deferred `e^{−hm}` deformation of the source Theorem 5) are introduced as **named hypotheses with citation docstrings**, never axioms.

Content: **H1.5** — the operator φ-function via the resolvent (Definition 2.4): the scalar function `psi k γ w := φ_k(γ − w⁻¹)` and its spectral-consistency identity `psi_shift_eq_phi` (`ψ_{k,γ}((γ − z)⁻¹) = φ_k(z)`). **H2.2** — the SIRK compression `compress V X := V∗ X V` (this is exactly the paper's `Hₘ Kₘ⁻¹`, eq. 10) with the full rational-function transfer chain `compress_X_comp_V`, `compress_pow` (`Xⁿ∘V = V∘Bⁿ`), `compress_transfer`, `compress_inv_transfer`, giving the load-bearing identity `r(Xₘ)v = Vₘ r(HₘKₘ⁻¹) Vₘ∗ v`. **H2.3** — the SIRK convergence headline (Theorem 4.1): `sirk_error_bound` (the eq.-(13)→(14) triangle-inequality core `≤ 2C·D·‖v‖`, conditional on the two named Crouzeix bounds) and `sirk_error_bound_decay` (the eq.-(12) form `≤ 2C·e^{−hm}·Dmin·‖v‖`). **H2.4** — the existing-methods comparison (Remark 4.2): `sia_error_bound` (the SIA bound (15)) and `sirk_le_sia` (the `e^{−hm}` advantage of SIRK over SIA as an inequality of the two bounds).

With this pass the **N13 (Hashimoto SIRK) package is complete** (H1.1–H2.4). Documentation: added a Wave 44 entry to `BookProof/STATUS.md`. Remaining open work is the concrete `p̂ = −i ∂` / `x̂` integration-by-parts function-space model underlying N14's F2.1/F2.2 (whose algebraic cores are already done in `ChapterF5`); the QFM pure-proof definition of done is otherwise complete. The out-of-scope `RiemannProof/` sorries are unchanged. All work is committed and pushed.

---

# Summary of changes for run aea415f2-3ff9-488d-9663-d5010ef55a26
Executed the next `FORMALIZATION_ROADMAP.md` step, continuing the N14 (Quantum Flow Matching) work package, then updated `ARISTOTLE_SUMMARY.md` as requested.

**New deliverable — F3.5, the Misra–Gries heavy-hitter bound (QFM §8 Phase 4).** Added one new module, `BookProof/ChapterF6.lean` (registered in `BookProof.lean`), all `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via verification), with no `EXTERNAL` hypothesis and no `axiom`. The full project `lake build` is green (8121 jobs).

The complete streaming frequency-estimation state machine is formalized: the counter table is a finitely-supported map `T : α →₀ ℕ`; `mgStep k` processes one stream item (increment when present or a slot is free, else decrement every counter by one); `mgT k`/`mg k` fold the step over the stream; `mgD k` counts the decrement rounds. The headline `misra_gries_bound` proves the top-1 peak-recovery guarantee `f(x) − N/k ≤ f̂(x) ≤ f(x)` for capacity `k ≥ 1`, where `f(x) = s.count x` is the true frequency, `f̂(x) = (mg k s) x` the estimate, and `N = s.length`. The proof rests on three induction invariants: `mg_upper` (never overshoots), `mg_lower` (undershoots by at most the decrement count `D`), and `mgD_bound` (`k·D ≤ N`) from the mass-conservation identity `mgSum(mgT) + (k+1)·D = mgSum(T₀) + N` (`mgT_sum_add`), using the capacity invariant `mgStep_card_le` and `mgSum_mapRange_pred`.

This was the next open pure-proof deliverable of N14. Remaining N14/N13 items stay documented rather than asserted (the concrete `p̂ = −i ∂` / `x̂` function-space model for F2.1/F2.2, and the N13 CFC/`CrouzeixBound` layers), so nothing is stated without proof.

Documentation: added a Wave 43 entry to `BookProof/STATUS.md` and a new top summary section to `ARISTOTLE_SUMMARY.md`. The out-of-scope `RiemannProof/` sorries are unchanged. All work is committed and pushed.

# Summary of changes — N14 QFM: F3.5 Misra–Gries heavy-hitter bound (`ChapterF6`)

Executed the next `FORMALIZATION_ROADMAP.md` step, continuing the **N14 (Quantum
Flow Matching)** work package.  Added one new module, `BookProof/ChapterF6.lean`
(registered in `BookProof.lean`), all **`sorry`-free** and **`axiom`-free** (only
`propext`, `Classical.choice`, `Quot.sound`, confirmed via `lean_verify`), with
**no `EXTERNAL` hypothesis and no `axiom`**.  The full project `lake build` is
green (8121 jobs).

New result:
- **F3.5 — the Misra–Gries heavy-hitter bound (QFM §8 Phase 4).**  The complete
  streaming frequency-estimation state machine is formalized: the counter table
  is a finitely-supported map `T : α →₀ ℕ`; `mgStep k` processes one stream item
  (increment its counter when it is already present or a slot is free, else
  decrement *every* counter by one); `mgT k` / `mg k` fold the step over the
  stream; and `mgD k` counts the decrement rounds.  The headline
  `misra_gries_bound` proves the top-1 peak-recovery guarantee
  `f(x) − N/k ≤ f̂(x) ≤ f(x)` for capacity `k ≥ 1`, where `f(x) = s.count x` is the
  true frequency, `f̂(x) = (mg k s) x` the estimate, and `N = s.length`.
  The proof combines three invariants proved by induction over the stream:
  `mg_upper` (the estimate never overshoots), `mg_lower` (it undershoots by at
  most the number of decrement rounds `D`), and `mgD_bound` (`k · D ≤ N`), the
  last derived from the mass-conservation identity
  `mgSum(mgT) + (k+1)·D = mgSum(T₀) + N` (`mgT_sum_add`) — each decrement round
  removes exactly `k` units of stored mass once the table is full, using the
  capacity invariant `mgStep_card_le` and `mgSum_mapRange_pred`.

This was the next open pure-proof deliverable of N14.  Remaining N14/N13 items
stay documented rather than asserted (the concrete `p̂ = −i ∂` / `x̂`
function-space model for F2.1/F2.2, and the N13 CFC/`CrouzeixBound` layers), so
nothing is stated without proof.  `BookProof/STATUS.md` gained a Wave 43 entry.
The out-of-scope `RiemannProof/` sorries are unchanged.  All work is committed
and pushed.

---

# Summary of changes for run 4cf3b228-17c7-421f-b5fb-b136ce4eda1f
Executed the next `FORMALIZATION_ROADMAP.md` steps, continuing the N14 (Quantum Flow Matching) work package. Added one new module, `BookProof/ChapterF5.lean` (registered in `BookProof.lean`), all `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`), with no `EXTERNAL` hypothesis and no `axiom`. The full project `lake build` is green (8120 jobs).

New results:
- F2.1 (continuity-Hamiltonian Hermiticity, algebraic core): `anticommutator_isSymmetric` — the symmetrized product `K ∘ V + V ∘ K` of two symmetric operators is symmetric with no commutation hypothesis, the reason `H = ½(p̂·v(x̂) + v(x̂)·p̂)` is Hermitian.
- F2.2 (conservative commutator form, algebraic core): `i_commutator_isSymmetric` — `i • [K, V]` is symmetric whenever `K, V` are, the reason `H^c = i • [K, V(x̂)]` is Hermitian.
- F2.5 (exact commutativity / time-averaging): `commuting_flow_two` and `commuting_flow_finset` — a pairwise-commuting family of channel generators has a factorizing time-ordered flow `exp(−i t • ∑ⱼ Hⱼ) = ∏ⱼ exp(−i t • Hⱼ)`.

Remaining N14 items (F3.5 Misra–Gries; the concrete `p̂ = −i ∂`/`x̂` model) and N13 items (H1.5, H2.2, H2.3/H2.4) stay documented rather than asserted, as they need larger infrastructure or remain conditional on the named `CrouzeixBound` input.

Documentation updated as requested: `BookProof/STATUS.md` gained a Wave 42 entry and `ARISTOTLE_SUMMARY.md` gained a new summary section at the top. All work is committed and pushed.

# Summary of changes (continued run) — N14 QFM: F2.1/F2.2 symmetric generators + F2.5 commuting flows

Executed the next `FORMALIZATION_ROADMAP.md` steps, continuing the **N14 (Quantum
Flow Matching)** package. Added one new module, `BookProof/ChapterF5.lean`
(registered in `BookProof.lean`), all **`sorry`-free** and **`axiom`-free** (only
`propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`), with
**no `EXTERNAL` hypothesis and no `axiom`**. The full project `lake build` is
green.

New results:
- **F2.1** — continuity-Hamiltonian Hermiticity, algebraic core (§4 eq. 4.2):
  `anticommutator_isSymmetric` shows the symmetrized product `K ∘ V + V ∘ K` of
  two symmetric operators is symmetric with no commutation hypothesis — the
  reason `H = ½(p̂·v(x̂) + v(x̂)·p̂)` is Hermitian even when `p̂` and `v(x̂)` do
  not commute.
- **F2.2** — conservative commutator form, algebraic core (§4 eqs. 4.4–4.6):
  `i_commutator_isSymmetric` shows `i • [K, V] = i • (K ∘ V − V ∘ K)` is
  symmetric whenever `K, V` are (commutator of symmetrics is skew, `i` restores
  symmetry) — the reason `H^c = i • [K, V(x̂)]` is Hermitian.
- **F2.5** — exact commutativity and time-averaging (§5.4): `commuting_flow_two`
  and `commuting_flow_finset` prove a pairwise-commuting family of channel
  generators has a factorizing time-ordered flow
  `exp(−i t • ∑ⱼ Hⱼ) = ∏ⱼ exp(−i t • Hⱼ)`.

Remaining N14 items stay documented rather than asserted: F3.5 (Misra–Gries,
optional) needs a streaming state machine, and the concrete `p̂ = −i ∂` / `x̂`
integration-by-parts symmetry underlying F2.1/F2.2 needs the function-space
differentiation model. Remaining N13 items are unchanged: H1.5 (operator φ via
CFC), H2.2 (SIRK compression assembly), H2.3/H2.4 (convergence, conditional on
the named `CrouzeixBound`). Documentation updated: `BookProof/STATUS.md` gained a
Wave 42 entry. All work is committed and pushed.

# Summary of changes for run 7e179af5-a4c7-427b-975a-75587e56b814
Executed the next `FORMALIZATION_ROADMAP.md` steps, continuing the N13 (Hashimoto SIRK) package that was previously left documented-but-not-asserted. Added one new module, `BookProof/ChapterH3.lean` (registered in `BookProof.lean`), all `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`), with no `EXTERNAL` hypothesis and no `axiom`. The full project `lake build` is green.

New results:
- H1.3 — exponential-integrator Duhamel identity (scalar/per-spectral-component core): `duhamel_scalar` proves `∫₀^δ e^{(δ−s) z} ds = δ·φ₁(δ z)` and `duhamel_scalar_smul` its constant-forcing corollary, where `φ₁` is `ChapterH1.phi 1` from H1.1/H1.2.
- H1.7 — rational-Krylov ⊆ rational functions of Xₘ: `sirkKrylov` (the SIRK Krylov iterates) and `sirk_krylov_mem_adjoin`, showing that under the H1.6 shift identity `X_j = Y_j · Xₘ`, every Krylov iterate is a rational function of the single operator `Xₘ` applied to `v` (lies in the image of `v` under the subalgebra generated by `Xₘ` and the resolvent factors).

Remaining N13 items stay documented rather than asserted: H1.5 (operator φ via continuous functional calculus) and H2.2 (SIRK compression assembly) need the full operator-φ CFC layer, and H2.3/H2.4 (convergence) remain conditional on the named `CrouzeixBound` deep analytic input (kept a named hypothesis, never an axiom).

Documentation updated as requested: `BookProof/STATUS.md` gained a Wave 41 entry and `ARISTOTLE_SUMMARY.md` gained a new summary section at the top. The out-of-scope `RiemannProof/` sorries are unchanged. All work is committed and pushed.

# Summary of changes (continued run) — N13 SIRK: H1.3 Duhamel + H1.7 rational-Krylov

Picking up where the previous run left off, I executed the next `FORMALIZATION_ROADMAP.md` steps: two further **N13 (Hashimoto SIRK)** deliverables that were previously documented-but-not-asserted. Added one new module, `BookProof/ChapterH3.lean` (registered in `BookProof.lean`), **`sorry`-free** and **`axiom`-free** (only `propext`, `Classical.choice`, `Quot.sound`; verified with `#print axioms`), with **no `EXTERNAL` hypothesis and no `axiom`**. Full project `lake build` is green.

- **H1.3 — exponential-integrator Duhamel identity (scalar/per-spectral-component core, §0 S3):** `duhamel_scalar` proves `∫₀^δ e^{(δ−s) z} ds = δ·φ₁(δ z)` and `duhamel_scalar_smul` its constant-forcing corollary `∫₀^δ e^{(δ−s) z}·g ds = δ·φ₁(δ z)·g`, where `φ₁` is `ChapterH1.phi 1` from H1.1/H1.2. Proof: reflection substitution `u = δ−s` and rescaling `u = δ t`.
- **H1.7 — rational-Krylov ⊆ rational functions of `Xₘ` (eq. 11):** `sirkKrylov` (the SIRK Krylov iterates `w_j = X_j ⋯ X_1 v`) and `sirk_krylov_mem_adjoin` — given the H1.6 shift identity `X_j = Y_j · Xₘ`, every Krylov iterate lies in `{ r v | r ∈ adjoin ℂ ({Xₘ} ∪ range Y) }`, i.e. is a rational function of the single operator `Xₘ` applied to `v`. This is the load-bearing inclusion behind the SIRK convergence theory (the reverse/surjectivity direction is noted in the docstring, not needed for the error bound).

Remaining N13 items stay documented (not asserted): H1.5 (operator φ via CFC) and H2.2 (SIRK compression assembly) need the full continuous-functional-calculus operator-φ layer; H2.3/H2.4 (convergence) remain conditional on the named `CrouzeixBound` deep analytic input. `BookProof/STATUS.md` updated with a Wave 41 entry. The out-of-scope `RiemannProof/` sorries are unchanged.

---

# Summary of changes for run e4c19907-e1ba-465e-8250-70f8336f7173
Executed `FORMALIZATION_ROADMAP.md`. On entry the entire original work-package queue (N1–N12) was already complete and the `BookProof` library was sorry-free; the only open items were the two flagship packages the roadmap promoted 2026-07-06: **N13 (Hashimoto Shift-invert Rational Krylov, SIRK)** and **N14 (Quantum Flow Matching, QFM)**. I formalized and proved both, adding four new modules — all `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`), with **no `EXTERNAL` hypothesis and no `axiom`**. The full project `lake build` is green (8118 jobs).

New modules (registered in `BookProof.lean`):
- `BookProof/ChapterH1.lean` (N13): H1.1 the φ-functions (`phi`, `phi_zero`, `phi_at_zero`); H1.2 the φ-recurrence (`phi_succ_mul`, `phi_one`); H1.4 numerical range and eigenvalue inclusion (`eigenvalue_mem_numericalRange`); H1.6 the SIRK resolvent algebra core (`resolvent_identity`, `resolvent_shift_mul`).
- `BookProof/ChapterH2.lean` (N13): H2.1 the Arnoldi/Krylov compression is upper-Hessenberg (`hessenberg_vanishing`, `compression_upper_hessenberg`).
- `BookProof/ChapterF3.lean` (N14): F2.3 disjoint-support identities; F2.4 diagonal-Gram closed-form training; F2.6 the vacuum projector (`projOnto`, idempotent/self-adjoint/= orthogonal projection); F2.7 the diagonal generator's eigenstates (reusing N12's `numberOp`); F2.8 the dressed-vacuum Bessel bound `Σεⱼ²≤1` plus the single-arc integral and overlap positivity; F2.9 the Mehler-projector matrix elements.
- `BookProof/ChapterF4.lean` (N14): F3.1 Count-Sketch linearity and unbiasedness (`countsketch_unbiased`, with the Rademacher `sign_pair_expectation`); F3.2 the observable-matrix identity; F3.3 the unitary reduced flow (`unitary_preserves_dotProduct`, `selfAdjoint_exp_star_mul_self`); F3.4 the pseudo-inverse left-inverse.

N14's complete pure-proof "definition of done" is delivered. For N13, all pure-proof items are delivered except H1.7 (the rational-Krylov characterization); the remaining N13 items (H1.3/H1.5/H2.2 core-reductions and H2.3/H2.4, which are conditional on the deep analytic `CrouzeixBound` input) are documented in `BookProof/STATUS.md` rather than asserted, so nothing is stated without proof. Documentation updated in `BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md`.

The out-of-scope `RiemannProof/` (Riemann Hypothesis chapter) sorries are unchanged, as the roadmap directs. All work is committed and pushed.

# Summary of changes — N13 (Hashimoto SIRK) + N14 (QFM) flagship packages

Executed `FORMALIZATION_ROADMAP.md`.  On entry the entire original queue
(N1–N12) was complete; the only open items were the two flagship packages
promoted 2026-07-06: **N13 (Hashimoto SIRK)** and **N14 (Quantum Flow
Matching)**.  This pass lands them in four new modules, all `sorry`-free and
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`), with **no
`EXTERNAL` hypothesis and no `axiom`**.  `lake build` is green (8118 jobs).

- **`BookProof/ChapterH1.lean`** (N13): H1.1 φ-functions (`phi`, `phi_zero`,
  `phi_at_zero`), H1.2 recurrence (`phi_succ_mul`, `phi_one`), H1.4 numerical
  range (`eigenvalue_mem_numericalRange`), H1.6 the SIRK resolvent algebra
  (`resolvent_identity`, `resolvent_shift_mul`).
- **`BookProof/ChapterH2.lean`** (N13): H2.1 Krylov/Arnoldi compression is
  upper-Hessenberg (`hessenberg_vanishing`, `compression_upper_hessenberg`).
- **`BookProof/ChapterF3.lean`** (N14): F2.3, F2.4, F2.6, F2.7, F2.8, F2.9 —
  disjoint-support identities, diagonal-Gram closed-form training, the vacuum
  projector, the diagonal-generator eigenstates (reusing N12 `numberOp`), the
  dressed-vacuum Bessel bound `Σεⱼ²≤1`, and the Mehler-projector matrix.
- **`BookProof/ChapterF4.lean`** (N14): F3.1 Count-Sketch linearity +
  unbiasedness (`countsketch_unbiased`), F3.2 observable-matrix identity, F3.3
  unitary reduced flow, F3.4 pseudo-inverse left-inverse.

N14's full pure-proof *definition of done* is complete.  N13's pure-proof set is
complete except H1.7 (rational-Krylov characterization); the remaining N13
items (H1.3/H1.5/H2.2 core-reductions and H2.3/H2.4 conditional on the named
`CrouzeixBound`) are documented in `BookProof/STATUS.md`, not asserted.

The out-of-scope `RiemannProof/` (Riemann Hypothesis) sorries are unchanged.

---

# Summary of changes for run c14d1ff7-3dcc-433d-ba8a-23f8068b42d8
Per your choice, I re-verified the whole project and confirmed there is no remaining roadmap work.

Findings:
- The FORMALIZATION_ROADMAP.md work-package queue is fully complete (N1–N12, including N7(c), the Bargmann–Fock mass gap). The entire BookProof library is sorry-free.
- `lake build` on all default targets (RiemannProof, PnpProof, BookProof) completes successfully: "Build completed successfully (8114 jobs)" with no errors. The only diagnostics are style-linter warnings plus the expected `declaration uses 'sorry'` notices inside RiemannProof/RcpEuler.lean — the Riemann Hypothesis chapter, which the roadmap explicitly places out of scope. Nothing in BookProof or PnpProof emits a sorry warning.
- A grep across BookProof confirmed no `sorry`/`admit` in tactic position, and an axiom check on the most recent headline BookProof.ChapterF2.mass_gap reports only propext, Classical.choice, Quot.sound (no sorry, no non-standard axioms).

No source code changes were required this pass since the roadmap deliverables were already complete and verified green. I added a new verification-run section at the top of ARISTOTLE_SUMMARY.md recording the above. All changes are committed and pushed.

Note: the only outstanding sorry's in the project are in RiemannProof/ (the Riemann Hypothesis chapter), which the roadmap intentionally leaves out of scope. If you'd like, a future pass could target those, but that is a substantial, largely open-problem effort and outside the current roadmap.

# Summary of changes for the re-verification run

The user asked to "do the next steps" and then update this file. On entry the
`FORMALIZATION_ROADMAP.md` work-package queue was already fully exhausted: all
of N1–N12 (including N7(c), the Bargmann–Fock mass gap) are complete, and the
entire `BookProof` library is `sorry`-free and `axiom`-free. The only remaining
`sorry`s anywhere in the project are in `RiemannProof/` (the Riemann Hypothesis
chapter), which the roadmap explicitly places out of scope. After confirming
with the user, the agreed next step was to re-verify the whole project and
report completion — no roadmap work remained to do.

**Verification performed.**
- `lake build` on all default targets (`RiemannProof`, `PnpProof`, `BookProof`)
  completes successfully: **Build completed successfully (8114 jobs)**, no
  errors. The only diagnostics are style-linter warnings and the expected
  `declaration uses 'sorry'` notices inside `RiemannProof/RcpEuler.lean`
  (out-of-scope RH material); nothing in `BookProof` or `PnpProof` emits a
  `sorry` warning.
- Grep across `BookProof/*.lean` finds no `sorry`/`admit` in tactic position
  (only the docstring text "`sorry`-free").
- Axiom check on the most recent headline `BookProof.ChapterF2.mass_gap`
  reports only `propext`, `Classical.choice`, `Quot.sound` — no `sorry`, no
  non-standard axioms.

**Conclusion.** The `FORMALIZATION_ROADMAP.md` deliverables are complete and
verified green; no code changes were required this pass. The out-of-scope
`RiemannProof/` `sorry`s remain, as designed by the roadmap. Only this summary
section was added; it is committed and pushed to `origin/main`.

---

# Summary of changes for run 56e838d9-083f-497c-a83d-6aa8d373554e
Continued `FORMALIZATION_ROADMAP.md` where the previous run stopped. On entry the `BookProof` library was already complete and `sorry`/`axiom`-free through Wave 38 (N11, N12, and the S7 hygiene docstrings), leaving exactly one remaining work item: **N7(c)**, the book's *"Mass gap"* section (`book.tex` ~line 4060). I formalized it.

**N7(c) — the mass gap in the Bargmann–Fock model (`BookProof/ChapterF2.lean`, new).** Building on the Wave-38 `ChapterF1` model (vacuum `|0⟩ = 1`, annihilation `a = d/dX`, creation `a† = X·`, number operator `N = a†a`), and following the book's own definition of the mass gap as the eigenvalue of the Hamiltonian closest to the vacuum's null eigenvalue, the Hamiltonian is the quadratically-ordered `H := a†a = N`; on the monomial basis `H Xⁿ = n·Xⁿ`, so the spectrum is `ℕ`, the vacuum has energy `0`, and the mass gap is `Δ = 1`. Delivered:
- F2.1 `numberOp_coeff` (`(N p)_n = n·p_n`), `numberOp_support`;
- F2.2 real forms `bargmann_self_re`/`bargmann_numberOp_re` and `hamiltonian_expectation_nonneg` (`H` is positive / bounded below, from the quadratic ordering);
- F2.3 `deformedHamiltonian c := c•N` with `deformedHamiltonian_monomial` (`H_c Xⁿ = (c·n)·Xⁿ`, arbitrary mass gap `c`, unchanged eigenstates) and `deformedHamiltonian_commutes_numberOp`/`hamiltonian_commutes_numberOp` (`[H_c, N] = 0` — the book's claim that adding the number operator modifies the mass gap without observable consequences);
- F2.4 HEADLINE `mass_gap` (for any state `ψ` orthogonal to the vacuum, `⟨ψ|H|ψ⟩ ≥ ⟨ψ|ψ⟩` — spectrum above the vacuum bounded below by `Δ = 1`), with `mass_gap_attained` (`⟨X|H|X⟩ = ⟨X|X⟩`, gap is tight), `vacuum_energy_zero`, and `massGap_smallest_excited` (eigenvalue form).

The module is registered in `BookProof.lean`. `lake build BookProof` is green (8114 jobs); every new declaration is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed with the theorem checker on `mass_gap`, `hamiltonian_expectation_nonneg`, `deformedHamiltonian_monomial`). No `axiom`, `@[implemented_by]`, or `EXTERNAL` hypothesis was introduced.

I updated `BookProof/STATUS.md` (new Wave 39 entry) and, as requested, `ARISTOTLE_SUMMARY.md` (new top section). With N7(c) landed, all work items of `FORMALIZATION_ROADMAP.md` are complete. All changes are committed and pushed to `origin/main`.

# Summary of changes for the mass-gap (N7(c)) run

Continued `FORMALIZATION_ROADMAP.md` after Wave 38 (which had closed N11, N12,
and the S7 hygiene docstrings). On entry the only remaining roadmap work item
was **N7(c)** — the book's *"Mass gap"* section (`book.tex` ~line 4060), flagged
"ask before building" only because it depends on which inequality the book
isolates; that section states it explicitly, so this pass formalizes it.

**N7(c) — the mass gap in the Bargmann–Fock model (`BookProof/ChapterF2.lean`, new).**
Building on the Wave-38 `ChapterF1` model (vacuum `|0⟩ = 1`, `a = d/dX`,
`a† = X·`, `N = a†a`), and following the book's own definition (*"the mass gap
is the eigenvalue of the Hamiltonian which is closer to the null eigenvalue
corresponding to the vacuum state"*), the Hamiltonian is the quadratically-
ordered `H := a†a = N`; its spectrum on the monomial basis is `ℕ` (`H Xⁿ = n·Xⁿ`),
so the vacuum has energy `0` and the mass gap is `Δ = 1`.
- F2.1 `numberOp_coeff` (`(N p)_n = n·p_n`) and `numberOp_support`;
- F2.2 real forms `bargmann_self_re`/`bargmann_numberOp_re` and
  `hamiltonian_expectation_nonneg` (`H` positive / bounded below by the
  quadratic ordering);
- F2.3 `deformedHamiltonian c := c•N` with `deformedHamiltonian_monomial`
  (`H_c Xⁿ = (c·n)·Xⁿ`, arbitrary mass gap `c`, unchanged eigenstates) and
  `deformedHamiltonian_commutes_numberOp` / `hamiltonian_commutes_numberOp`
  (`[H_c, N] = 0` — the book's "add the number operator, modify the mass gap
  without observable consequences");
- F2.4 HEADLINE `mass_gap` (for `ψ ⟂ vacuum`, `⟨ψ|H|ψ⟩ ≥ ⟨ψ|ψ⟩` — spectrum above
  the vacuum bounded below by `Δ = 1`), with `mass_gap_attained`
  (`⟨X|H|X⟩ = ⟨X|X⟩`, the gap is tight), `vacuum_energy_zero`, and
  `massGap_smallest_excited` (eigenvalue form).

The new module is registered in `BookProof.lean`; `lake build BookProof` is green
(8114 jobs) and every new declaration is `sorry`-free and `axiom`-free (only
`propext`, `Classical.choice`, `Quot.sound`, confirmed with `lean_verify`). No
`axiom` or `@[implemented_by]` was introduced, and no `EXTERNAL` hypothesis is
needed. `BookProof/STATUS.md` records this as Wave 39. With N7(c) landed, all
work items of `FORMALIZATION_ROADMAP.md` are now complete.

---

# Summary of changes for run 11785fa7-6f70-4cf9-897f-ba14c92cd844
Executed the remaining open items of `FORMALIZATION_ROADMAP.md`. On entry the `BookProof` library was already `sorry`/`axiom`-free through Wave 37, with the roadmap listing exactly three outstanding items — **N11**, **N12**, and a pending **S7 hygiene** docstring task. All three are now delivered; `lake build BookProof` is green (8113 jobs) and every new declaration is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed with `lean_verify`).

**N12 — S7 Bargmann–Fock / CCR field package (`BookProof/ChapterF1.lean`, new).** The polynomial (Bargmann–Fock) model of the CCR algebra on `ℂ[X]` (vacuum `|0⟩ = 1`, annihilation `a = d/dX`, creation `a† = X·`), following the `../unfer` design (§0 S7):
- F1.1 `ccr` (`[a,a†]=1`) and multi-mode `ccr_mv` (`[a_i,a†_j]=δ_ij`);
- F1.2 Hermitian field rep `fieldPhi`, `fieldPi`, `field_ccr` (`[φ,π]=2i·1`); the Bargmann pairing with `bargmann_monomial` (`⟪Xᵐ,Xⁿ⟫=n!·δ_{mn}`) and the adjoint relation `bargmann_creat_annih`;
- F1.3 number operator `numberOp`, `numberOp_monomial` (`N Xⁿ = n·Xⁿ`);
- F1.4 headline `quadratic_ordering_vacuum` (`⟨0|H|0⟩=0`) vs. `symmetric_ordering_vacuum` (`½`) and `orderings_differ`;
- F1.5 `field_gauge_invariant_iff` BRST bridge to `ChapterG2`.

**N11 — Wigner/Mackey/Weyl exhaustiveness bundle (`BookProof/ChapterA4h.lean` and `BookProof/ChapterA3w.lean`, new).** Following the established `IsSchurFull`/`PauliFundamental` design, the genuinely external theorems (Mackey imprimitivity, Wigner little-group classification, Weyl complete reducibility) are introduced as named hypotheses with citation docstrings (never axioms), and the conditional headlines are proved around the on-disk cores:
- concrete `localizable_iff_massShell` (Majorana energy symbol singular iff `|p⃗|²=m₁²+m₂²`) plus the tachyon and zero-momentum exclusions;
- `prop87_assembled` (a localizable induced irrep is massive or massless-discrete), `prop88_energy_sign_not_conserved`, `cor1_energy_sectors_swapped`, and the combined `prop87_88_assembled`;
- `WeylCompleteReducibility` with `weyl_invariant_complement`, and the concrete `lemma52_parity_gluing` (chirality is not parity-invariant; parity swaps the chiral blocks `V_{(m,n)} ↔ V_{(n,m)}`).

**Hygiene.** Added the pending §0 S7 `../unfer` cross-reference docstrings to `born_conditioning` and `prodEquiv` in `BookProof/ChapterU.lean`; the three new modules are lint-clean and registered in `BookProof.lean`. `BookProof/STATUS.md` records this as Wave 38.

Not done, by roadmap instruction: N7(c) (Ch. P mass-gap re-scan) is flagged author-dependent ("ask before building"), and the STOP RULE forbids extending the dimension-count thread beyond N=6; these were intentionally left. All changes are committed and pushed to `origin/main` (latest commit `3a9386e`).

# Summary of changes for run e3a68ecc-57d0-4ec5-a57c-76abdcdef3b5
Executed the next step of the formalization roadmap (Wave 37), continuing the §A.3 Note 50 / Lemma 52 complete-reducibility thread past the previous `N = 5` dimension count.

New module `BookProof/ChapterA3v.lean` (registered in `BookProof.lean`) computes the ranks (traces) of the three complete-reducibility projectors at `N = 6` for the tensor sixth power of the 4-dimensional Dirac spinor `V` (`dim V^{⊗6} = 4⁶ = 4096`). As at `N = 5`, the totally antisymmetric summand `Λ⁶V` vanishes (a 4-dimensional space has no nonzero 6-fold exterior power):
- `trace_projSym_six`: `tr(projSym 6) = 84` (`= dim Sym⁶V = C(9,6)`);
- `trace_projAnti_six`: `tr(projAnti 6) = 0` (`= dim Λ⁶V = C(4,6) = 0`);
- `trace_projMixed_six`: `tr(projMixed 6) = 4012` (`= 4096 − 84 − 0`);
- `trace_decomposition_six`: the headline `84 + 0 + 4012 = 4096 = dim V^{⊗6}`.

The proof reuses Wave 36's general orbit-count machinery from `ChapterA3u` (`card_fixedTuples`, `trace_permMat_pow`: `tr(permMat σ) = 4^{c(σ)}`). The symmetric and antisymmetric traces reduce to finite sums over `S₆` of small numbers (`Σ 4^{c(σ)} = 60480`, `Σ sgn(σ)·4^{c(σ)} = 0`) discharged by kernel `decide` (raised `maxRecDepth`/`maxHeartbeats` for the 720 permutations; no `native_decide`).

All deliverables are `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`; confirmed with the axiom checker on `trace_decomposition_six`). The full project builds green (8110 jobs). `ARISTOTLE_SUMMARY.md` and `BookProof/STATUS.md` were updated with a new Wave 37 section (existing content left intact; the new summary is prepended). All work is committed and pushed.

Remaining open items are unchanged in kind: the external Wigner/Mackey backbone of the §A.4/A.5 classification (roadmap-tracked named-hypothesis work), and the pre-existing `sorry`s in `RiemannProof/RcpEuler.lean` (placed out of scope by the roadmap).

# Summary of changes (Wave 37) — §A.3 Note 50 / Lemma 52 dimensions at `N = 6`

Executed the next step of the formalization roadmap (Wave 37), continuing the
§A.3 Note 50 / Lemma 52 complete-reducibility thread past the previous `N = 5`
dimension count.

New module `BookProof/ChapterA3v.lean` (registered in `BookProof.lean`) computes
the ranks (traces) of the three complete-reducibility projectors at `N = 6` for
the tensor sixth power of the 4-dimensional Dirac spinor `V`
(`dim V^{⊗6} = 4⁶ = 4096`). As at `N = 5`, the totally antisymmetric summand
`Λ⁶V` vanishes (a 4-dimensional space has no nonzero 6-fold exterior power):
- `trace_projSym_six`: `tr(projSym 6) = 84` (`= dim Sym⁶V = C(9,6)`);
- `trace_projAnti_six`: `tr(projAnti 6) = 0` (`= dim Λ⁶V = C(4,6) = 0`);
- `trace_projMixed_six`: `tr(projMixed 6) = 4012` (`= 4096 − 84 − 0`);
- `trace_decomposition_six`: the headline `84 + 0 + 4012 = 4096 = dim V^{⊗6}`.

The proof reuses Wave 36's general orbit-count machinery from `ChapterA3u`
(`card_fixedTuples`, `trace_permMat_pow`: `tr(permMat σ) = 4^{c(σ)}` where
`c(σ)` is the number of orbits of `σ`). With that, the symmetric and
antisymmetric traces reduce to finite sums over `S₆` of small numbers
(`Σ 4^{c(σ)} = 60480`, `Σ sgn(σ)·4^{c(σ)} = 0`) discharged by kernel `decide`
(`maxRecDepth 100000`, `maxHeartbeats 4000000` for the 720 permutations; no
`native_decide`).

All deliverables are `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`; confirmed with the axiom checker on
`trace_decomposition_six`). The full project builds green (8110 jobs).
`BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md` were updated with a new Wave 37
section (existing content left intact; the new summary is prepended).

Remaining open items are unchanged in kind: the external Wigner/Mackey backbone
of the §A.4/A.5 classification, which the roadmap tracks as named-hypothesis
work; and the pre-existing `sorry`s in `RiemannProof/RcpEuler.lean`, which the
roadmap places out of scope.

# Summary of changes for run b8f1f928-6450-4462-803b-ae0a998e809a
Executed the next step of the formalization roadmap (Wave 36), continuing the §A.3 Note 50 / Lemma 52 complete-reducibility thread past the previous `N = 4` dimension count.

New module `BookProof/ChapterA3u.lean` (registered in `BookProof.lean`) computes the ranks (traces) of the three complete-reducibility projectors at `N = 5` for the tensor fifth power of the 4-dimensional Dirac spinor `V` (`dim V^{⊗5} = 4⁵ = 1024`). `N = 5` is the first case where the totally antisymmetric summand `Λ⁵V` vanishes (a 4-dimensional space has no nonzero 5-fold exterior power):
- `trace_projSym_five`: `tr(projSym 5) = 56` (`= dim Sym⁵V = C(8,5)`);
- `trace_projAnti_five`: `tr(projAnti 5) = 0` (`= dim Λ⁵V = C(4,5) = 0`);
- `trace_projMixed_five`: `tr(projMixed 5) = 968` (`= 1024 − 56 − 0`);
- `trace_decomposition_five`: the headline `56 + 0 + 968 = 1024 = dim V^{⊗5}`.

Because the brute-force `S₅ × 4⁵` count (120 permutations over 1024 index tuples) is far too large for kernel `decide`, this wave first proves a general **orbit-count** lemma `card_fixedTuples`: for any `σ ∈ S_N`, the number of index tuples `a : Fin N → Fin 4` fixed by `σ` equals `4^{c(σ)}`, where `c(σ) = (N − Σ cycleType σ) + #(cycleType σ)` is the number of orbits of `σ`. Its proof uses an explicit bijection between the fixed tuples and functions on `{fixed points} ⊕ {cycle factors}`, supported by the helpers `invariant_apply_zpow` / `invariant_sameCycle` (an invariant tuple is constant along each orbit). With `trace(permMat σ) = 4^{c(σ)}` (`trace_permMat_pow`), the symmetric and antisymmetric traces then reduce to small finite sums over `S₅` discharged by kernel `decide` (`maxRecDepth 100000`, no `native_decide`).

All deliverables are `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`; confirmed with the axiom checker on `trace_decomposition_five` and `card_fixedTuples`). The full project builds green (8109 jobs). `BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md` were updated with a new Wave 36 section (existing content left intact; the new summary is prepended). All work is committed and pushed.

Remaining open items are unchanged in kind: the external Wigner/Mackey backbone of the §A.4/A.5 classification, which the roadmap tracks as named-hypothesis work; and the pre-existing `sorry`s in `RiemannProof/RcpEuler.lean`, which the roadmap places out of scope.

# Summary of changes (latest run) — Wave 36: dimensions of the complete-reducibility summands at `N = 5`

Executed the next step of `FORMALIZATION_ROADMAP.md` (Wave 36), continuing the §A.3 Note 50 / Lemma 52 complete-reducibility thread past Wave 35's `N = 4` dimension count. `N = 5` is the first case where the totally antisymmetric summand `Λ⁵V` vanishes (a 4-dimensional space has no nonzero 5-fold exterior power).

New module `BookProof/ChapterA3u.lean` (registered in `BookProof.lean`) computes the ranks (traces) of the three complete-reducibility projectors at `N = 5` for the tensor fifth power of the 4-dimensional Dirac spinor `V` (`dim V^{⊗5} = 4⁵ = 1024`):
- `trace_projSym_five`: `tr(projSym 5) = 56` (`= dim Sym⁵V = C(8,5)`);
- `trace_projAnti_five`: `tr(projAnti 5) = 0` (`= dim Λ⁵V = C(4,5) = 0`);
- `trace_projMixed_five`: `tr(projMixed 5) = 968` (`= 1024 − 56 − 0`);
- `trace_decomposition_five`: the headline `56 + 0 + 968 = 1024 = dim V^{⊗5}`.

The brute-force `S₅ × 4⁵` count (120 permutations over 1024 index tuples) is far too large for kernel `decide`, so this wave first proves the general **orbit-count** lemma `card_fixedTuples`: for any `σ : S_N`, the number of index tuples `a : Fin N → Fin 4` fixed by `σ` equals `4^{c(σ)}`, where `c(σ) = (N − Σ cycleType σ) + #(cycleType σ)` is the number of orbits of `σ`. The proof uses an explicit bijection between the fixed tuples and functions on `{fixed points} ⊕ {cycle factors}`, plus helpers `invariant_apply_zpow` / `invariant_sameCycle`. With `trace (permMat σ) = 4^{c(σ)}` (`trace_permMat_pow`), the symmetric and antisymmetric projector traces reduce to small finite sums over `S₅` discharged by kernel `decide` (`maxRecDepth 100000`, no `native_decide`).

All deliverables are `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`; verified with the axiom checker on `trace_decomposition_five` and `card_fixedTuples`). The full project builds green (8109 jobs). `BookProof/STATUS.md` and this file were updated with a new Wave 36 section (existing content left intact; the new summary is prepended). All work is committed and pushed.

Remaining open items are unchanged in kind: the `EXTERNAL` Wigner/Mackey backbone of the §A.4/A.5 classification, which the roadmap tracks as named-hypothesis work. The only remaining `sorry`s in the project are in the pre-existing `RiemannProof/RcpEuler.lean`, which the roadmap places out of scope.

---

# Summary of changes for run b17181ee-dba9-4450-a4c6-0ff2f53d83fa
Executed the next step of the formalization roadmap (Wave 35), continuing the §A.3 Note 50 / Lemma 52 complete-reducibility thread past the previous `N = 2` and `N = 3` dimension counts.

New module `BookProof/ChapterA3t.lean` (registered in `BookProof.lean`) computes the ranks (traces) of the three complete-reducibility projectors at `N = 4`, for the tensor fourth power of the 4-dimensional Dirac spinor `V` (`dim V^{⊗4} = 4⁴ = 256`). Reusing the general lemma `trace_permMat`, it establishes:
- `trace_projSym_four`: `tr(projSym 4) = 35` (`= dim Sym⁴V = C(7,4)`);
- `trace_projAnti_four`: `tr(projAnti 4) = 1` (`= dim Λ⁴V = C(4,4)`);
- `trace_projMixed_four`: `tr(projMixed 4) = 220` (the mixed-symmetry piece, `256 − 35 − 1`);
- `trace_decomposition_four`: the headline `35 + 1 + 220 = 256 = dim(V ⊗ V ⊗ V ⊗ V)`.

All four theorems are `sorry`-free with no external hypothesis; their only axioms are `propext`, `Classical.choice`, `Quot.sound` (verified with the axiom checker). The larger finite count (24 permutations over `4⁴ = 256` index tuples) is discharged by kernel `decide`/`norm_cast` under a raised `maxRecDepth`, with no `native_decide`. The full project builds green (8108 jobs).

`BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md` were updated with a new Wave 35 section (existing content left intact; the new summary is prepended). All work is committed and pushed.

Remaining open items are unchanged in kind: the external Wigner/Mackey backbone of the §A.4/A.5 classification, which the roadmap tracks as named-hypothesis work. The only remaining `sorry`s in the project are in the pre-existing `RiemannProof/RcpEuler.lean`, which the roadmap places out of scope.

# Summary of changes (latest run) — Wave 35: dimensions of the complete-reducibility summands at `N = 4`

Executed the next step of `FORMALIZATION_ROADMAP.md` (Wave 35), continuing the §A.3 Note 50 / Lemma 52 complete-reducibility thread past Wave 34's `N = 3` dimension count.

New module `BookProof/ChapterA3t.lean` (registered in `BookProof.lean`) computes the ranks (traces) of the three complete-reducibility projectors at `N = 4` for the tensor fourth power of the 4-dimensional Dirac spinor `V` (`dim V^{⊗4} = 4⁴ = 256`). It reuses Wave 33's general lemma `trace_permMat` (from `ChapterA3r`) and establishes:
- `trace_projSym_four`: `tr(projSym 4) = 35` (`= dim Sym⁴V = C(7,4)`);
- `trace_projAnti_four`: `tr(projAnti 4) = 1` (`= dim Λ⁴V = C(4,4)`);
- `trace_projMixed_four`: `tr(projMixed 4) = 220` (the mixed-symmetry piece, `256 − 35 − 1`);
- `trace_decomposition_four`: the headline `35 + 1 + 220 = 256 = dim(V ⊗ V ⊗ V ⊗ V)`.

By cycle type in `S₄`, `Σ_σ tr(permMat σ) = 256 + 6·64 + 8·16 + 3·16 + 6·4 = 840` gives `840/24 = 35`, and the signed sum `256 − 6·64 + 8·16 + 3·16 − 6·4 = 24` gives `24/24 = 1`. The `symMat`/`projAnti` proofs mirror the `N = 3` pattern; the larger finite count (24 permutations over `4⁴ = 256` index tuples) needed `set_option maxRecDepth 10000` for the kernel `decide`/`norm_cast` (no `native_decide`).

All four theorems are `sorry`-free with no `EXTERNAL` hypothesis; the axioms are only `propext`, `Classical.choice`, `Quot.sound` (verified with the axiom checker on `trace_decomposition_four`, `trace_projSym_four`). The full project builds green (8108 jobs). `BookProof/STATUS.md` (new Wave 35 section) and `ARISTOTLE_SUMMARY.md` were updated. All work is committed and pushed.

Remaining open items are unchanged in kind: the `EXTERNAL` Wigner/Mackey backbone of the §A.4/A.5 classification. The only remaining `sorry`s in the project are in the pre-existing `RiemannProof/RcpEuler.lean`, which the roadmap places out of scope.

# Summary of changes for run 9d615e3c-81fc-4325-91ea-93868e410e07
Executed the next step of `FORMALIZATION_ROADMAP.md` (Wave 34), continuing the §A.3 Note 50 / Lemma 52 complete-reducibility thread past Wave 33's `N = 2` dimension count.

New module `BookProof/ChapterA3s.lean` (registered in `BookProof.lean`) computes the ranks (traces) of the three complete-reducibility projectors at `N = 3` — the first case where the mixed-symmetry piece is nonzero — for the tensor cube of the 4-dimensional Dirac spinor `V` (`dim V^{⊗3} = 64`). It reuses Wave 33's general lemma `trace_permMat` and establishes:
- `trace_projSym_three`: `tr(projSym 3) = 20` (`= dim Sym³V`);
- `trace_projAnti_three`: `tr(projAnti 3) = 4` (`= dim Λ³V`);
- `trace_projMixed_three`: `tr(projMixed 3) = 40` (the mixed-symmetry piece);
- `trace_decomposition_three`: the headline `20 + 4 + 40 = 64 = dim(V ⊗ V ⊗ V)`.

All four are `sorry`-free with no `EXTERNAL` hypothesis; the finite count is discharged by `decide` (no `native_decide`), so the axioms are only `propext`, `Classical.choice`, `Quot.sound` (verified with the axiom checker). The full project builds green (8107 jobs). `BookProof/STATUS.md` (new Wave 34 section) and `ARISTOTLE_SUMMARY.md` were updated. All work is committed and pushed.

Remaining open items are unchanged in kind: the `EXTERNAL` Wigner/Mackey backbone of the §A.4/A.5 classification. The only remaining `sorry`s in the project are in the pre-existing `RiemannProof/RcpEuler.lean`, which the roadmap places out of scope.

# Summary of changes (latest run) — Wave 34: dimensions of the complete-reducibility summands at `N = 3`

Continued executing `FORMALIZATION_ROADMAP.md` with the next step (Wave 34),
building directly on Wave 33's `N = 2` dimension count (`ChapterA3r.lean`) and
the Wave 29–32 arbitrary-`N` complete-reducibility machinery
(`projSym`/`projAnti`/`projMixed` in `ChapterA3n`/`A3o`/`A3q`).

New module `BookProof/ChapterA3s.lean` (registered in `BookProof.lean`) computes
the ranks (traces) of the three complete-reducibility projectors at `N = 3` —
the **first** case with a nonzero mixed-symmetry piece.  Reusing Wave 33's
general lemma `trace_permMat` (the trace of a slot-braiding matrix counts the
index tuples it fixes, `= 4^{cycles(σ)}`), it establishes, without any
`EXTERNAL` hypothesis:

- `trace_projSym_three`: `tr (projSym 3) = 20` (`= dim Sym³V`);
- `trace_projAnti_three`: `tr (projAnti 3) = 4` (`= dim Λ³V`);
- `trace_projMixed_three`: `tr (projMixed 3) = 40` (the first nonzero mixed-symmetry piece);
- `trace_decomposition_three`: the headline count `20 + 4 + 40 = 64 = dim (V ⊗ V ⊗ V)`
  for the `N = 3` complete-reducibility decomposition `V^{⊗3} = Sym³V ⊕ Λ³V ⊕ (mixed)`.

All new declarations are `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound` — the finite ℕ count `Σ_σ #{a | a∘σ = a} = 120`
is discharged by `decide`, no `native_decide`; confirmed with the axiom checker
on `trace_decomposition_three` and `trace_projSym_three`).  The whole project
builds green (8107 jobs).  `BookProof/STATUS.md` (new Wave 34 section) and this
`ARISTOTLE_SUMMARY.md` were updated as requested.  All work is committed and
pushed.

Remaining open items are unchanged in kind: the `EXTERNAL` Wigner/Mackey
exhaustiveness backbone of the §A.4/A.5 classification.  The only remaining
`sorry`s anywhere in the project are in the pre-existing
`RiemannProof/RcpEuler.lean`, which the roadmap places out of scope.

# Summary of changes for run 4674b84d-20a2-48c8-8939-f985156c402e
Continued executing `FORMALIZATION_ROADMAP.md` with the next step (Wave 33), building on the arbitrary-`N` complete-reducibility machinery from earlier waves (`projSym`/`projAnti`/`projMixed` in `BookProof/ChapterA3n.lean`, `ChapterA3o.lean`, `ChapterA3q.lean`).

New module `BookProof/ChapterA3r.lean` (registered in `BookProof.lean`) supplies the dimension-counting payoff of §A.3 Note 50 (Weyl) / Lemma 52. Since each complete-reducibility projector is idempotent, its trace equals its rank — the dimension of the summand it projects onto. The file establishes, without any `EXTERNAL` hypothesis:
- `trace_permMat` (general `N`): the trace of a slot-braiding matrix `permMat σ` counts the index tuples `a : Fin N → Fin 4` fixed by `σ`;
- `trace_projSym_two`: `tr (projSym 2) = 10` (`= dim Sym²V`);
- `trace_projAnti_two`: `tr (projAnti 2) = 6` (`= dim Λ²V`, the Def 57 antisymmetric pinor pair);
- `trace_projMixed_two`: `tr (projMixed 2) = 0` (no mixed piece for `N = 2`);
- `trace_decomposition_two`: the headline count `10 + 6 + 0 = 16 = dim (V ⊗ V)` for `V ⊗ V = Sym²V ⊕ Λ²V`.

All new declarations are `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed with the axiom checker on the headline lemmas). The whole project builds green (8106 jobs). `BookProof/STATUS.md` (new Wave 33 section) and `ARISTOTLE_SUMMARY.md` were updated as requested. All work is committed and pushed.

Remaining open items are unchanged in kind: the `EXTERNAL` Wigner/Mackey exhaustiveness backbone of the §A.4/A.5 classification. The only remaining `sorry`s anywhere in the project are in the pre-existing `RiemannProof/RcpEuler.lean`, which the roadmap places out of scope.

# Summary of changes (latest run) — Wave 33: dimensions (ranks) of the complete-reducibility summands

Continued executing `FORMALIZATION_ROADMAP.md` with the next step (Wave 33),
building on Wave 29–32's arbitrary-`N` complete-reducibility machinery
(`projSym`/`projAnti`/`projMixed` in `ChapterA3n`/`A3o`/`A3q`).

New module `BookProof/ChapterA3r.lean` (registered in `BookProof.lean`) supplies
the **dimension-counting payoff** of §A.3 Note 50 (Weyl) / Lemma 52.  Each of the
three complete-reducibility projectors is idempotent, so its trace equals its
rank — the dimension of the summand it projects onto.  The file computes these in
the base case `N = 2` (the tensor square of the 4-dimensional Dirac spinor `V`),
still **without** the `EXTERNAL` Weyl hypothesis:

- `trace_permMat` (general `N`): `tr (permMat σ)` = number of index tuples
  `a : Fin N → Fin 4` fixed by the slot permutation `σ`;
- `trace_projSym_two`: `tr (projSym 2) = 10` (`= dim Sym²V`);
- `trace_projAnti_two`: `tr (projAnti 2) = 6` (`= dim Λ²V`, the Def 57 pinor pair);
- `trace_projMixed_two`: `tr (projMixed 2) = 0` (no mixed piece for `N = 2`);
- `trace_decomposition_two`: the headline count `10 + 6 + 0 = 16 = dim (V ⊗ V)`
  for `V ⊗ V = Sym²V ⊕ Λ²V`.

All declarations are `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`; verified via the axiom checker on
`trace_decomposition_two` and `trace_projSym_two`).  The full project builds
green (8106 jobs).  `BookProof/STATUS.md` (new Wave 33 section) and this file
were updated per the request; all work is committed and pushed.

Remaining open items are unchanged in kind: the `EXTERNAL` Wigner/Mackey
exhaustiveness backbone of the §A.4/A.5 Bargmann–Wigner/CPT classification.  The
only remaining `sorry`s in the project are in the pre-existing
`RiemannProof/RcpEuler.lean`, which the roadmap places out of scope.

# Summary of changes for run 1a6484c8-965b-4636-86e0-770b192bfb77
Continued executing `FORMALIZATION_ROADMAP.md` with the next step (Wave 32), building on Wave 31's concrete `N = 2` tensor-square decomposition.

New module `BookProof/ChapterA3q.lean` (registered in `BookProof.lean`) extends the complete-reducibility payoff of §A.3 Note 50 (Weyl) / Lemma 52 from `N = 2` to **arbitrary `N`**, still without the `EXTERNAL` Weyl hypothesis. It isolates the mixed-symmetry remainder (which appears for `N ≥ 3`) as the complementary projector `projMixed N := 1 − projSym N − projAnti N`, and proves the triple `{projSym N, projAnti N, projMixed N}` is a complete system of pairwise orthogonal, idempotent, full-Lorentz–invariant projectors for every `N ≥ 2`:
- `projSym_add_projAnti_add_projMixed` (sum to 1);
- orthogonality `projSym_mul_projMixed`, `projMixed_mul_projSym`, `projAnti_mul_projMixed`, `projMixed_mul_projAnti` (all 0);
- idempotency `projMixed_idem`;
- full-Lorentz invariance `projMixed_diagGen_comm`, `projMixed_uniform_comm`, `projMixed_spinGenDiag_comm`, `projMixed_parityDiag_comm`;
- `projMixed_two_eq_zero` (consistency with the `N = 2` case);
- headline `tensorPow_complete_reducibility`, realizing `V^{⊗N} = Sym^N V ⊕ Λ^N V ⊕ (mixed symmetry)`.

All declarations are `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`; verified via the axiom checker on the headline and `projMixed_two_eq_zero`). The full project builds green. `BookProof/STATUS.md` (new Wave 32 section) and `ARISTOTLE_SUMMARY.md` (new top section) were updated per the request. All work is committed and pushed.

Remaining open items are unchanged in kind: the `EXTERNAL` Wigner/Mackey exhaustiveness backbone of the §A.4/A.5 Bargmann–Wigner/CPT classification. The only remaining `sorry`s in the project are in the pre-existing `RiemannProof/RcpEuler.lean`, which the roadmap places out of scope.

# Summary of changes (latest run) — Wave 32: general-`N` complete reducibility via the mixed-symmetry complement

Continued executing `FORMALIZATION_ROADMAP.md`. Wave 31 had established the
concrete `N = 2` complete-reducibility decomposition `V ⊗ V = Sym²V ⊕ Λ²V`
(`BookProof/ChapterA3p.lean`) using the symmetrizer `projSym`
(`ChapterA3n`) and antisymmetrizer `projAnti` (`ChapterA3o`). The natural next
open item was the **general-`N`** form of Note 50 (Weyl complete reducibility) /
Lemma 52 — the mixed-symmetry pieces that appear for `N ≥ 3` — which can still
be done **without** the `EXTERNAL` Weyl hypothesis.

New work — module `BookProof/ChapterA3q.lean` (registered in `BookProof.lean`).
It isolates the mixed-symmetry remainder as the complementary projector
`projMixed N := 1 − projSym N − projAnti N` and shows the triple
`{projSym N, projAnti N, projMixed N}` is a complete system of pairwise
orthogonal, idempotent, full-Lorentz–invariant projectors for every `N ≥ 2`.
Deliverables, all `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`):
- `projSym_add_projAnti_add_projMixed`: the three projectors sum to `1`;
- `projSym_mul_projMixed` / `projMixed_mul_projSym` /
  `projAnti_mul_projMixed` / `projMixed_mul_projAnti`: pairwise orthogonality
  (`N ≥ 2`);
- `projMixed_idem`: the mixed projector is genuinely idempotent (`N ≥ 2`);
- `projMixed_diagGen_comm`, `projMixed_uniform_comm`,
  `projMixed_spinGenDiag_comm`, `projMixed_parityDiag_comm`: full-Lorentz
  invariance (diagonal `Spin⁺` and diagonal parity), inherited from the
  `projSym`/`projAnti` commutation lemmas;
- `projMixed_two_eq_zero`: at `N = 2` the mixed piece vanishes (consistency
  with Wave 31's `projSym 2 + projAnti 2 = 1`);
- `tensorPow_complete_reducibility`: the bundled headline for arbitrary
  `N ≥ 2` — the complete orthogonal idempotent system realizing
  `V^{⊗N} = Sym^N V ⊕ Λ^N V ⊕ (mixed symmetry)`.

No external/assumed hypotheses were introduced. The full project builds green
(8105 jobs); the new module is free of linter warnings, and
`tensorPow_complete_reducibility` / `projMixed_two_eq_zero` were verified
axiom-clean. `BookProof/STATUS.md` (new Wave 32 section) and this file were
updated per the request. All work is committed and pushed.

Remaining open items are unchanged in kind: the `EXTERNAL` Wigner/Mackey
exhaustiveness backbone of the §A.4/A.5 Bargmann–Wigner/CPT classification
(identifying the concrete mixed-symmetry summands with the abstract irreps
`V_{(m,n)}` still relies on the cited Weyl/Wigner backbone). The only remaining
`sorry`s in the project are in the pre-existing `RiemannProof/RcpEuler.lean`,
which the roadmap places out of scope.

# Summary of changes for run 398916f8-608f-49eb-86c1-4f90cbd2d390
Continued executing `FORMALIZATION_ROADMAP.md`. Waves 29–30 had built, for arbitrary `N`, the totally symmetric power (`BookProof/ChapterA3n.lean`, `projSym`) and its dual the totally antisymmetric power (`BookProof/ChapterA3o.lean`, `projAnti`). The natural next open item was the complete-reducibility payoff of §A.3 Note 50 (Weyl) / Lemma 52 — which, in the base case `N = 2`, can be proved outright without the `EXTERNAL` Weyl hypothesis.

New work — module `BookProof/ChapterA3p.lean` (registered in `BookProof.lean`), realizing the concrete decomposition `V ⊗ V = Sym²V ⊕ Λ²V` of the Lorentz representation via the complementary orthogonal projectors `projSym 2` / `projAnti 2`. Deliverables, all `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`):
- `sum_signC_eq_zero`: the signed group sum `Σ_{σ∈S_N} sgn(σ) = 0` once `N ≥ 2`;
- `projSym_mul_projAnti` / `projAnti_mul_projSym`: for `N ≥ 2` the symmetrizer and antisymmetrizer are orthogonal (products vanish);
- `projSym_add_projAnti_two`: for `N = 2` they are complementary (`projSym 2 + projAnti 2 = 1`);
- `tensorSquare_complete_reducibility`: the bundled headline — a complete system of complementary, orthogonal, idempotent projectors (the `EXTERNAL`-free `N = 2` instance of Note 50); each summand is full-Lorentz invariant by `ChapterA3n`/`ChapterA3o`.

No external/assumed hypotheses were introduced. The full project builds green (8104 jobs); the new module is free of long-line/whitespace linter warnings, and `tensorSquare_complete_reducibility` was verified axiom-clean. `BookProof/STATUS.md` (new Wave 31 section) and `ARISTOTLE_SUMMARY.md` (new top section) were updated per the request. All work is committed and pushed.

Remaining open items are unchanged in kind: the general-`N` `EXTERNAL` Weyl/Note-50 complete-reducibility layer (mixed-symmetry pieces for `N ≥ 3`) and the `EXTERNAL` Wigner/Mackey exhaustiveness backbone of the §A.4/A.5 Bargmann–Wigner/CPT classification. The only remaining `sorry`s in the project are in the pre-existing `RiemannProof/RcpEuler.lean`, which the roadmap places out of scope.

# Summary of changes (latest run) — Wave 31: concrete complete reducibility of the tensor square

Continued executing `FORMALIZATION_ROADMAP.md`. Waves 29–30 built, for arbitrary
`N`, the totally symmetric power (`BookProof/ChapterA3n.lean`, `projSym`) and its
dual the totally antisymmetric power (`BookProof/ChapterA3o.lean`, `projAnti`).
The natural next open item is the **complete-reducibility payoff** of §A.3
Note 50 (Weyl: finite-dimensional reps of `SL(2,ℂ)` are completely reducible)
and Lemma 52 — which, in the base case `N = 2`, can be proved *outright* without
the `EXTERNAL` Weyl hypothesis.

Added a new module `BookProof/ChapterA3p.lean` (registered in `BookProof.lean`)
realizing the concrete decomposition `V ⊗ V = Sym²V ⊕ Λ²V` of the Lorentz
representation via the pair of complementary orthogonal projectors
`projSym 2` / `projAnti 2`. Deliverables (all `sorry`-free, `axiom`-free — only
`propext`, `Classical.choice`, `Quot.sound`):
- `sum_signC_eq_zero`: the signed group sum `Σ_{σ∈S_N} sgn(σ) = 0` once `N ≥ 2`
  (left-multiply by a fixed transposition; the sign flips, so the sum equals its
  own negative);
- `projSym_mul_projAnti` / `projAnti_mul_projSym`: for `N ≥ 2` the symmetrizer
  and antisymmetrizer are orthogonal (their products vanish — the reindexed
  cross term factors through `Σ_σ sgn σ = 0`);
- `projSym_add_projAnti_two`: for `N = 2` they are complementary
  (`projSym 2 + projAnti 2 = 1`);
- `tensorSquare_complete_reducibility`: the bundled headline — `projSym 2` and
  `projAnti 2` form a complete system of complementary, orthogonal, idempotent
  projectors, the concrete `EXTERNAL`-free instance of Note 50 for the tensor
  square. Each summand is full-Lorentz invariant by `ChapterA3n`/`ChapterA3o`.

No external/assumed hypotheses were introduced. The full project builds green
(8104 jobs); the new module is free of long-line/whitespace linter warnings.
The only remaining `sorry`s are in the pre-existing `RiemannProof/RcpEuler.lean`,
which the roadmap places out of scope. Updated `BookProof/STATUS.md` (new
Wave 31 section) and this `ARISTOTLE_SUMMARY.md`. All work is committed and
pushed. Remaining open items are unchanged in kind: the general-`N` `EXTERNAL`
Weyl/Note-50 complete-reducibility layer (mixed-symmetry pieces for `N ≥ 3`) and
the `EXTERNAL` Wigner/Mackey exhaustiveness backbone of the §A.4/A.5
Bargmann–Wigner/CPT classification.

# Summary of changes for run a6ecca45-05a9-4a01-b732-6d08b23535ab
Continued executing `FORMALIZATION_ROADMAP.md`. The prior wave (`BookProof/ChapterA3n.lean`) built the arbitrary `N`-fold **symmetric** power for §A.3 Note 51 / Lemma 52; the natural next open item is its dual, explicitly called for by Def 57 (`Pinor₀` = the antisymmetric pair).

Added a new module `BookProof/ChapterA3o.lean` (registered in `BookProof.lean`) formalizing, for arbitrary `N`, the totally **antisymmetric** power (the `N`-fold exterior power `Λ^N V`). It reuses the tensor model of `ChapterA3n` verbatim (carrier `Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ`, the tensor operator `tensorPow`, the permutation representation `permMat`, the diagonal `Spin⁺` generator `diagGen`, the uniform parity operator `uniform`), changing only the group average from the trivial character to the sign character. Deliverables (all `sorry`-free):
- `projAnti N = (N!)⁻¹ • Σ_{σ∈S_N} sgn(σ)·permMat σ`, the total antisymmetrizer onto `Λ^N V`;
- `sum_signed_permMat_sq`: the signed group identity `(Σ_σ sgn(σ)·ρ(σ))² = N!·Σ_σ sgn(σ)·ρ(σ)`;
- `projAnti_idem`: `projAnti N` is a genuine projector;
- `projAnti_diagGen_comm` / `projAnti_uniform_comm` and the Lemma-52 payoff `projAnti_spinGenDiag_comm` (invariance under the diagonal `Spin⁺` generators `γ^μγ^ν`) and `projAnti_parityDiag_comm` (invariance under diagonal parity `γ⁰⊗…⊗γ⁰`) — i.e. the real antisymmetric power is automatically a full-Lorentz subrepresentation.

Together with `ChapterA3n` this completes the pair of totally (anti)symmetric tensor-power constructions of Notes 50–51 / Def 57. No external/assumed hypotheses were introduced. All new declarations are axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified via the axiom checker on `projAnti_idem` and `projAnti_parityDiag_comm`), and the new module is warning-free. The full project builds green (8103 jobs); the only remaining `sorry`s are in the pre-existing `RiemannProof/RcpEuler.lean`, which the roadmap places out of scope.

Updated `BookProof/STATUS.md` (new Wave 30 section) and, as requested, `ARISTOTLE_SUMMARY.md` (new top section). All work is committed and pushed. Remaining open items are unchanged in kind: the external Weyl/Note-50 complete-reducibility layer and the external Wigner/Mackey exhaustiveness backbone of the §A.4/A.5 Bargmann–Wigner/CPT classification.

# Summary of changes (latest run) — Wave 30: the arbitrary `N`-fold *antisymmetric* power

Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item past
the previous wave's arbitrary `N`-fold **symmetric** power
(`BookProof/ChapterA3n.lean`): the exact **dual** construction, the arbitrary
`N`-fold **antisymmetric** power (the `N`-fold exterior power `Λ^N V`) of §A.3
Note 51 / Lemma 52 / Def 57 (`Pinor₀` = the antisymmetric pair).

Added a new module `BookProof/ChapterA3o.lean` (registered in `BookProof.lean`),
reusing the tensor model of `ChapterA3n` verbatim — carrier
`MN N = Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ`, the tensor operator
`tensorPow`, the permutation representation `permMat`, the diagonal `Spin⁺`
generator `diagGen`, and the uniform parity operator `uniform` — and changing
only the group average from the trivial character to the **sign** character
`sgn : S_N → {±1}`. For arbitrary `N` it formalizes:

- **Total antisymmetrizer** `projAnti N = (N!)⁻¹ • Σ_{σ∈S_N} sgn(σ)·permMat σ`
  onto `Λ^N V`, with `signC σ = ((Equiv.Perm.sign σ : ℤ) : ℂ)`.
- **Signed group identity** `sum_signed_permMat_sq`:
  `(Σ_σ sgn(σ)·ρ(σ))² = N!·Σ_σ sgn(σ)·ρ(σ)`, via reindexing `ρ = στ` and the
  fact that `sgn` is a `{±1}`-valued homomorphism (`sgn(σ)·sgn(σ⁻¹ρ) = sgn(ρ)`).
- **Idempotency** `projAnti_idem`: `projAnti N` is a genuine projector.
- **Lemma 52 payoff (antisymmetric case)**: since every braiding `permMat σ`
  already commutes with `diagGen A` and `uniform A`, so does the signed average
  (`projAnti_diagGen_comm`, `projAnti_uniform_comm`). Specialising to the §A.3
  γ-matrix data, the exterior power is a **full-Lorentz** subrepresentation,
  invariant under the diagonal `Spin⁺` generators `γ^μγ^ν`
  (`projAnti_spinGenDiag_comm`) **and** under diagonal parity `γ⁰⊗…⊗γ⁰`
  (`projAnti_parityDiag_comm`). Together with `ChapterA3n` this completes the
  pair of totally (anti)symmetric tensor-power constructions of Notes 50–51 /
  Def 57.

All 6 declarations are `sorry`-free and axiom-clean (only `propext`,
`Classical.choice`, `Quot.sound`, confirmed via verification on `projAnti_idem`
and `projAnti_parityDiag_comm`), with no assumed/external hypothesis introduced.
The whole project builds green (8103 jobs); the new module is warning-free. The
only remaining `sorry`s are in the pre-existing `RiemannProof/RcpEuler.lean`,
which the roadmap places out of scope. Updated `BookProof/STATUS.md` (new
Wave 30 section). Remaining open items are unchanged in kind: the `EXTERNAL`
Weyl/Note-50 complete-reducibility layer and the `EXTERNAL` Wigner/Mackey
exhaustiveness backbone of the §A.4/A.5 Bargmann–Wigner/CPT classification.

---

# Summary of changes for run 695b17a8-6c92-4d74-a65a-53501e09f947
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item past the previous wave's threefold braiding / `S₃` symmetric-cube structure (`BookProof/ChapterA3m.lean`): the **arbitrary `N`-fold symmetric power** of §A.3 Note 51 / Lemma 52.

Added a new module `BookProof/ChapterA3n.lean` (registered in `BookProof.lean`). Rather than iterated Kronecker products it uses the clean `N`-fold tensor model with carrier `Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ` (tuple-indexed), and formalizes for arbitrary `N`:

- Tensor operator `tensorPow M a b = ∏ i, (M i)(a i)(b i)`, proven multiplicative (`tensorPow_mul`, via `Finset.prod_univ_sum`) and unital (`tensorPow_one`).
- Permutation representation `permMat σ a b = [b = a ∘ σ]`, a homomorphism from `S_N` (`permMat_mul`, `permMat_one`), and the braiding relation `permMat σ * tensorPow M = tensorPow (M ∘ σ⁻¹) * permMat σ` (`permMat_braiding`).
- Full-Lorentz invariance of the diagonal action: the diagonal `Spin⁺` generator `diagGen A = Σᵢ(1⊗…⊗A⊗…⊗1)` and the uniform parity operator `uniform A = A⊗…⊗A` each commute with every `permMat σ` (`permMat_diagGen_comm`, `permMat_uniform_comm`).
- Lemma-52 payoff (general `N`): the group identity `(Σ_{σ∈S_N} σ)² = N!·(Σ_{σ∈S_N} σ)` (`sum_permMat_sq`) makes the total symmetrizer `projSym N = (1/N!)·Σ_σ permMat σ` a genuine projector (`projSym_idem`) onto a full-Lorentz subrepresentation, invariant under the diagonal `Spin⁺` generators `γ^μγ^ν` (`projSym_spinGenDiag_comm`) and under diagonal parity `γ⁰⊗…⊗γ⁰` (`projSym_parityDiag_comm`). This generalises the concrete `N=2`/`N=3` symmetric-square/cube constructions to all `N`.

All 13 declarations are `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via verification on `projSym_idem`, `projSym_spinGenDiag_comm`, `projSym_parityDiag_comm`), with no assumed/external hypothesis introduced. The whole project builds green (8102 jobs); the only remaining `sorry`s are in the pre-existing `RiemannProof/RcpEuler.lean`, which the roadmap places out of scope. Proofs were cleaned of leftover `exact?`, unused simp args, over-long lines, and a missing trailing newline.

Updated `BookProof/STATUS.md` (new Wave 29 section) and `ARISTOTLE_SUMMARY.md` (new top section) as requested. Remaining open items are unchanged in kind: the external Weyl/Note-50 complete-reducibility layer and the cited Wigner/Mackey exhaustiveness backbone of the §A.4/A.5 classification. All changes committed and pushed.

# Summary of latest changes

Continued executing `FORMALIZATION_ROADMAP.md`, landing the **next open item**
past the previous wave's threefold braiding / `S₃` symmetric-*cube* structure
(`BookProof/ChapterA3m.lean`): the **arbitrary `N`-fold symmetric power** of §A.3
Note 51 / Lemma 52 — the general case toward which the two-fold (Wave 27, `S₂`)
and three-fold (Wave 28, `S₃`) constructions were building.

New module `BookProof/ChapterA3n.lean` (registered in `BookProof.lean`).  Instead
of iterated left-associated Kronecker products, it uses the clean `N`-fold tensor
model: the carrier `V^{⊗N}` is `Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ`, indexed
by tuples `a : Fin N → Fin 4`.  It formalizes, for *arbitrary* `N`:

- **Tensor operator** `tensorPow M a b = ∏ i, (M i) (a i) (b i)`, proven
  multiplicative (`tensorPow_mul`, via `Finset.prod_univ_sum`) and unital
  (`tensorPow_one`).
- **Permutation representation** `permMat σ a b = [b = a ∘ σ]`, a homomorphism
  from the symmetric group `S_N` (`permMat_mul`, `permMat_one`), and the
  **braiding relation** `permMat σ * tensorPow M = tensorPow (M ∘ σ⁻¹) * permMat σ`
  (`permMat_braiding`).
- **Full-Lorentz invariance of the diagonal action**: the diagonal `Spin⁺`
  generator `diagGen A = Σᵢ (1⊗…⊗A⊗…⊗1)` and the uniform parity operator
  `uniform A = A⊗…⊗A` each commute with every `permMat σ`
  (`permMat_diagGen_comm`, `permMat_uniform_comm`).
- **Lemma-52 payoff (general `N`)**: the group identity
  `(Σ_{σ∈S_N} σ)² = N!·(Σ_{σ∈S_N} σ)` (`sum_permMat_sq`, via `Fintype.card_perm`)
  makes the total symmetrizer `projSym N = (1/N!)·Σ_{σ∈S_N} permMat σ` a genuine
  projector (`projSym_idem`) onto a full-Lorentz subrepresentation:
  `projSym_diagGen_comm`/`projSym_spinGenDiag_comm` (diagonal `Spin⁺`-invariant)
  and `projSym_uniform_comm`/`projSym_parityDiag_comm` (parity-invariant).  This
  generalises the concrete `N = 2`/`N = 3` symmetric-square/cube constructions to
  all `N`.

All 13 declarations are `sorry`-free and axiom-clean (only `propext`,
`Classical.choice`, `Quot.sound`, confirmed via `lean_verify` on `projSym_idem`,
`projSym_spinGenDiag_comm`, `projSym_parityDiag_comm`), with **no `EXTERNAL`/assumed
hypothesis** introduced.  The whole project builds green (8102 jobs); the only
remaining `sorry`s in the build are in the pre-existing
`RiemannProof/RcpEuler.lean`, which the roadmap explicitly places out of scope.
Updated `BookProof/STATUS.md` (new Wave 29 section).  Remaining open items are
unchanged in kind: the `EXTERNAL` Weyl/Note-50 complete-reducibility layer and
the cited Wigner/Mackey exhaustiveness backbone of the §A.4/A.5 classification.
All changes committed and pushed.

---

# Summary of changes for run cb65663f-96b4-4184-93de-4a4517ad6bd5
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item past the previous wave's symmetric tensor-*square* braiding structure (`BookProof/ChapterA3l.lean`): the **threefold braiding / `S₃` symmetric-cube structure** of §A.3 Note 51 / Lemma 52 — the next step toward the arbitrary `N`-fold symmetric powers by which Note 51 builds the general irreps `V_{(m,n)}`.

New module `BookProof/ChapterA3m.lean` (registered in `BookProof.lean`), formalizing the three-fold tensor product `V ⊗ V ⊗ V` (carrier of the symmetric cube `V ⊙ V ⊙ V`, which contains the top irrep `V⁺_{3/2}`) on the `4×4 ⊗ 4×4 ⊗ 4×4` left-associated Kronecker model, together with the symmetric group `S₃` acting by braidings:

- Three transposition operators `swap12 = τ ⊗ 1` (built from `ChapterA3l.swap`), `swap23`, `swap13`, with braiding relations `swap12_kronecker`, `swap23_kronecker`, `swap13_kronecker`.
- The `S₃` (Coxeter) presentation: involutivity `swap12_sq`, `swap23_sq`, `swap13_sq` and the braid relation `swap12·swap23·swap12 = swap13 = swap23·swap12·swap23` (`braid_left`, `braid_right`, `braid_rel`).
- Full-Lorentz invariance of the diagonal action: the diagonal `Spin⁺` generator `spinGenDiag3` and diagonal parity `parityDiag3 = γ⁰⊗γ⁰⊗γ⁰` each commute with all three transpositions.
- Lemma-52 payoff: the total symmetrizer `projSym3 = (1/6)·Σ_{g∈S₃} ρ(g)` is a genuine projector (`projSym3_idem`, encoding `(Σg)² = 6·Σg`) onto a full-Lorentz subrepresentation — `projSym3_spinGenDiag_comm` and `projSym3_parityDiag_comm` — so the real symmetric-cube construction is automatically a full-Lorentz representation, exactly as at the symmetric-square level.

All 11 declarations are `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, confirmed by verification on `projSym3_idem` and `projSym3_parityDiag_comm`), with no `EXTERNAL`/assumed hypothesis introduced. The whole project builds green (8101 jobs); the only remaining `sorry`s in the build are in the pre-existing `RiemannProof/RcpEuler.lean`, which the roadmap explicitly places out of scope. Updated `BookProof/STATUS.md` (new Wave 28 section) and `ARISTOTLE_SUMMARY.md` (new top section). Remaining open items are unchanged in kind: extending Lemma 52 to arbitrary `N`-fold symmetric powers plus the cited Weyl/Note-50 layer, and the cited Wigner/Mackey exhaustiveness backbone of the §A.4/A.5 classification. All changes committed and pushed.

# Summary of changes — next steps (§A.3 Note 51 / Lemma 52: threefold braiding / `S₃` symmetric-cube structure)

Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item past the previous wave's symmetric tensor-*square* braiding structure (`BookProof/ChapterA3l.lean`): the **threefold braiding / `S₃` symmetric-cube structure** of §A.3 Note 51 / Lemma 52, the next step toward the arbitrary `N`-fold symmetric powers by which Note 51 builds the general irreps `V_{(m,n)}`.

New module `BookProof/ChapterA3m.lean` (registered in `BookProof.lean`). It formalizes the three-fold tensor product `V ⊗ V ⊗ V` — carrier of the symmetric cube `V ⊙ V ⊙ V`, which contains the top irrep `V⁺_{3/2}` — on the `4×4 ⊗ 4×4 ⊗ 4×4` left-associated Kronecker model (index type `((Fin 4 × Fin 4) × Fin 4)`), together with the action of the symmetric group `S₃` by braidings:

- **Three transposition (braiding) operators**: `swap12 = τ ⊗ 1` (built from `ChapterA3l.swap`), `swap23`, `swap13` (entrywise permutation matrices), with braiding relations `swap12_kronecker`, `swap23_kronecker`, `swap13_kronecker` (each conjugates a Kronecker product into the correspondingly permuted product).
- **The `S₃` (Coxeter) presentation**: involutivity `swap12_sq`, `swap23_sq`, `swap13_sq` (`τ²=1`) and the braid relation `swap12·swap23·swap12 = swap13 = swap23·swap12·swap23` (`braid_left`, `braid_right`, `braid_rel`).
- **Full-Lorentz invariance of the diagonal action**: the diagonal `Spin⁺` generator `spinGenDiag3 = A⊗1⊗1 + 1⊗A⊗1 + 1⊗1⊗A` and diagonal parity `parityDiag3 = γ⁰⊗γ⁰⊗γ⁰` each commute with all three transpositions (`swap12_spinGenDiag_comm`, …, `swap13_parityDiag_comm`).
- **Lemma 52 payoff (symmetric-cube step)**: the total symmetrizer `projSym3 = (1/6)·Σ_{g∈S₃} ρ(g)` is a genuine projector (`projSym3_idem`, encoding `(Σ_{g∈S₃} g)² = 6·Σ_{g∈S₃} g`) onto a full-Lorentz subrepresentation: `projSym3_spinGenDiag_comm` (diagonal `Spin⁺`-invariant) and `projSym3_parityDiag_comm` (parity-invariant). So, as at the symmetric-square level, the real symmetric-cube construction is automatically a representation of the full Lorentz group.

The module is fully sorry-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via verification on `projSym3_idem` and `projSym3_parityDiag_comm`), with no `EXTERNAL`/assumed hypothesis introduced. The whole project builds green (8101 jobs). Updated `BookProof/STATUS.md` (new Wave 28 section) and this file (new top section) as requested. Remaining open items are unchanged in kind: extending Lemma 52 to arbitrary `N`-fold symmetric powers plus the cited Weyl/Note-50 layer, and the cited Wigner/Mackey exhaustiveness backbone of the §A.4/A.5 classification. All changes committed and pushed.

# Summary of changes for run 1d4c77ba-7719-4d9d-8d6b-f0aabbc4f222
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item past the previous wave's tensor-square chiral decomposition (`BookProof/ChapterA3k.lean`): the **symmetric tensor-square (braiding) structure** of §A.3 Note 51 / Lemma 52.

New module `BookProof/ChapterA3l.lean` (registered in `BookProof.lean`). Note 51 builds the general irreps `V_{(m,n)}` as *symmetric* tensor powers of the chiral spinors, so this file introduces the braiding (swap) operator `τ : u ⊗ v ↦ v ⊗ u` on `V ⊗ V` — the commutation matrix `τ_{(i,j),(k,l)} = [i=l ∧ j=k]` on the `4×4 ⊗ 4×4` Kronecker model of §A.3 — and the symmetric/antisymmetric decomposition it induces:

- Braiding relation `swap_kronecker` (`τ·(A⊗B) = (B⊗A)·τ`), involutivity `swap_sq` (`τ²=1`), and exchange of the two per-slot chirality operators (`swap_chir1`, `swap_chir2`).
- `τ` commutes with the diagonal Lorentz/parity action (`swap_spinGenDiag_comm`, `swap_parityDiag_comm`), fixes the pure chirality blocks and braids the mixed ones (`swap_projLL_comm`, `swap_projRR_comm`, `swap_swaps_LR_RL`, `swap_swaps_RL_LR`).
- Symmetric/antisymmetric projectors `projSym = ½(1+τ)`, `projAsym = ½(1-τ)` with idempotency, complementarity (`projSym_add_projAsym`), and orthogonality.
- Payoff: the symmetric tensor square `V ⊙ V` is a full-Lorentz subrepresentation — it commutes with both the diagonal `Spin⁺` action and diagonal parity (`projSym_spinGenDiag_comm`, `projSym_parityDiag_comm`; likewise for the antisymmetric part) — so, unlike a single pure chirality block, the symmetric (real) tensor construction is automatically a full-Lorentz representation, the Lemma-52 mechanism at the symmetric-tensor-power level. `projLL_projSym_comm` places the pure `(1,0)` block inside the symmetric square.

The module is fully sorry-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via verification), with no `EXTERNAL`/assumed hypothesis introduced. The whole project builds green (8100 jobs). Updated `BookProof/STATUS.md` (new Wave 27 section) and `ARISTOTLE_SUMMARY.md` (new top section) as requested. Remaining open items are unchanged in kind: extending Lemma 52 to arbitrary N-fold symmetric powers plus the cited Weyl/Note-50 layer, and the cited Wigner/Mackey exhaustiveness backbone of the §A.4/A.5 classification. All changes committed and pushed.

# Summary of changes — next steps (§A.3 Note 51 / Lemma 52: symmetric tensor-square braiding structure)
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item after the previous wave's tensor-square chiral decomposition (`ChapterA3k`): the **symmetric tensor-square (braiding) structure** of Note 51 / Lemma 52 (book §A.3, Notes 50–51).

**New module `BookProof/ChapterA3l.lean`** (registered in `BookProof.lean`). Note 51 builds the general irreps `V_{(m,n)}` as *symmetric* tensor powers of the chiral spinors, so this file introduces the **braiding (swap) operator** `τ : u ⊗ v ↦ v ⊗ u` on `V ⊗ V` — the commutation matrix `τ_{(i,j),(k,l)} = [i=l ∧ j=k]` on the `4×4 ⊗ 4×4` Kronecker model of §A.3 — and the symmetric/antisymmetric decomposition it induces:

- **Braiding relation** `swap_kronecker` (`τ·(A⊗B) = (B⊗A)·τ`), involutivity `swap_sq` (`τ²=1`), and the exchange of the two per-slot chirality operators (`swap_chir1`, `swap_chir2`).
- **`τ` commutes with the diagonal Lorentz/parity action** (`swap_spinGenDiag_comm`, `swap_parityDiag_comm`), and **fixes the pure chirality blocks while braiding the mixed ones** (`swap_projLL_comm`, `swap_projRR_comm`, `swap_swaps_LR_RL`).
- **Symmetric/antisymmetric projectors** `projSym = ½(1+τ)`, `projAsym = ½(1-τ)` with idempotency, complementarity, and orthogonality.
- **Payoff:** the symmetric tensor square `V ⊙ V` is a **full-Lorentz** subrepresentation — it commutes with both the diagonal `Spin⁺` action **and** diagonal parity (`projSym_spinGenDiag_comm`, `projSym_parityDiag_comm`), so — unlike a single pure chirality block (`ChapterA3k.projLL_not_parity_invariant`) — the symmetric (real) tensor construction is automatically a representation of the full Lorentz group, the Lemma-52 mechanism at the symmetric-tensor-power level.

The module is fully `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `lean_verify`); no `EXTERNAL`/assumed hypothesis is introduced. The whole project builds green (8100 jobs). Updated `ARISTOTLE_SUMMARY.md` (this section) and `BookProof/STATUS.md` (new Wave 27 section). Remaining open items are unchanged in kind: extending Lemma 52 to arbitrary `N`-fold symmetric powers plus the cited Weyl/Note-50 layer, and the cited Wigner/Mackey exhaustiveness backbone of the §A.4/A.5 Bargmann–Wigner/CPT classification. All changes committed and pushed.

# Summary of changes for run b3e483a9-8bff-420e-832d-d0a3cf1853b1
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item after the previous wave's §A.4 Prop 81 Bargmann–Wigner rep group laws: the **tensor-power step of Lemma 52** (book §A.3, Notes 50–51).

**New module `BookProof/ChapterA3k.lean`** (registered in `BookProof.lean`) takes the next step past the `m=n=½` base case (`ChapterA3j`) of the finite-dim real-irrep classification. It formalizes the first nontrivial tensor power `V ⊗ V` — a 16-dimensional space modeled by the Kronecker product `4×4 ⊗ 4×4` of the §A.3 Majorana Clifford model — in which the four chirality blocks `V⁺⊗V⁺` (label `(1,0)`), `V⁻⊗V⁻` (`(0,1)`), and the mixed `V⁺⊗V⁻`, `V⁻⊗V⁺` appear explicitly, and the two structural facts of Lemma 52 are proved:

- Per-slot chirality operators `iγ⁵⊗1`, `1⊗iγ⁵` (square to −1, commute), the diagonal `Spin⁺` action `γ^μγ^ν⊗1 + 1⊗γ^μγ^ν`, and the diagonal parity `γ⁰⊗γ⁰` (an involution, anticommuting with each chirality).
- The four chirality projectors decompose the identity (`projSum`), and the two pure blocks are diagonal-`Spin⁺` subrepresentations.
- **Payoff:** diagonal parity intertwines `V⁺⊗V⁺ ↔ V⁻⊗V⁻` (i.e. `(1,0) ↔ (0,1)`) and swaps the mixed blocks; the headline `projLL_not_parity_invariant` shows the pure `(1,0)` block is not parity-invariant, so the real full-Lorentz irrep must glue `V_{(m,n)}` to its parity image `V_{(n,m)}` — the Lemma 52 mechanism, now at the tensor-power level.

The module is fully `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`); no `EXTERNAL`/assumed hypothesis is introduced. The whole project builds green (8099 jobs). Proofs were kept clean (no `native_decide`, no leftover `exact?`).

Updated `ARISTOTLE_SUMMARY.md` (new top section) and `BookProof/STATUS.md` (new Wave 26 section) to record this work. Remaining open items are unchanged in kind: extending Lemma 52 to arbitrary `N`-fold symmetric powers plus the cited Weyl/Note-50 layer, and the cited Wigner/Mackey exhaustiveness backbone of the §A.4/A.5 Bargmann–Wigner/CPT classification. All changes committed and pushed.

# Summary of changes — next steps (§A.3 Notes 50–51 / Lemma 52 tensor-power chiral decomposition)
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item after the previous wave's §A.4 Prop 81 Bargmann–Wigner rep group laws: the **tensor-power step of Lemma 52** — the mechanism by which the finite-dim real irreps `V_{(m,n)}` are built from symmetric tensor powers of the chiral spinors and glued by parity to `V_{(n,m)}` (book §A.3, line ~5560).

New module `BookProof/ChapterA3k.lean` (registered in `BookProof.lean`) takes the next step past the `m=n=½` base case of `ChapterA3j`: it formalizes the **first nontrivial tensor power** `V ⊗ V` (a 16-dimensional space, modeled by the Kronecker product `4×4 ⊗ 4×4` of the Majorana model of §A.3), where the four chirality blocks `V⁺⊗V⁺`, `V⁻⊗V⁻`, `V⁺⊗V⁻`, `V⁻⊗V⁺` appear explicitly. It is fully `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`; verified via `#print axioms` on `projLL_not_parity_invariant`, `parity_swaps_LL_RR`, `parityDiag_sq`, `chir2_spinGenDiag_comm`, `projSum`). The whole project builds green (8099 jobs). No `EXTERNAL`/assumed hypothesis is introduced (Note 50 / Weyl complete reducibility and the extension to arbitrary `N`-fold symmetric powers remain the cited backbone).

Contents (all Kronecker-algebra consequences of the base-case facts of `ChapterA3j`):
- **Per-slot chirality operators** `chir1 = iγ⁵⊗1`, `chir2 = 1⊗iγ⁵`: `chir1_sq`, `chir2_sq` (`(iγ⁵)⊗-part squares to -1`), `chir1_chir2_comm` (commute, different slots).
- **Diagonal `Spin⁺` action** `spinGenDiag μ ν = γ^μγ^ν⊗1 + 1⊗γ^μγ^ν`: `chir1_spinGenDiag_comm`, `chir2_spinGenDiag_comm` (each chirality operator commutes with the diagonal Lorentz generator).
- **Diagonal parity** `parityDiag = γ⁰⊗γ⁰`: `parity_chir1_anticomm`, `parity_chir2_anticomm` (anticommutes with each per-slot chirality); `parityDiag_sq` (`(γ⁰⊗γ⁰)² = 1`, an involution).
- **Four chirality projectors** `projLL, projLR, projRL, projRR = P_{L/R}⊗P_{L/R}`: `projSum` (`P_LL+P_LR+P_RL+P_RR = 1`, complete decomposition); `projLL_spinGenDiag_comm`, `projRR_spinGenDiag_comm` (the pure blocks are diagonal-`Spin⁺` subrepresentations).
- **Parity gluing (Lemma 52 payoff)**: `parity_swaps_LL_RR` / `parity_swaps_RR_LL` (`γ⁰⊗γ⁰` intertwines `V⁺⊗V⁺ ↔ V⁻⊗V⁻`, i.e. `(1,0) ↔ (0,1)`), `parity_swaps_LR_RL` (swaps the mixed `(½,½)` blocks); `projLL_ne_projRR`; headline **`projLL_not_parity_invariant`** — the pure `(1,0)` block is not parity-invariant, so a single pure-chirality `Spin⁺`-subrep is not full-Lorentz irreducible and the real irrep must combine `V_{(m,n)}` with its parity image `V_{(n,m)}` (the mechanism of Lemma 52, now at the tensor-power level).

Updated `ARISTOTLE_SUMMARY.md` (this section) and `BookProof/STATUS.md` (new Wave 26 section). Remaining open items are unchanged in kind: the extension of Lemma 52 to arbitrary `N`-fold symmetric powers plus the `EXTERNAL` Weyl/Note-50 layer, and the `EXTERNAL` Wigner/Mackey exhaustiveness backbone of the §A.4/A.5 Bargmann–Wigner/CPT classification. All changes committed and pushed.

---

# Summary of changes for run 8e508b5a-1898-4930-8648-428ced618ecd
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open §A.4 item after the previous wave's Proposition 87 localizability exclusions.

New module `BookProof/ChapterA4g.lean` (registered in `BookProof.lean`) formalizes the concrete, self-contained **group-representation axioms of the little-group and translation factors of the Bargmann–Wigner Poincaré representations** — roadmap §A.4 Notes 80–83 / Proposition 81 ("state the reps as structures and verify the group-rep axioms for the given `L_S, T_a`"). It is fully `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`; verified via the axiom check on `SUtwo_mul_mem`, `transPhase_add`, `rotGen_projPos_comm`). The whole project builds green (8098 jobs); the only remaining `sorry` warnings anywhere are the pre-existing ones in `RiemannProof/RcpEuler.lean`, which the roadmap handles separately. No `EXTERNAL`/assumed hypothesis is introduced.

Contents (on the 2×2 little-group models of ChapterA4c/A4d and the 4×4 Majorana model of §A.3/§A.5):
- Massive little group `SU(2)`, spin-½ defining rep: `SUtwo_one_mem`, `SUtwo_mul_mem` (closure, `L_{ST}=L_S L_T`), `SUtwo_conjTranspose_mem`/`SUtwo_mul_conjTranspose` (`S⁻¹ = S† ∈ SU(2)`).
- Massless little group `SE(2)`: `SEtwo_one_mem`, `SEtwo_mul_mem`.
- Translation factor `T_a(p⃗)=e^{i p⃗·a⃗}` (`transPhase`): `transPhase_add`, `transPhase_zero`, `transPhase_abs` (unitarity).
- Massive-rep constraint preservation: the spatial rotation generators `γⁱγʲ` (`rotGen`) commute with the energy-sign operator `iγ⁰` (`rotGen_enSign_comm`), hence with the positive-energy Dirac projector `P₊` (`rotGen_projPos_comm`) — the massive little-group action preserves the positive-energy constraint subspace.

Updated `ARISTOTLE_SUMMARY.md` (new top section) and `BookProof/STATUS.md` (new Wave 25 section) to record this work and the remaining open items (Bargmann–Wigner classification exhaustiveness of Props 81/87/88 with the external Wigner/Mackey backbone; the Lemma 52 symmetric-tensor-power generalization; the external Wigner/Mackey bundle). All changes committed and pushed.

# Summary of changes — next steps (§A.4 Prop 81 / Notes 80–83 Bargmann–Wigner rep group laws)
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open §A.4 item after the previous wave's Prop 87 localizability exclusions: the concrete, self-contained **group-representation axioms of the massive/massless little-group and translation factors of the Bargmann–Wigner Poincaré representations** (roadmap §A.4 Notes 80–83 / Proposition 81 — the directive to "state the reps as structures and verify the group-rep axioms for the given `L_S, T_a`").

New module `BookProof/ChapterA4g.lean` (registered in `BookProof.lean`), fully `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`; verified with `lean_verify` on `SUtwo_mul_mem`, `transPhase_add`, `rotGen_projPos_comm`). The whole project builds green (8098 jobs); the only `sorry` warnings anywhere remain the pre-existing ones in `RiemannProof/RcpEuler.lean`, which the roadmap handles separately. No `EXTERNAL`/assumed hypothesis is introduced — Wigner 1939 exhaustiveness (that these are *all* the irreps) remains the cited backbone, not these axiom checks.

Contents (on the 2×2 little-group models of §A.4c/§A.4d and the 4×4 Majorana model of §A.3/§A.5):
- **Massive little group `SU(2)` — spin-½ defining-rep axioms:** `SUtwo_one_mem` (identity), `SUtwo_mul_mem` (closure under composition, `L_{ST}=L_S L_T`), `SUtwo_conjTranspose_mem` and `SUtwo_mul_conjTranspose` (`S⁻¹ = S†` again in `SU(2)`).
- **Massless little group `SE(2)` — discrete-helicity-rep axioms:** `SEtwo_one_mem`, `SEtwo_mul_mem`.
- **Translation factor `T_a(p⃗)=e^{i p⃗·a⃗}`:** `transPhase` with `transPhase_add` (`T_{a+b}=T_a T_b`), `transPhase_zero` (`T_0=1`), `transPhase_abs` (`|T_a|=1`, unitarity of the abelian translation subgroup).
- **Massive-rep constraint preservation:** the spatial rotation generators `γⁱγʲ` (`rotGen`, `SU(2)` Lie algebra) commute with the energy-sign operator `iγ⁰` (`rotGen_enSign_comm`, via the integer-model `decide` lemma `rotGenZ_coeffMass1Z_comm`) and hence with the positive-energy Dirac projector `P₊` (`rotGen_projPos_comm`): the massive little-group action preserves the positive-energy (Dirac) constraint subspace.

---

# Summary of changes for run e64e8637-ebae-442b-89e1-0d5926ce8b72
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open §A.4 item after the previous wave's Prop 88 / Corollary 1 core and Lemma 52 chiral core: the concrete algebraic cores of the **three exclusion lemmas of §A.4 Proposition 87** (the roadmap's directive to "state the three exclusions as lemmas").

New module `BookProof/ChapterA4f.lean` (registered in `BookProof.lean`), fully `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`; verified with `lean_verify` on `infinite_spin_excluded` and `no_tachyon`). The whole project builds green (8097 jobs); the only `sorry` warnings anywhere are the pre-existing ones in `RiemannProof/RcpEuler.lean`, which the roadmap explicitly handles separately. No `EXTERNAL`/assumed hypothesis is introduced — Wigner little-group theory + Mackey imprimitivity remain the cited backbone of the exhaustiveness clause, not of these reductions.

Proposition 87 (any localizable unitary Poincaré representation is a direct sum of massive / massless-discrete-helicity irreducibles) is proved by ruling out three families. The module formalizes the honest, self-contained algebraic core of each, on the 2×2 Pauli / 4×4 Majorana models of §A.3–§A.5:
- Exclusion 1 (no tachyons, m² ≥ 0): `massSq_nonneg` and `no_tachyon` — the real energy symbol squares to (|p|² − (m₁²+m₂²))·1, so the physical mass² is a sum of squares.
- Exclusion 2 (zero-momentum point): `zeroMomentum_symbol` — at p = 0 the symbol reduces to the pure mass operator with square −(m₁²+m₂²)·1, so the single zero-momentum point is a measure-zero, non-invariant subset.
- Exclusion 3 (no infinite/continuous spin): on the SE(2) massless little group of Prop 79, the z-boost `boostZ l = diag(l, l⁻¹)` conjugates an SE(2) element while fixing the SO(2) angle (`boostZ_preserves_angle`) and scaling the translation modulus by l⁻² (`boostZ_scales_translation`), keeping it in SE(2) (`boostZ_conj_mem`); headline `infinite_spin_excluded` shows the z-boost conjugate can realize any nonzero translation label, so there is no boost-invariant nonzero SE(2) translation modulus.
Supporting algebra: `boostZ_det`, `boostZ_mul_inv`.

I also updated `ARISTOTLE_SUMMARY.md` (new top section) and `BookProof/STATUS.md` (new wave-24 section), each recording the result and the remaining open items (Props 81/87/88 exhaustiveness with the external Wigner/Mackey backbone; the Lemma 52 symmetric-tensor-power generalization; and the external Wigner/Mackey bundle). All changes are committed and pushed.

# Summary of changes — §A.4 Prop 87: the localizability exclusion lemmas (wave 24)

Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open §A.4 item
after the wave-22 Prop 88 / Corollary 1 core and the wave-23 Lemma 52 chiral
core: the concrete algebraic cores of the **three exclusion lemmas of §A.4
Proposition 87** (book §A.4, line ~5636 — the roadmap's directive to state the
three exclusions as lemmas).

New module `BookProof/ChapterA4f.lean` (registered in `BookProof.lean`), fully
`sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`;
verified with `lean_verify` on `infinite_spin_excluded` and `no_tachyon`). The
whole project builds green (8097 jobs). No `EXTERNAL` hypothesis is introduced —
Wigner little-group theory + Mackey imprimitivity remain the cited backbone of
the decomposition/exhaustiveness clause of Prop 87, not of these reductions.

Prop 87 (any localizable unitary Poincaré rep is a direct sum of massive /
massless-discrete-helicity irreducibles) is proved by ruling out three families
of irreducibles as localizable subspaces. This module formalizes the honest,
self-contained algebraic core of each exclusion on the `2x2` Pauli / `4x4`
Majorana models of §A.3–§A.5:

- Exclusion 1 — no tachyons (`m² ≥ 0`): `massSq_nonneg` (`0 ≤ m₁²+m₂²`) and
  `no_tachyon` (the real §A.5 energy symbol squares to `(|p|² − (m₁²+m₂²))·1`, so
  the physical mass² is a sum of squares, excluding a tachyonic `m²<0` case).
- Exclusion 2 — the zero-momentum point: `zeroMomentum_symbol` (at `p = 0` the
  energy symbol reduces to the pure mass operator with square `−(m₁²+m₂²)·1`, so
  the single zero-momentum point is a measure-zero, non-invariant subset).
- Exclusion 3 — no infinite (continuous) spin: on the `SE(2)` massless little
  group of Prop 79 (`ChapterA4d.SEtwo`), the `z`-boost `boostZ l = diag(l, l⁻¹)`
  conjugates an `SE(2)` element to `!![a,0; l⁻²c, a⁻¹]`: `boostZ_preserves_angle`
  (fixes the `SO(2)` angle), `boostZ_scales_translation` (scales the translation
  modulus by `l⁻²`), `boostZ_conj_mem` (conjugate stays in `SE(2)`), and headline
  `infinite_spin_excluded` — the `z`-boost conjugate realizes any nonzero
  translation label, so there is no boost-invariant nonzero `SE(2)` translation
  modulus (continuous/infinite spin is excluded).

Supporting `boostZ` algebra: `boostZ_det`, `boostZ_mul_inv`. `STATUS.md` gets a
new wave-24 section; remaining open items are unchanged (Props 81/87/88
exhaustiveness with `EXTERNAL` Wigner/Mackey, the Lemma 52
symmetric-tensor-power generalization, and the N7 Wigner/Mackey bundle). All
changes committed and pushed.

# Summary of changes for run 06dab516-9872-4443-9682-be06d60c977e
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item after wave 22: the concrete algebraic **base case** of the §A.3 **Notes 50–51 / Lemma 52** finite-dimensional-irrep classification (the roadmap's remaining §A.3 classification residue, previously flagged "still open: Lemma 52 real-irrep classification").

New module `BookProof/ChapterA3j.lean` (registered in `BookProof.lean`), fully `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified with `lean_verify` on the headline results). The whole project builds green (8096 jobs) with no new linter warnings. No `EXTERNAL`/assumed hypothesis is introduced — Note 50 (Weyl complete reducibility) and the symmetric-tensor-power generalization to arbitrary (m,n) remain the cited backbone.

The module is the chirality analogue of the energy-sign story of `ChapterA4e`, built on the 4×4 Majorana Clifford model of §A.3. Since the chirality operator iγ⁵ squares to −1, its eigenvalues are ±i and the chiral projectors P_{L/R} = ½(1 ∓ i·iγ⁵) live over ℂ. It establishes:
- the chirality operator and Spin⁺(3,1) generators, with iγ⁵ commuting with every even Clifford element γ^μγ^ν and anticommuting with γ⁰;
- the two chiral projectors and the full projector algebra (complementarity, idempotence, orthogonality);
- Note 51 core: each chiral projector commutes with every Spin⁺ generator, so the chiral subspaces V_L, V_R are genuine connected-Lorentz subrepresentations (the Weyl irreps V⁺_½, V⁻_½);
- Lemma 52 core: the parity operator γ⁰ intertwines the two chiral projectors (P_L γ⁰ = γ⁰ P_R), gluing V_{(m,n)} to its parity image V_{(n,m)};
- headline `chirality_not_parity_invariant`: γ⁰ does not commute with P_L, so a single-chirality Spin⁺-irrep is not full-Lorentz irreducible — the mechanism underlying Lemma 52 (real irreps are automatically full-Lorentz projective reps).

I also updated `ARISTOTLE_SUMMARY.md` (new top section) and `BookProof/STATUS.md` (new wave-23 section), each recording the result and the remaining open items (the full symmetric-tensor-power generalization of Lemma 52 plus the EXTERNAL Weyl layer; the §A.4/A.5 Bargmann–Wigner/CPT exhaustiveness layer; and the N7 external Wigner/Mackey bundle). All changes are committed and pushed.

# Summary of changes — §A.3 Notes 50–51 / Lemma 52: the chiral (`γ⁵`) decomposition core

Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item after wave 22: the concrete algebraic **base case** of the §A.3 **Notes 50–51 / Lemma 52** finite-dimensional-irrep classification (book §A.3, line ~5560). This is the roadmap's remaining §A.3 classification residue (`ARISTOTLE_SUMMARY.md`/`STATUS.md` "still open: Lemma 52 real-irrep classification").

New module `BookProof/ChapterA3j.lean` (registered in `BookProof.lean`), fully `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified via `lean_verify` on the headlines). The whole project builds green (8096 jobs) with no new linter warnings. **No `EXTERNAL` hypothesis** is introduced — Note 50 (Weyl complete reducibility) and the symmetric-tensor-power generalization to arbitrary `(m,n)` remain the cited backbone, not this algebraic base case.

Built on the `4×4` Majorana Clifford model of §A.3 (`ChapterA3.mgamma`, `mgamma5`), this is the exact chirality analogue of the energy-sign story of `ChapterA4e`. The chirality operator `iγ⁵ = mgamma5` squares to `-1` (`mgamma5_sq`), so its eigenvalues are `±i` and the chiral projectors `P_{L/R} = ½(1 ∓ i·iγ⁵)` live over `ℂ`. The module provides:
- `chir` (`iγ⁵`), `spinGen μ ν` (`γ^μγ^ν`, the `Spin⁺(3,1)` generators), `chir_sq`.
- `chir_mgamma_anticomm`, `chir_spinGen_comm` (`iγ⁵` commutes with every even Clifford element `γ^μγ^ν`), `chir_parity_anticomm` (`iγ⁵` anticommutes with `γ⁰`).
- The chiral projectors `projChirL`, `projChirR` and the full projector algebra: complementarity (`projChirL_add_projChirR`), idempotence (`projChirL_idem`, `projChirR_idem`), orthogonality (`projChirL_mul_projChirR`) — genuine complementary projectors.
- **Note 51 core** (`projChirL_spinGen_comm` / `projChirR_spinGen_comm`): each chiral projector commutes with every `Spin⁺` generator, so `V_L = P_L V` and `V_R = P_R V` are genuine connected-Lorentz subrepresentations — the Weyl / chiral irreps `V⁺_½`, `V⁻_½`.
- **Lemma 52 core** (`parity_swaps_chirL` / `parity_swaps_chirR`): the parity operator `γ⁰` intertwines the two chiral projectors, `P_L γ⁰ = γ⁰ P_R`, so parity glues `V_{(m,n)}` to its parity image `V_{(n,m)}`.
- `projChirL_parity_commutator` — `[P_L, γ⁰] = i·γ⁰(iγ⁵)`, an explicit nonzero matrix.
- headline **`chirality_not_parity_invariant`** — there is a parity operator (`γ⁰`) that does not commute with `P_L`; hence a single-chirality `Spin⁺`-irrep is not full-Lorentz irreducible, so the real full-Lorentz irrep must combine `V_{(m,n)}` with `V_{(n,m)}` — the mechanism underlying the Lemma 52 classification (unlike complex irreps, real irreps are automatically full-Lorentz projective reps).

I also updated `BookProof/STATUS.md` (new wave-23 section). Remaining open items after this wave: the full symmetric-tensor-power generalization of Lemma 52 to arbitrary `(m,n)` plus the `EXTERNAL` Weyl/Note-50 layer; the exhaustiveness layer of §A.4/A.5 Bargmann–Wigner/CPT (`EXTERNAL` Wigner/Mackey); and the N7 external Wigner/Mackey bundle. All changes committed and pushed.

# Summary of changes for run fdca8f10-8160-4370-a2ae-116723a078bd
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item after the previously-recorded wave 21: the concrete algebraic core of the §A.4 CPT / "causality ⇒ antiparticles" statement (book §A.4, Props 87–88 and Corollary 1). This fulfills the roadmap's explicit "prove the reductions … the projector-non-conservation in Prop 88 / Cor 1" directive for the §A.4/A.5 classification layer.

New module `BookProof/ChapterA4e.lean` (registered in `BookProof.lean`), fully `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified on the headlines). The whole project builds green (8095 jobs) with no new linter warnings. No external/assumed hypotheses are introduced — Wigner/Mackey enter only in the exhaustiveness clauses of Props 87/88, which remain the cited backbone.

Built on the existing 4×4 Majorana Clifford model of §A.3/§A.5, the module provides:
- `enSign` (iγ⁰) and `spatialOp j` (γʲγ⁰), with `enSign_sq : iγ⁰·iγ⁰ = -1` and the generalized Clifford anticommutation `{iγ⁰, γʲγ⁰} = 0` (`enSign_spatialOp_anticomm`).
- The complex energy-sign projectors P± = ½(1 ∓ i·iγ⁰) and the full projector algebra: complementarity (`projPos_add_projNeg`), idempotence (`projPos_idem`, `projNeg_idem`), orthogonality (`projPos_mul_projNeg`).
- Prop 88 core (`spatialOp_swaps_pos`/`spatialOp_swaps_neg`): every spatial-gradient operator intertwines the two sign projectors, so a positive-energy subspace is mapped onto the negative one (antiparticles).
- Headline `energy_sign_not_conserved` (Cor 1 core): a spatial operator does not commute with P₊, so a full-Poincaré-irreducible localizable representation cannot use the non-conserved iγ⁰-sign projectors — the reduction underlying the CPT / position-operator payoff.

I also updated `BookProof/STATUS.md` (new wave-22 section) and `ARISTOTLE_SUMMARY.md` (new top section), each recording the result and the remaining open items (Lemma 52 real-irrep classification; the external-Wigner/Mackey exhaustiveness layer of §A.4/A.5; the N7 external bundle). All changes are committed and pushed.

# Summary of changes for run — §A.4 Props 88 / Corollary 1: the CPT / antiparticle payoff (work-package N4)

Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item after
wave 21: the concrete algebraic core of the **§A.4 CPT / "causality ⇒
antiparticles"** statement (book §A.4, Props 87–88 and Corollary 1). This is the
roadmap's explicit "prove the reductions ... the projector-non-conservation in
Prop 88 / Cor 1" directive for the §A.4/A.5 classification layer.

New module `BookProof/ChapterA4e.lean` (registered in `BookProof.lean`), fully
`sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`;
checked on the headlines `energy_sign_not_conserved` and `spatialOp_swaps_pos`).
The whole project builds green (`lake build`, 8095 jobs). **No `EXTERNAL`
hypothesis** — Wigner/Mackey enter only in the *exhaustiveness* clauses of
Props 87/88, which are the cited backbone, not this algebraic core.

What it contains, built on the `4×4` Majorana Clifford model of §A.3/§A.5
(`ChapterA5.coeffMass1Z = iγ⁰`, `ChapterA5.coeffBoostZ j = γʲγ⁰`):

- `enSign` (`iγ⁰`) and `spatialOp j` (`γʲγ⁰`) as complex casts of the integer
  model, with `enSign_sq : iγ⁰·iγ⁰ = -1` (so the energy-sign eigenvalues are
  `±i` and the sign projectors need `ℂ` coefficients).
- `enSign_spatialOp_anticomm` — the generalized Clifford relation
  `{iγ⁰, γʲγ⁰} = 0`, from `ChapterA5.coeffBoostZ_mass1_anticomm`.
- The energy-sign projectors `P± = ½(1 ∓ i·iγ⁰)` and the full projector algebra:
  `projPos_add_projNeg` (`P₊+P₋=1`), `projPos_idem`/`projNeg_idem` (idempotent),
  `projPos_mul_projNeg` (`P₊P₋=0`).
- `spatialOp_swaps_pos`/`spatialOp_swaps_neg` (Prop 88 core): every spatial
  operator intertwines the two sign projectors (`P₊(γʲγ⁰)=(γʲγ⁰)P₋`), so `γʲγ⁰`
  swaps the energy-sign subspaces — a positive-energy subrep forces the negative
  one (antiparticles).
- `projPos_spatialOp_commutator`: `[P₊, γʲγ⁰] = i·(γʲγ⁰)(iγ⁰)`, an explicit
  nonzero matrix.
- Headline `energy_sign_not_conserved` (Cor 1 core): a spatial operator does not
  commute with `P₊`, so a localizable rep that is irreducible under the *full*
  Poincaré group cannot use the (non-conserved) `iγ⁰`-sign projectors — the
  reduction underlying the CPT / position-operator payoff.

`BookProof/STATUS.md` was updated with a new wave-22 section recording the result
and the remaining open items (Lemma 52 real-irrep classification; the
`EXTERNAL`-Wigner/Mackey exhaustiveness layer of §A.4/A.5; the N7 external
bundle). All changes are committed and pushed.

# Summary of changes for run 2d165ad4-3d76-4c49-8403-0ea9bdf70852
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item recorded in `BookProof/STATUS.md`: the **Σ / bridge half of Lemma 48** (book §A.3). This connects the two concrete double covers of the Lorentz group established in earlier waves — the Pauli/SL(2,ℂ) cover `Υ` (`BookProof/ChapterA3h.lean`) and the Majorana/Pinor cover `Λ` (`BookProof/ChapterA3c.lean`).

New module `BookProof/ChapterA3i.lean` (registered in `BookProof.lean`), fully `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`; checked on the headline). The whole project builds green (`lake build`, 8094 jobs).

What it contains:
- The explicit integer isomorphism Σ = !![1,0,0,-1; 0,-1,-1,0; 0,-1,1,0; 1,0,0,1] matching the ±-eigenspaces of γ⁰γ³ (Pinor) with those of σ³ (Pauli), with Σ·Σᵀ = Σᵀ·Σ = 2·1 (so Σ⁻¹ = ½Σᵀ).
- `Treal` (the real 4×4 form of the ℂ-linear action of a 2×2 matrix on ℂ²), the adjugate `adj2`, and the concrete spin-group element `Spinor T = Σ·Treal T·(½Σᵀ)` with inverse `SpinorInv T`.
- Supporting lemmas: `Treal_mul` (multiplicativity of the real form), `Treal_one`, `T_mul_adj2`/`adj2_mul_T`, `spinor_mul_spinorInv`/`spinorInv_mul_spinor`, and `spinor_inv_eq` ((Spinor T)⁻¹ = SpinorInv T).
- The core bridge `spinorInv_conj_mgamma`, a pure polynomial identity (no det=1 needed): SpinorInv T · iγ^μ · Spinor T = ∑_ν Υ(T)^ν_μ · iγ^ν.
- Headline `lemma48_bridge`: for T ∈ SL(2,ℂ), (Spinor T)⁻¹ · iγ^μ · Spinor T = ∑_ν Υ(T)^ν_μ · iγ^ν — i.e. Λ(Σ T Σ⁻¹) = Υ(T) in the concrete model (transposed by the two files' index conventions), the content of Lemma 48.

No external hypotheses were introduced. As requested, `ARISTOTLE_SUMMARY.md` was updated (new top section) along with `BookProof/STATUS.md` (new wave-21 section), recording the result and the remaining open items: Lemma 52 (real-irrep classification), the deeper §A.4/A.5 Bargmann–Wigner/CPT classification layer (which relies on external Wigner/Mackey inputs), and the N7 external bundle. All changes are committed and pushed.

# Summary of changes for run — §A.3 Lemma 48: the `Σ`/bridge `Λ(Σ T Σ⁻¹) = Υ(T)` (work-package N4)
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item recorded in `BookProof/STATUS.md`: the **`Σ` / bridge half of Lemma 48** (book §A.3, line 5458), which connects the two concrete double covers of the Lorentz group built in earlier waves — the Pauli/`SL(2,ℂ)` cover `Υ` (`BookProof/ChapterA3h.lean`, Note 47) and the Majorana/Pinor cover `Λ` (`BookProof/ChapterA3c.lean`, Prop 46).

New module `BookProof/ChapterA3i.lean` (registered in `BookProof.lean`), fully `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`; verified with the axiom checker on the headline `lemma48_bridge`). The whole project builds green (`lake build`, 8094 jobs).

The book's real-linear isomorphism `Σ : Pauli → Pinor` (book eq. 5468) matches the `±`-eigenspaces of `γ⁰γ³` (on `Pinor = ℂ⁴`) with those of `σ³` (on `Pauli = ℂ²`). With `M₊ = e₀+e₃`, `M₋ = e₀-e₃`, the concrete integer matrix is `Σ = !![1,0,0,-1; 0,-1,-1,0; 0,-1,1,0; 1,0,0,1]`, satisfying `Σ Σᵀ = Σᵀ Σ = 2·1` (so `Σ⁻¹ = ½ Σᵀ`). For `T ∈ SL(2,ℂ)` the spin-group element `Σ T Σ⁻¹` is realised as the real `4×4` matrix `Spinor T := Σ · Treal T · (½ Σᵀ)`, where `Treal T` is the real form of the `ℂ`-linear action of `T` on `ℂ²` in the ordered real basis `(P₊, iP₊, P₋, iP₋)`; its inverse is `SpinorInv T`, built the same way from the `2×2` adjugate `adj2 T`.

Deliverables: `Treal`/`adj2`/`Spinor`/`SpinorInv`; the orthogonality facts `sigmaZ_mul_transpose`, `sigmaC_mul_transpose`, `sigmaC_transpose_mul`; `Treal_mul` (multiplicativity of the real form), `Treal_one`, `T_mul_adj2`/`adj2_mul_T`; `spinor_mul_spinorInv`/`spinorInv_mul_spinor` and hence `spinor_inv_eq` (`(Spinor T)⁻¹ = SpinorInv T`); the core `spinorInv_conj_mgamma` — a pure polynomial identity (no `det T = 1` needed) giving `SpinorInv T · iγ^μ · Spinor T = ∑_ν Υ(T)^ν_μ · iγ^ν`; and the headline `lemma48_bridge`: for `T ∈ SL(2,ℂ)`, `(Spinor T)⁻¹ · iγ^μ · Spinor T = ∑_ν Υ(T)^ν_μ · iγ^ν`, i.e. the Pinor cover `Λ` of `Σ T Σ⁻¹` equals the Pauli cover `Υ` of `T` (transposed by the `Λ`/`Υ` index conventions) — the identity `Λ(Σ T Σ⁻¹) = Υ(T)` of Lemma 48 in the concrete model.

No external hypotheses were introduced. Both `BookProof/STATUS.md` (new wave-21 section) and this file were updated to record the result and the remaining open items (Lemma 52; the deeper §A.4/A.5 Bargmann–Wigner/CPT classification layer with external Wigner/Mackey inputs; and the N7 external bundle). All changes are committed and pushed.

# Summary of changes for run 9c44a0c4-f6ae-48d6-94b3-c7428a935348
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item of work-package N4: the concrete **massless little group** of **Proposition 79** (book §A.4), the companion of the massive `SU(2)` case previously done in `BookProof/ChapterA4c.lean`.

New module `BookProof/ChapterA4d.lean` (registered in `BookProof.lean`), fully `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`; verified with the axiom checker on the headline theorem). The whole project builds green (`lake build`, 8093 jobs).

The module builds on the `Υ : SL(2,ℂ) → O(1,3)` covering map of `BookProof/ChapterA3h.lean` (Note 47) and reuses helpers from `ChapterA4c.lean`. For a massless particle the standard 4-momentum is the null vector `n = e₀ + e₃ = (1,0,0,1)` (the book's `i l̸ = iγ⁰ + iγ³`), so its little group is the stabiliser of `n` under `Υ`, which the book records as `SE(2)`. On the concrete 2×2 Pauli model (`n·σ = σ⁰ + σ³ = diag(2,0)`):
- `FixesNullAxis` / `SEtwo` (SE(2) as the lower-triangular unimodular matrices with unit-modulus top-left entry).
- `pauliCoeff_add`, `pauliCoeff_null`, `upsilonC_nullCol` (the null-column sum of `Υ(T)` is `½ tr(σ^μ T†(σ⁰+σ³)T)`).
- `fixesNullAxis_iff_conj`: `Υ(T)` fixes `n` iff `T†(σ⁰+σ³)T = σ⁰+σ³`.
- `nullConj_iff_form`: that matrix identity holds iff `T` is lower triangular with unit-modulus top-left entry.
- headline `massless_little_group`: `{T ∈ SL(2,ℂ) | Υ(T) fixes n} = SEtwo`; plus `SEtwo_lower_triangular` (the explicit `SE(2)` shape `T = !![a,0;c,a⁻¹]`, `|a| = 1`) and `upsilon_massless_lorentz` (each such `Υ(T)` is a genuine Lorentz transformation fixing the null axis).

No external hypotheses were introduced. Both `BookProof/STATUS.md` (new wave-20 section) and `ARISTOTLE_SUMMARY.md` were updated to record the result and the remaining open items (the Σ/bridge half of Lemma 48; Lemma 52; the deeper §A.4/A.5 Bargmann–Wigner/CPT classification layer with external Wigner/Mackey inputs; and the N7 external bundle). All changes are committed and pushed.

# Summary of changes for run — §A.4 Prop 79: the massless little group is `SE(2)` (work-package N4)
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item of work-package N4: the concrete **massless little group** of **Proposition 79** (book §A.4, line 5636), the companion of the massive `SU(2)` case done previously in `ChapterA4c.lean`.

New module `BookProof/ChapterA4d.lean` (registered in `BookProof.lean`), fully `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified with the axiom checker on `massless_little_group`). The whole project builds green (`lake build`, 8093 jobs).

The module builds directly on the `Υ : SL(2,ℂ) → O(1,3)` covering map of `BookProof/ChapterA3h.lean` (Note 47) and reuses `upsilon_re` / `pauliCoeff_one` from `ChapterA4c.lean`. For a massless particle the standard 4-momentum is the null vector `n = e₀ + e₃ = (1,0,0,1)` (the book's `i l̸ = iγ⁰ + iγ³`), so its little group is the stabiliser of `n` under `Υ`; the book records this as the massless little group being `SE(2)`. On the concrete `2×2` Pauli model (`n·σ = σ⁰ + σ³ = diag(2,0)`):
- `FixesNullAxis` (a real `4×4` matrix fixes `n`, i.e. its `col₀ + col₃ = n`) / `SEtwo` (`SE(2)` realized as the lower-triangular unimodular matrices with unit-modulus top-left entry).
- `pauliCoeff_add`, `pauliCoeff_null` (`½ tr(σ^μ(σ⁰+σ³)) = δ_{μ0}+δ_{μ3}`), `upsilonC_nullCol` (the null-column sum of `Υ(T)` is `½ tr(σ^μ T†(σ⁰+σ³)T)`).
- `fixesNullAxis_iff_conj`: `Υ(T)` fixes `n` iff `T†(σ⁰+σ³)T = σ⁰+σ³` (Pauli-basis reconstruction, no `det T = 1` needed).
- `nullConj_iff_form`: that matrix identity holds iff `T 0 1 = 0 ∧ |T 0 0| = 1` (i.e. `T` lower triangular with unit-modulus top-left entry).
- headline `massless_little_group`: `{T ∈ SL(2,ℂ) | Υ(T) fixes n} = SEtwo`; plus `SEtwo_lower_triangular` (the explicit `SE(2)` shape `T = !![a,0;c,a⁻¹]`, `|a| = 1`: a `SO(2)` angle `a` and a translation `c ∈ ℂ ≅ ℝ²`) and `upsilon_massless_lorentz` (each such `Υ(T)` is a genuine Lorentz transformation fixing the null axis).

No external hypotheses were introduced. `BookProof/STATUS.md` (new wave-20 section) was updated to record the result and the remaining open items (the `Σ`/bridge half of Lemma 48; Lemma 52; the deeper §A.4/A.5 Bargmann–Wigner/CPT classification layer with external Wigner/Mackey inputs; and the N7 external bundle). All changes are committed and pushed.

---

# Summary of changes for run 28c64d36-dc40-4655-b0ca-1790f1c14881
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item of work-package N4: the concrete **massive little group** of **Proposition 79** (book §A.4).

New module `BookProof/ChapterA4c.lean` (registered in `BookProof.lean`), fully `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified with the axiom checker). The whole project builds green (`lake build`, 8092 jobs).

The module builds directly on the `Υ : SL(2,ℂ) → O(1,3)` covering map of `BookProof/ChapterA3h.lean` (Note 47). For a massive particle the standard 4-momentum lies along the time axis `e₀ = (1,0,0,0)`, so its little group is the stabiliser of `e₀` under `Υ`; the book records this as the massive little group being `SU(2)`. Formalized on the concrete `2×2` Pauli model:
- `FixesTimeAxis` / `SUtwo` (`SU(2) = {T | det T = 1 ∧ T† T = 1}`).
- `pauliCoeff_one` (`½ tr σ^μ = δ_{μ0}`), `upsilonC_timeCol` (the time column of `Υ(T)` is `½ tr(σ^μ T† T)` since `σ⁰ = 1`), `upsilon_re` (entries of `Υ(T)` are real).
- `fixesTimeAxis_iff_unitary`: `Υ(T)` fixes `e₀` iff `T† T = 1` (the Pauli-basis reconstruction forces unitarity without needing `det T = 1`).
- headline `massive_little_group`: `{T ∈ SL(2,ℂ) | Υ(T) e₀ = e₀} = SU(2)`; plus `upsilon_little_group_lorentz` (each such `Υ(T)` is a genuine Lorentz transformation fixing the time axis, i.e. a spatial rotation).

No external hypotheses were introduced. Both `BookProof/STATUS.md` (new wave-19 section) and `ARISTOTLE_SUMMARY.md` were updated to record the result and the remaining open items (the Σ/bridge half of Lemma 48; Lemma 52; the massless SE(2) little group and the deeper §A.4/A.5 Bargmann–Wigner/CPT classification layer with external Wigner/Mackey inputs; and the N7 external bundle). All changes are committed and pushed.

# Summary of changes for run — §A.4 Prop 79: the massive little group is `SU(2)` (work-package N4)
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item of work-package N4: the concrete **massive little group** of **Proposition 79** (book §A.4, line 5636).

New module `BookProof/ChapterA4c.lean` (registered in `BookProof.lean`), fully `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified with the axiom checker). The whole project builds green (`lake build`, 8092 jobs).

This builds directly on the `Υ : SL(2,ℂ) → O(1,3)` covering map of `ChapterA3h.lean` (Note 47). For a massive particle the standard 4-momentum lies along the time axis `e₀ = (1,0,0,0)`, so the little group `G_l = {T | T l̸ = l̸ T}` is exactly the stabiliser of `e₀` under `Υ`; the book records this as `i l̸ = iγ⁰ ⇒ G_l = SU(2)`. Formalized on the concrete `2×2` Pauli model:
- `FixesTimeAxis` / `SUtwo` (`SU(2) = {T | det T = 1 ∧ T† T = 1}`).
- `pauliCoeff_one` (`½ tr σ^μ = δ_{μ0}`), `upsilonC_timeCol` (the time column of `Υ(T)` is `½ tr(σ^μ T† T)`, since `σ⁰ = 1`), `upsilon_re` (entries of `Υ(T)` are real).
- `fixesTimeAxis_iff_unitary`: `Υ(T)` fixes `e₀` iff `T† T = 1` (no `det T = 1` needed — the Pauli-basis reconstruction already forces unitarity).
- headline **`massive_little_group`**: `{T ∈ SL(2,ℂ) | Υ(T) e₀ = e₀} = SU(2)`; and `upsilon_little_group_lorentz` (each `Υ(T)` is a Lorentz transformation fixing the time axis, i.e. a spatial rotation).

No external hypotheses were introduced. `BookProof/STATUS.md` (new wave-19 section) and this file were updated. Still open: the `Σ`/bridge half of Lemma 48; Lemma 52; the massless (`SE(2)`) little group and the deeper §A.4/A.5 Bargmann–Wigner/CPT classification layer (`EXTERNAL` Wigner/Mackey); and the N7 external Wigner/Mackey bundle. All changes are committed and pushed.

# Summary of changes for run 444809e4-7d64-49f3-b794-7736e392a704
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item of work-package N4: **Note 47** (book §A.3, line 5440), the `SL(2,ℂ)` side of **Lemma 48** — the two-to-one covering map `Υ : SL(2,ℂ) → O(1,3)` defined by `Υᵘ_ν(T) σᵛ = T† σᵘ T`.

New module `BookProof/ChapterA3h.lean` (registered in `BookProof.lean`), fully `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified with the axiom checker). The whole project builds green (`lake build`, 8091 jobs).

What was formalized on a concrete `2×2` Pauli model:
- `pauliσ`, `pauliσ_herm`, `pauliσ_trace` (`tr(σᵘσᵛ)=2δᵘᵛ`), and `pauli_expand`/`pauliCoeff_comb` (the four Pauli matrices are a basis of `Mat₂(ℂ)`).
- `UpsilonC`/`upsilon_recon` (the complex coefficient matrix `Υ(T)` with `T† σᵛ T = ∑_μ Υ(T)ᵘ_ν σᵘ`); `upsilonC_antihom` (`Υ(TU)=Υ(U)Υ(T)`); `upsilonC_real`/`Upsilon`/`toC_Upsilon` (entries are real).
- `det_pauli_comb`: `det(∑_ν x_ν σᵛ) = x₀²−x₁²−x₂²−x₃²` (the Minkowski norm as a determinant), with `upsilon_apply_comb` and `upsilonC_Qc` (a unimodular `T` preserves the form).
- A polarization layer (`bilC`, `bilC_ext`, `bilC_minkowski`, `bilC_conj`, `toC_minkowski_symm`) feeding `upsilonC_metric`/`upsilon_metric` (`Υ(T)ᵀηΥ(T)=η`) and the headline **`upsilon_mem_lorentz`**: for `T ∈ SL(2,ℂ)`, `Upsilon T ∈ O(1,3)`.

No external hypotheses were introduced. `BookProof/STATUS.md` (wave-18 section) and `ARISTOTLE_SUMMARY.md` were updated to record the new results and the remaining open items (the explicit `Σ : Pauli → Pinor` isomorphism and bridge `Λ(S)=Υ(Σ⁻¹SΣ)` completing Lemma 48; Lemma 52; the §A.4/A.5 Bargmann–Wigner/CPT classification layer; and the N7 external Wigner/Mackey bundle). All changes are committed and pushed.

# Summary of changes for run — §A.3 Note 47: the covering map `Υ : SL(2,ℂ) → O(1,3)` (work-package N4)
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item: **Note 47** (book §A.3, line 5440), the `SL(2,ℂ)` side of **Lemma 48**.

New module `BookProof/ChapterA3h.lean` (registered in `BookProof.lean`), fully `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified with the axiom checker). The whole project builds green (`lake build`, 8091 jobs).

The book defines a two-to-one surjection `Υ : SL(2,ℂ) → SO⁺(1,3)` by `Υᴼ_ν(T) σᵛ = T† σᴼ T`, with `σ⁰ = 1` and `σʲ` the Pauli matrices. Formalized on a concrete `2×2` Pauli model:
- `pauliσ` (the four Pauli matrices), `pauliσ_herm`, `pauliσ_trace` (`tr(σᴼσᵛ) = 2δᴼᵛ`), and `pauli_expand`/`pauliCoeff_comb` (the four are a basis of `Mat₂(ℂ)`, coefficient `½ tr(σᴼ M)`).
- `UpsilonC`/`upsilon_recon`: the complex coefficient matrix `Υ(T)` with `T† σᵛ T = ∑_μ Υ(T)ᴼ_ν σᴼ`; `upsilonC_antihom` (`Υ(TU) = Υ(U)Υ(T)`); `upsilonC_real`/`Upsilon`/`toC_Upsilon` (entries are real, giving the real matrix `Upsilon T`).
- `det_pauli_comb`: `det(∑_ν x_ν σᵛ) = x₀² − x₁² − x₂² − x₃²`, i.e. the Minkowski norm as a `2×2` determinant; with `upsilon_apply_comb` and `upsilonC_Qc` (a unimodular `T` preserves this form).
- A small polarization layer (`bilC`, `bilC_ext`, `bilC_minkowski`, `bilC_conj`, `toC_minkowski_symm`) feeding `upsilonC_metric`/`upsilon_metric` (`Υ(T)ᵀ η Υ(T) = η`) and the headline **`upsilon_mem_lorentz`**: for `T ∈ SL(2,ℂ)`, `Upsilon T ∈ O(1,3)`.

No external hypotheses were introduced. Still open for the full Lemma 48: the explicit `Σ : Pauli → Pinor` isomorphism and the bridge `Λ(S) = Υ(Σ⁻¹ S Σ)` (the group-level Lorentz image of `Spin⁺(3,1)` is already covered via the exponential route in `ChapterA3g.lean`); Lemma 52; the §A.4/A.5 Bargmann–Wigner/CPT classification layer; and the N7 external Wigner/Mackey bundle.

Updated `BookProof/STATUS.md` (wave-18 section) and this file. All changes are committed and pushed.

# Summary of changes for run 0e1502c1-2127-41ef-959d-5042a443209e
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item — the §A.5 "Spinor frame and CPT theorem" (book line 6453), the closing section of Chapter A's work-package N4 (following the §A.4 unitarity props and Prop 61 from previous runs).

New module `BookProof/ChapterA5.lean` (registered in `BookProof.lean`), fully `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified with the axiom checker). The whole project builds green.

The book's claim: in space coordinates the most general Lorentz-covariant mass term of the Hamiltonian is `iH = ∂⃗·γ⃗γ⁰ + iγ⁰ m₁ + γ⁰γ⁵ m₂`, which — being real in the Majorana basis — is automatically PT/CPT invariant. Formalized on the 4×4 Majorana Clifford model of §A.3:
- The five coefficient matrices of `iH` (`coeffBoostZ j = γʲγ⁰`, `coeffMass1Z = iγ⁰`, `coeffMass2Z = γ⁰γ⁵`), all real integer matrices.
- Generalized Clifford relations: mutual anticommutation of all five, with `(γʲγ⁰)² = 1` and `(iγ⁰)² = (γ⁰γ⁵)² = -1`.
- Mass-shell identity `energySymbolZ_sq`: the symbol `D = p₁γ¹γ⁰ + p₂γ²γ⁰ + p₃γ³γ⁰ + m₁ iγ⁰ + m₂ γ⁰γ⁵` satisfies `D² = (|p⃗|² − m₁² − m₂²)·1`, i.e. the Klein–Gordon relation `H² = |p⃗|² + m₁² + m₂²`.
- The real Majorana model (`coeffBoostR`/`coeffMass1R`/`coeffMass2R`, `energySymbolR`) with the same mass-shell identity `energySymbolR_sq`.

No external hypotheses were introduced; the covariance motivating the form of `iH` reuses the existing §A.3 adjoint-action machinery, and the PT/CPT physics discussion is captured in docstrings.

Updated `BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md` with a wave-17 section (preserving prior history), recording the new results and the remaining open items (explicit SL(2,ℂ)/Σ/Υ cover of Lemma 48, Lemma 52, the §A.4/A.5 Bargmann–Wigner/CPT classification layer, and the N7 external Wigner/Mackey bundle). All changes are committed and pushed.

# Summary of changes for run — §A.5 CPT / energy operator (work-package N4)
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open item: the **§A.5** "Spinor frame and CPT theorem" (book line 6453), the closing section of Chapter A's work-package N4. This follows the §A.4 unitarity props (73/74/76) and Prop 61 from the previous runs.

New module `BookProof/ChapterA5.lean` (registered in `BookProof.lean`), `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified via `lean_verify`); the whole project builds green (`lake build`, 8090 jobs).

The book's claim: in space coordinates the most general Lorentz-covariant mass term of the Hamiltonian is `iH = ∂⃗·γ⃗γ⁰ + iγ⁰ m₁ + γ⁰γ⁵ m₂`, which — being real in the Majorana basis — is automatically invariant under a parity–time reversal (essentially the CPT theorem). This module formalizes the concrete matrix core on the `4×4` Majorana Clifford model of §A.3.

Delivered and proved:
- The five coefficient matrices of `iH` in the integer Majorana model (`coeffBoostZ j = γʲγ⁰`, `coeffMass1Z = iγ⁰`, `coeffMass2Z = γ⁰γ⁵`) — all real integer matrices (the reality property underlying CPT).
- The **generalized Clifford relations** (`decide`): mutual anticommutation of all five matrices, with `(γʲγ⁰)² = 1` and `(iγ⁰)² = (γ⁰γ⁵)² = -1`.
- The **mass-shell identity** `energySymbolZ_sq`: the momentum-space symbol `D = p₁γ¹γ⁰ + p₂γ²γ⁰ + p₃γ³γ⁰ + m₁ iγ⁰ + m₂ γ⁰γ⁵` satisfies `D² = (|p⃗|² - m₁² - m₂²)·1`, i.e. the Klein–Gordon relation `H² = |p⃗|² + m₁² + m₂²` with the two masses combining as `m² = m₁² + m₂²`.
- The real Majorana model (`coeffBoostR`/`coeffMass1R`/`coeffMass2R`, `energySymbolR`) via `(Int.castRingHom ℝ).mapMatrix`, with the same mass-shell identity `energySymbolR_sq`.

No `EXTERNAL` hypothesis (the covariance that motivates the form of `iH` is the on-disk §A.3 adjoint-action machinery; the PT/CPT physics discussion is captured in docstrings, per the roadmap's §A.4/A.5 recommendation). The subagent-generated proofs were cleaned up into fast, robust component-wise computations.

Documentation: appended a wave-17 section to `BookProof/STATUS.md` and this file (preserving all prior history), recording the new results and the remaining open items (explicit `SL(2,ℂ)`/`Σ`/`Υ` cover of Lemma 48, Lemma 52, the §A.4/A.5 Bargmann–Wigner/CPT classification layer, and the N7 external Wigner/Mackey bundle). All changes are committed and pushed.

# Summary of changes for run 1d05cd95-8125-4d78-b178-9552daf6e895
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open §A.4 item flagged "doable" — **Proposition 61**, the operator-algebra "unitarity by direct computation" result of work-package N4. This complements the §A.4 unitarity props (73/74/76) done in the previous run.

New module `BookProof/ChapterA4b.lean` (registered in `BookProof.lean`), `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified via `#print axioms`); the whole project builds green.

The book's claim: with `iH = γ⁰∂̸ + iγ⁰m` and `E ≥ m ≥ 0`, the operator `U' := (E + U H γ⁰ U†)/(√(E+m)·√(2E))` is unitary, proved by `(U')†U' = 1 = U'(U')†`. The mathematical heart is a C*-algebra identity: writing `c := U H γ⁰ U†`, the Dirac anticommutator `{γ⁰,H}=2m` and `(γ⁰)²=1` give `c + c† = 2m·1` and `E² = c†c` (E = |c|), whence `(E + c†)(E + c) = 2E(E+m) = (E + c)(E + c†)`, so dividing by `p := √(2E)·√(E+m)` makes `U' := p⁻¹(E+c)` a unitary.

Delivered and proved:
- `prop61_unitary_core` — the abstract engine over any ℂ-*-algebra (Prop 61's `(U')†U' = 1 = U'(U')†` argument).
- `prop61_energyMap_unitary` — the C*-algebra existence wrapper: for a unit `c` with `c + c† = 2m·1` (`m ≥ 0`), the positive square roots `E := √(c†c)` and `p := √(2E² + 2m·E)` exist via continuous functional calculus, are invertible, and satisfy the core's hypotheses, so `U'` is genuinely unitary.
- Two reusable generic helpers: `isSelfAdjoint_of_mul_eq_one` and `Commute.of_mul_eq_one`.

The subagent-generated proofs were cleaned up (removed leftover `grind`/unused simp arguments and rewrote the heavy wrapper proof into a fast, lint-clean form so it builds within normal resource limits).

Documentation: appended a wave-16 section to both `BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md` (preserving all prior history), recording the new results and the remaining open items (explicit SL(2,ℂ)/Σ/Υ cover of Lemma 48, Lemma 52, the §A.4/A.5 Bargmann–Wigner/CPT classification layer, and the N7 external Wigner/Mackey bundle). All changes are committed and pushed.

# Summary of changes for run — Prop 61 unitarity (§A.4, work-package N4)
Continued executing `FORMALIZATION_ROADMAP.md`, taking the next open §A.4 item flagged "doable": **Proposition 61**, the operator-algebra "unitarity by direct computation" statement (`iH = γ⁰∂̸ + iγ⁰m`, `E ≥ m ≥ 0`; `U' := (E + UHγ⁰U†)/(√(E+m)·√(2E))` is unitary). New module `BookProof/ChapterA4b.lean`, registered in `BookProof.lean`, `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified via `#print axioms`); `lake build` green (8089 jobs).

The mathematical heart is a C*-algebra identity. Writing `c := U H γ⁰ U†` (so `c† = U γ⁰ H U†`), the Dirac anticommutator `{γ⁰,H} = 2m` with `(γ⁰)² = 1` gives `c + c† = 2m·1` and `E² = c†c = cc†` (E = |c|), whence a pure ring computation yields `(E + c†)(E + c) = 2E(E+m) = (E + c)(E + c†)`, so dividing by `p := √(2E)·√(E+m)` (with `p² = 2E(E+m)`) makes `U' := p⁻¹(E+c)` a unitary.

Delivered:
* `prop61_unitary_core` — abstract engine over any ℂ-*-algebra: given `c` with `c + c† = 2m·1`, self-adjoint `E` with `E² = c†c` commuting with `c`, and a self-adjoint normaliser `p` with `p² = 2E² + 2m·E` invertible with inverse `q` (self-adjoint, commuting with `E`, `c`), the element `U' := q(E+c)` satisfies `U'†U' = 1 = U'U'†`. This is Prop 61's `(U')†U' = 1 = U'(U')†` argument.
* `prop61_energyMap_unitary` — C*-algebra existence wrapper: for `c` with `c + c† = 2m·1` (`m ≥ 0` real) and `c` a unit, the positive square roots `E := √(c†c)` and `p := √(2E² + 2m·E)` exist (continuous functional calculus, `CFC.sqrt`), are invertible, and satisfy the core's hypotheses, so `U' := p⁻¹(E+c)` is genuinely a unitary.
* Two reusable generic helpers: `isSelfAdjoint_of_mul_eq_one` (a two-sided inverse of a self-adjoint element is self-adjoint) and `Commute.of_mul_eq_one` (an inverse commutes with whatever the original element commutes with).

`BookProof/STATUS.md` updated with a wave-16 section preserving all prior history and recording remaining open items: the explicit `SL(2,ℂ)`/Σ/Υ cover of Lemma 48, Lemma 52, the §A.4/A.5 Bargmann–Wigner/localizable-rep/CPT classification layer, and the N7 external Wigner/Mackey bundle.

# Summary of changes for run 81e63149-fc45-4536-9411-18617825e9cc
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next two open items from the top of the wave-14 "still open" list. Both new modules are `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified via `#print axioms`), registered in `BookProof.lean`, and `lake build` is green (8088 jobs).

New module `BookProof/ChapterA4.lean` — the tractable §A.4 unitarity core (Note 62 / Props 73, 74, 76). The book's Majorana–Fourier transform `𝓕_M := (𝓕_P)^Θ` is the Θ-conjugate of the complex Pauli Fourier transform, and the argument is "a Θ-conjugate of a unitary is unitary". Formalized: `LinearIsometryEquiv.restrictScalarsₗᵢ` (the small missing Mathlib helper letting a real-linear Θ conjugate a complex unitary), the conjugation engine `conjugateₗᵢ` with `conjugateₗᵢ_symm` (Prop 74), `pauliFourier` (Mathlib's `Lp.fourierTransformₗᵢ`, unitary by Plancherel, as a real unitary), `majoranaFourier` (Prop 73) with `majoranaFourier_symm`/`_apply`, and `energyTransform` (Prop 76). No EXTERNAL hypothesis; the Pauli↔Pinor iso Θ is a parameter.

New module `BookProof/ChapterB3b.lean` — the N3 residue `denseCore_svd`, the finite-rank singular-value decomposition the §0 dense-core method reduces the book's `Ψ = W D U†` (§B.3(b)) to. It comprises `gram_svd` (spectral half: `Aᴴ A = U·diag(D²)·Uᴴ` from the spectral theorem on the PSD Gram matrix, `D = √eigenvalues ≥ 0`), `svd_completion` (from `Bᴴ B = diag(D²)` build a unitary `W` with `B = W·diag(D)` via orthonormal-basis extension), and the headline `denseCore_svd`: every square matrix over ℝ/ℂ factors as `A = W·diagonal D·Uᴴ` with `W, U` unitary and `D ≥ 0`. This plugs directly into the existing `ChapterB3.conditional_operator_identity` (B.3c).

`BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md` were updated with a wave-15 section preserving all prior history and recording what remains open: the explicit SL(2,ℂ)/Σ/Υ cover of Lemma 48, Lemma 52, the remaining §A.4/A.5 classification layer plus Prop 61, and the N7 external Wigner/Mackey bundle. All changes are committed and pushed to origin.

# Wave 15 — N4 §A.4 unitarity (Props 73/74/76) + N3 residue `denseCore_svd`

Continued executing `FORMALIZATION_ROADMAP.md`, taking the next two open steps
from the top of the wave-14 "still open" list: the **§A.4 unitarity core**
(Note 62 / Props 73, 74, 76 — work-package N4) and the **N3 residue**
`denseCore_svd` (the finite-rank singular-value decomposition). Both landed
`sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`);
`lake build` is green (8088 jobs).

**New module `BookProof/ChapterA4.lean`** (registered in `BookProof.lean`) —
the tractable unitarity core of §A.4. The book's Majorana–Fourier transform
`𝓕_M := (𝓕_P)^Θ` is the `Θ`-conjugate of the complex Pauli Fourier transform
(`Θ` = the real-linear isometric `Pauli^r ≅ Pinor` identification), and the
book's proof is *a `Θ`-conjugate of a unitary is unitary*. Formalized:
- `LinearIsometryEquiv.restrictScalarsₗᵢ`: a `𝕜`-linear isometry equivalence is
  an `R`-linear one for a compatible sub-scalar-ring (the small Mathlib helper
  that lets a real-linear `Θ` conjugate a complex unitary).
- `conjugateₗᵢ` (engine): `A^Θ := Θ ∘ A ∘ Θ⁻¹` is a `LinearIsometryEquiv`;
  `conjugateₗᵢ_symm` = **Prop 74** (`(A^Θ)⁻¹ = (A⁻¹)^Θ`), plus `_trans`, `_refl`.
- `pauliFourier`: Mathlib's `MeasureTheory.Lp.fourierTransformₗᵢ` (unitary by
  Plancherel) as a real unitary `𝓕_P`.
- `majoranaFourier` (**Prop 73**, `𝓕_M := 𝓕_P^Θ`, a real unitary) with
  `majoranaFourier_symm` (**Prop 74**); `energyTransform` (**Prop 76**, `𝓔`).
  No `EXTERNAL` hypothesis (Plancherel is in Mathlib); `Θ` is a parameter.

**New module `BookProof/ChapterB3b.lean`** (registered in `BookProof.lean`) —
the finite-rank SVD the §0 dense-core method reduces `Ψ = W D U†` (§B.3(b)) to:
- `gram_svd`: `Aᴴ A = U · diag(D²) · Uᴴ` (spectral theorem on the PSD Gram
  matrix; `D = √eigenvalues ≥ 0`).
- `svd_completion`: from `Bᴴ B = diag(D²)` build a unitary `W` with
  `B = W · diag(D)` (normalize nonzero columns, complete to an orthonormal
  basis via `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`).
- headline `denseCore_svd`: every square matrix over `ℝ`/`ℂ` factors
  `A = W · diagonal D · Uᴴ` with `W, U` unitary and `D ≥ 0`. Plugs into
  `ChapterB3.conditional_operator_identity` (B.3c).

Verification: `lake build` green, no `sorry`/`admit` in the new files, and the
headline theorems (`majoranaFourier`, `majoranaFourier_symm`, `denseCore_svd`,
`svd_completion`, `gram_svd`) check axiom-clean via `#print axioms`.
`BookProof/STATUS.md` was updated with a wave-15 section recording what remains
open (the explicit `SL(2,ℂ)/Σ/Υ` cover of Lemma 48, Lemma 52, the remaining
§A.4/A.5 classification layer + Prop 61, and the N7 external Wigner/Mackey
bundle). All changes are committed and pushed to origin.

# Summary of changes for run 92a957cc-28be-43c1-8414-8299f30c36fe
Continued executing `FORMALIZATION_ROADMAP.md`, taking the next open step from the top of the wave-13 "still open" list: the remaining **group-level** content of Note 47 / Lemma 48 of §A.3 (work-package N4). Its two recorded obstructions were the adjoint-exponential identity `exp(-G)·X·exp(G) = exp(-ad_G)(X)` and the Lie-algebra → group exponential `A ∈ 𝔬(1,3) ⟹ exp A ∈ O(1,3)`; both are now discharged.

New module `BookProof/ChapterA3g.lean` (registered in `BookProof.lean`), all sorry-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`), `lake build` green:
- `exp_neg_mul_exp` / `exp_matrix_inv`: `exp(-G)` is the matrix inverse of `exp G`.
- `conj_exp_hasAdLambda`: the adjoint-exponential identity in Majorana form — from `HasAdLambda G A` (commutator `[G, iγ^μ]` described by real matrix `A`), `exp(-G)·iγ^μ·exp(G) = Σ_ν (exp(-A))^μ_ν iγ^ν`. Proved by a one-parameter ODE argument entirely inside `Matrix (Fin 4) (Fin 4) ℝ` (`φ(t) = exp(t•G)·Z(t)·exp(-t•G)` has zero derivative since `Z'(t) = -[G, Z(t)]`, hence is constant `= iγ^μ`).
- `hasLambda_exp`: `HasLambda (exp G) (exp (-A))`.
- `lorentzLie_exp`: `A ∈ 𝔬(1,3) ⟹ exp A ∈ O(1,3)`.
- `isPin_exp_of_isSpinLie`: every `G ∈ 𝔰𝔭𝔦𝔫⁺(3,1)` exponentiates into `Pin(3,1)`.
- `spinLie_exp_hasLambda_lorentz` (headline): for `G ∈ 𝔰𝔭𝔦𝔫⁺(3,1)`, the conjugation action of `exp G` on the Majorana basis is a Lorentz matrix `Λ = exp(-A) ∈ O(1,3)` — the infinitesimal → group Lorentz-image half of Lemma 48.

Verification: `lake build` is green, the file has no `sorry`/`admit`, and the two headline theorems check axiom-clean via `lean_verify`. `ARISTOTLE_SUMMARY.md` and `BookProof/STATUS.md` were updated with a wave-14 section preserving all prior history and recording what remains open (the explicit SL(2,ℂ)/Σ/Υ cover of Lemma 48, Lemma 52, the §A.4–A.5 layer, the N3 `denseCore_svd` residue, and the N7 external Wigner/Mackey bundle). All changes are committed and pushed to origin.

# Wave 14 — N4 §A.3 group-level Lemma 48: the infinitesimal → group bridge

Continued executing `FORMALIZATION_ROADMAP.md`, taking the next open step from the top of the wave-13 "still open" list: the remaining **group-level** content of Note 47 / Lemma 48 of §A.3 (work-package N4), whose two recorded obstructions were the **adjoint-exponential identity** `exp(-G)·X·exp(G) = exp(-ad_G)(X)` and the **Lie-algebra → group exponential** `A ∈ 𝔬(1,3) ⟹ exp A ∈ O(1,3)`.

New module `BookProof/ChapterA3g.lean` (registered in `BookProof.lean`) discharges both ingredients and assembles the group-level Lemma 48 statements. Delivered, all sorry-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`; verified with `lean_verify`); `lake build` green (8086 jobs):
- `exp_neg_mul_exp` / `exp_matrix_inv`: `exp(-G)` is the (two-sided, hence matrix) inverse of `exp G`.
- `conj_exp_hasAdLambda`: the **adjoint-exponential identity** in Majorana form — if `HasAdLambda G A` (the commutator `[G, iγ^μ]` is described by the real matrix `A`, from `ChapterA3e`), then `exp(-G) · iγ^μ · exp(G) = Σ_ν (exp(-A))^μ_ν iγ^ν`. Proved by the one-parameter ODE argument entirely inside `Matrix (Fin 4) (Fin 4) ℝ` (no operator exponential): `φ(t) = exp(t•G)·(Σ_ν (exp(-t•A))^μ_ν iγ^ν)·exp(-t•G)` has zero derivative because `Z'(t) = -[G, Z(t)]`, hence is constant `= iγ^μ`; evaluate at `t = 1`.
- `hasLambda_exp`: `HasLambda (exp G) (exp (-A))` whenever `HasAdLambda G A` (via `exp_matrix_inv`).
- `lorentzLie_exp`: `A ∈ 𝔬(1,3) ⟹ exp A ∈ O(1,3)`, via `Matrix.exp_conj`/`Matrix.exp_transpose` and `η² = 1`.
- `isPin_exp_of_isSpinLie`: every `G ∈ 𝔰𝔭𝔦𝔫⁺(3,1)` exponentiates into `Pin(3,1)` (using `ChapterA3f.spinLie_det_exp_eq_one` for `det (exp G) = 1`).
- `spinLie_exp_hasLambda_lorentz`: for `G ∈ 𝔰𝔭𝔦𝔫⁺(3,1)`, the conjugation action of `exp G` on the Majorana basis is a Lorentz matrix `Λ = exp(-A) ∈ O(1,3)` — the infinitesimal → group Lorentz-image half of Lemma 48.

Verification: `lake build` is green, the file has no `sorry`/`admit`, and both headline theorems (`spinLie_exp_hasLambda_lorentz`, `isPin_exp_of_isSpinLie`) check axiom-clean. `ARISTOTLE_SUMMARY.md` and `BookProof/STATUS.md` were updated (this section) preserving all prior history. All changes are committed and pushed to origin.

**Still open after wave 14** (unchanged otherwise): the explicit `SL(2,ℂ)`/`Σ`/`Υ` cover `Λ(S) = Υ(Σ⁻¹SΣ)` of Lemma 48 (the concrete Pauli↔Pinor isomorphism); Lemma 52 (real-irrep classification via symmetric tensor powers + Weyl); the §A.4–A.5 layer (Bargmann–Wigner scaffolding, Majorana–Fourier/Energy unitarity Props 61/73/74/76, localizable-rep classification, CPT/Cor 1); the N3 residue `denseCore_svd`; and the N7 external Wigner/Mackey bundle.

---

# Summary of changes for run b35e00a7-ca00-4166-b29a-7a86f44a346e
Continued executing `FORMALIZATION_ROADMAP.md`, taking the next open step from the top of the wave-12 "still open" list: the group-level half of Note 47 / Lemma 48 of §A.3, whose recorded obstruction was the matrix-exponential determinant identity `det (exp A) = exp (tr A)` (a listed TODO in Mathlib's `MatrixExponential.lean`).

New module `BookProof/ChapterA3f.lean` (registered in `BookProof.lean`) discharges that ingredient over ℝ for arbitrary n×n matrices and derives the `det = 1` half of the group-level Lemma 48. Delivered, all sorry-free:
- `detExpPath A t := det (exp (t • A))`, with `detExpPath_zero` and the one-parameter-group law `detExpPath_add` (from `NormedSpace.exp_add_of_commute` + `Matrix.det_mul`);
- `differentiable_det` (det is polynomial in the entries);
- `hasDerivAt_det_line` (Jacobi along `1 + t • A`; derivative at 0 is the trace, from `Matrix.det_one_add_smul`);
- `hasDerivAt_detExpPath_zero` (Jacobi at the identity via the chain rule + uniqueness of the derivative) and `hasDerivAt_detExpPath` (derivative at any point, from the group law);
- the headline `det_exp_eq_exp_trace` (`det (exp A) = exp (tr A)`, the Jacobi–Liouville formula) by the ODE argument that `t ↦ detExpPath A t · exp(-(tr A · t))` has zero derivative, hence is constant 1;
- the downstream `spinLie_det_exp_eq_one`: every element of the spin Lie algebra `𝔰𝔭𝔦𝔫⁺(3,1)` (traceless, from `ChapterA3e.spinLie_traceless`) exponentiates to a matrix of unit determinant — the infinitesimal-to-group `det = 1` half of Lemma 48.

Verification: `lake build` is green (8085 jobs), the file has no `sorry`/`admit`, and both headline theorems check axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`). `ARISTOTLE_SUMMARY.md` (as requested) and `BookProof/STATUS.md` were updated with a new wave-13 section preserving all prior history; the summaries also record what remains open (the explicit SL(2,ℂ)/Σ/Υ cover and adjoint-exponential identity for the rest of Lemma 48, Lemma 52, the §A.4–A.5 layer, the N3 `denseCore_svd` residue, and the N7 external Wigner/Mackey bundle). All changes are committed and pushed to origin.

# Wave 13 — N4 §A.3 group-level Lemma 48: `det (exp A) = exp (tr A)` and `det Spin⁺(3,1) = 1`

Continued executing `FORMALIZATION_ROADMAP.md`, taking the next open step from the top of the wave-12 "still open" list: the **group-level** part of Note 47 / Lemma 48 of §A.3 (work-package N4), whose recorded obstruction was the matrix-exponential determinant identity `det (exp A) = exp (tr A)` — a listed `TODO` in Mathlib (`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`, line 57).

**New module `BookProof/ChapterA3f.lean`** (registered in `BookProof.lean`) discharges that analytic ingredient over ℝ for arbitrary `n × n` matrices, and derives the `det = 1` half of the group-level Lemma 48.

Delivered (all `sorry`-free, axiom-clean — only `propext`, `Classical.choice`, `Quot.sound`, verified with the axiom checker):
- `detExpPath A t := (exp (t • A)).det`, the one-parameter determinant function, with `detExpPath_zero` and the one-parameter-group law `detExpPath_add` (`f (s+t) = f s · f t`, from `NormedSpace.exp_add_of_commute` + `Matrix.det_mul`);
- `differentiable_det` (the determinant is a polynomial in the entries, hence differentiable);
- `hasDerivAt_det_line` (Jacobi's formula along `1 + t • A`: derivative at `0` is the trace, from `Matrix.det_one_add_smul`);
- `hasDerivAt_detExpPath_zero` (Jacobi at the identity along the exponential path: `HasDerivAt (detExpPath A) (tr A) 0`, via the chain rule composing `differentiable_det` with `hasDerivAt_exp_smul_const'` and identifying the differential with the trace by uniqueness against `hasDerivAt_det_line`);
- `hasDerivAt_detExpPath` (derivative at an arbitrary point, `A.trace * detExpPath A t`, from the group law);
- the headline **`det_exp_eq_exp_trace`** (`det (exp A) = exp (tr A)`, the Jacobi–Liouville formula) by the ODE argument: `t ↦ detExpPath A t · exp(-(tr A · t))` has zero derivative, hence is the constant `1`;
- the downstream **`spinLie_det_exp_eq_one`**: every element of the spin Lie algebra `𝔰𝔭𝔦𝔫⁺(3,1)` (traceless, `ChapterA3e.spinLie_traceless`) exponentiates to a matrix of unit determinant — the infinitesimal-to-group `det = 1` half of Lemma 48.

The whole project builds green (`lake build`, 8085 jobs), `sorry`-free and axiom-clean. `BookProof/STATUS.md` and this file were updated with a wave-13 section (existing history preserved). All changes committed and pushed to origin.

**Still open after wave 13** (unchanged otherwise): the remaining group-level Lemma 48 content beyond `det = 1` (the explicit `SL(2,ℂ)`/`Σ`/`Υ` cover `Λ(S) = Υ(Σ⁻¹SΣ)` and the `exp(-ad_G)` adjoint-exponential identity); Lemma 52 (real-irrep classification via symmetric tensor powers + Weyl); the §A.4–A.5 layer (Bargmann–Wigner scaffolding, Majorana–Fourier/Energy unitarity Props 61/73/74/76, localizable-rep classification, CPT/Cor 1); the N3 residue `denseCore_svd`; and the N7 external Wigner/Mackey bundle.

---

# Summary of changes for run a7eb70e1-bc7e-42b7-bc98-6c2fd995206e
Continued executing `FORMALIZATION_ROADMAP.md`, taking the next open step from the top of the wave-11 "still open" list: **Note 47 / Lemma 48** of §A.3 (work-package N4).

**New module `BookProof/ChapterA3e.lean`** (registered in `BookProof.lean`) formalizes the *infinitesimal* content of Note 47 / Lemma 48 — the differential `Λ_* : 𝔰𝔭𝔦𝔫⁺(3,1) → 𝔬(1,3)` of the two-to-one cover `Λ : Pin(3,1) → O(1,3)` built earlier in `BookProof/ChapterA3c.lean`. The book characterizes the restricted spin group by its Lie algebra `Spin⁺(3,1) = { e^{θʲ iγ⁵γ⁰γʲ + bʲ γ⁰γʲ} }`, spanned by the six spinor Lorentz generators (three boosts `γ⁰γʲ`, three rotations `iγ⁵γ⁰γʲ`). Everything is over ℝ on the concrete 4×4 Majorana model, and every per-generator fact is a decidable integer-matrix computation, so the file is fully self-contained (no external Pauli/Weyl hypothesis).

Delivered:
- the six generators `spinBoost j`/`spinRot j` and their explicit adjoint matrices `adBoost j`/`adRot j`;
- the predicate `HasAdLambda G A` (`[G, iγ^μ] = Σ_ν A^μ_ν iγ^ν`, the infinitesimal analogue of `HasLambda`) and the Lorentz Lie algebra `LorentzLie = {A | A η + η Aᵀ = 0}`, with integer-model transport helpers;
- the per-generator adjoint identities and `𝔬(1,3)` membership of each adjoint matrix (all by `decide`);
- tracelessness of the generators (`spinLie_traceless`, the infinitesimal `det = 1` of Lemma 48);
- linearity lemmas plus the headline `spinLie_hasAdLambda_lorentzLie`: every element of `𝔰𝔭𝔦𝔫⁺(3,1)` has an adjoint matrix lying in `𝔬(1,3)`, i.e. the infinitesimal Lorentz map `Λ_*` is well-defined and lands in the Lorentz Lie algebra.

The group-level Lemma 48 (`Spin⁺(3,1) ⊆ Pin(3,1)`, `Λ(S) = Υ(Σ⁻¹SΣ)`) requires exponentiating this and depends on the matrix-exponential determinant identity `det (exp A) = exp (tr A)` — currently a TODO in Mathlib — together with the adjoint-exponential identity; these analytic ingredients are recorded as the remaining open step in `BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md`.

Everything is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified with the axiom checker); the whole project builds green (`lake build`, 8084 jobs). `ARISTOTLE_SUMMARY.md` and `BookProof/STATUS.md` were updated with a wave-12 section (existing history preserved). All changes are committed and pushed to origin.

# Wave 12 — N4 §A.3 Note 47 / Lemma 48: the Lie algebra 𝔰𝔭𝔦𝔫⁺(3,1)

Continued executing `FORMALIZATION_ROADMAP.md`, taking the next open step from the
top of the wave-11 "still open" list: **Note 47 / Lemma 48** of §A.3
(work-package N4, book line 5445).

**New module `BookProof/ChapterA3e.lean`** (registered in `BookProof.lean`)
formalizes the *infinitesimal* content of Note 47 / Lemma 48 — the differential
`Λ_* : 𝔰𝔭𝔦𝔫⁺(3,1) → 𝔬(1,3)` of the two-to-one cover `Λ : Pin(3,1) → O(1,3)`
built in `ChapterA3c.lean`. The book characterizes the restricted spin group by
its Lie algebra `Spin⁺(3,1) = { e^{θʲ iγ⁵γ⁰γʲ + bʲ γ⁰γʲ} }`, spanned by the six
spinor Lorentz generators (three boosts `γ⁰γʲ`, three rotations `iγ⁵γ⁰γʲ`).
Everything is over `ℝ` on the concrete `4×4` Majorana model (`mgammaR`), and every
per-generator fact is a decidable integer-matrix computation — the file is fully
self-contained: **no external hypothesis** (no Pauli/Weyl input) is needed.

Delivered (all `sorry`-free and axiom-clean — only `propext`, `Classical.choice`,
`Quot.sound`, verified with `lean_verify`; whole project builds green,
`lake build`, 8084 jobs):
- the six generators `spinBoost j`/`spinRot j` and their explicit adjoint
  matrices `adBoost j`/`adRot j`;
- the predicate `HasAdLambda G A` (`[G, iγ^μ] = Σ_ν A^μ_ν iγ^ν`, infinitesimal
  `HasLambda`) and the Lorentz Lie algebra `LorentzLie = {A | A η + η Aᵀ = 0}`,
  with integer-model transport helpers;
- per-generator adjoint identities (`spinBoost_hasAdLambda`,
  `spinRot_hasAdLambda`) and `𝔬(1,3)` membership (`adBoost_mem_lorentzLie`,
  `adRot_mem_lorentzLie`), all by `decide`;
- tracelessness of the generators (`spinLie_traceless`, the infinitesimal
  `det = 1` of Lemma 48);
- linearity lemmas (`hasAdLambda_add/_smul/_sum`, `lorentzLie` a subspace) and
  the headline **`spinLie_hasAdLambda_lorentzLie`**: every element of
  `𝔰𝔭𝔦𝔫⁺(3,1)` has an adjoint matrix in `𝔬(1,3)`, i.e. `Λ_*` is well-defined
  and lands in the Lorentz Lie algebra.

**Recorded obstruction.** The group-level Lemma 48 (`Spin⁺(3,1) ⊆ Pin(3,1)`,
`Λ(S) = Υ(Σ⁻¹SΣ)`) requires exponentiating this: the matrix-exponential
determinant identity `det (exp A) = exp (tr A)` (a listed *TODO* in Mathlib) and
the adjoint-exponential identity `exp(-G)·X·exp(G) = exp(-ad_G)(X)`. Those
analytic ingredients are the recorded open step; the algebraic Lie-algebra core is
complete.

Documentation: prepended a wave-12 section to `BookProof/STATUS.md` and this
section to `ARISTOTLE_SUMMARY.md` (existing history preserved). Remaining open
items: §A.3 Lemma 48 group-level exponentiation, Lemma 52; the §A.4–A.5 layer;
the N3 residue `denseCore_svd`; and the N7 external Wigner/Mackey bundle. All work
is committed and pushed to origin.

---

# Summary of changes for run 78f422ea-6d39-4b6b-a2c9-f09ba33571f6
Continued executing `FORMALIZATION_ROADMAP.md`, taking the next open step from the top of the previous wave's "still open" list: **Definition 49** of §A.3 (work-package N4).

**New module `BookProof/ChapterA3d.lean`** (registered in `BookProof.lean`) formalizes the *discrete Pin subgroup* `Ω = {±1, ±iγ⁰, ±γ⁰γ⁵, ±iγ⁵} ⊆ Pin(3,1)` as the **double cover** of the *discrete Lorentz subgroup* `Δ = {1, η, -η, -1} ⊆ O(1,3)`. It builds on the earlier `HasLambda`/`IsPin`/`LambdaOf`/`lambda_mem_lorentz`/`lambdaOf_neg` machinery (`ChapterA3c.lean`) and the concrete 4×4 Majorana matrix model, and is fully self-contained — **no external hypothesis** (no Pauli/Weyl input) is needed, since Ω is a finite explicit set and every membership/Λ-value is a concrete matrix computation.

Delivered:
- the sets `OmegaPin` (Ω) and `LorentzDelta` (Δ), and the real generators iγ⁰, iγ⁵, γ⁰γ⁵;
- generic helpers (`inv_of_sq_neg_one`, `det_sq_of_sq_neg_one`, `isPin_of_sq_neg_one`) and the integer-model reduction `hasLambda_of_intModel` that closes the conjugation identities by `decide`;
- per-generator `IsPin`/`LambdaOf` values with the explicit images Λ(±iγ⁰)=η, Λ(±γ⁰γ⁵)=-η, Λ(±iγ⁵)=-1, Λ(±1)=1;
- the headlines `omega_subset_pin` (Ω ⊆ Pin(3,1)) and `lambda_omega_mem_delta` (Λ(ω) ∈ Δ for every ω ∈ Ω — the 2-to-1 cover Ω → Δ), plus the corollary `delta_subset_lorentz` (Δ ⊆ O(1,3)).

Everything is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified with `lean_verify`); the whole project builds green (`lake build`, 8083 jobs). `ARISTOTLE_SUMMARY.md` and `BookProof/STATUS.md` were updated with a wave-11 section (existing history preserved) recording the new file and the remaining open items (§A.3 Lemma 48/Lemma 52, the §A.4–A.5 layer, the N3 `denseCore_svd` residue, and the N7 external bundle). All changes are committed and pushed to origin.

# Summary of changes for the latest run
Executed the next step of the formalization roadmap — **Definition 49** at the top of wave-10's "still open" list — and updated `ARISTOTLE_SUMMARY.md` and `BookProof/STATUS.md`. The full project builds green (`lake build`, 8083 jobs); all new content is `sorry`-free and axiom-clean (`lean_verify`/`#print axioms` show only `propext`, `Classical.choice`, `Quot.sound`).

New module `BookProof/ChapterA3d.lean` (registered in `BookProof.lean`) — **Definition 49** (§A.3, book line 5476): the *discrete Pin subgroup* `Ω = {±1, ±iγ⁰, ±γ⁰γ⁵, ±iγ⁵} ⊆ Pin(3,1)` is the double cover of the *discrete Lorentz subgroup* `Δ = {1, η, -η, -1} ⊆ O(1,3)`. It builds on wave-10's `HasLambda`/`IsPin`/`LambdaOf`/`lambda_mem_lorentz`/`lambdaOf_neg` (`ChapterA3c.lean`) and the concrete `4×4` Majorana model, and is **fully self-contained (no external hypothesis)** since `Ω` is a finite explicit set and every membership/`Λ`-value is a concrete matrix computation. Proved:
- sets `OmegaPin` (`Ω`), `LorentzDelta` (`Δ`); the real generators `omegaA0`=iγ⁰, `omegaA5`=iγ⁵, `omegaG05`=γ⁰γ⁵;
- generic helpers `inv_of_sq_neg_one` (S²=-1 ⇒ S⁻¹=-S), `det_sq_of_sq_neg_one`, `isPin_of_sq_neg_one`, and the integer-model reduction `hasLambda_of_intModel` (conjugations closed by `decide`);
- per-generator `HasLambda`/`IsPin`/`LambdaOf` values, with explicit images Λ(±iγ⁰)=η, Λ(±γ⁰γ⁵)=-η, Λ(±iγ⁵)=-1, Λ(±1)=1;
- headlines `omega_subset_pin` (Ω ⊆ Pin(3,1)), `lambda_omega_mem_delta` (Λ(ω) ∈ Δ for all ω ∈ Ω — the 2-to-1 cover Ω → Δ), and the corollary `delta_subset_lorentz` (Δ ⊆ O(1,3)).

Remaining open items (recorded in `BookProof/STATUS.md`): §A.3 Lemma 48 (`Spin⁺(3,1) = Σ∘SL(2,ℂ)∘Σ⁻¹`) and Lemma 52 (real-irrep classification); the §A.4–A.5 layer (Bargmann–Wigner, Majorana–Fourier/Energy unitarity Props 61/73/74/76, CPT/Cor 1); the N3 residue `denseCore_svd`; and the N7 Wigner/Mackey external bundle. All work is committed and pushed to origin.

# Wave 11 — N4 §A.3 Definition 49 (discrete Pin subgroup Ω, double cover of Δ)

Executed the next open step of `FORMALIZATION_ROADMAP.md` (the top of wave-10's "still open" list), landing **Definition 49** in the new file `BookProof/ChapterA3d.lean`. It formalizes the discrete Pin subgroup `Ω = {±1, ±iγ⁰, ±γ⁰γ⁵, ±iγ⁵}` as a self-contained 2-to-1 cover of the discrete Lorentz subgroup `Δ = {1, η, -η, -1}`, with headlines `omega_subset_pin`, `lambda_omega_mem_delta`, and `delta_subset_lorentz`. All content is `sorry`-free and axiom-clean; `lake build` green (8083 jobs); committed and pushed.

# Summary of changes for run 2aed7ae0-4ae5-4dee-b9af-75c01ae68228
Executed the next open steps of the formalization roadmap (the two items at the top of the wave-9 "still open" list) and updated `ARISTOTLE_SUMMARY.md`. The full project builds green (`lake build`, 8082 jobs); all new content is `sorry`-free and axiom-clean (`#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`).

New module `BookProof/ChapterA3c.lean` (registered in `BookProof.lean`) — the group-theoretic wrapper of **Prop 46**, completing the map `Λ : Pin(3,1) → O(1,3)` as a **2-to-1 surjective homomorphism**. It builds on wave-9's `lorentz_of_conj` and `real_pauli` (`ChapterA3b.lean`), working over ℝ with the real Majorana matrices `mgammaR`. Proved:
- Foundations `mgammaR`, `toC_mgammaR`, `mgammaR_clifford` (real Clifford set), `mgammaR_indep` (linear independence of the four iγ^μ, making Λ(S) well-defined);
- definitions `LorentzO` (O(1,3)), `HasLambda`, `IsPin` (Pin(3,1)), `LambdaOf`, with `hasLambda_unique`;
- lands in O(1,3): `lorentz_of_conjR`, `lambda_mem_lorentz`;
- homomorphism: `lambdaOf_mul` (Λ(S₁S₂)=Λ(S₁)Λ(S₂)) via `hasLambda_mul`, `isPin_mul`;
- 2-to-1 surjectivity: `cliffordR_lorentz_comb`, the ±S symmetry (`hasLambda_neg`/`isPin_neg`/`lambdaOf_neg`), `lambda_surjective`, and `lambda_two_to_one` (the fibre over λ is exactly {±S}). Surjectivity/2-to-1 use the external named hypothesis `PauliFundamental` (never an axiom).

`BookProof/ChapterB3.lean` — added `conditional_operator_identity`, the §B.3c algebraic identity: with Ψ = W D U† and D self-adjoint, Ψ R Ψ† = W D U† R U D W†, i.e. a change of reference marginal p₀→p (operator R = p/p₀) becomes conjugation of the singular-value factorization.

Documentation: prepended a wave-10 section to `BookProof/STATUS.md` and to `ARISTOTLE_SUMMARY.md` (existing history preserved), including the remaining open items: §A.3 Lemma 48 / Lemma 52; the §A.4–A.5 layer (Bargmann–Wigner, Majorana–Fourier/Energy unitarity, CPT); the N3 residue `denseCore_svd` (needs compact-operator spectral theory not in Mathlib); and the N7 Wigner/Mackey external bundle. All work is committed and pushed to origin.

# Wave 10 — N4 §A.3 Prop 46 group form (`Λ : Pin(3,1) → O(1,3)`) + N3 residue B.3c

Executed the next open steps of `FORMALIZATION_ROADMAP.md`: the two items at the
top of wave-9's "still open" list.  All new content is `sorry`-free and
axiom-clean (`#print axioms` shows only `propext`, `Classical.choice`,
`Quot.sound`); the full project builds green (`lake build`, 8082 jobs).

**New module `BookProof/ChapterA3c.lean`** (registered in `BookProof.lean`) — the
group-theoretic wrapper of **Prop 46**, completing the map
`Λ : Pin(3,1) → O(1,3)` as a **2-to-1 surjective homomorphism**.  It builds on
wave-9's metric-preservation core `lorentz_of_conj` and real Pauli theorem
`real_pauli` (`ChapterA3b.lean`), working over `ℝ` with the real Majorana
matrices `mgammaR` (the `iγ^μ` have integer entries).  Proved:
- Foundations: `mgammaR`, `toC_mgammaR`, `mgammaR_clifford` (real Clifford set),
  and `mgammaR_indep` (the four `iγ^μ` are `ℝ`-linearly independent, which makes
  the Lorentz matrix `Λ(S)` well-defined — `hasLambda_unique`).
- Definitions `LorentzO` (`O(1,3)`), `HasLambda`, `IsPin` (`Pin(3,1)`), `LambdaOf`.
- **Lands in `O(1,3)`** (`lorentz_of_conjR`, `lambda_mem_lorentz`).
- **Homomorphism** `lambdaOf_mul` : `Λ(S₁ S₂) = Λ(S₁) Λ(S₂)` (via `hasLambda_mul`,
  `isPin_mul`).
- **2-to-1 surjective**: `cliffordR_lorentz_comb`, the `±S` symmetry
  (`hasLambda_neg`/`isPin_neg`/`lambdaOf_neg`), `lambda_surjective` (every
  `λ ∈ O(1,3)` is `Λ(S)` for some `S ∈ Pin(3,1)`), and `lambda_two_to_one` (the
  fibre over `λ` is exactly `{±S}`).  Surjectivity/2-to-1 use the EXTERNAL named
  hypothesis `PauliFundamental` (Note 36), never an `axiom`.

**`BookProof/ChapterB3.lean`** — added `conditional_operator_identity`, the
**§B.3c** algebraic identity: with `Ψ = W D U†` and `D` self-adjoint,
`Ψ R Ψ† = W D U† R U D W†`, i.e. a change of reference marginal `p₀ → p`
(the operator `R = p/p₀`) becomes conjugation of the singular-value
factorization.  The compact-operator SVD `denseCore_svd` (producing `W, D, U`
from a Hilbert–Schmidt `Ψ`) needs compact-operator spectral theory absent from
Mathlib and stays the recorded open N3 residue.

Documentation: added a wave-10 section to `BookProof/STATUS.md` and this section
to `ARISTOTLE_SUMMARY.md` (existing history preserved).

Remaining open items (see `BookProof/STATUS.md`): §A.3 Lemma 48 (`Spin⁺(3,1)`) and
Lemma 52 (real-irrep classification); the §A.4–A.5 layer (Bargmann–Wigner,
Majorana–Fourier/Energy unitarity, CPT); the N3 residue `denseCore_svd`; and the
N7 mining (Wigner/Mackey `EXTERNAL` bundle, Ch. P re-scan).

All work is committed and pushed to origin.

---

# Summary of changes for run f422e952-3a4d-4f5d-a962-055deb3e45a9
Executed the next open steps of the formalization roadmap: the §A.3 EXTERNAL representation-theory layer (work-package N4), building on the existing concrete 4×4 Majorana / gamma-matrix model (`BookProof/ChapterA3.lean`).

New module `BookProof/ChapterA3b.lean` (registered in `BookProof.lean`), `sorry`-free and axiom-clean (`#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`). The full project builds green (`lake build`, 8081 jobs); only pre-existing cosmetic linter notes remain, none in scope of the new content beyond a single long-line note.

Proved:
- Lemma 40 (charge conjugation Θ) — fully concrete, no external input: entrywise complex conjugation on ℂ⁴ (`chargeConj`) is an anti-linear involution commuting with every Majorana matrix iγ^μ (`chargeConj_involutive`/`_add`/`_smul`, `chargeConj_mgamma_commutes`).
- Prop 37 (real Pauli theorem) `real_pauli` — two real Clifford sets α^μ, β^μ are related by a real S with |det S| = 1, β^μ = S α^μ S⁻¹, unique up to sign. Derived from the Pauli fundamental theorem (Note 36), introduced as the EXTERNAL named hypothesis `PauliFundamental` (never an axiom, matching the §A.2/§A.3 design). Supporting complexification API (`IsCliffordC`/`IsCliffordR`, `toC`, `isCliffordC_toC`, `toC_mul`/`_one`/`_det`/`_conj`/`_inv`, `exists_real_of_conj_fixed`, `toC_injective`) is all proven.
- Prop 46 (metric-preservation core) `lorentz_of_conj` — if S is invertible and a real matrix Λ describes its conjugation action on the Majorana basis (S⁻¹ iγ^μ S = Σ_ν Λ^μ_ν iγ^ν), then Λ η Λᵀ = η, i.e. Λ ∈ O(1,3); the computational heart of Λ : Pin(3,1) → O(1,3).

Documentation: recorded a wave-9 section in `BookProof/STATUS.md` and prepended a matching section to `ARISTOTLE_SUMMARY.md` (existing history preserved).

Remaining open items (noted in `BookProof/STATUS.md`): the group-theoretic wrapper of Prop 46 (Λ as homomorphism, 2-to-1 surjectivity), Lemma 48/52 and the §A.4–A.5 layer (Bargmann–Wigner, Majorana–Fourier/Energy unitarity, CPT); the N3 residue (`denseCore_svd` + B.3c); and the N1 hard converse of Prop 11.

All work is committed and pushed to origin.

# Wave 9 — N4 §A.3: charge conjugation (Lemma 40), real Pauli theorem (Prop 37), metric-preservation core of Prop 46

Executed the next open steps of `FORMALIZATION_ROADMAP.md`: the **§A.3 EXTERNAL
representation-theory layer** (work-package **N4**), building on the concrete
`4×4` Majorana / gamma-matrix model already in `BookProof/ChapterA3.lean`.

**New module `BookProof/ChapterA3b.lean`** (registered in `BookProof.lean`),
`sorry`-free and axiom-clean (`#print axioms` shows only `propext`,
`Classical.choice`, `Quot.sound`). The full project builds green
(`lake build`, 8081 jobs).

What it proves:
- **Lemma 40 (charge conjugation `Θ`)** — fully concrete, no external input:
  `chargeConj` (entrywise complex conjugation on `ℂ⁴`) is an anti-linear
  involution commuting with every Majorana matrix `iγ^μ`
  (`chargeConj_involutive`/`_add`/`_smul`, `chargeConj_mgamma_commutes`), the
  finite-dimensional instance of the §A.0 Def 8 C-conjugation.
- **Prop 37 (real Pauli theorem)** `real_pauli` — two real Clifford sets
  `α^μ, β^μ` are related by a real `S` with `|det S| = 1`, `β^μ = S α^μ S⁻¹`,
  unique up to sign. Proved from the **Pauli fundamental theorem** (Note 36),
  introduced as the EXTERNAL named hypothesis `PauliFundamental` (cite
  `Good1955Properties`; never an `axiom`, matching the §A.2/§A.3 design). The
  proof complexifies, uses uniqueness-up-to-scalar to show the conjugate
  `T̄ = c·T` with `|c| = 1`, then rescales `S = (|det T|^{-1/4}·exp(i·arg c/2))·T`
  to a real matrix of unit-modulus determinant. Supporting complexification
  API: `IsCliffordC`/`IsCliffordR`, `toC`, `isCliffordC_toC`,
  `toC_mul`/`_one`/`_det`/`_conj`/`_inv`, `exists_real_of_conj_fixed`,
  `toC_injective`.
- **Prop 46 (metric-preservation core)** `lorentz_of_conj` — if `S` is
  invertible and a real matrix `Λ` gives its conjugation action on the Majorana
  basis (`S⁻¹ iγ^μ S = Σ_ν Λ^μ_ν iγ^ν`), then `Λ η Λᵀ = η`, i.e.
  `Λ ∈ O(1,3)` — the computational heart of `Λ : Pin(3,1) → O(1,3)`, from the
  Clifford relation.

Documentation: added a matching wave-9 section to `BookProof/STATUS.md`.

Remaining open items (recorded in `BookProof/STATUS.md`): the group-theoretic
wrapper of Prop 46 (`Λ` as homomorphism, 2-to-1 surjectivity), Lemma 48/52 and
the §A.4–A.5 layer (Bargmann–Wigner, Majorana–Fourier/Energy unitarity, CPT);
the N3 residue (`denseCore_svd` + B.3c); and the N1 hard converse of Prop 11.

All work is committed and pushed to `origin/main`.

# Summary of changes for run e708899c-81d4-4678-9445-d21b83d2ec44
Executed the next open step of the formalization roadmap: the **real side of Prop 11** (§A.1, the N1 residue), complementing the earlier complex-side classification.

**New module `BookProof/ChapterA1h.lean`** (registered in `BookProof.lean`), `sorry`-free and axiom-clean (`#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`). The full project builds green (`lake build`, 8080 jobs) and the new file is warning-free.

What it proves:
- R-type predicates for a real system, phrased via the R-imaginary operators of Def 8.2 (the endomorphism division-algebra / Frobenius trichotomy): `IsRRealType` (no commuting R-imaginary, algebra ℝ), `IsRComplexType` (a commuting R-imaginary but no anticommuting pair, algebra ℂ), `IsRPseudorealType` (an anticommuting `HasQuaternionicRImaginary` pair, algebra ℍ).
- `rType_exhaustive` — every real system is of exactly one R-type — with the three mutual-exclusion lemmas.
- `cxSystem_reducible_of_commuting_rImaginary` — the Def-10 link: a real system on a non-trivial space with a commuting R-imaginary has a reducible complexification, proved by the concrete V ⊕ V̄ eigenspace splitting (the complexified operator `Jc := cxMap J` is ℂ-linear with `(Jc)² = -1`, commutes with the complexified system, and its `+i` eigenspace `ker (Jc − i)` is a proper, non-trivial subsystem).
- Corollaries `IsRReal.isRRealType`, `IsRReal.excludes_other_types`, `IsRComplexType.not_isRReal`, `IsRPseudorealType.not_isRReal`.

Documentation: added matching wave-8 sections to `BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md`.

Remaining open items (recorded in `BookProof/STATUS.md`): the hard converse of Prop 11 (a reducible complexification actually yields a commuting R-imaginary — the Frobenius/Schur division-algebra direction), the N3 residue `denseCore_svd` (infinite-dimensional compact-operator SVD, absent from Mathlib), and the N4 external Pauli/Weyl layer (§A.4–A.5).

All work is committed and pushed to `origin/main`.

# Wave 8 — N1 residue: real-system R-type trichotomy (Prop 11, real side)

Executed the next open step of `FORMALIZATION_ROADMAP.md`: the **real side of
Prop 11** (§A.1), complementing wave 7's complex-side `realification_classification`.

New module `BookProof/ChapterA1h.lean` (registered in `BookProof.lean`),
`sorry`-free and axiom-clean (`#print axioms` shows only `propext`,
`Classical.choice`, `Quot.sound`). The whole project builds green with
`lake build` (8080 jobs); the new file is warning-free.

Headline results proved:
- Def-9-dual R-type predicates on a real system, via the **R-imaginary**
  operators of Def 8.2 (endomorphism division-algebra / Frobenius trichotomy):
  `IsRRealType` (no commuting R-imaginary, algebra `ℝ`), `IsRComplexType`
  (a commuting R-imaginary but no anticommuting pair, algebra `ℂ`),
  `IsRPseudorealType` (an anticommuting `HasQuaternionicRImaginary` pair,
  algebra `ℍ`).
- `rType_exhaustive` — every real system is of exactly one R-type (with the
  three mutual-exclusion lemmas).
- `cxSystem_reducible_of_commuting_rImaginary` — the Def-10 link: a real system
  on a non-trivial space with a commuting R-imaginary has a **reducible**
  complexification. Proof = the concrete `V ⊕ V̄` eigenspace splitting: the
  complexified `Jc := cxMap J` (`rImagCx`) is `ℂ`-linear with `(Jc)² = -1`
  (`rImagCx_sq`) and commutes with the complexified system (`rImagCx_commutes`),
  so its `+i` eigenspace `ker (Jc - i)` is a proper, non-trivial subsystem of
  `(M, Cx W)`.
- `IsRReal.isRRealType`, `IsRReal.excludes_other_types`,
  `IsRComplexType.not_isRReal`, `IsRPseudorealType.not_isRReal` — an R-real
  system (irreducible complexification) is of R-real type and excludes the
  other two.

Documentation updated: `BookProof/STATUS.md` gains a matching wave-8 section at
the top. Remaining open items recorded there: the *hard converse* of Prop 11
(reducible complexification ⇒ commuting R-imaginary exists — the Frobenius/Schur
division-algebra direction), the N3 residue (`denseCore_svd`, infinite-
dimensional compact-operator SVD absent from Mathlib), and the N4 `EXTERNAL`
Pauli/Weyl layer (§A.4–A.5).

---

# Summary of changes for run 427d165b-e64c-46a8-b06c-9339c73e88ee
Executed the next open step of `FORMALIZATION_ROADMAP.md` — the first item in the work-package queue, the **N1 residue** (§A.1, Prop 12 converse). This was the recorded crux `realification_irreducible_of_not_isCReal`, which earlier waves left open because it appeared to require the Frobenius–Schur orthogonality `Y ⊥ J Y`.

New module `BookProof/ChapterA1g.lean` (registered in `BookProof.lean`), sorry-free and axiom-clean (`#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`; no new `axiom` or `@[implemented_by]`). The whole project builds green with `lake build` (8079 jobs); the new file is free of warnings and sorries.

Headline results proved:
- `realification_irreducible_of_not_isCReal` — a normal, complex-irreducible Schur system that is not C-real has an irreducible realification (the R-pseudoreal / R-complex cases of Prop 12; the converse of the existing `realification_reducible_of_conjugation`).
- `realification_irreducible_iff` — the full Def-10 dichotomy: realification irreducible ⇔ not C-real.
- `realification_classification` — the complex-side statement of Prop 11's trichotomy: exactly one of C-real (realification reducible) / C-pseudoreal / C-complex (both irreducible) holds.

Method: rather than establishing `Y ⊥ J Y` directly, the proof runs the Frobenius–Schur construction through the linear/antilinear decomposition from `ChapterA2c.lean`. From a reducible realification it takes the real orthogonal projection `E` onto a proper subsystem `Y` (self-adjoint; commutes with the system via `starProjection_realCommutes`, using that the realification of a normal system is normal). Its ℂ-antilinear part `Q = Qanti E` is self-adjoint and ℂ-antilinear; by the Schur hypothesis `Q² = r·1` with real `r ≥ 0` (`Qanti_sq_scalar`). If `r > 0`, `θ = r^(-1/2)·Q` is an anti-unitary involution commuting with the system — a C-conjugation — giving C-real (contradiction); if `r = 0`, then `Q = 0`, so `E` is ℂ-linear and `Y` is a proper complex subsystem, contradicting complex irreducibility. The Schur input is the named hypothesis `IsSchurFull`, never an axiom, matching the §A.2 design.

Documentation updated as requested: `ARISTOTLE_SUMMARY.md` gains a wave-7 section at the top (existing content preserved) and `BookProof/STATUS.md` gains a matching wave-7 section.

Remaining open roadmap items (recorded in `BookProof/STATUS.md`): the other N1 sub-item `real_system_trichotomy` (Prop 11 stated intrinsically on a real system, which needs new R-pseudoreal/R-complex predicate definitions), the N3 residue (`denseCore_svd`, an infinite-dimensional compact-operator SVD absent from Mathlib), and the N4 external Pauli/Weyl layer (§A.4–A.5). All changes are committed and pushed.

# Summary of changes (wave 7) — N1 residue: converse realification dichotomy complete

Continued the `FORMALIZATION_ROADMAP.md` queue in the `BookProof` library.  The
first open queue item was the **N1 residue** (§A.1, Prop 12 converse): the
recorded crux `realification_irreducible_of_not_isCReal`, previously blocked on
the Frobenius–Schur orthogonality obstruction.  This wave discharges it in full.

**New module `BookProof/ChapterA1g.lean`, sorry-free and axiom-clean**
(`#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`; no new
`axiom` or `@[implemented_by]`).  Registered in `BookProof.lean`; the whole
project builds green (`lake build`, 8079 jobs), the new file free of warnings and
sorries.

Headline results:
- **`realification_irreducible_of_not_isCReal`** — a *normal*, complex-irreducible
  Schur system `(M, V)` that is **not** C-real has an **irreducible**
  realification `(M, V^r)`.  This is the converse of the existing
  `realification_reducible_of_conjugation` and was the recorded N1 obstruction.
- **`realification_irreducible_iff`** — the full Def-10 dichotomy: for such a
  system, the realification is irreducible iff the system is not C-real.
- **`realification_classification`** — the complex-side statement of Prop 11's
  trichotomy: exactly one of C-real (realification reducible) / C-pseudoreal
  (irreducible) / C-complex (irreducible) holds.

How the orthogonality crux was resolved.  Instead of proving `Y ⊥ J Y` for a
proper real subsystem `Y` directly, the proof runs the **Frobenius–Schur**
construction through the linear/antilinear decomposition of `ChapterA2c.lean`.
From a reducible realification take `E := Y.starProjection` (self-adjoint;
commutes with `M` via `starProjection_realCommutes`, using that the realification
of a normal system is normal, `rxSystem_isNormal`/`adjoint_rxMap`).  Its
`ℂ`-antilinear part `Q := Qanti E` is self-adjoint (`Qanti_selfAdjoint`),
commutes with `M`, and `ℂ`-antilinear (`anti_conj_smul`).  By the Schur
hypothesis its square is a non-negative real scalar `Q² = r·1`
(`Qanti_sq_scalar`, extracting `r ∈ ℝ`, `r ≥ 0` from the complex Schur scalar via
the real-inner-product identities `real_inner_smul_I`/`real_inner_smul_self`).
If `r > 0`, `θ := r^{-1/2}·Q` is an anti-unitary involution commuting with `M`
(built as a `LinearIsometryEquiv` over `starRingEnd ℂ`), a C-conjugation — so `M`
is C-real (`isCReal_of_antilinear_sq_pos`), contradiction.  If `r = 0`, then
`Q = 0` (`selfAdjoint_sq_eq_zero`), so `E` is `ℂ`-linear
(`clinear_of_Qanti_eq_zero`) and `Y` is a proper non-trivial *complex*
subsystem, contradicting complex irreducibility.  The Schur input is the named
hypothesis `IsSchurFull` (never an `axiom`), matching the §A.2 design.

Remaining open items in the roadmap: the other N1 sub-item
`real_system_trichotomy` (Prop 11's full type assignment stated intrinsically on
a real system, which needs new R-pseudoreal/R-complex predicate definitions) is
still open and recorded in `BookProof/STATUS.md`; the N3 residue (`denseCore_svd`,
an infinite-dimensional compact-operator SVD absent from Mathlib) and the N4
external Pauli/Weyl layer (§A.4–A.5) remain.  Documentation updated:
`BookProof/STATUS.md` gains a wave-7 section; this file gains this section at the
top (existing content preserved).  All changes are committed and pushed.

# Summary of changes for run 169671c5-c79e-4813-9350-af1c2222ae34
Executed the next open step of `FORMALIZATION_ROADMAP.md`: I discharged **Prop 16** of work-package **N2** (§A.2, the ℝ/ℂ/ℍ commutant classification), which was the last remaining N2 item after the previous wave finished Prop 15. This **completes work-package N2 in full**.

New module `BookProof/ChapterA2e.lean`, `sorry`-free and axiom-clean (`#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`; no new `axiom` or `@[implemented_by]`). It is registered in `BookProof.lean`; the whole project builds green (`lake build`, 8078 jobs), with the new file free of warnings and sorries.

What Prop 16 says, in the project's framework: a complex system's *realification* is the space viewed over ℝ with operators restricted to ℝ-scalars; a *realification system isometry* `β : V ≃ₗᵢ[ℝ] W` (`IsRealSystemIso`) carries the realified `M` onto the realified `N`. A complex system isometry is such a `β` that is ℂ-linear (`CLinear`); an antiisometry is one that is ℂ-antilinear (`CAntilinear`). Prop 16 ("two C-complex/C-pseudoreal Schur systems are isometric or antiisometric iff their realifications are isometric") becomes: a ℂ-linear-or-ℂ-antilinear realification isometry exists iff a realification isometry exists.

Both cases are proved:
- C-complex (`Ccomplex_realification_dichotomy`, `Ccomplex_iso_or_antiiso_iff_realification_iso`): via the already-proven Prop 18, the real commutant is ℂ, forcing the transported complex structure `K = β∘(i·)∘β⁻¹` to be `±i`, so `β` itself is ℂ-linear or ℂ-antilinear.
- C-pseudoreal (`Cpseudoreal_realification_dichotomy`, `Cpseudoreal_iso_or_antiiso_iff_realification_iso`): built on quaternion rotation operators `rot θ p s : w ↦ p•w + s•θw` with `rot_comp` (composition = quaternion multiplication), a Frobenius–Schur orthogonality lemma `theta_inner_self_zero` (`x ⊥ θx` when `θ²=-1`) giving `rot_isometry`/`rotEquiv`, and `qembed_eq_rot` bridging Prop 19; a unit rotation conjugates `K` to `i`, making `β` composed with it ℂ-linear (or `β` already ℂ-antilinear in the degenerate case). No new external hypotheses beyond the `IsSchurFull` Schur predicate already used by Props 18–19.

Documentation updated as requested: `BookProof/STATUS.md` gains a wave-6 section recording N2 as DONE with a refreshed open list, and `ARISTOTLE_SUMMARY.md` gains a new wave-6 section at the top (existing content preserved).

Remaining open items in the roadmap (unchanged, documented in `BookProof/STATUS.md`): the N1 residue (Prop 11 trichotomy + Prop 12 converse), the N3 residue (`denseCore_svd`, an infinite-dimensional compact-operator SVD absent from Mathlib), and the N4 external Pauli/Weyl layer (§A.4–A.5). All changes are committed and pushed.

# Summary of changes (wave 6) — N2 Prop 16 complete (work-package N2 DONE)

Continued the `FORMALIZATION_ROADMAP.md` queue in the `BookProof` library. The
previous wave (wave 5) had discharged the §A.2 N2 leftover **Prop 15**; the only
remaining N2 item was **Prop 16**, which this wave completes in full.

**New module `BookProof/ChapterA2e.lean` (N2, Prop 16), sorry-free and
axiom-clean** (`#print axioms` shows only `propext`, `Classical.choice`,
`Quot.sound`; no new `axiom` or `@[implemented_by]`). This **completes
work-package N2** (§A.2 — the ℝ / ℂ / ℍ commutant classification and its
isometry criteria).

Framework. A complex system `(M, V)`'s *realification* is `V` as a real
inner-product space with each operator restricted to `ℝ`-scalars; a
**realification system isometry** `β : V ≃ₗᵢ[ℝ] W` (`IsRealSystemIso`) carries
the realified `M` onto the realified `N` by conjugation. A complex system
isometry is such a `β` that is additionally `ℂ`-linear (`CLinear`); a complex
system antiisometry is one that is `ℂ`-antilinear (`CAntilinear`). So **Prop 16**
("two C-complex / C-pseudoreal Schur systems are isometric *or* antiisometric iff
their realifications are isometric") becomes: a `ℂ`-linear-or-`ℂ`-antilinear
realification isometry exists **iff** a realification isometry exists.

- Shared machinery: `betaR`, `conjClmR`, `IsRealSystemIso`, `CLinear`,
  `CAntilinear`, and the transported complex structure `transK β = β ∘ (i·) ∘ β⁻¹`
  (`transK_sq`: `K² = -1`; `transK_realCommutes`: `K` lies in the real commutant
  of `N`).
- **C-complex case** — `Ccomplex_realification_dichotomy` and its packaged iff
  `Ccomplex_iso_or_antiiso_iff_realification_iso`: by Prop 18
  (`Rcomplex_realCommutant_eq_complex`) the real commutant is `ℂ`, so `K = c·1`
  with `c² = -1`, forcing `c = ±i`; hence `β` is *itself* `ℂ`-linear or
  `ℂ`-antilinear.
- **C-pseudoreal case** — `Cpseudoreal_realification_dichotomy` and its packaged
  iff `Cpseudoreal_iso_or_antiiso_iff_realification_iso`: built on the quaternion
  operators `rot θ p s : w ↦ p•w + s•θw` (the quaternion `p + s·j` acting on
  `w`), with `rot_comp` (composition = quaternion multiplication), the
  Frobenius–Schur orthogonality `theta_inner_self_zero` (`x ⊥ θx` for `θ² = -1`)
  yielding `rot_isometry` / `rotEquiv` (unit `rot`s are isometric equivalences),
  and `qembed_eq_rot` bridging Prop 19's output. By Prop 19 `K = rot pK sK`; the
  unit rotation `u = (pK + i, sK)/n` conjugates `K` to `mulI`, so `β` composed
  with `rotEquiv u` is `ℂ`-linear (or, in the degenerate `K = -mulI` case, `β`
  is already `ℂ`-antilinear). No new `EXTERNAL` input beyond the `IsSchurFull`
  named Schur predicate already used by Props 18–19.

The module is registered in `BookProof.lean`; `lake build BookProof` is green
(8078 jobs), the new file free of warnings and sorries. Documentation updated:
`BookProof/STATUS.md` records the wave-6 completion (N2 DONE) with a refreshed
open list.

Remaining open (documented in `BookProof/STATUS.md`): the N1 residue (Prop 11
`real_system_trichotomy` + Prop 12 converse
`realification_irreducible_of_not_isCReal`), the N3 residue (`denseCore_svd`,
infinite-dimensional compact-operator SVD absent from Mathlib), and the N4
`EXTERNAL` Pauli/Weyl layer (§A.4–A.5). All changes committed and pushed.

---

# Summary of changes for run b7e12fd4-2852-4316-904c-fc1cb53ffd66
Continued the `FORMALIZATION_ROADMAP.md` queue in the `BookProof` library after the previous wave (which had completed work-packages N9 and N10). The next open item was the §A.2 N2 leftover (Props 15–16); I discharged **Prop 15** in full.

**New module `BookProof/ChapterA2d.lean` (N2, Prop 15), sorry-free and axiom-clean** (`#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`; no new `axiom` or `@[implemented_by]`):
- `conjCLM` — conjugation of an operator by a ℂ-linear isometric equivalence, and `IsSystemIso` — a system isometry carries `M` onto `N` by conjugation.
- `conjAU` — transport of an anti-unitary along an isometry, with `conjAU_commutesAntiUnitary`.
- `unitScaleEquiv` (multiplication by a unit-modulus scalar as a ℂ-linear isometric equivalence), `exists_unit_sqrt` (unit scalars have unit-modulus square roots), and `conjCLM_unitScale`.
- Headline `Rreal_isometric_iff_complexification_isometric` (**Prop 15**): for complex Schur systems `(M,V)`, `(N,W)` with C-conjugations, a conjugation-intertwining system isometry (equivalently, a real-form isometry) exists iff a system isometry exists — the "R-real systems are isometric iff their complexifications are isometric" criterion, proved from Lemma 14 (`antiisometry_unique_up_to_phase`) by phase-rescaling.

The module is registered in `BookProof.lean`; `lake build BookProof` is green (8077 jobs), with the new file free of warnings.

Documentation updated as requested: `BookProof/STATUS.md` records the wave-5 completion with a dedicated Prop 15 section and a refreshed open list, and `ARISTOTLE_SUMMARY.md` has a new wave-5 section.

Remaining open (documented with reasons in `BookProof/STATUS.md`): the N2 residue is now only Prop 16 (iso-or-antiiso ⇔ realifications isometric — needs an ℝ-linear-isometry decomposition into ℂ-linear/ℂ-antilinear parts, a Schur scalar extraction, and a ℂ→ℝ `LinearIsometryEquiv.restrictScalars` bridge absent from Mathlib), plus the previously recorded harder residues N1 (Prop 11 trichotomy + Prop 12 converse, needing a Frobenius–Schur orthogonality argument), N3 (`denseCore_svd`, infinite-dimensional compact-operator SVD absent from Mathlib), and N4 (Pauli/Weyl `EXTERNAL` layer, §A.4–A.5). All changes are committed and pushed.

# Summary of changes for run 8296bfb3-69af-4cfc-ade5-561edad0b73c
Executed the open, fully-specified work packages from `FORMALIZATION_ROADMAP.md`, adding two brand-new modules to the `BookProof` library. Both build cleanly (`lake build` green, 8076 jobs), contain no `sorry`/`admit`, and every result is axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified with `#print axioms`). No new `axiom` or `@[implemented_by]` was introduced, and no `EXTERNAL` hypothesis is used in the new files.

**N9 — Chapter G II (`BookProof/ChapterG2.lean`), deliverables G.8–G.12, all proved:**
- G.8 `cond_of_null`, `not_isProbabilityMeasure_cond_null` (conditioning fails on null constraint sets).
- G.9 `no_translation_invariant_probabilityMeasure`, `translation_invariant_l2_eq_zero`, `no_translation_invariant_unit_vector` (the Dirac obstruction for any countably infinite gauge group).
- G.10 headline `no_continuous_gauge_fixing_circle` and `gauge_fixing_section_discontinuous` (the Gribov ambiguity, via an intermediate-value/connectedness argument).
- G.11 the BRST cohomology layer: `brstKer`, `brstIm`, `brstIm_le_brstKer`, `mem_brstKer_iff`, `mem_brstIm_iff`, `brstCohomology`, the full splitting isomorphism `brstCohomology_equiv : H ≃ₗ[A] ker(·Q) × (A ⧸ (Q))` (I hand-built the forward/inverse linear maps and the two round-trip identities), and the headline `brst_physical_iff_gauge_invariant`.
- G.12 `haarAverage_invariant`, `haarAverage_idempotent`, `integral_haarAverage` (Haar averaging is the invariant projection preserving expectations).

**N10 — Chapter B §§7–9 (`BookProof/ChapterB7.lean`), deliverables B7.1–B7.4, all proved:**
- B7.1 `koopman_comp`, `koopman_refl`, `koopmanRep_mul` (Koopman functoriality / unitary group representation).
- B7.2 `koopman_const` (Koopman fixes constants).
- B7.3 `eventMap_measure`/`_inter`/`_union`/`_compl`/`_leftInverse` and `koopman_indicatorConstLp` (deterministic transformations = event-algebra automorphisms).
- B7.4 `hadamard_not_deterministic` (complementarity = a non-deterministic unitary).

Both files are registered in `BookProof.lean`, and `BookProof/STATUS.md` now records the wave-4 completion.

**Not attempted (documented in `BookProof/STATUS.md`):** the remaining roadmap residues N1 (Prop 11 trichotomy + Prop 12 converse), N2 (Props 15–16), N3 (`denseCore_svd`), and N4 (Pauli/Weyl layer). These depend on mathematical infrastructure that is absent from Mathlib or not yet built in the project (e.g. a cross-system isometry/equivalence notion for Props 15–16, and an infinite-dimensional compact-operator singular-value decomposition for N3); they had already resisted earlier passes, and attempting them without that infrastructure risked introducing unfaithful statements, so they are left as honest open items rather than forced.

# Summary of changes for run dd4a78d1-89b6-4729-a746-897882522b4f
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next open queue item — the **N3 residue** (Chapter B §B.3, the partial-isometry layer of the singular-value expansion `Ψ = W D U†`). Since Mathlib has no `PartialIsometry` type for operators, I built the API from scratch in a new file `BookProof/ChapterB3.lean` (now imported by `BookProof.lean`):

- `IsPartialIsometry V := V ∘L V† ∘L V = V` and its pointwise form `IsPartialIsometry.apply`.
- `adjointComp_isSelfAdjoint` / `compAdjoint_isSelfAdjoint`: `V†V` and `VV†` are always self-adjoint.
- `IsPartialIsometry.adjointComp_isIdempotent` / `IsPartialIsometry.compAdjoint_isIdempotent`: for a partial isometry `V†V` and `VV†` are orthogonal projections (the requested `V†V`/`VV†`-projection API triple).
- `IsPartialIsometry.adjoint`: the adjoint of a partial isometry is a partial isometry (`V† V V† = V†`).
- `isPartialIsometry_of_adjointComp_isIdempotent` and the packaged equivalence `isPartialIsometry_iff_adjointComp_isIdempotent`: the textbook characterization `V` partial isometry ⇔ `V†V` an orthogonal projection.
- `norm_map_of_adjointComp_eq`: a partial isometry is norm-preserving on its initial space (`V†V x = x ⇒ ‖V x‖ = ‖x‖`).

Everything is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, checked via `#print axioms`/verification); the whole project builds green with no new warnings. The still-open part of N3 — the dense-core singular-value expansion itself (`denseCore_svd`) and the B.3c conditional operator identity — is recorded in `BookProof/STATUS.md`; nothing was introduced as an `axiom` or `sorry`.

As requested, I updated `ARISTOTLE_SUMMARY.md` (new top section) and `BookProof/STATUS.md` (new `ChapterB3.lean` section plus refreshed N3 obstruction note). `FORMALIZATION_ROADMAP.md` and content outside the N3 scope were left untouched. All changes are committed and pushed.

# Summary of changes (latest run) — N3 residue, partial-isometry API (§B.3)
Continued executing `FORMALIZATION_ROADMAP.md`, taking the next open queue item.
With N8 (Chapter U), N2 (commutant classification, Props 17–19) and the
realification half of N1 already landed, the next open package was the **N3
residue** (Chapter B §B.3, the partial-isometry layer of the singular-value
expansion `Ψ = W D U†`). Mathlib has no `PartialIsometry` for operators, so I
added the new file **`BookProof/ChapterB3.lean`** (now imported by
`BookProof.lean`) building the API from scratch:

- `IsPartialIsometry V := V ∘L V† ∘L V = V` (Def) with pointwise form
  `IsPartialIsometry.apply`.
- `adjointComp_isSelfAdjoint` / `compAdjoint_isSelfAdjoint`: `V†V` and `VV†` are
  always self-adjoint.
- `IsPartialIsometry.adjointComp_isIdempotent` /
  `IsPartialIsometry.compAdjoint_isIdempotent`: for a partial isometry, `V†V`
  and `VV†` are orthogonal projections — the requested `V†V`/`VV†`-projection
  API triple.
- `IsPartialIsometry.adjoint`: the adjoint of a partial isometry is a partial
  isometry (`V† V V† = V†`).
- `isPartialIsometry_of_adjointComp_isIdempotent` and the equivalence
  `isPartialIsometry_iff_adjointComp_isIdempotent`: the textbook
  characterization `V` partial isometry ⇔ `V†V` an orthogonal projection
  (proved via the `‖V(1 - V†V)x‖² = 0` inner-product computation).
- `norm_map_of_adjointComp_eq`: a partial isometry is norm-preserving on its
  initial space (`V†V x = x ⇒ ‖V x‖ = ‖x‖`).

Everything in the new file is `sorry`-free and axiom-clean (only `propext`,
`Classical.choice`, `Quot.sound`, verified with `#print axioms` /
`lean_verify`), builds with no new warnings, and the whole project builds green
(`lake build`, 8074 jobs). The remaining N3 residue — the dense-core
singular-value expansion `denseCore_svd` itself and the B.3c conditional
operator identity — is recorded precisely in `BookProof/STATUS.md`; nothing was
introduced as an `axiom` or `sorry`.

`BookProof/STATUS.md` was updated (new `ChapterB3.lean` section, N3 obstruction
note refreshed) and this new section prepended to `ARISTOTLE_SUMMARY.md`.
`FORMALIZATION_ROADMAP.md` and content outside the N3 scope were left
untouched. All changes are committed and pushed.

# Summary of changes for run 063a1a2b-8e78-48b4-b55c-8ef8620be820
Continued executing `FORMALIZATION_ROADMAP.md`, taking the next open queue item — the **N1 residue** (§A.1, Props 11/12 of Chapter A). I added a new file **`BookProof/ChapterA1f.lean`** (imported by `BookProof.lean`) that formalizes the realification-side half of the Def 10 / Prop 12 dichotomy, complementing the existing `V ⊕ V̄` splitting in `ChapterA1e.lean`:

- `conjFixed θ := {v : θ v = v}` — the real fixed space of an anti-unitary `θ`, packaged as a real subspace of the realification `V^r` (the real form `W` with `V = W ⊕ i·W`), with supporting API `mem_conjFixed`, `conjFixed_isClosed`, `conjFixed_invariant`, `conjFixed_isSubsystem`, and the non-triviality/properness lemmas `conjFixed_ne_bot` / `conjFixed_ne_top`.
- Headline `realification_reducible_of_conjugation`: if a complex system `(M, V)` on a non-trivial space admits a C-conjugation `θ` (so `M` is C-real), its realification `(M, V^r)` is reducible (`conjFixed θ` is a proper non-trivial subsystem).
- `isCReal_realification_reducible` (C-real ⇒ realification reducible) and its contrapositive `not_isCReal_of_realification_irreducible`.

Everything is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified via `#print axioms`), builds with no warnings, and the whole project builds green (`lake build`, 8073 jobs).

I also attempted the deeper converse direction (a normal irreducible complex system that is not C-real has an irreducible realification — the R-pseudoreal / R-complex cases of Prop 12), but this is a genuine Frobenius–Schur invariant-real-structure construction whose crux (the orthogonality `Y ⊥ J Y`) does not follow from normality alone and is tied to the §A.2 commutant classification. It could not be discharged in this pass, so I reverted the attempt to keep the codebase `sorry`-free and recorded it precisely as remaining N1 residue in `BookProof/STATUS.md` — never introduced as an `axiom` or `sorry`.

As requested, I updated `BookProof/STATUS.md` (new `ChapterA1f.lean` section plus obstruction note) and prepended a new top section to `ARISTOTLE_SUMMARY.md` describing this pass. `FORMALIZATION_ROADMAP.md` and content outside the N1 scope were left untouched. All changes are committed and pushed.

# Summary of changes (latest run) — N1 residue, R-real realification dichotomy
Continued executing `FORMALIZATION_ROADMAP.md`, taking the next open step in the queue — the **N1 residue** (§A.1, Props 11/12). The previous passes had built the whole §A.1 substructure (`ChapterA1`/`A1b`/`A1c`/`A1d`/`Complexification`) and the `V ⊕ V̄` splitting `realification_splits` (`ChapterA1e.lean`). This pass adds the new file **`BookProof/ChapterA1f.lean`** (now imported by `BookProof.lean`), formalizing the realification-side half of the Def 10 / Prop 12 dichotomy:

- `conjFixed θ := {v : θ v = v}` — the real fixed space of an anti-unitary `θ`, packaged as a real subspace of the realification `V^r` (the real form `W` with `V = W ⊕ i·W`), with the supporting API `mem_conjFixed`, `conjFixed_isClosed`, `conjFixed_invariant`, `conjFixed_isSubsystem`, and the non-triviality/properness lemmas `conjFixed_ne_bot` / `conjFixed_ne_top`.
- **`realification_reducible_of_conjugation`** — if a complex system `(M, V)` on a non-trivial space admits a C-conjugation `θ` (so `M` is C-real), its realification `(M, V^r)` is **reducible**: `conjFixed θ` is a proper non-trivial real subsystem.
- **`isCReal_realification_reducible`** (C-real ⇒ realification reducible) and its contrapositive **`not_isCReal_of_realification_irreducible`** (realification irreducible ⇒ not C-real).

Everything in the new file is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified with `#print axioms`), builds with no warnings, and the whole project builds green (`lake build`, 8073 jobs).

The *converse* direction (`realification_irreducible_of_not_isCReal`: a normal irreducible complex system that is **not** C-real has an irreducible realification — the R-pseudoreal / R-complex cases of Prop 12) remains open and is recorded as the N1 residue in `BookProof/STATUS.md`: it is a Frobenius–Schur invariant-real-structure construction whose crux is the orthogonality `Y ⊥ J Y`, which does not follow from normality alone and is tied to the §A.2 commutant classification (Props 17–19). It stays documented as future work, never as an `axiom` or `sorry`.

`BookProof/STATUS.md` was updated with the `ChapterA1f.lean` section (and its obstruction note). `FORMALIZATION_ROADMAP.md` and pre-existing content outside the N1 scope were left untouched. All work is committed and pushed.

# Summary of changes for run beea881e-7c79-43fc-a571-c56e28abf36e
Continued executing `FORMALIZATION_ROADMAP.md`, taking the next step — the **N2 residue** (§A.2, the ℝ/ℂ/ℍ commutant classification). The previous pass had landed Lemma 14 (`BookProof/ChapterA2.lean`) and the R-real case, Prop 17 (`BookProof/ChapterA2b.lean`). This pass **completes the trichotomy** with the new file `BookProof/ChapterA2c.lean` (now imported by `BookProof.lean`):

- **Prop 18 (`Rcomplex_realCommutant_eq_complex`)** — the R-complex commutant is ℂ: for a complex Schur system with no nonzero commuting ℂ-antilinear operator (`NoAntilinearCommutant`, the algebraic content of the C-complex type), an ℝ-linear operator commutes with the system iff it is multiplication by a complex scalar.
- **Prop 19 (`Rpseudoreal_realCommutant_eq_quaternion`)** — the R-pseudoreal commutant is ℍ: for a complex Schur system with a commuting anti-unitary θ satisfying θ² = -1, an ℝ-linear operator commutes with the system iff it is `qembed θ hθ q` for some quaternion q; together with `qembed_injective` this exhibits the real commutant as ≅ ℍ.

Supporting infrastructure (all proved): the real commutant predicate `RealCommutes` with subalgebra closure lemmas; the real-linear operators `mulI` (mult-by-i, `mulI*mulI = -1`) and `thetaR θ` (via `toRealCLM`); the ℝ-algebra embeddings `cembed : ℂ →ₐ[ℝ] (V →L[ℝ] V)` and `qembed : ℍ →ₐ[ℝ] (V →L[ℝ] V)` (via `Complex.lift` / `QuaternionAlgebra.lift`) with commutation and injectivity; and the linear/antilinear decomposition `Plin`/`Qanti` plus `cplxify` (a real-linear operator commuting with `mulI` is ℂ-linear), which drives both reverse inclusions via the named Schur hypothesis `IsSchurFull`.

Everything in the new file is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified with `#print axioms`), builds with no warnings, and the whole project builds green (`lake build`, 8072 jobs). The only remaining §A.2 inputs are the genuinely external Lemmas 20/28/34 (Schur for unitary/imprimitivity representations, not in Mathlib), which stay carried by named predicates, never as axioms.

`BookProof/STATUS.md` was updated with the `ChapterA2c.lean` section (N2 residue marked discharged) and, as requested, `ARISTOTLE_SUMMARY.md` was updated with a new top section describing this pass. `FORMALIZATION_ROADMAP.md` and pre-existing content outside the N2 scope were left untouched. All work is committed and pushed.

# Summary of changes (continuation) — N2 residue completed (Props 18 & 19)
Continued executing `FORMALIZATION_ROADMAP.md`, taking the next step in the
**N2 residue** (§A.2, the ℝ/ℂ/ℍ commutant classification).  The previous pass
landed Lemma 14 (`ChapterA2.lean`) and the R-real case, Prop 17
(`ChapterA2b.lean`).  This pass **completes the trichotomy** by formalizing the
remaining two entries in the new file `BookProof/ChapterA2c.lean` (now imported
by `BookProof.lean`):

- **Prop 18 (`Rcomplex_realCommutant_eq_complex`)** — the R-complex commutant is
  `ℂ`: for a complex Schur system with no nonzero commuting `ℂ`-antilinear
  operator (`NoAntilinearCommutant`, the algebraic content of C-complex), an
  `ℝ`-linear operator commutes with the system **iff** it is multiplication by a
  complex scalar (`cembed c`).
- **Prop 19 (`Rpseudoreal_realCommutant_eq_quaternion`)** — the R-pseudoreal
  commutant is `ℍ`: for a complex Schur system with a commuting anti-unitary `θ`
  satisfying `θ² = -1`, an `ℝ`-linear operator commutes with the system **iff**
  it is `qembed θ hθ q` for some quaternion `q`; with `qembed_injective` this
  exhibits the real commutant as `≅ ℍ`.

Supporting infrastructure, all `sorry`-free and axiom-clean (only `propext`,
`Classical.choice`, `Quot.sound`, verified with `#print axioms`; the whole
project builds green with `lake build`): the real commutant predicate
`RealCommutes` with its subalgebra closure lemmas; the real-linear incarnations
`mulI` (mult-by-`i`, `mulI * mulI = -1`) and `thetaR θ` (via `toRealCLM`); the
`ℝ`-algebra embeddings `cembed : ℂ →ₐ[ℝ] (V →L[ℝ] V)` and
`qembed : ℍ →ₐ[ℝ] (V →L[ℝ] V)` (via `Complex.lift` / `QuaternionAlgebra.lift`),
with commutation and injectivity; the linear/antilinear decomposition
`Plin`/`Qanti` (`Plin S + Qanti S = S`, `Plin` commuting and `Qanti`
anticommuting with `mulI`) and `cplxify` (a real-linear operator commuting with
`mulI` is `ℂ`-linear), the engine of both reverse inclusions via `IsSchurFull`.
Schur's lemma for the representation is used only through the named hypothesis
`IsSchurFull`, never an `axiom`.

`BookProof/STATUS.md` was updated with the `ChapterA2c.lean` section and the N2
residue marked discharged (only the genuinely `EXTERNAL` Lemmas 20/28/34 remain,
carried by named predicates).  `FORMALIZATION_ROADMAP.md` was left untouched;
pre-existing items outside the N2 scope were not modified.  Everything is
committed and pushed.

---

# Summary of changes for run 51fc0f4b-f24b-4efa-820e-53a5fb38b7b6
Continued executing `FORMALIZATION_ROADMAP.md`, advancing the next open queue item — the **N2 residue** (§A.2, the ℝ/ℂ/ℍ commutant classification). With Lemma 14 already on disk (`BookProof/ChapterA2.lean`), the next step was the commutant-classification payoff, and I formalized the **R-real case (Prop 17)** in the new file `BookProof/ChapterA2b.lean` (now imported by `BookProof.lean`).

Deliverables (all `sorry`-free and axiom-clean — only `propext`, `Classical.choice`, `Quot.sound`, verified with `lean_verify`/`#print axioms`; whole project builds green with `lake build`):
- `IsSchurFull` — Schur's lemma for the representation as a named predicate (never an `axiom`, per the roadmap's `EXTERNAL` policy): every continuous ℂ-linear operator commuting with `M` is a complex scalar.
- `commutant_eq_complex_scalars` — the packaged "commutant = ℂ": an operator is in the commutant iff it is a complex scalar.
- `CommutesConj` (an operator commuting with an anti-unitary θ = preserving the real form V_θ) and `real_scalar_commutesConj`.
- **`Rreal_commutant_eq_real_scalars` (Prop 17)** — for a complex Schur system with a C-conjugation θ, an operator commutes with `M` and with θ iff it is a *real* scalar `(r:ℂ)•1`. Via the real-form correspondence this is exactly "the real commutant of an R-real Schur system is ℝ" — the first entry of the ℝ/ℂ/ℍ trichotomy.

`BookProof/STATUS.md` was updated with a section for `ChapterA2b.lean` and a recorded obstruction note: the remaining trichotomy entries — Prop 18 (R-complex commutant ≅ ℂ) and Prop 19 (R-pseudoreal commutant ≅ ℍ) — live on the real form and require sorting the ℝ-linear commutant into its ℂ-linear and ℂ-antilinear parts using the realification bookkeeping of `ChapterA1d.lean`; they are left for a later pass. `FORMALIZATION_ROADMAP.md` and `ARISTOTLE_SUMMARY.md` were left untouched as requested; pre-existing sorries outside the `BookProof` scope were not modified. Everything is committed and pushed.

# Summary of changes for run 494ca4d9-1b1c-4499-9dad-5454c5a13e5a
Continued executing `FORMALIZATION_ROADMAP.md`. With Chapter U (N8) already landed by the previous pass, the next open queue item was the **N1 residue** — the `V ⊕ V̄` decomposition of a reducible realification, the remaining structural ingredient of §A.1 Props 11/12. I implemented it in full as the new file `BookProof/ChapterA1e.lean` (now imported by `BookProof.lean`). The whole project builds green (`lake build`), and every new declaration is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified with `lean_verify`/`#print axioms`).

Deliverables (roadmap §A.1, N1 residue), all built on the realification correspondence already on disk (`ChapterA1d.lean`'s R-imaginary operator `Jmap : u ↦ i·u` and `complex_irreducible_iff_no_Jinvariant_subsystem`):
- `JY Y := Jmap '' Y` (image of a real subspace under `J`), with `mem_JY`, `Jmap_mem_JY`, `Jmap_mem_of_mem_JY`, and the involution `JY_JY` (`J(JY) = Y`).
- `JY_isClosed`, `JY_isSubsystem` — `JY` inherits closedness and `M`-invariance from `Y` (since `J` commutes with every ℂ-linear operator).
- The two `J`-invariant subsystems `Y ⊓ JY` and the closure `(Y ⊔ JY)‾`, with their `J`-invariance and subsystem lemmas (`inf_JY_Jinvariant`, `inf_JY_isSubsystem`, `sup_JY_Jinvariant`, `sup_JY_closure_Jinvariant`, `sup_JY_closure_isSubsystem`).
- Headline **`realification_splits`**: if a complex system `(M,V)` is irreducible and `Y` is a real subsystem of its realification, then either `Y` is trivial (`⊥`/`⊤`) or `V` is the closure of the internal direct sum `Y ⊕ JY` (`Y ⊓ JY = ⊥` and `(Y ⊔ JY)‾ = ⊤`) — the `V ⊕ V̄` conjugate-space splitting.
- Corollary **`proper_realification_subsystem_splits`**: any proper non-trivial real subsystem always realizes this splitting.

`BookProof/STATUS.md` was updated with a section for `ChapterA1e.lean` and a recorded obstruction note (the final Prop 11 type assignment and the R-pseudoreal/R-complex cases of Prop 12 still need the anti-unitary construction *on* the split, which now has the `V ⊕ V̄` decomposition it requires). `FORMALIZATION_ROADMAP.md` and `ARISTOTLE_SUMMARY.md` were left untouched as requested. Pre-existing `RiemannProof/RcpEuler.lean` sorries (the Riemann-Hypothesis chapter, explicitly out of scope) were not modified. Everything is committed and pushed.

# Summary of changes for run e3ffd49f-0a41-404f-8d0b-def8fd27af10
Continued executing `FORMALIZATION_ROADMAP.md` by landing its designated first open work package, **N8 — Chapter U (unitary inference / `unfer`)**, as the new file `BookProof/ChapterU.lean` (now imported by `BookProof.lean`). The whole project builds green (`lake build`), and every declaration in the new file is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified via `#print axioms`).

Deliverables (roadmap §U):
- **U.1 (headline).** `bornMeasure` (the Born measure `|Ψ|²·μ`), `bornMeasure_isProbability`, `conditionedState` (collapse by projection + renormalization), and `born_conditioning`: the Born measure of a wave-function collapsed onto an event equals the classical conditional measure `ProbabilityTheory.cond` (`μ[|E]`) — i.e. quantum wave-function collapse onto an event *is* Bayesian conditioning.
- **U.3.** The bosonic Fock exponential property `prodEquiv : Sym(M × N) ≃ₐ[R] Sym M ⊗[R] Sym N`, constructed from the two universal-property algebra maps `prodToTensor`/`tensorToProd` together with the two round-trip identities.
- **U.4.** `no_differentiable_trajectory` and `differentiable_trajectory_null`: the measure-theoretic wrapper turning the (external, scoped as a named hypothesis rather than an axiom; cited Paley–Wiener–Zygmund 1933 / Bertoin 1994) a.s.-nowhere-differentiability of stochastic paths into `P(differentiable trajectory) = 0` / full-measure nowhere-differentiability.
- **U.5.** `portfolio_risk_inv_sqrt` (the variance of the average of `n` independent equal-variance components is `σ²/n`) and `portfolio_std_inv_sqrt` (aggregate standard deviation `σ/√n`).
- U.2 (sphere→Gaussian / Gegenbauer→Hermite) is a cross-reference to the already-proven `PnpProof/SphereGaussian.lean`; no new code needed.

`BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md` were updated to record the Chapter U package. The fermionic (exterior-algebra, graded-sign) analogue of U.3 and the U.6 prose/software items remain out of scope per the roadmap; the remaining Chapter A residues (Props 11/17–19, the §B.3 SVD, and the §A.3–A.5 material) depend on external theorems absent from Mathlib and are, per the roadmap, to be handled as named hypotheses in later dedicated passes. All pre-existing libraries and the roadmap text were left untouched. Everything is committed and pushed.

# Summary of changes for run (Chapter U / N8)
Continued executing `FORMALIZATION_ROADMAP.md`, landing the first open work
package **N8 — Chapter U (unitary inference / `unfer`)** as the new file
`BookProof/ChapterU.lean` (imported by `BookProof.lean`). The whole project
builds green and the file is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`; verified with `#print axioms`).

Deliverables (roadmap §U):
- **U.1 (headline)** `bornMeasure`, `bornMeasure_isProbability`,
  `conditionedState`, and `born_conditioning` — the Born measure of a
  wave-function collapsed onto an event equals the classical conditional
  measure `ProbabilityTheory.cond`; quantum collapse = Bayesian conditioning.
- **U.3** the bosonic Fock exponential property
  `prodEquiv : Sym(M × N) ≃ₐ[R] Sym M ⊗[R] Sym N`, built from the two
  universal-property algebra maps `prodToTensor`/`tensorToProd` and the two
  round-trip identities.
- **U.4** `no_differentiable_trajectory` / `differentiable_trajectory_null` —
  the measure-theoretic wrapper around the (external, scoped as a named
  hypothesis, cited Paley–Wiener–Zygmund 1933 / Bertoin 1994) a.s.-nowhere-
  differentiability of stochastic paths.
- **U.5** `portfolio_risk_inv_sqrt` (variance of the average of `n` independent
  equal-variance components is `σ²/n`) and `portfolio_std_inv_sqrt`
  (aggregate standard deviation `σ/√n`).
- U.2 is a cross-reference to the existing `PnpProof/SphereGaussian.lean`.

`BookProof/STATUS.md` updated with a Chapter U section. The fermionic
exterior-algebra analogue of U.3 and the U.6 prose/software items remain out of
scope per the roadmap. Pre-existing libraries and the roadmap were left
untouched. All work committed and pushed.

# Summary of changes for run 36c1628b-2657-489d-8a60-70aa6a5c9240
Continued executing `FORMALIZATION_ROADMAP.md`, landing two more work-package steps on top of the existing `BookProof` library. Both new files are `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`), added to the `BookProof` root module, and the full project builds green (only pre-existing cosmetic style warnings in `ChapterE.lean` remain).

**N1 — realification correspondence (`BookProof/ChapterA1d.lean`).** The dual of the previously-built complexification correspondence: the realification of a *complex* system and the reduction of complex irreducibility to the `J`-invariant real subspace lattice (the `(M, Vʳ)` / `J u := i·u` half of the Def 10 / Prop 12 machinery). The real inner-product structure on a complex Hilbert space is supplied via `InnerProductSpace.rclikeToReal`, registered as a local instance only (avoiding the real/complex diamond). Deliverables: `rxMap`/`rxSystem` (realification of a complex operator/system), the canonical R-imaginary operator `Jmap` with `Jmap_sq` (`J(Jx) = -x`) and `Jmap_isRImaginary` (Def 8.2), the `realSub`/`cplxSub` correspondence with both round-trips, extremal values, and subsystem preservation, and the headline `complex_irreducible_iff_no_Jinvariant_subsystem` (a complex system is irreducible iff its realification has no proper non-trivial `J`-invariant subsystem).

**N2 — Schur / Lemma 14 (`BookProof/ChapterA2.lean`).** The self-contained algebraic layer of §A.2. The unitary-representation Schur lemma (flagged external by the roadmap and absent from Mathlib) is introduced as a named predicate `IsSchurUnitary`, never an axiom. Deliverables: `CommutesUnitary`/`IsSchurUnitary` (Def 13, unitary form), `antiisometry_unique_up_to_phase` (Lemma 14 — any two anti-unitaries commuting with a Schur system differ by a unit complex phase), and the corollary `commuting_antiUnitary_scalar_multiple`.

`BookProof/STATUS.md` was updated with sections describing both new files; `BookProof.lean` now imports them. The finer R-pseudoreal / R-complex sorting of Props 11–12 (requiring the `V ⊕ V̄` conjugate-space decomposition) and the full ℝ/ℂ/ℍ commutant classification (Props 17–19) remain for a later pass, as already noted in the status file. `ARISTOTLE_SUMMARY.md`, `FORMALIZATION_ROADMAP.md`, and the pre-existing `RiemannProof`/`PnpProof` libraries were left untouched. All work is committed and pushed.

# Summary of changes for run 49208d71-d22c-42ad-b27c-6f09b9931c6e
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next step of work-package **N1** (§A.1, Defs 9/10 and Props 11/12): the **C-type / R-type classification predicates** on top of the complexification infrastructure and subspace correspondence built in earlier passes.

New file `BookProof/ChapterA1c.lean` (added to the `BookProof` root module), all `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, checked with `#print axioms`), with no external hypotheses:

- **Def 9** predicates on a complex system: `CommutesAntiUnitary`, `HasCommutingAntiUnitary`, `IsCReal` (a C-conjugation exists), `IsCPseudoreal` (no C-conjugation but a commuting anti-unitary exists), `IsCComplex` (no commuting anti-unitary at all), with `IsCReal.hasCommutingAntiUnitary`.
- The **C-type trichotomy**: `cType_exhaustive` (every complex system is one of the three types) together with the three mutual-exclusion lemmas.
- `cxSystem_isCReal`: the complexification of a real system is always C-real (Def 9.1 form of the previously proved `cxConj_isConjugation`).
- **Def 10 / Prop 12 (R-real case)**: `IsRReal` (a real system is R-real iff its complexification is irreducible as a complex system — automatically C-real), and `IsRReal.isIrreducible`, the R-real half of Prop 12 (an R-real real system is irreducible), obtained from the existing `irreducible_iff_no_conj_subsystem` reduction.

The full project builds (`lake build`, 8066 jobs green); the only remaining warnings are the pre-existing long-line/style notices in `ChapterE.lean`. `BookProof/STATUS.md` was updated to record the new file and to note that the C-type classification and the R-real case are now discharged, with the finer R-pseudoreal / R-complex sorting (which requires the `V ⊕ V̄` conjugate-space decomposition of a reducible complexification) recorded as remaining for a later pass. The pre-existing `RiemannProof` and `PnpProof` libraries and `ARISTOTLE_SUMMARY.md` were left untouched. All work is committed and pushed.

# Summary of changes for run ebd0107a-0d99-4324-b8bc-0ca171b1d035
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next step of work-package **N1** (§A.1, Props 11/12): the real↔complex *subsystem correspondence* that the roadmap flags as "the main work" of the trichotomy. It builds on the complex inner-product infrastructure of `BookProof/Complexification.lean` established in the previous pass.

New file `BookProof/ChapterA1b.lean` (added to the `BookProof` root module), all `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, checked with `#print axioms`), and with no external hypotheses:

- `Cx.complexify` / `Cx.realPart` — the two directions between real subspaces of `W` and complex subspaces of the complexification `Cx W`, with membership simp lemmas.
- Coordinate-map continuity `Cx.continuous_re`/`continuous_im`/`continuous_ofReal` (each is 1-Lipschitz), used for closedness.
- The two round-trips `realPart_complexify` (`= Y`) and `complexify_realPart_of_invariant` (for a conjugation-invariant `X`, `= X`), plus `complexify_cxConj_invariant` and the extremal values `complexify_bot`/`complexify_top`/`realPart_bot`/`realPart_top`.
- Subsystem preservation in both directions: `complexify_isSubsystem`, `realPart_isSubsystem`.
- Headline `irreducible_iff_no_conj_subsystem`: a real system `(M, W)` is irreducible iff its complexification `(M, Cx W)` has no proper non-trivial conjugation-invariant subsystem — the reduction of real irreducibility to the `cxConj`-stable part of the complexified subspace lattice used throughout Props 11/12.

The full project builds (`lake build`, 8065 jobs green); the only remaining warnings are the pre-existing long-line style notices in `ChapterE.lean`. `BookProof/STATUS.md` was updated to record the new file and to note that the subspace-correspondence portion of the Prop 11/12 obstruction is now discharged, with the finer R-type sorting (C-real / C-pseudoreal / C-complex classification and the Prop 12 converse) recorded as remaining for a later pass. The pre-existing `RiemannProof` and `PnpProof` libraries and `ARISTOTLE_SUMMARY.md` were left untouched.

# Summary of changes for run 0aa1c16d-bcff-42d4-9e7a-714889669196
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next queued step of the `BookProof` library: the §A.1 complexification inner-product infrastructure (work-package N1), which the previous pass had recorded as a genuine obstruction ("a complex inner product on the complexification is not in Mathlib"). The full project builds (`lake build`, 8064 jobs green) and the new file is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, checked via `#print axioms`). The pre-existing `RiemannProof` and `PnpProof` libraries are untouched.

New file `BookProof/Complexification.lean` (added to the `BookProof` root module):
- `Cx W`, the complexification of a real inner-product space `W`, modelled as pairs `⟨re, im⟩ ≃ re + i·im`, equipped from scratch with `AddCommGroup`, `Module ℂ`, a Hermitian `Inner ℂ` (conjugate-linear in the first argument, matching Mathlib's convention), and the full `NormedAddCommGroup` + `InnerProductSpace ℂ` instances (built via `InnerProductSpace.Core`). Also `CompleteSpace (Cx W)` when `W` is complete, so `Cx W` is a complex Hilbert space.
- Basic API: `inner_re`/`inner_im`, `norm_sq` (`‖x‖² = ‖x.re‖² + ‖x.im‖²`), coordinate-projection Lipschitz bounds, the real embedding `ofReal`, and `smul_I` (`i·⟨u,v⟩ = ⟨-v,u⟩`).
- The canonical conjugation `cxConj : Cx W ≃ₗᵢ⋆[ℂ] Cx W` (`⟨u,v⟩ ↦ ⟨u,-v⟩`), an anti-unitary involution, with `cxConj_involutive`, `cxConj_inner` (`⟪θx,θy⟫ = conj⟪x,y⟫`), and `cxConj_fixed_iff` (fixed set = real form).
- The complexification of a real bounded operator `cxMap : (W →L[ℝ] W) → (Cx W →L[ℂ] Cx W)` (coordinatewise, same operator-norm bound), with `cxMap_one`, `cxMap_mul`, `cxMap_add`, and `cxConj_comm_cxMap`.
- Connection to Chapter A's `System` framework: `cxSystem` (complexification of a real system) and the headline `cxConj_isConjugation` — the canonical conjugation is a C-conjugation (Def 8.1) of the complexified system, i.e. the complexification of any real system is C-real. This is the foundational, easy half of §A.1's real↔complex correspondence (Props 11/12).

`BookProof/STATUS.md` was updated to record the new file and its deliverables, and to note that the previously-recorded "complexification not in Mathlib" obstruction is now discharged; the remaining Prop 11/12 irreducibility transfer (the invariant-subspace bookkeeping sorting a real irreducible system into the three R-types) is left for a later pass and now has the inner-product infrastructure it needs. `ARISTOTLE_SUMMARY.md` was left unedited as requested. The only remaining build warnings are the pre-existing long-line style notices in `ChapterE.lean`.

# Summary of changes for run d2047b6e-2249-413b-9915-ab168f0157a1
Continued executing `FORMALIZATION_ROADMAP.md`, landing the next two work packages of the `BookProof` library. The full project builds (`lake build`, 8063 jobs green) and both new files are `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, checked with `#print axioms`). The pre-existing `RiemannProof` and `PnpProof` libraries are untouched (the two `RcpEuler.lean` sorries are the previously-documented, author-excluded Riemann-Hypothesis obstruction).

New files (both added to the `BookProof` root module and recorded in `BookProof/STATUS.md`):

- `BookProof/ChapterA1.lean` — §A.1 anti-unitary / Def 8 scaffolding (work-package N1, partial). Defines `AntiUnitary V` (a conjugate-linear isometric equivalence `V ≃ₗᵢ⋆[ℂ] V`) with `inner_map_map` (`⟪θ x, θ y⟫ = conj ⟪x, y⟫`) and `comp_inner`; the `IsConjugation` (C-conjugation) and `IsRImaginary` (R-imaginary) predicates on a `System`; and structural lemmas — `conjugation_smul_I_of_neg`, `conjugation_avg_fixed`/`_antifixed`, `conjugation_decomp` (real-form splitting), `rimaginary_orthogonal` (`⟪J x, x⟫_ℝ = 0`), `rimaginary_symm_apply` (`J⁻¹ = -J`).

- `BookProof/ChapterA3.lean` — §A.3 concrete 4×4 Majorana/gamma-matrix model (work-package N4, partial). The four Majorana matrices `iγ^μ`, the fifth `iγ⁵`, the Dirac matrices `γ^μ = -i(iγ^μ)`, and the Minkowski metric, with: `mgamma_clifford` (`(iγ^μ)(iγ^ν)+(iγ^ν)(iγ^μ) = -2 η^{μν}`), `mgamma_map_conj` (reality), `mgamma_unitary` (`(iγ^μ)ᴴ(iγ^μ)=1`), `mgamma5_eq_prod`, `mgamma5_sq` (`(iγ⁵)²=-1`), `mgamma5_anticomm`, and `dgamma_clifford` (`γ^μγ^ν+γ^νγ^μ = 2 η^{μν}`). The matrices are defined over `ℤ` (Clifford identities closed by `decide`) and cast into `ℂ` via `Int.castRingHom ℂ`, each complex statement transported from its integer form.

Recorded obstructions (in `STATUS.md`, left for a later pass, consistent with the roadmap's coverage policy): the deep §A.1 propositions (Prop 11/12 R-real/R-complex trichotomy) need a complex inner-product structure on the complexification `ℂ ⊗_ℝ W`, which is not in Mathlib; and the later §A.3 results (Prop 37, Lemma 40, Prop 46, Lemma 52) depend on the external Pauli fundamental theorem and Weyl complete reducibility. Style/linter warnings in the new files were resolved at the source; the only remaining warnings are pre-existing long-line notices in `ChapterE.lean`.

# Summary of changes for run bee1f248-2ee0-4ea1-bafb-088aa2622641
Executed the next implementation pass of `FORMALIZATION_ROADMAP.md`, landing three work packages in the `BookProof` library. Everything compiles (`lake build` green across all default targets) and is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified with `#print axioms`).

**N6 — Chapter G (flagship, complete): `BookProof/ChapterG.lean` (new file).** Full formalization of "Gauge transformations in probability spaces" (book line 2128), deliverables G.0–G.7, none needing an external hypothesis:
- G.0 `gaugeGroup` of a parametrization (fiber-preserving permutations).
- G.1 `swap_mem_gaugeGroup`, `gaugeOrbit_eq_fiber` (orbit = fiber), `gaugeInvariant_iff_factors` (gauge-invariance ⇔ factoring through π).
- G.2 `gaugeInvariantSubalgebra`, `gaugeInvariantOperators` (= centralizer), `expectation_gauge_invariant`.
- G.3 the Dirac obstruction: `no_shift_invariant_probabilityMeasure`, `shift_invariant_l2_eq_zero`, `no_shift_invariant_unit_vector`, plus `one_mem_gaugeInvariantSubalgebra` (the invariant algebra stays nontrivial).
- G.4 `IsCompleteGaugeFixing`, `exists_complete_gaugeFixing`.
- G.5 `haarAverage` with its four properties (`_smul`, `_of_invariant`, `_one`, `_nonneg`) and the headline `gauge_constraint_pushforward_full_measure` (the constrained set carries measure 1, not null).
- G.6 the BRST ghost algebra: `ghostAnnih`/`ghostCreat`, `ghost_car`, `ghost_annih_sq`, `ghost_creat_sq`, `ghost_creat_conjTranspose`, `BRST`, `BRST_nilpotent` (Ω²=0).
- G.7 dissipative/Koopman dynamics: `dampedCoupledMatrix`, `dampedFlow_add`/`dampedFlow_zero`, `evolution_conserves_probability`, and the Koopman unitary `koopmanEquiv` (assembled from `koopman_comp_left`/`koopman_comp_right`).

**N5 — §0 substrate glue (complete): `BookProof/Substrate.lean` (new file).** Instantiates Chapter B at the already-formalized Kopperman substrate measure: `substrate_born_forward`, `substrate_born_backward`, `substrate_unit_vector_extends`.

**N3 — Chapter B.2′ (partial): added to `BookProof/ChapterB.lean`.** `condKernel_disintegration` — the regular-conditional-probability disintegration `ρ.fst.compProd ρ.condKernel = ρ` on standard Borel spaces (the book's p(y|x)). The B.3b/B.3c singular-value-expansion (dense-core SVD + partial-isometry API) is recorded as an outstanding obstruction for a future pass.

Both new files were added to the `BookProof` root module. `BookProof/STATUS.md` was updated with the new deliverables and the recorded N3 obstruction, and a stray trailing-whitespace linter warning in `ChapterE.lean` was fixed. The remaining roadmap packages (N1/N2/N4 — the large representation-theory subprojects that rely on external named hypotheses, and N3's SVD) are left for subsequent passes as the roadmap anticipates.

# Summary of changes for run 866cdb39-1978-4b25-bf3a-a8075c6d6977
I executed `FORMALIZATION_ROADMAP.md` by formalizing its self-contained, provable mathematical content into a new Lean library `BookProof` (added to `lakefile.toml` alongside the untouched `RiemannProof` and `PnpProof`). Everything is **`sorry`-free and `axiom`-free** (only the standard `propext`, `Classical.choice`, `Quot.sound`), verified by `lake build` and `#print axioms`. A per-chapter status write-up is in `BookProof/STATUS.md`.

Completed chapters:

- **Chapter C** (`BookProof/ChapterC.lean`, §C.1): the probability that a random discrete map `Fin n → Fin n` is invertible is `n!/nⁿ`, its Stirling asymptotic `~ √(2πn)·e⁻ⁿ`, and its limit `→ 0`.
- **Chapter D** (`BookProof/ChapterD.lean`, §D.1): computable functions `ℕ→ℕ` and `ℕ→Bool` are countable, hence null under any atomless measure ("almost all functions are uncomputable").
- **Chapter E** (`BookProof/ChapterE.lean`, all of §E): the 2-state probability clock (surjectivity of `cos²`, the Euler rotation via the matrix exponential of `t•J`, the collapse/density decomposition), the singularity of a stochastic map sending uniform to a vertex, the Hadamard (`n=2`) and general DFT "black-hole" uniformizers (unitary with all `|·|²=1/n`), and the hyperspherical Born / stick-breaking recursion's surjectivity onto the probability simplex.
- **Chapter B** (`BookProof/ChapterB.lean`, §B.1–B.2): the Born parametrization both ways (`Ψ=√p` gives a unit `L²` vector with `|Ψ|²=p`, and `|Ψ|²` of a unit vector is a probability density), and that every unit vector extends to a Hilbert basis (`Ψ = 𝒰 e₀`).
- **Chapter A** (`BookProof/ChapterA.lean`, §A.0–A.2 foundational core): the `System` framework (systems, commutant, normal systems, subsystems, irreducibility) plus the two results the roadmap flags "do in Lean directly, high value": Lemma 26 (the orthogonal complement of a subsystem of a normal system is a subsystem) and Lemma 27 (a Schur normal system is irreducible), with the Schur property taken as a named hypothesis as the roadmap prescribes.

Scope note: the remaining Chapter A material (§A.1 real↔complex trichotomy, §A.2 ℝ/ℂ/ℍ commutant classification, §A.3 Clifford/γ-matrix model and `Pin(3,1)→O(1,3)`, §A.4–A.5 Bargmann–Wigner/CPT) is a large representation-theory development whose deep inputs are, by the roadmap's own coverage policy, external theorems absent from Mathlib (unitary/imprimitivity Schur, Weyl, Mackey, Wigner, Pauli). These were not built out. Chapters F/G/H and the physics chapter P contain no numbered theorems (triaged non-formalizable), and the ODE/P≠NP/Riemann chapters are excluded by the author. `BookProof/STATUS.md` records this breakdown. The pre-existing libraries continue to build unchanged.

# Summary of changes for run 1400d993-f611-4597-8e51-b640227d688e
I worked through `IMPLEMENTATION_PLAN_RCP.md`, which is a route to prove the Riemann Hypothesis (standard analytic ζ-form) via a bounded-coefficient prior and regular conditional probability. The route is implemented in `RiemannProof/RcpEuler.lean`: the final theorem `riemann_hypothesis_via_rcp` is fully assembled and reduces, via the shared conditional-probability object `L` and a short `by_contra` (`riemannZeta_ne_zero_of_mem_strip`), to exactly two load-bearing lemmas:

- `transfer_equality` : `L s₀ R = (if riemannZeta s₀ = 0 then 1 else 0)`
- `L_ne_one`          : `L s₀ R ≠ 1`

Honest assessment of what could and could not be done:

1. The project builds successfully with these two `sorry`s in place (verified), and the supporting layers the plan calls "done" (the radius-2 prior `priorBall`, the general non-multiplicative series `etaX`, absolute convergence `summable_etaXTerm`, the rcp kernel `rcpKernelX`, and the final assembly) are present and compile.

2. The two remaining obligations cannot be honestly discharged. They are documented — in the plan text, the code docstrings, and the maintainer's own 2026-06-23 notes — as deep analytic inputs that are "not weaker than RH itself": `transfer_equality` is the rcp-at-interior-support transfer principle, and `L_ne_one` is Bagchi/Voronin universality (local form). Neither is available in Mathlib, and the maintainer notes themselves flag that with the on-disk full-boundary conditioning the route is currently circular (one of the two is RH-in-disguise). The Riemann Hypothesis is an open problem; completing these to a `sorry`-free proof is therefore not possible here.

3. During an attempt on these lemmas, an automated proof of `L_ne_one` was produced that merely invoked the still-open `transfer_equality` — a circular, parasitic "discharge" that would have given a false impression of progress while violating the plan's own requirement that the two load-bearers be independent. I rejected and reverted it, restoring `RiemannProof/RcpEuler.lean` to its faithful state with both inputs left as clearly documented `sorry`s.

Net effect: the file is left building cleanly with the two genuine, honestly-marked load-bearing `sorry`s intact (no circular or vacuous proofs introduced). The plan cannot be executed to a complete proof because its two remaining steps are equivalent to / no weaker than the Riemann Hypothesis and depend on results not present in Mathlib.

# Summary of changes for run e95705ca-1719-49ef-94b6-b474bf6ec5c4
Completed the final outstanding item of the PnpProof formalization plan — N1, the explicit `O(k)` comparator-circuit upgrade of the model's "NP side" — leaving the whole development sorry-free and axiom-free (only `propext`, `Classical.choice`, `Quot.sound`). The pre-existing `RiemannProof` library is untouched, and `lake build` (both default targets) succeeds.

New file `PnpProof/Comparator.lean` builds the construction from scratch on top of the existing `Circuit` theory in `PnpProof/Counting.lean`:
- A clean single-gate append API: `Gate.eval`, `Circuit.snoc`, and the two evaluation lemmas `snoc_nodeValNat_lt` / `snoc_nodeValNat_top` (plus `nodeValNat_input`, `clampFin`).
- `step`, one ripple-comparator stage (9 gates) updating an eq/lt register pair, with its value lemmas `step_eqN_val` / `step_ltN_val` and `step_preserves`.
- `buildLT`, the MSB-first fold of `step` over the bit positions, with the correctness invariant `buildLT_spec` (proved by induction using the relocated bit-recursion lemma `div_pow_succ_compare`).
- `baseSt` seeding the registers from TRUE/FALSE constant nodes; `bitsOf` packing three k-bit numbers; the two chained comparators `cmp1`/`cmp2` (with `cmp1_ltN_val`/`cmp2_ltN_val`); and `fullCircuit` combining them with a final ¬·∧¬·.
- The headline theorem `verify_circuit_cheap`: for every k ≥ 1 there is an explicit `Circuit (3*k) (s+1)` of size `s ≤ 50*k + 50` deciding `(glo ≤ u ∧ u ≤ ghi)` on the packed inputs.

In `PnpProof/Main.lean` the N1-OPEN note was replaced by the NEW theorem `model_P_ne_NP_circuit`, whose NP-side conjunct is the circuit family from `verify_circuit_cheap` (phrased with `verifyBits`) and whose P-side conjunct is T2 (`almost_all_not_computable`); it carries the same "theorem about the model, not the Clay statement" docstring. As mandated by the plan, the original `model_P_ne_NP` is left exactly as it was, so both the computability form and the circuit form coexist. The bit-recursion lemma `div_pow_succ_compare` was moved from `Main.lean` to `Comparator.lean` (no longer duplicated) and `PnpProof.lean` now imports the new module.

`PnpProof/IMPLEMENTED.md` was updated with a `Comparator.lean` section and the N1-complete status. Only stylistic linter warnings (line length / whitespace / multiGoal) remain, several of them pre-existing; the build itself is clean.

# Summary of changes for run 170e5877-d03a-49ef-b371-c44798f0030a
Continued the `PnpProof` development and completed almost all of the remaining next-step queue (N1–N5 in Part 7 of the plan). The whole library still builds with `lake build PnpProof`, every new result is sorry-free, and all of them depend only on the standard axioms `propext`, `Classical.choice`, `Quot.sound` (verified with `#print axioms`). The pre-existing `RiemannProof` library is untouched.

New work, all in `PnpProof/SphereGaussian.lean` unless noted:

- N3 (G5 certificate — rotation invariance of the uniform sphere measure): `sphereProj_equivariant`, `gaussianE_rotation_invariant` (via characteristic functions), and the combined `sphereUniform_rotation_invariant`. This is the certificate that `sphereUniform` deserves the name "uniform".
- N2 (G4 second half — the Hermite normalization integral): `physHermite_hasDerivAt` (the derivative recurrence H_{n+1}'=2(n+1)H_n), `hermite_sq_integral` (∫ H_n(x)² e^{−x²} dx = √π·2ⁿ·n!, by an integration-by-parts induction with base `integral_gaussian`), and `hermite_normalization` (the chapter's value √π·2ⁿ/n!).
- N1 (G4 first half — the normalization-constant limit): `gegenbauerScaled_rec` (the rescaled three-term recurrence), `gegenbauerScaled_bound` (a uniform-in-λ polynomial bound proved by recurrence induction), and `normalization_tendsto` (the chapter's limit, proved by dominated convergence). It is stated in the post-change-of-variables form, as the plan permits.
- N4 (Poincaré–Borel): `gammaMeasure` (the infinite product of standard Gaussians, via `Measure.infinitePi`), `normSq`, `gaussian_concentration_sphere` (G7, the a.s. strong-law concentration), and `poincare_borel_ae` (G6, a.s. coordinatewise convergence of the √k-sphere normalization to the Gaussian coordinates).

N5 (the explicit O(k) comparator-circuit upgrade of T3's NP side) is the one item left OPEN. Its driving bit-recursion lemma `div_pow_succ_compare` is proved, but assembling the full explicit `Circuit (3*k) (s+1)` together with its node-by-node correctness proof is a large standalone construction that exceeded the available budget. Following the plan's standing instruction for N5, no `sorry` was committed and the existing `model_P_ne_NP` was left untouched, so the development remains sorry-free and axiom-free. The finite-k Chebyshev fallback (G7′) and the bounded-continuous weak-convergence corollary of G6 were not needed once the a.s. forms were in place.

`PnpProof/IMPLEMENTED.md` has been updated to record the new lemmas, files, deviations, and the OPEN status of N5. `ARISTOTLE_SUMMARY.md` was left unedited as requested.

# Summary of changes for run 3e124399-f441-48ea-b531-c69e452360c5
Implemented `PNP_IMPLEMENTATION_PLAN.md` as a new Lean library `PnpProof` (added alongside the existing `RiemannProof` in the lake project). Everything compiles and `lake build PnpProof` succeeds; every result is sorry-free and depends only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`. A full report is in `PnpProof/IMPLEMENTED.md`.

What was formalized (≈55 definitions/theorems across 6 files):

- `PnpProof/Foundations.lean` (Part 1, F1–F8): points/countable sets are null, the disintegration/conditional-kernel existence, no countable history realizes a target event, countability of atoms of a finite measure, mutual singularity of diffuse vs atomic parts, the CDF-jump separation, and atomlessness of the diffuse conditioning.
- `PnpProof/Counting.lean` (Part 2, C1–C5 and C2): countability of computable functions; a from-scratch Boolean-circuit theory (`Gate`, `Circuit`, evaluation, size monotonicity); circuit counting; the Shannon bound that almost all Boolean functions need many gates (stated for n ≥ 8); and the Lebesgue-null set of computably-coded reals via binary-digit reconstruction.
- `PnpProof/FunctionSpace.lean` (Part 3): L²([0,1]) is separable, L^∞([0,1]) is not, the wave-function √p ∈ L² with unit norm, polynomials are dense in L², the classification theorem that all infinite-dimensional separable real Hilbert spaces are isometric (the honest surrogate for the Fock–Guichardet isomorphism), and an atomless Borel probability measure on the unit sphere.
- `PnpProof/SphereGaussian.lean` (Part 3b): physicists' Hermite and Gegenbauer polynomials, the lopez99 limit (rescaled Gegenbauer → Hermite, proved by the mandated recurrence-induction route), the weight → Gaussian limit, and the construction of the uniform measure on the √k-sphere as a Gaussian pushforward (probability measure, concentrated on the sphere).
- `PnpProof/Model.lean` (Part 4): dyadic discretization, the inverse-transform verifier, machine computation of a selection function with a uniqueness theorem and countability of computable selections, and a concrete atomless probability prior on the space of selection functions C([0,1], ℝ).
- `PnpProof/Main.lean` (Part 5): T1 `selection_not_history`, T2 `almost_all_not_computable` (prior-probability-1 uncomputability of the selected function), T3 `model_P_ne_NP` (the in-model separation: the candidate verifier is computable while the solution is prior-a.s. uncomputable), and the §5→§6 glue `mixed_to_continuous`.

Faithfulness and deviations (all documented in the report and in docstrings):
- T3 is explicitly a theorem *about the paper's model*, not the Clay statement; no implication to standard P ≠ NP is asserted (per Part 6).
- Because adding axioms is not permitted, the NP side of T3 is formalized as the computability of the verifier (faithful to "verification is cheap") rather than via an explicit O(k) comparator circuit or a model axiom.
- T4 (the §7 "realistic version") is left genuinely open with an explanatory note rather than committing to a possibly-incorrect statement.
- A few heavy, standalone items are noted as future work: the dominated-convergence normalization limit and Hermite orthogonality value (G4), the Poincaré–Borel / infinite-product-measure concentration (G6/G7), rotation invariance of the sphere measure, and the elaborate ratStep family of H4 (whose essential "countable dense subset of L²" content is covered by separability and polynomial density).

The pre-existing `RiemannProof` library is untouched and still builds.
---

# Wave 5 update (2026-07-03) — N2 Prop 15

Continuing the `FORMALIZATION_ROADMAP.md` queue after wave 4 (which landed N9 and
N10), this pass discharges **Prop 15** of the §A.2 N2 leftover.  The result builds
cleanly (`lake build BookProof` green, 8077 jobs), contains no `sorry`/`admit`,
and is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`; verified with
`#print axioms`).  No new `axiom` or `@[implemented_by]` was introduced.

**New module `BookProof/ChapterA2d.lean` (work-package N2, Prop 15):**
- `conjCLM` (conjugation of an operator by a ℂ-linear isometric equivalence) and
  `IsSystemIso` (a system isometry carries `M` onto `N` by conjugation).
- `conjAU` (transport of an anti-unitary along an isometry) with
  `conjAU_commutesAntiUnitary`.
- `unitScaleEquiv` / `unitScaleEquiv_apply` (multiplication by a unit-modulus
  scalar as a ℂ-linear isometric equivalence), `exists_unit_sqrt` (unit scalars
  have unit-modulus square roots), and `conjCLM_unitScale`.
- Headline `Rreal_isometric_iff_complexification_isometric` (**Prop 15**): for
  complex Schur systems `(M, V)`, `(N, W)` with C-conjugations `θ_M`, `θ_N`, a
  conjugation-intertwining system isometry (a real-form isometry) exists **iff**
  a system isometry exists — the "R-real systems are isometric iff their
  complexifications are isometric" criterion, proved from Lemma 14
  (`antiisometry_unique_up_to_phase`) by phase-rescaling.

`ChapterA2d` is registered in `BookProof.lean`; `BookProof/STATUS.md` records the
wave-5 completion and the updated open list.

**Still open (documented in `BookProof/STATUS.md`):** the N2 residue is now only
Prop 16 (iso-or-antiiso ⇔ realifications iso — needs the ℝ-linear
isometry ℂ-linear/ℂ-antilinear decomposition and a Schur scalar extraction, plus
a ℂ→ℝ `LinearIsometryEquiv.restrictScalars` bridge absent from Mathlib), together
with the previously recorded residues N1 (Prop 11 trichotomy + Prop 12 converse),
N3 (`denseCore_svd`), and N4 (Pauli/Weyl `EXTERNAL` layer §A.4–A.5).
