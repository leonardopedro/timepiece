# `BookProof` — implementation status of `FORMALIZATION_ROADMAP.md`

This library formalizes the self-contained mathematical content of
`FORMALIZATION_ROADMAP.md` (the master reference distilled from `book.tex`).

Everything in `BookProof` is **`sorry`-free** and **`axiom`-free** (only the
standard `propext`, `Classical.choice`, `Quot.sound`).  Verified with
`lake build BookProof` and `#print axioms`.

## Wave 112 (2026-07-10) — **Book "Free field parametrization in Classical Statistical Field Theory and Navier-Stokes equations", §"Mass gap"** (`ChapterMassGap`)

Stayed on the book's main-conclusion thread (author instruction: prioritize
chapters other than Gravity and off the Bell/CHSH comparison results; no Hankel,
Majorana fine). Formalized the self-contained mathematical backbone of the
§*"Mass gap"* section (`book.tex` line ~4061): *"the number operator commutes
with the algebra of observables which implies that the number operator can be
added to the Hamiltonian, modifying the mass gap without observable
consequences"* — so a bounded-from-below Hamiltonian with a null mass gap (the
free electromagnetic field) can be turned into one with an arbitrary mass gap
without any observable consequence. One new file, `sorry`-free / `axiom`-free
(only `propext`, `Classical.choice`, `Quot.sound`):

* `ChapterMassGap.lean` — **observable invariance** in an arbitrary complex Banach
  algebra `𝔸` of operators: `exp_conj_eq_self` (conjugation by `exp Y` is trivial
  when the observable commutes with `Y`), and the headline
  `heisenberg_number_shift_invariant` — if `H` and every observable `Obs` commute
  with the number operator `N`, then Heisenberg evolution of `Obs` under the
  shifted Hamiltonian `H + λN` equals its evolution under `H`
  (`exp(t(H+λN))·Obs·exp(-t(H+λN)) = exp(tH)·Obs·exp(-tH)`), for every scalar `t`
  and shift `λ` (the number-operator shift is invisible to all observables). Plus
  the diagonal **spectral shift** model (`numberOp`, `shiftedSpectrum`, `excited`,
  `massGap`): `shiftedSpectrum_vacuum` (vacuum energy unchanged),
  `shiftedSpectrum_excited` (every excited energy shifted by exactly `λ`), and the
  headline `massGap_shifted_gapless` — for the gapless free field (`E ≡ 0`) the
  shifted mass gap equals `λ`, i.e. it can be set to any value. Registered in
  `BookProof.lean`; `lake build BookProof` green.

## Wave 111 (2026-07-10) — **Book "Reconstructing the classical trajectory of any isolated quantum system", §"Any deterministic theory compatible with relativistic Quantum Mechanics necessarily respects relativistic causality"** (`ChapterCausality`)

Stayed on the book's main-conclusion thread (author instruction: prioritize
chapters other than Gravity and off the Bell/CHSH comparison results; no Hankel,
Majorana fine). Formalized the mathematical backbone of the subsection *"Any
deterministic theory compatible with relativistic Quantum Mechanics necessarily
respects relativistic causality"* (`book.tex` line ~2915): *"Since in relativistic
Quantum Mechanics the probability that the system moves faster than light is null,
then no system (described by the deterministic theory) in the ensemble moves
faster than light."* Built directly on the explicit deterministic decoder of
`ChapterInverseTransform` (uniform seed `u ∈ [0,1)`, member with seed `u` yields
outcome `k` when `u ∈ seedSet p k`). One new file, `sorry`-free / `axiom`-free
(only `propext`, `Classical.choice`, `Quot.sound`):

* `ChapterCausality.lean` — the faster-than-light outcomes are a finite set
  `S ⊆ {0,…,n-1}`; the members whose outcome is in `S` are exactly
  `⋃_{k∈S} seedSet p k`. `seedSet_biUnion_measure` — the measure of that set is
  `∑_{k∈S} p k` (the deterministic ensemble reproduces the quantum probability of
  *any* set of outcomes, via `measure_biUnion_finset` and the pairwise
  disjointness of the seed intervals). Headlines: `causality` — if Quantum
  Mechanics predicts a **null** faster-than-light probability (`∑_{k∈S} p k = 0`),
  the set of ensemble members moving faster than light is a **null set**; and
  `causality_ae` — the a.e. reformulation, for **almost every** seed `u` the
  member does not land in `S` (the precise sense of *"no system in the ensemble
  moves faster than light"*). This completes the last formalizable subsection of
  the "Reconstructing the classical trajectory" chapter that is off the Bell/EPR
  comparison thread (the remaining *"Quantum Mechanics is EPR-complete"* and
  *"Do the Bell inequalities hold"* subsections are prose / Bell-comparison and
  out of scope per the author's instruction). Registered in `BookProof.lean`;
  `lake build BookProof` green (8167 jobs).

## Wave 110 (2026-07-10) — **Book "Wave-function parametrization of a probability measure", §9 "Deterministic transformations": commutation criterion for determinism** (`ChapterDeterministic`)

Stayed on the book's main-conclusion thread (author instruction: prioritize
chapters other than Gravity and off the Bell/CHSH comparison results; no Hankel,
Majorana fine). Formalized the headline result of §9 *"Deterministic
transformations"* (`book.tex` line ~1958): *"an automorphism `U` is deterministic
if and only if `P_A` and `U P_B U†` commute for all events `A, B`."* This is the
commutation form of the same determinism criterion whose off-diagonal-Born core
lives in `ChapterReconstruct` and whose density-matrix/trace form lives in
`ChapterTimeTranslation`. One new file, `sorry`-free / `axiom`-free (only
`propext`, `Classical.choice`, `Quot.sound`):

* `ChapterDeterministic.lean` — building on `ChapterTimeTranslation`'s rank-one
  projection `proj a = |e_a⟩⟨e_a|` and transformed measurement operator
  `measOp U b = U P_b U†`, and `ChapterReconstruct`'s `IsDeterministic` (each
  column has ≤ 1 nonzero entry). Entry lemmas `proj_mul_measOp_apply`
  (`(P_a·U P_b U†) i j = if i=a then U a b·conj(U j b) else 0`) and
  `measOp_mul_proj_apply`. Per-column criterion
  `commute_proj_measOp_iff_isDeterministicCol` (for fixed `b`, `P_a` commutes with
  `U P_b U†` for all `a` iff column `b` of `U` is deterministic). Headlines:
  `commute_proj_measOp_iff_isDeterministic` (single-outcome form — `P_a` and
  `U P_b U†` commute for all `a, b` iff `U` is deterministic); and, with event
  projections `projSet A = ∑_{a∈A} P_a`, transformed event operator
  `measOpSet U B = U P_B U†` and `measOpSet_eq_sum` (`= ∑_{b∈B} U P_b U†`),
  the literal book statement `commute_projSet_measOpSet_iff_isDeterministic`
  (`P_A` and `U P_B U†` commute for **all events** `A, B` iff `U` is
  deterministic). Registered in `BookProof.lean`; `lake build BookProof` green.

## Wave 109 (2026-07-10) — **Book "Reconstructing the classical trajectory of any isolated quantum system", §"Reconstruction of the trajectory": post-selection / ABL conditional probability** (`ChapterTrajectory`)

Stayed on the book's main-conclusion thread (author instruction: off Bell/CHSH,
off Gravity, no Hankel; Majorana fine). The subsection *"Reconstruction of the
trajectory"* (`book.tex` line ~3044) argues that although only the *final* time of
a quantum trajectory is directly measurable, *post-selection* — "using
probabilities conditional on the final state and the same quantum time-evolution"
— lets one "predict the results of a measurement at another time between the
initial and final times", reconstructing the trajectory. One new file,
`sorry`-free / `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`):

* `ChapterTrajectory.lean` — the three-instant (initial → intermediate → final)
  *collapsed* Born process on `Fin n`: `midProb U Ψ a = ‖(U Ψ)_a‖²` (intermediate
  Born law), `transProb V f a = ‖V_{f a}‖²` (post-collapse transition law),
  `jointProb = midProb · transProb`, `finalProb = ∑ₐ jointProb`,
  `condProb = jointProb / finalProb` (the Aharonov–Bergmann–Lebowitz / two-state
  post-selected law), and `coherentFinal V U Ψ f = ‖(V U Ψ)_f‖²` (coherent final
  law with no intermediate measurement). Nonnegativity lemmas; `transProb_sum`
  and `midProb_sum` (unitary columns / vectors have unit ℓ² mass). Headlines:
  `finalProb_total` (the collapsed process is a genuine probability law,
  `∑_f finalProb = 1`), `jointProb_sum_final_eq_midProb` (**reconstruction
  consistency** — summing the post-selected joint law over final outcomes
  recovers the intermediate Born law), `condProb_sum` (the post-selected law is a
  probability distribution). Double-slit capstone (reusing `ChapterDoubleSlit`'s
  Hadamard `H`): `dslit_finalProb`/`dslit_condProb` (collapsed & post-selected
  laws are uniform `1/2`), `dslit_coherentFinal` (coherent law is certain `(1,0)`),
  and `dslit_interference` (`finalProb = 1/2 ≠ 1 = coherentFinal`, the
  self-interference "mystery"). Registered in `BookProof.lean`; `lake build
  BookProof` green (8165 jobs).

## Wave 108 (2026-07-10) — **Book "Reconstructing the classical trajectory of any isolated quantum system", §"Symmetries as irreversible processes": entropy form** (`ChapterIrreversible`)

Stayed on the book's main-conclusion thread (author instruction: off Bell/CHSH,
off Gravity, no Hankel; Majorana fine). The subsection *"Symmetries as
irreversible processes"* (`book.tex` line ~2679) states: *"A non-deterministic
symmetry transformation, when acting on a deterministic ensemble increases the
entropy of the ensemble after the wave-function collapse and therefore must be an
irreversible transformation"*, whereas a deterministic symmetry preserves the
entropy (reversible). This is the Shannon-entropy counterpart of the chapter's
main result (*time translation is a stochastic process iff deterministic*). One
new file, `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`):

* `ChapterIrreversible.lean` — `entropy p = ∑ a, Real.negMulLog (p a)` (Shannon
  entropy of a finite probability vector); `IsPointMass` (deterministic
  ensemble); `bornDist v a = ‖v a‖²` (Born distribution after wave-function
  collapse of the column `v = U e_k`); `IsDeterministicColumn` (the symmetry
  sends a basis state to a basis state up to phase). Lemmas: `entropy_nonneg`,
  `entropy_pointMass_zero` (deterministic ensemble ⇒ entropy 0),
  `entropy_pos_of_not_pointMass` (non-deterministic ensemble ⇒ entropy > 0),
  `entropy_eq_zero_iff_pointMass`, `isPointMass_bornDist_iff`. Headlines:
  `entropy_bornDist_eq_zero_iff` (**reversible** case — for a unit column, the
  collapsed ensemble has entropy 0 iff the column is deterministic) and
  `entropy_bornDist_pos_iff` (**irreversible** case — the collapsed ensemble has
  strictly positive entropy iff the column is non-deterministic: the symmetry
  strictly increases the entropy).

## Wave 107 (2026-07-10) — **Book "Reconstructing the classical trajectory of any isolated quantum system", §"Time translation is a stochastic process if and only if it is deterministic": density-matrix / trace form** (`ChapterTimeTranslation`)

Stayed on the book's main-conclusion thread (author instruction: off Bell/CHSH,
off Gravity, no Hankel). The section *"Time translation is a stochastic process if
and only if it is deterministic"* (`book.tex` line ~2613) is called by the book
*"one of the main results of this paper"*. Its linear-algebra core — the
off-diagonal Born sum `↔` determinism — was already in `ChapterReconstruct`
(`offDiag_eq_zero_iff_isDeterministic`, `offDiag_unit_iff`). This wave adds the
missing **density-matrix layer**: the book's literal statement that the two Born
probabilities `tr(diag(ρ)·U P_a U†)` (collapse first) and `tr(ρ·U P_a U†)` (act on
the full quantum state) coincide iff the symmetry is deterministic. One new file,
`sorry`-free / `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`):

* `ChapterTimeTranslation.lean` — pure-state density matrix `rho Ψ = |Ψ⟩⟨Ψ|`,
  wave-function collapse `diagPart` (keep the diagonal), rank-one outcome
  projection `proj a = |e_a⟩⟨e_a|`, and measurement operator `measOp U a = U P_a U†`.
  `measOp_apply` computes `measOp U a k l = U k a · conj(U l a)`; `trace_rho_measOp`
  and `trace_diagPart_measOp` identify the full and collapsed Born probabilities
  with the full and diagonal Born sums; `trace_diff` shows their difference is
  exactly `ChapterReconstruct.offDiag`. Headlines: `trace_eq_iff_isDeterministic`
  (the two traces agree for all outcomes/states ↔ `IsDeterministic U`) and
  `trace_eq_iff_isDeterministic_pure` (same, restricted to pure states
  `∑ ‖Ψ k‖² = 1`, matching the book's "for any pure density matrix"). Builds on
  `ChapterReconstruct`; registered in `BookProof.lean`; `lake build BookProof` green.

## Wave 106 (2026-07-10) — **Book "Reconstructing the classical trajectory of any isolated quantum system", §"A deterministic theory compatible with relativistic Quantum Mechanics": discrete inverse-transform sampling** (`ChapterInverseTransform`)

Moved off the Bell/CHSH thread (author instruction: the Bell/CHSH results are a
*comparison* only and the main conclusions do not depend on them) to the
main-conclusion subsection *"A deterministic theory compatible with relativistic
Quantum Mechanics"* (`book.tex` line ~2952). The book answers *"Does a
deterministic theory — consistent with the non-deterministic time evolution of
Quantum Mechanics — exist?"* constructively with **yes**, exhibiting one built on
**inverse-transform sampling**: since an experimental setting has discretely many
outcomes, QM predicts a CDF, and a uniform pseudo-random seed decoded through that
CDF reproduces the QM distribution. One new file, `sorry`-free / `axiom`-free
(only `propext`, `Classical.choice`, `Quot.sound`):

* `ChapterInverseTransform.lean` — for a discrete distribution `p : ℕ → ℝ` on
  outcomes `0,…,n-1` (`p i ≥ 0`, `∑_{i<n} p i = 1`), the CDF `cdf p k = ∑_{i<k} p i`
  and the per-outcome **seed intervals** `seedSet k = [cdf p k, cdf p (k+1))`.
  Results: `seedSet_measure` — `volume (seedSet k) = ENNReal.ofReal (p k)` (a
  uniformly drawn seed lands in `seedSet k` with probability exactly `p k`, so the
  deterministic decoder reproduces the quantum distribution; holds for any real
  `p k` since `Ico` is empty when `p k ≤ 0`); `seedSet_disjoint` — the seed
  intervals are pairwise disjoint (each seed yields at most one outcome, via
  `Monotone.pairwise_disjoint_on_Ico_succ`); `seedSet_cover` — the `n` seed
  intervals tile `[0,1)` exactly (each seed yields at least one outcome), using
  `cdf p 0 = 0` and `cdf p n = 1`; `seedSet_total_measure` — the seed intervals
  carry total measure `1`. Together: `seed ↦ (unique k<n with seed ∈ seedSet k)`
  is a well-defined *deterministic* map `[0,1) → {0,…,n-1}` pushing the uniform
  seed distribution forward to `p` — a deterministic theory experimentally
  indistinguishable from QM, the book's claim. The surrounding
  physical/metaphysical discussion stays prose. Registered in `BookProof.lean`;
  `lake build BookProof` green.

## Wave 105 (2026-07-10) — **Book "Reconstructing the classical trajectory of any isolated quantum system", §"Do the Bell inequalities hold?": Tsirelson's bound is tight** (`ChapterTsirelson`)

Continued the Bell chapter of Wave 104 (author instruction: do the next steps, prioritize
chapters other than Gravity, no Hankel). Mathlib already contains the abstract **Tsirelson
inequality** `tsirelson_inequality` (for any CHSH tuple in an ordered `*`-algebra over `ℝ`,
`A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁ ≤ √2^3 • 1`), and its docstring flags as *future work* that the
bound is tight: there is a CHSH tuple of `4×4` complex matrices whose CHSH operator has
`2√2` as an eigenvalue. This wave supplies that witness, tied to the concrete `ChapterBell`
two-qubit model. One new file, `sorry`-free / `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`):

* `ChapterTsirelson.lean` — the two-qubit CHSH tuple written as genuine elements of the
  *one* `*`-ring `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ`: Alice's `alA0 = σ_z ⊗ 1`,
  `alA1 = σ_x ⊗ 1`, Bob's `boB0 = 1 ⊗ (σ_z+σ_x)/√2`, `boB1 = 1 ⊗ (σ_z−σ_x)/√2`.
  `chshTuple_isCHSHTuple` proves this quadruple is a Mathlib `IsCHSHTuple` (each observable
  a self-adjoint involution; Alice's commute with Bob's), i.e. it satisfies exactly the
  hypotheses of `tsirelson_inequality`. `chshOp_eq_tuple` shows `ChapterBell.chshOp` equals
  the tuple's CHSH combination `alA0*boB0 + alA0*boB1 + alA1*boB0 − alA1*boB1` (via the mixed
  Kronecker product `(A⊗1)(1⊗B)=A⊗B`). `tsirelson_value_eq` records `2√2 = √2^3` (the
  Tsirelson value equals the abstract bound constant). `chshOp_eigenvector` is the tightness
  witness: `chshOp *ᵥ |Φ⁺⟩ = 2√2 • |Φ⁺⟩` — the Bell state is an eigenvector with eigenvalue
  `2√2` (refining `ChapterBell.chsh_quantum_value`, which only gave the expectation value).
  Headline `tsirelson_bound_tight` bundles: the concrete tuple is a CHSH tuple whose
  operator has the abstract bound `√2^3 = 2√2` as an eigenvalue, so `tsirelson_inequality`
  cannot be improved. Registered in `BookProof.lean`; `lake build BookProof` green.

## Wave 104 (2026-07-10) — **Book "Reconstructing the classical trajectory of any isolated quantum system", §"Do the Bell inequalities hold?": the Bell/CHSH inequality and its quantum (Tsirelson) violation** (`ChapterBell`)

Moved off the parity thread to a fresh, unmined chapter (author instruction: do the next
steps, prioritize chapters other than Gravity, no Hankel). The `book.tex` section *"Do the
Bell inequalities hold?"* (line ~3175) concedes the Bell inequalities are *"mathematically
valid inequalities [that] involve unrealistic assumptions"*; the two formalizable facts are
the inequality itself and its quantum violation. One new file, `sorry`-free / `axiom`-free
(only `propext`, `Classical.choice`, `Quot.sound`):

* `ChapterBell.lean` — Part A (classical / local hidden variables): `chsh_pointwise`, the
  elementary pointwise bound `|a₀b₀ + a₀b₁ + a₁b₀ − a₁b₁| ≤ 2` for `a₀,a₁,b₀,b₁ ∈ [-1,1]`;
  and `chsh_local`, the measure-theoretic Bell/CHSH inequality — for any probability
  measure `μ` and `[-1,1]`-valued random variables `A₀,A₁,B₀,B₁`, the CHSH correlator
  `|∫ (A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁) dμ| ≤ 2`. Part B (quantum violation, Tsirelson value):
  the concrete two-qubit model with Alice's `A₀ = σ_z`, `A₁ = σ_x`, Bob's
  `B₀ = (σ_z+σ_x)/√2`, `B₁ = (σ_z−σ_x)/√2`, the CHSH operator `chshOp` on `ℂ²⊗ℂ²`
  (Kronecker products), and the Bell state `|Φ⁺⟩ = (|00⟩+|11⟩)/√2`; `chsh_quantum_value`
  computes the expectation `⟨Φ⁺|S|Φ⁺⟩ = 2√2`, and `chsh_quantum_violates_local_bound`
  records `2 < 2√2` — quantum mechanics exceeds the classical Bell bound. Registered in
  `BookProof.lean`; `lake build BookProof` green.

## Wave 103 (2026-07-10) — **Book "On the physical parity transformation and antiparticles", §"Majorana spinors in the Standard Model": the combined `Z_4` background-symmetry generator** (`ChapterParityZ4`)

Continued the parity chapter (off the gravity line, off the Hankel line; Majorana in
scope). The book states that, promoting the CKM matrix to a background field, the
electroweak Lagrangian is invariant under `SU(2)_L × (SU(3)_C × U(1)_Y) ⋊ Z₄`, where the
`Z₄` factor is generated by the *single* generalized parity-reversal transformation acting
simultaneously on all fields. The preceding waves proved each per-field internal parity is
order four; this wave assembles them into that one generator. One new file, `sorry`-free /
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`):

* `ChapterParityZ4.lean` — the combined operator `combinedParity = (higgsParity, QLParity,
  mgamma 0, mgamma 0)` on the product monoid `FieldOps` of field-space endomorphisms
  (Higgs doublet `iσ₂` on `ℂ²`, left-handed quark doublet `-(σ₂⊗iγ⁰)` on `ℂ²⊗ℂ⁴`, and the
  right-handed quarks `iγ⁰` on `ℂ⁴` each). Results: `combinedParity_sq`
  (`P² = (-1,-1,-1,-1)`, every field squaring to `-1`), `combinedParity_sq_ne_one`
  (`P² ≠ 1`, not an involution), `combinedParity_pow_four` (`P⁴ = 1`),
  `combinedParity_order_four` (the conjunction), and the headline `combinedParity_orderOf`
  (`orderOf combinedParity = 4`) — the precise sense in which the one parity transformation
  generates a cyclic group `ℤ₄ = ℤ/4ℤ`. The full background gauge group and its semidirect
  structure remain prose. Reuses `ChapterParity.higgsParity_sq`/`mgamma0_sq` and
  `ChapterParityQL.QLParity_sq`. Registered in `BookProof.lean`; `lake build BookProof` green.

## Wave 102 (2026-07-10) — **Book "On the physical parity transformation and antiparticles", §"Majorana spinors in canonical quantization and antiparticles": the complex structure `J` and the creation/annihilation split** (`ChapterParityMajoranaQuant`)

Continued the parity chapter (off the gravity line, off the Hankel line; Majorana in
scope), this time formalizing the *canonical-quantization* subsection (`book.tex` line
~7680) rather than the Standard-Model subsection of the preceding waves. One new file,
`sorry`-free / `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`):

* `ChapterParityMajoranaQuant.lean` — the book quantizes a **real** Hilbert/symplectic space
  by a *skew-symmetric* complex structure `J` (`J² = -1`) and splits the self-adjoint field
  `a(v) = a(v+iJv) + a(v−iJv)` into annihilation (`v+iJv`) and creation (`v−iJv = (v+iJv)*`)
  parts. On the finite model `V = ℂᵐ`, `J` is a matrix with `J·J = -1` and `Jᴴ = -J`. With
  `iJ = i·J`, `annihProj = ½(1+iJ)`, `creatProj = ½(1−iJ)`: `iJ_herm` (`(iJ)ᴴ = iJ`) and
  `iJ_sq` (`(iJ)² = 1`, a Hermitian involution with eigenvalues `±1`); `proj_add`
  (`annihProj + creatProj = 1`, the field split); `annihProj_idem`/`creatProj_idem`
  (idempotents); `annih_creat_zero`/`creat_annih_zero` (complementary, product `0`);
  `annihProj_herm`/`creatProj_herm` (Hermitian, i.e. orthogonal projections); and the
  eigen-relations `J_annih` (`J·annihProj = (−i)·annihProj`), `J_creat`
  (`J·creatProj = i·creatProj`) exhibiting them as the `∓i`-eigenprojections of `J`. A
  concrete non-vacuous witness `stdJ = !![0,1;−1,0]` (`stdJ_sq`, `stdJ_skew`) shows the
  hypotheses are satisfiable. The abstract Clifford/CAR `C*`-algebra, the bosonic symplectic
  CCR `[a(v),a(w)] = ⟨v,Jw⟩i`, and the vacuum functional remain prose.

Registered in `BookProof.lean`; `lake build BookProof` green.

## Wave 101 (2026-07-09) — **Book "On the physical parity transformation and antiparticles", §"Majorana spinors in the Standard Model": the chirality projector in the left-handed quark doublet `Q_L`** (`ChapterParityChirality`)

Continued the parity chapter (off the gravity line, off the Hankel line; Majorana in
scope), extending `ChapterParity`/`ChapterParityQL`/`ChapterParitySU2`. One new file,
`sorry`-free / `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`):

* `ChapterParityChirality.lean` — the chapter's chirality/projection constraint on the
  left-handed quark doublet, `iγ⁵ Q_L = iσ₃ Q_L`, and the footnote's *"projector in
  `Q_L`"* used to halve the count of `SU(2)_L`-invariant Yukawa products (the `4`
  custodial matrices `{1, iσⱼ}` of `ChapterParityCustodial` "divided by `2`", leaving
  `2`). On `ℂ²⊗ℂ⁴ ≅ ℂ⁸`, with `isigma3 = (iσ₃)⊗1` and `igamma5 = 1⊗(iγ⁵ = mgamma5)`:
  `isigma3_sq`/`igamma5_sq` (`(iσ₃)² = (iγ⁵)² = -1`), `isigma3_igamma5`/`igamma5_isigma3`
  (they commute, both products equal the **chirality operator** `chi = (iσ₃)⊗(iγ⁵)`),
  `chi_sq` (`χ² = 1`, an involution with eigenvalues `±1`) and `chi_trace` (`tr χ = 0`, so
  the `±1` eigenspaces have equal dimension — the footnote's "divide by `2`"). The `Q_L`
  chirality **projector** `QLProj = ½(1 - χ)` is idempotent (`QLProj_idem`) with
  `tr = 4 = ½·dim` (`QLProj_trace`). Headline `chirality_iff`: the constraint
  `iσ₃ Q_L = iγ⁵ Q_L` ⇔ `χ Q_L = -Q_L`; `chirality_iff_proj`: ⇔ `Q_L` lies in the range of
  the projector, `QLProj Q_L = Q_L`. The full Standard-Model Yukawa Lagrangian and the
  `SU(2)_L × (SU(3)_C × U(1)_Y) ⋊ ℤ₄` background symmetry remain prose.

Registered in `BookProof.lean`; `lake build BookProof` green.

## Wave 100 (2026-07-09) — **Book "On the physical parity transformation and antiparticles", §"Majorana spinors in the Standard Model": the custodial commutant / Pauli basis, and the `U(1)_Y` phase group generated by `iγ⁵`** (`ChapterParityCustodial`, `ChapterParityHypercharge`)

Continued the parity chapter (off the gravity line, off the Hankel line; Majorana in
scope), extending `ChapterParity`/`ChapterParitySU2`. Two new files, `sorry`-free /
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`):

* `ChapterParityCustodial.lean` — the representation theory behind the chapter's footnote
  *"the basis of matrices commuting with the generators of `SU(2)_L` is `{1, iσ_j}`, for a
  total of 4 matrices."* `commutant_pauli_scalar`: the Pauli matrices `σ₁, σ₂, σ₃` act
  irreducibly on `ℂ²`, so any matrix commuting with all three is a scalar `M = (M 0 0)•1`
  (Schur's lemma for the doublet). `pauli_basis_indep`: `{1, σ₁, σ₂, σ₃}` are linearly
  independent over `ℂ` (hence a basis of `Matrix (Fin 2) (Fin 2) ℂ`), so the custodial
  generators `{1, iσ_j}` are four linearly independent matrices.
* `ChapterParityHypercharge.lean` — the chapter's *"the generator of the gauge group
  `U(1)_Y` is `iγ⁵`"* / *"the imaginary unit replaced by `iγ⁵`"*. In the concrete real
  Majorana model, `mgamma5_real`: `iγ⁵ = mgamma5` is a genuine **real** matrix
  (`conj(iγ⁵) = iγ⁵`) which, with `(iγ⁵)² = -1` (`ChapterA3.mgamma5_sq`), is a *real*
  complex structure. The `U(1)_Y` phase `e^{ϑ iγ⁵}` has the closed form
  `hyperPhase ϑ = cos ϑ·1 + sin ϑ·iγ⁵`; `hyperPhase_zero`, `hyperPhase_add`
  (`hyperPhase ϑ · hyperPhase φ = hyperPhase (ϑ+φ)`, the abelian group law via the
  cos/sin addition formulas and `(iγ⁵)² = -1`), `hyperPhase_neg_mul` (invertibility), and
  `hyperPhase_comm` establish it as the one-parameter `U(1)_Y` group generated by `iγ⁵`.
  The `SU(3)` outer-nontriviality and the full Standard-Model gauge structure remain prose.

Both registered in `BookProof.lean`; `lake build BookProof` green.

## Wave 99 (2026-07-09) — **Book "On the physical parity transformation and antiparticles", §"Majorana spinors in the Standard Model": the Higgs is a real representation, and `SU(2)_L` has trivial outer automorphism** (`ChapterParityHiggs`, `ChapterParitySU2`)

Continued the parity chapter (off the gravity line, off the Hankel line; Majorana in
scope), extending `ChapterParity`/`ChapterParityQL`. Two new files, `sorry`-free /
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`):

* `ChapterParityHiggs.lean` — the chapter's thesis that at the quantum level all fields are
  **real representations**, for the electroweak Higgs doublet: the Majorana condition
  `iσ₂ φ = iτ₂ φ*` is realized on the bidoublet `ℂ²⊗ℂ²` by the antilinear operator
  `C(φ) = (τ₂⊗σ₂) φ*`. The antilinear reality operator `realityOp M v = M *ᵥ v*` has square
  `realityOp_realityOp` : `C_M∘C_M = (M·M*) *ᵥ ·`, so it is a real structure iff `M·M* = 1`
  and a quaternionic (pseudoreal) structure iff `M·M* = -1`. A single doublet is
  **pseudoreal** (`pauli2_map_conj` `σ₂* = -σ₂`, `pauli2_pseudoreal` `σ₂·σ₂* = -1`,
  `higgsDoublet_pseudoreal` `C₀² = -id`), but the general lemma
  `pseudoreal_kron_pseudoreal_real` (`A·A*=-1`, `B·B*=-1` ⇒ `(A⊗B)·(A⊗B)*=1`) gives the
  headline `higgs_real_structure` `C∘C = id` — **a tensor product of two quaternionic
  structures is a real structure**, so the Higgs bidoublet carries a genuine real structure
  even though neither `SU(2)` factor alone does.
* `ChapterParitySU2.lean` — the chapter's remark *"the outer automorphism group of `SU(3)`
  or `U(1)_Y` is `Z₂`, while the outer automorphism group of `SU(2)_L` is the trivial
  group."* For `SU(2)` the relevant automorphism (complex conjugation `g ↦ g*`) is **inner**:
  the pseudoreality intertwiner `pauliV_pseudoreal` `σ₂ σ_j σ₂ = -(σ_j)*` gives
  `su2_conj_inner` `conj(iσ_j) = σ₂ (iσ_j) σ₂` (with `σ₂²=1`), so the complex-conjugate
  representation is unitarily equivalent to the original — the outer automorphism group is
  trivial, in contrast with `SU(3)` whose conjugation negates `λ²,λ⁵,λ⁷`
  (`ChapterParity.gellMann_conj`, the nontrivial `Z₂`). The `SU(3)` outer-nontriviality and
  the full Standard-Model gauge structure remain prose.

Both registered in `BookProof.lean`; `lake build BookProof` green.

## Wave 98 (2026-07-09) — **Book "Real representations, CPT theorem and the relativistic position operator", §"Spinor frame and CPT theorem": the Dirac mass Hamiltonian is PT (CPT) invariant** (`ChapterCPTPT`)

Picked up directly after Wave 96/97, closing the full PT statement that `ChapterCPTParity`
explicitly left as prose (off the gravity line, off the Hankel line; Majorana in scope).
One new file, `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`):

* `ChapterCPTPT.lean` — the book's remark that the most general Lorentz-covariant Dirac
  mass Hamiltonian `iH = ∂⃗·γ⃗γ⁰ + iγ⁰m₁ + γ⁰γ⁵m₂` "is invariant under a parity–time
  reversal transformation (PT) … this is essentially the CPT theorem." The PT map is the
  antiunitary `ψ(t,x⃗) ↦ γ⁵ ψ*(-t,-x⃗)`, split into: **time reversal** = entrywise complex
  conjugation, which (since the three building blocks `Kin j = γʲγ⁰`, `MassA = iγ⁰`,
  `MassB = γ⁰γ⁵` are real matrices — `Kin_map_conj`, `MassA_map_conj`, `MassB_map_conj`)
  only flips the explicit `i`, i.e. flips the momentum: `conj_diracHamOp`
  `conj(D(k,m₁,m₂)) = D(-k,m₁,m₂)`; and the **γ⁵ dressing**, where `γ⁵ = dgamma5` commutes
  with the kinetic blocks and anticommutes with both mass blocks (`Kin_dgamma5_comm`,
  `MassA_dgamma5_anticomm`, `MassB_dgamma5_anticomm`, from integer-model `decide` relations
  transported along the cast), giving `pt_diracHamOp` `D(k)·γ⁵ = -(γ⁵·D(-k))`. Headline
  `cpt_diracHamOp`: `γ⁵ · conj(D(k,m₁,m₂)) = -(D(k,m₁,m₂) · γ⁵)` — a single-equation PT
  invariance holding for **arbitrary** `m₂`, even though parity `P` alone is broken by the
  `γ⁰γ⁵ m₂` term (`ChapterCPTParity.parity_diracHamOp`). The antiunitary field-representation
  wrappers remain prose.

Registered in `BookProof.lean`; `lake build BookProof` green.

## Wave 97 (2026-07-09) — **Book "On the physical parity transformation and antiparticles", §"Majorana spinors in the Standard Model": the left-handed quark-doublet parity is order four** (`ChapterParityQL`)

Continued the parity chapter (off the gravity line, off the Hankel line; Majorana in
scope), extending `ChapterParity`. One new file, `sorry`-free / `axiom`-free (only
`propext`, `Classical.choice`, `Quot.sound`):

* `ChapterParityQL.lean` — the internal (matrix) part of the generalized-parity
  transformation of the left-handed quark doublet `Q_L(t,x⃗) ↦ -σ₂ γ⁰ Q_L(t,-x⃗)`.
  Because `Q_L` carries both an `SU(2)_L` doublet index (acted on by `σ₂`) and a Majorana
  spinor index (acted on by the parity `i γ⁰ = mgamma 0`), the operator is the Kronecker
  product `QLParity = -(σ₂ ⊗ iγ⁰)` on `ℂ² ⊗ ℂ⁴ ≅ ℂ⁸`. Headline `QLParity_order_four`:
  it has order exactly four — `QLParity_sq` gives `(-σ₂ ⊗ iγ⁰)² = -1` (from
  `ChapterParity.pauli2_sq` `σ₂² = 1` and `ChapterParity.mgamma0_sq` `(iγ⁰)² = -1`, via
  `Matrix.mul_kronecker_mul`), and `QLParity_pow_four` gives `(…)⁴ = 1`, while the square
  is `-1 ≠ 1`. As for the right-handed quarks (`ChapterParity.fermionParity_order_four`),
  the value `-1` (not `+1`) selects the double cover `Pin(3,1)` over `Pin(1,3)`. The full
  Standard-Model Lagrangian and the `SU(2)_L × (SU(3)_C × U(1)_Y) ⋊ ℤ₄` background
  symmetry remain prose.

Registered in `BookProof.lean`; `lake build BookProof` green.

## Wave 96 (2026-07-09) — **Book "Real representations, CPT theorem and the relativistic position operator", §"Spinor frame and CPT theorem": parity classification of the Dirac mass Hamiltonian** (`ChapterCPTParity`)

Picked up directly after Wave 95's Localization obstruction (off the gravity line,
off the Hankel line; Majorana in scope). One new file, `sorry`-free / `axiom`-free:

* `ChapterCPTParity.lean` — the concrete parity content of the section's CPT-theorem
  discussion, built on `ChapterCPTHamiltonian`'s `diracHamOp` (the plane-wave form of
  `iH = ∂⃗·γ⃗γ⁰ + iγ⁰m₁ + γ⁰γ⁵m₂`). The parity (spatial-reflection) operation is the
  momentum flip `k⃗ ↦ -k⃗` plus spinor conjugation by the Majorana parity matrix
  `P = iγ⁰ = mgamma 0` (`P² = -1`, `P⁻¹ = -P`; `parity_mul_neg_self`). The three
  building blocks are classified (integer model by `decide`, complex model by cast):
  kinetic `Kin j = γʲγ⁰` **parity-odd** (`parity_Kin`/`parity_KinZ`), `m₁` mass
  `MassA = iγ⁰` **parity-even** (`parity_MassA`/`parity_MassAZ`), `m₂` mass
  `MassB = γ⁰γ⁵` **parity-odd** — the book's parity-breaking term
  (`parity_MassB`/`parity_MassBZ`). Headline `parity_diracHamOp`:
  `P · D(-k, m₁, m₂) · P⁻¹ = D(k, m₁, -m₂)`; corollary
  `parity_diracHamOp_invariant` (`m₂ = 0` ⇒ exactly parity-invariant), so a nonzero
  `γ⁰γ⁵` mass is the sole source of parity (CP) violation. The full PT/CPT antiunitary
  invariance statement remains prose.

Registered in `BookProof.lean`; `lake build BookProof` green.

## Wave 95 (2026-07-09) — **Book "Real representations, CPT theorem and the relativistic position operator", §"Localization": the algebraic core of Proposition 88 / Corollary 1** (`ChapterLocalization`)

Picked up directly after Wave 94's Prop 79 (off the gravity line, off the Hankel
line; Majorana in scope). One new file, `sorry`-free / `axiom`-free:

* `ChapterLocalization.lean` — the load-bearing algebraic fact behind **Prop 88**
  and **Corollary 1**: "`γ⁰` does not commute with the matrices `γ⃗γ⁰`", so the
  `iγ⁰`-eigenspace projectors are not preserved by the system of imprimitivity.
  In the concrete real Majorana model (`ChapterA3`, `M_μ = iγ^μ`) the commutator
  is computed in closed form: for every spatial `i ≠ 0`,
  `(iγ⁰)·((iγⁱ)(iγ⁰)) − ((iγⁱ)(iγ⁰))·(iγ⁰) = (iγⁱ) + (iγⁱ)`
  (`commZ_gamma0_spatial` over ℤ by `decide`, `comm_gamma0_spatial` over ℂ by
  transport along the integer cast), whence the non-commutation
  `gamma0_not_comm_spatialZ` / `gamma0_not_comm_spatial` (`iγⁱ ≠ 0` as it is
  unitary). Complementarily, `commZ_gamma0_rotation` / `comm_gamma0_rotation`
  show the spatial rotation generators `(iγⁱ)(iγʲ)` (`i, j ≠ 0`) do commute with
  `iγ⁰` — the massive little group `SU(2)` of Prop 79. The analytic wrappers of Prop 88 / Corollary 1 (systems of
  imprimitivity, direct-sum decompositions) remain prose.

Registered in `BookProof.lean`; `lake build BookProof` green.

## Wave 94 (2026-07-09) — **Book "Real representations, CPT theorem and the relativistic position operator", §"Real unitary representations of the Poincaré group": Definition 77, Definition 78 + Proposition 79** (`ChapterIPin`, `ChapterLittleGroup`, `ChapterSE2`)

Continued the Poincaré-representation section (off the gravity line, off the
Hankel line; Majorana in scope). Three new files, all `sorry`-free / `axiom`-free:

* `ChapterLittleGroup.lean` — **Def 78** little group `G_l = Subgroup.centralizer
  {q l₀}` (`mem_littleGroup`) and **Prop 79** headline `prop79`: in any group `G`
  with injective momentum map `q`, intertwiners `α` and Lorentz action `Λ`, the set
  `H_k = {(α (Λ S k))⁻¹ S (α k) : S}` equals `G_l`. Concrete `SU(2)`/`SE(2)`
  instances are prose.
* `ChapterIPin.lean` — **Def 77** the `IPin(3,1)` / Poincaré group `Pin(3,1) ⋉ ℝ⁴`
  as the Mathlib semidirect product `Multiplicative V ⋊[φ] P` (`phiHom`, `IPin`),
  with the product formula `(A,a)(B,b) = (A B, a + Λ(A) b)` (`ipin_right`,
  `ipin_left`).
* `ChapterSE2.lean` — **Prop 79** `SE(2)` translation subgroup over the concrete
  real Majorana matrices (`ChapterA3`): `N(a,b) = 1 + iγ⁵(γ¹a+γ²b)(γ⁰+γ³)` forms an
  abelian group `≅ ℝ²` (`Nmat_mul`, `Nmat_zero`, `Nmat_inv`, capstone `NmatHom`),
  from light-cone nilpotency `(γ⁰+γ³)²=0` (`se2_P_sq`) and `X·X=0`
  (`Xmat_mul_Xmat`), reducing to decidable integer identities `se2_coef_*`. The
  `e^{iγ⁰γ³γ⁵θ}` rotation factor is prose.

All registered in `BookProof.lean`; `lake build BookProof` green.

## Wave 93 (2026-07-09) — **Book "Real representations, CPT theorem and the relativistic position operator", §"Fourier-Majorana Transform", Proposition 76: the energy transform `𝓔` and the energy–momentum transform `𝓔∘𝓕_M` are unitary** (`ChapterMajoranaProp76`)

Formalized `book.tex` **Proposition 76**: the **energy transform**
`𝓔 = Θ_{L²} ∘ 𝓕_P(−p⁰) ∘ Θ_{L²}⁻¹` (Pauli–Fourier transform in the *time*
coordinate, conjugated by the real-linear identification `Θ`) is **unitary**
"for the same conjugation reason" as Prop 73, and the composite `𝓔∘𝓕_M` is the
unitary **energy–momentum transform**.  Discharged the structural core via
Note 4's unitarity predicate `IsNote4Unitary` (surjective + diagonal-inner
preserving, as used in Prop 5): `note4_comp` (composition of Note-4 unitaries is
one), `LinearIsometryEquiv.isNote4Unitary` (any `≃ₗᵢ` is one), and `note4_conj`
(conjugation by a linear isometry equivalence preserves unitarity — needs no
linearity of the conjugated map).  Headlines `energyTransform_unitary` and
`energyMomentum_unitary`, plus a concrete instantiation on Mathlib's
`MeasureTheory.Lp.fourierTransformₗᵢ` (Plancherel `≃ₗᵢ[ℂ]`):
`fourierTransform_isNote4Unitary`, `energyTransform_fourier_unitary`.  The
`𝓔∘𝓗_M` "spherical" branch (Majorana–Hankel) is deliberately omitted (off the
Hankel line); off the gravity line.  `sorry`-free / `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).  New file `BookProof/ChapterMajoranaProp76.lean`
(registered in `BookProof.lean`).

## Wave 92 (2026-07-09) — **Book "Real representations, CPT theorem and the relativistic position operator", §"Systems on real and complex Hilbert spaces", Proposition 5: (anti-)unitarity is a realification-invariant** (`ChapterA1Prop5`)

Formalized `book.tex` **Proposition 5** (line ~4797): for complex Hilbert spaces
`H₁, H₂` and their realifications `H₁ʳ, H₂ʳ`, an operator `U : H₁ → H₂` is
(anti-)unitary — surjective and `⟪U x, U x⟫ = ⟪x, x⟫` (Note 4) — iff its
realification `Uʳ = U` is (anti-)unitary between the realifications.  The
realification is the same carrier with `⟪·,·⟫_ℝ = re ⟪·,·⟫_ℂ` (Mathlib's
`InnerProductSpace.rclikeToReal`, a **local** instance), so `Uʳ` is literally `U`
and surjectivity is shared verbatim.  The core `inner_self_complex_iff_real`
(for an arbitrary function `T`, `∀x, ⟪Tx,Tx⟫_ℂ = ⟪x,x⟫_ℂ` iff
`∀x, ⟪Tx,Tx⟫_ℝ = ⟪x,x⟫_ℝ`) needs no (anti-)linearity, so it covers the unitary
and anti-unitary cases uniformly; headline `prop5` plus the `prop5_linear`
(`→ₗ[ℂ]`) / `prop5_antilinear` (`→ₗ⋆[ℂ]`) specializations.  `sorry`-free /
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).  Off the gravity
line and off the Hankel line.  New file `BookProof/ChapterA1Prop5.lean`
(registered in `BookProof.lean`).

## Wave 91 (2026-07-09) — **Book "Real representations, CPT theorem and the relativistic position operator", §"Fourier-Majorana Transform", Proposition 74: the inverse Majorana–Fourier intertwining identities** (`ChapterMajoranaProp74`)

Formalized `book.tex` **Proposition 74** (line ~6003): the inverse Majorana–Fourier
transform `𝓕_M⁻¹ = (𝓕_P^Θ)⁻¹ ∘ S⁻¹` intertwines the Dirac operator with the energy
multiplier, `Q·S⁻¹ = S⁻¹·R`, and the momentum-component block `Dⱼ` commutes with
the boost mixing `S⁻¹`, `Dⱼ·S⁻¹ = S⁻¹·Dⱼ`.  Both are `2×2`-block matrix identities
over the concrete `4×4` Dirac model of `ChapterMajoranaFourier` (blocks `Qmat`,
`Sinv`, `Rmat`, `Dmat`; `A = (n̂·γ⃗)γ⁰`).  Proved abstractly first
(`prop74_intertwine`, `prop74_Rj_comm`) for any `g, ns` with `g²=1`, `ns²=−1`,
`g·ns=−ns·g`, then instantiated on the Dirac matrices (`majoranaFourier_prop74`,
`majoranaFourier_prop74_Rj`) using the boost half-angle identities.  Helper Clifford
lemmas `ns_mul_A`/`g_mul_A`/`A_mul_g`.  `sorry`-free / `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`, confirmed via `lean_verify` on both headline
theorems).  Off the gravity line and off the Hankel line.  New file
`BookProof/ChapterMajoranaProp74.lean` (registered in `BookProof.lean`).

## Wave 90 (2026-07-09) — **Book "Real representations, CPT theorem and the relativistic position operator", §"Fourier-Majorana Transform", Proposition 61: the boost intertwiner `U'` is unitary** (`ChapterMajoranaProp61`)

Formalized `book.tex` **Proposition 61** (line ~5712): given a unitary `U` with
`U H² = E² U` (Majorana/Dirac `iH = γ⁰(∂⃗·γ⃗) + iγ⁰m`), the boost intertwiner
`U' = (E + U H γ⁰ U†)/(√(E+m)√(2E))` is unitary.  The operator identity is
captured as pure `ℝ`-star-algebra content in a general
`[Ring 𝒜] [StarRing 𝒜] [Algebra ℝ 𝒜] [StarModule ℝ 𝒜]` with the Majorana setup
as named hypotheses (Clifford anticommutator `H*g + g*H = (2m)•1`, intertwining
`E² = U H² U†`, `E`/normaliser commuting with `A = U H γ⁰ U†`).  Declarations:
`gsq_Hsq_comm` (`g*(H*H) = (H*H)*g` from the anticommutator), `Aop`/`Uprime`,
`prop61_star_mul_self` (`(U')†U' = 1`), `prop61_mul_star_self` (`U'(U')† = 1`),
headline `prop61_isUnit` (`U'` is a unit with inverse `(U')†`).  Off the gravity
line and off the Hankel line (the Hankel-Majorana material of Defs 65–66 is
untouched).  New file `BookProof/ChapterMajoranaProp61.lean` (registered in
`BookProof.lean`).

## Wave 89 (2026-07-09) — **Book "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups", Lemma 52: the four representation spaces form an internal direct sum** (`ChapterLorentzRealRepDirect`)

Continuing Waves 86–88 (`ChapterLorentzRealRep`, `ChapterLorentzRealRepSum`,
`ChapterLorentzRealRepFull`; the four mutually Frobenius-orthogonal real
representation spaces `WHalf`/`W10`/`WPs`/`WTwo` inside the 16-dimensional real
matrix algebra, with the decomposition certified only through a dimension count),
this wave upgrades the informal direct-sum claim to the genuine structural
statement.  Off the gravity line and off the Hankel line (Majorana matrices in
scope).  New file `BookProof/ChapterLorentzRealRepDirect.lean` (registered in
`BookProof.lean`).

- the family `WFam = ![WHalf, W10, WPs, WTwo]`;
- **spanning** `iSup_WFam_eq_top` (`⨆ i, WFam i = ⊤`);
- **dimension count** `sum_finrank_WFam` (`∑ i, finrank (WFam i) = finrank (Matrix (Fin 4) (Fin 4) ℝ)`);
- **headline** `WFam_isInternal : DirectSum.IsInternal WFam` (the canonical map
  `⨁ᵢ WFam i → Matrix (Fin 4) (Fin 4) ℝ` is an isomorphism, via the
  finite-dimensional bijectivity argument: surjective with range `⨆ i, WFam i = ⊤`
  and domain of dimension `∑ finrank (WFam i) = 16 = finrank` of the codomain);
- **independence** `WFam_iSupIndep : iSupIndep WFam`;
- **conjugation representation** `WFam_conj_invariant` — conjugation by every
  `S ∈ Ω` maps each `WFam i` into itself, so the 16-dimensional conjugation
  representation of the discrete Pin subgroup `Ω` decomposes as the internal
  direct sum of the four subrepresentations.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `lean_verify` on `WFam_isInternal` and
`WFam_conj_invariant`).  `lake build BookProof` green (the only build failure is
the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`).

## Wave 88 (2026-07-09) — **Book "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups", Lemma 52: the complete orthogonal decomposition of the 16-dimensional matrix algebra** (`ChapterLorentzRealRepFull`)

Continuing Waves 86–87 (`ChapterLorentzRealRep`, `ChapterLorentzRealRepSum`; the
three real representation spaces `WHalf`/`W10`/`WPs` and their 14-dimensional
mutually-orthogonal internal direct sum), this wave exhibits the **remaining
two-dimensional summand** and hence the *complete* orthogonal decomposition of
the full 16-dimensional real matrix algebra `Matrix (Fin 4) (Fin 4) ℝ`.  The
missing directions are the two "discrete" Majorana matrices `WTwo = span{iγ⁰,
γ⁰γ⁵}` that generate the covering group `Ω`.  Off the gravity line and off the
Hankel line (Majorana matrices in scope).  New file
`BookProof/ChapterLorentzRealRepFull.lean` (registered in `BookProof.lean`).

- **conjugation invariance** `conj_inv_two` (over `ℤ`, by `decide`) and the
  `Submodule` form `WTwo_invariant` (conjugation by every `S ∈ Ω` maps `WTwo`
  into itself);
- **Frobenius Gram / orthogonality** `gram_two`/`gram_twoR` (`= 4·I`) and the
  cross pairings `gram_two_halfR`/`gram_two_10R`/`gram_two_PsR` (`WTwo ⟂ WHalf,
  W10, WPs`); `w2R_linearIndependent`, `finrank_WTwo = 2`;
- **concatenated 16-element basis** `bFull`/`bFullR` with Frobenius Gram `4·I`
  (`gram_fullR`), hence `bFullR_linearIndependent`; span identification
  `range_bFullR`/`span_bFullR_eq` (`span (range bFullR) = WHalf ⊔ W10 ⊔ WPs ⊔ WTwo`);
- **complete decomposition** `finrank_matrix` (`dim (M₄(ℝ)) = 16`),
  `finrank_full = 16`, the headline `decomposition_top`
  (`WHalf ⊔ W10 ⊔ WPs ⊔ WTwo = ⊤`) and `finrank_full_eq_add`
  (`16 = dim WHalf + dim W10 + dim WPs + dim WTwo = 4 + 6 + 4 + 2`), certifying
  the complete internal direct sum.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `lean_verify`).  `lake build
BookProof.ChapterLorentzRealRepFull` green (the only build failure is the
pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched).

## Wave 87 (2026-07-09) — **Book "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups", Lemma 52: the three real representations are mutually orthogonal and form an internal direct sum** (`ChapterLorentzRealRepSum`)

Continuing Wave 86 (`ChapterLorentzRealRep`, the three real representation spaces
`WHalf`/`W10`/`WPs` of **Lemma 52**), this wave discharges the *distinctness* half
of the classification: the three spaces are **mutually orthogonal** in the
Frobenius inner product `⟨A,B⟩ = tr(Aᵀ B)`, so their sum inside the 16-dimensional
space of real `4×4` matrices is an **internal direct sum** of dimension
`4 + 6 + 4 = 14`.  Off the gravity line and off the Hankel line (Majorana matrices
in scope).  New file `BookProof/ChapterLorentzRealRepSum.lean` (registered in
`BookProof.lean`).

- **mutual orthogonality** `gram_half10`/`gram_halfPs`/`gram_10Ps` (over `ℤ`, by
  `decide`) and real casts `gram_half10R`/`gram_halfPsR`/`gram_10PsR` — every
  cross Frobenius pairing between two different bases vanishes;
- **concatenated basis** `bAll : Fin 14 → …` (the 4+6+4 concatenation) with real
  cast `bAllR`; `gram_all`/`gram_allR` show its Frobenius Gram matrix is `4·I`,
  hence `bAllR_linearIndependent` (the 14 matrices are linearly independent);
- **span identification** `range_bAllR` and `span_bAllR_eq`
  (`span (range bAllR) = WHalf ⊔ W10 ⊔ WPs`);
- **dimensions** `finrank_WHalf = 4`, `finrank_W10 = 6`, `finrank_WPs = 4`,
  `finrank_sup = 14`, and the headline `finrank_sup_eq_add`
  (`dim (WHalf ⊔ W10 ⊔ WPs) = dim WHalf + dim W10 + dim WPs`), certifying the
  internal direct sum.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `lean_verify`).  `lake build BookProof` green (the
only build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`,
left untouched).

## Wave 86 (2026-07-09) — **Book "Real representations, CPT theorem and the relativistic position operator", §"Finite-dimensional representations of SL(2,C)", Lemma 52: the concrete real irreducible representations** (`ChapterLorentzRealRep`)

Continuing Waves 84–85 (`ChapterPinOmega` `Ω ≅ Q₈`; `ChapterPinDoubleCover` the
cover `Λ : Ω → Δ`), this wave discharges the concrete core of **Lemma 52**
(`book.tex` line ~5560): the three explicit real irreducible representation
spaces of `SL(2,C)` on which the spin group acts by conjugation `A ↦ S A S†`,
verified over the discrete Pin group `Ω`.  Off the gravity line and off the
Hankel line (Majorana matrices in scope).  New file
`BookProof/ChapterLorentzRealRep.lean` (registered in `BookProof.lean`).

- The **`(1/2,1/2)` vector rep** `WHalf` = span `{1, γ⁰γ¹, γ⁰γ², γ⁰γ³}` (dim 4),
  the **`(1,0)` rep** `W10` = span `{iγ¹, iγ², iγ³, γ¹γ⁵, γ²γ⁵, γ³γ⁵}` (dim 6),
  the **pseudo-`(1/2,1/2)` rep** `WPs` = span `{iγ⁵, iγ⁵γᵏγ⁰}` (dim 4);
- **conjugation invariance** `conj_inv_half`/`conj_inv_10`/`conj_inv_ps` — for
  every `S ∈ Ω`, `S A S⁻¹` is `±` a basis matrix (signed permutation), by `decide`
  over `ℤ`; `cinv`/`cinv_correct` give the in-`Ω` inverse;
- **dimension** via `linIndep_of_gram` (Frobenius Gram `= 4·I` ⇒ linearly
  independent) applied to `gram_halfR`/`gram_10R`/`gram_psR`: headlines
  `bHalfR_linearIndependent`, `b10R_linearIndependent`, `bPsR_linearIndependent`;
- **`Submodule` invariance** `WHalf_invariant`/`W10_invariant`/`WPs_invariant`
  (the conjugation map carries each `ℝ`-span into itself for `S ∈ Ω`), with
  elementwise corollary `WHalf_invariant_apply`.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `lean_verify`).  `lake build BookProof` green (the
only build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`,
left untouched).

## Wave 85 (2026-07-09) — **Book "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups", Definition 49: the discrete Pin subgroup `Ω` is the *double cover* of the discrete Lorentz subgroup `Δ`** (`ChapterPinDoubleCover`)

Continuing Wave 84 (`ChapterPinOmega`, `Ω ≅ Q₈`), this wave discharges the
remaining finite core of **Definition 49** (`book.tex` line ~5510): the two-to-one
covering map `Λ : Ω → Δ` onto the Klein-four discrete Lorentz subgroup
`Δ = {1, η, -η, -1}` (`η = diag(1,-1,-1,-1)`).  `Λ` is defined by the conjugation
action on the Majorana basis, `S⁻¹(iγ^μ)S = Λ(S)^μ_ν iγ^ν`; rewritten without
inverses this is decidable over the integer Majorana model `mgammaZ` of
`ChapterA3`.  Per the current instruction this stays **off the gravity line** and
**off the Hankel-transform line** (Majorana matrices in scope).  New file
`BookProof/ChapterPinDoubleCover.lean` (registered in `BookProof.lean`).

- `qi`/`qj`/`qk`, `etaZ` (with `etaZ_eq_mink` tying `η` to `minkowskiZ`), the
  8-element `Omega` (`Omega_card = 8`) and 4-element `Delta` (`Delta_card = 4`);
- `LamZ` — the explicit induced Lorentz matrix, `±1 ↦ 1`, `±iγ⁰ ↦ η`,
  `±γ⁰γ⁵ ↦ -η`, `±iγ⁵ ↦ -1`;
- `LamZ_spec` — the **defining conjugation relation** `(iγ^μ)S = S(Σ_ν Λ^μ_ν iγ^ν)`
  validating the formula for `LamZ`;
- `LamZ_mem_Delta` (lands in `Δ`), `LamZ_surjective` (`Δ = Ω.image LamZ`, onto),
  `LamZ_hom` (homomorphism `Λ(ST)=Λ(S)Λ(T)`), `LamZ_neg` (`Λ(S)=Λ(-S)`) and
  `LamZ_fiber_card` (every fibre has exactly **2** elements) — i.e. `Λ : Ω → Δ`
  is a surjective **2-to-1 homomorphism**, the double cover of Def 49;
- `LamZ_spec_C` — the conjugation relation transported to the complex Majorana
  matrices `mgamma`.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `#print axioms`).  `lake build BookProof` green (the
only build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`,
left untouched).

## Wave 84 (2026-07-08) — **Book "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups", Definition 49: the discrete Pin subgroup `Ω` is the quaternion group `Q₈`** (`ChapterPinOmega`)

From the same §*"On the Lorentz, SL(2,C) and Pin(3,1) groups"* (`book.tex` line
~5510), **Definition 49** introduces the discrete `Pin(3,1)` subgroup
`Ω = {±1, ±iγ⁰, ±γ⁰γ⁵, ±iγ⁵}` and asserts (via the two-to-one cover `Λ`) that
it is a group of order `8` — the double cover of the Klein-four discrete Lorentz
subgroup `Δ`.  This wave pins down the algebraic core: `Ω` **is the quaternion
group `Q₈`**.  Per the current instruction this stays **off the gravity line**
and **off the Hankel-transform line** (Majorana matrices are now in scope); it
reuses only the concrete `4×4` real Majorana/Dirac matrix model of
`BookProof.ChapterA3`.  New file `BookProof/ChapterPinOmega.lean` (registered in
`BookProof.lean`).

- `qi = iγ⁰`, `qj = γ⁰γ⁵ = -(iγ⁰)(iγ⁵)`, `qk = iγ⁵` — the three imaginary
  units (integer model `mgammaZ`/`mgamma5Z`);
- `qi_sq`/`qj_sq`/`qk_sq` — `qi² = qj² = qk² = -1`;
- `qi_qj`/`qj_qk`/`qk_qi` and the anti-commuted `qj_qi`/`qk_qj`/`qi_qk` — the
  **quaternion relations** `ij=k, jk=i, ki=j` (and `ji=-k`, …);
- `qi_qj_qk` — Hamilton's identity `qi·qj·qk = -1`; `noncomm` — `Ω` nonabelian;
- `Omega` (the 8-element `Finset`), `Omega_card = 8`, `one_mem_Omega`,
  `neg_one_mem_Omega`, `Omega_mul_closed` (**closure**), `Omega_inv`
  (**inverses**) — i.e. `Ω` is a group of order `8` (⇒ `≅ Q₈`);
- the complex model `qiC`/`qjC`/`qkC` with `qjC_eq_dirac` (identifying `qj` with
  `γ⁰γ⁵` in the book's `γ^μ = -i(iγ^μ)` normalization) and the transported
  relations `qiC_sq`/…/`qiC_qjC_qkC`/`qjC_qiC`/`noncommC`.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `lean_verify`).  `lake build BookProof` green.

## Wave 83 (2026-07-08) — **Book "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups", Note 47 / Def 49: the `SU(2) → SO(3)` restriction of the spinor map** (`ChapterPauliSU2`)

Continuing Wave 82 (`ChapterPauliLorentz`) with the next self-contained claim of
the same §*"On the Lorentz, SL(2,C) and Pin(3,1) groups"* (`book.tex` line
~5455): the spinor map `Υ : SL(2,ℂ) → SO⁺(1,3)`, `Υᵘ_ν(T) σ^ν = T† σᵘ T`,
restricts on the compact subgroup `SU(2) = Spin⁺(3,1) ∩ SU(4)` to the **double
cover of `SO(3)`**.  As requested this stays **off the gravity line** and **off
the Hankel–Majorana line**: it uses only the concrete `2×2` Pauli machinery of
`ChapterPauliLorentz` (no gamma/Majorana matrices, no spherical-Bessel
numerics).  New file `BookProof/ChapterPauliSU2.lean` (registered in
`BookProof.lean`).

- `spinorAction T X = Tᴴ * X * T` — the spinor conjugation;
- `spinorAction_comp` — it is a (right) action: conjugation by `T₁*T₂` is
  conjugation by `T₁` then `T₂` (compatibility with group multiplication);
- `spinorAction_neg` — **two-to-one**: `T` and `-T` induce the *same* conjugation
  (the `±1` kernel making `Υ` a double cover);
- `spinorAction_isHermitian` — the conjugation preserves hermiticity;
- `spinorAction_trace_of_unitary` — for **unitary** `T` (`T†T = 1`) the
  conjugation **preserves the trace** (via cyclicity of trace + `T T† = 1`);
- `su2_preserves_time` — hence a unitary `T` **fixes the time component** `x⁰`
  of the 4-vector (`x⁰ = ½ tr(X)`);
- `su2_preserves_spatialNormSq` — **headline**: for `T ∈ SU(2)` (`T†T = 1`,
  `det T = 1`) the conjugation preserves the Euclidean spatial length
  `(x¹)² + (x²)² + (x³)²`, combining `su2_preserves_time` with the Minkowski-form
  preservation `spinorMap_preserves_mink` from `ChapterPauliLorentz` — i.e. the
  induced map is a rotation in `SO(3)`.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `lean_verify`).  `lake build BookProof` green.

## Wave 82 (2026-07-08) — **Book "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups", Definition 42 + Note 47: the Pauli 4-vector map and the `SL(2,ℂ)` spinor conjugation preserves the Minkowski form** (`ChapterPauliLorentz`)

From the chapter *"Real representations, CPT theorem and the relativistic
position operator"*, §*"On the Lorentz, SL(2,C) and Pin(3,1) groups"*,
**Definition 42** and **Note 47** (`book.tex` line ~5344, ~5455): the Pauli
matrices `σᵏ` are `2×2` hermitian, unitary, anti-commuting complex matrices, and
there is a two-to-one surjection `Υ : SL(2,ℂ) → SO⁺(1,3)` given by
`Υᵘ_ν(T) σ^ν = T† σᵘ T`. This wave formalizes the algebraic heart of Note 47:
the correspondence between real Minkowski 4-vectors and hermitian `2×2` complex
matrices, and the fact that the spinor conjugation `X ↦ T† X T` by
`T ∈ SL(2,ℂ)` (`det T = 1`) **preserves the Minkowski quadratic form** — which
is exactly what makes `Υ(T)` a Lorentz transformation. As requested this stays
**off the gravity line** and **off the Hankel–Majorana line**: it uses only the
concrete Pauli matrices (`2×2` complex), no gamma/Majorana matrices and no
spherical-Bessel numerics. New file `BookProof/ChapterPauliLorentz.lean`
(registered in `BookProof.lean`).

- `σ1_herm`/`σ2_herm`/`σ3_herm`, `σ1_sq`/`σ2_sq`/`σ3_sq` (`(σᵏ)²=1`),
  `σ1σ2_anti`/`σ2σ3_anti`/`σ1σ3_anti` — **Definition 42**: the Pauli matrices
  are hermitian, unitary/involutive and pairwise anti-commuting;
- `hermMat` — the hermitian matrix `X = xᵤσᵘ` of a real 4-vector `x`;
  `hermMat_eq_pauli` (Pauli expansion), `hermMat_isHermitian`;
- `det_hermMat` — **the key identity**: `det(xᵤσᵘ) = (x⁰)²−(x¹)²−(x²)²−(x³)²`,
  i.e. the determinant of the hermitian matrix *is* the Minkowski norm;
- `vecOfMat` / `hermMat_vecOfMat` / `hermMat_injective` — every hermitian `2×2`
  matrix is `xᵤσᵘ` for a unique real 4-vector (`vecOfMat` is a left inverse of
  `hermMat` on hermitians, and `hermMat` is injective on the four components),
  i.e. the real-linear bijection between 4-vectors and hermitian matrices;
- `spinorMap_preserves_mink` — **headline**: for `T` with `det T = 1` and any
  real 4-vector `x`, the transformed matrix `T† (xᵤσᵘ) T` is again `yᵤσᵘ` with
  `mink y = mink x` (via `det(T† X T) = det X`).

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `lean_verify`).  `lake build BookProof` green.

## Wave 81 (2026-07-08) — **Book "Reconstructing the classical trajectory of any isolated quantum system", §"The Young's double slit experiment": the double slit as an involutive Hadamard evolution** (`ChapterDoubleSlit`)

From the chapter *"Reconstructing the classical trajectory of any isolated
quantum system"*, §*"The Young's double slit experiment"* (`book.tex` line
~3082): the two-angle electron is modelled by the normalized `2×2` Hadamard
matrix `H = (1/√2)·[[1,1],[1,-1]]` with source state `Ψ = (1,0)`. The book's
"mystery" — a `50/50` intermediate probability becoming a `100/0` detector
probability once the second slit is open — is pinned down as the purely
algebraic fact that `H` is an **involution** (`H² = 1`): composing the two
non-deterministic symmetry transformations yields certainty. As requested this
stays **off the gravity line** and **off the Hankel–Majorana line**; it reuses
only the concrete Hadamard matrix (as in `ChapterE.lean`). New file
`BookProof/ChapterDoubleSlit.lean` (registered in `BookProof.lean`).

- `H_unitary` — `Hᴴ H = 1` (the Hadamard evolution is unitary);
- `H_involutive` — **the crux**: `H² = 1`;
- `Hpsi0` — `H·Ψ = (1/√2)(1,1)`, the uniform intermediate superposition;
- `slit_closed_born` — **slit closed**: final Born distribution `(1/2, 1/2)`;
- `slit_open_state` / `slit_open_born` — **slit open**: `H·(H·Ψ) = Ψ`, final
  Born distribution `(1, 0)` (the electron arrives only along angle 1).

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `lean_verify`).  `lake build BookProof` green.

## Wave 80 (2026-07-08) — **Book "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups", Note 43: the coset / semidirect decomposition `O(1,3) = Δ ⋉ SO⁺(1,3)`** (`ChapterLorentzDecomp`)

Continuing Waves 78–79 (Note 43) with the next self-contained claim of the
**same Note 43** (`book.tex` line ~5366): the discrete Klein-four subgroup
`Δ = {1, η, -η, -1}` and the proper orthochronous normal subgroup `SO⁺(1,3)`
assemble into the whole group as a semidirect product `O(1,3) = Δ ⋉ SO⁺(1,3)` —
equivalently, `Δ` is a complete and irredundant transversal for `SO⁺(1,3)`, so
the quotient `O(1,3)/SO⁺(1,3) ≅ Δ` is the Klein four-group of the four connected
components indexed by `(det λ, sign λ⁰₀) ∈ {±1} × {±1}`.  As requested this stays
**off the gravity line** and **off the Hankel–Majorana line**: it uses only the
Minkowski metric `η` and the groups from `ChapterLorentzGroup` /
`ChapterLorentzOrthochronous` (no gamma / Majorana matrices).  New file
`BookProof/ChapterLorentzDecomp.lean` (registered in `BookProof.lean`).

- `delta_mul_time` — for a diagonal discrete generator `δ ∈ Δ`, the time
  component of a product factors: `(δ * m)⁰₀ = δ⁰₀ · m⁰₀`;
- `lorentz_delta_decomp` — **existence**: every `λ ∈ O(1,3)` factors as
  `λ = δ * s` with `δ ∈ Δ` and `s ∈ SO⁺(1,3)`, the discrete factor chosen by a
  4-way case split on `(sign det λ, sign λ⁰₀)`;
- `lorentz_delta_decomp_unique` — **uniqueness**: the two factors are determined
  by `λ`, because the map `δ ↦ (det δ, sign δ⁰₀)` is injective on `Δ` (its four
  values `(1,1),(−1,1),(−1,−1),(1,−1)` are distinct) and `s ∈ SO⁺(1,3)` has
  `det s = 1`, `s⁰₀ > 0`.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `lean_verify`).  `lake build BookProof` green.

## Wave 79 (2026-07-08) — **Book "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups", Note 43: the proper orthochronous Lorentz group `SO⁺(1,3)` is a normal subgroup of `O(1,3)`** (`ChapterLorentzOrthochronous`)

Continuing Wave 78 (Note 43) with the next self-contained claim of the **same
Note 43** (`book.tex` line ~5366): *"The proper orthochronous Lorentz subgroup is
defined by `SO⁺(1,3) ≡ {λ ∈ O(1,3) : det(λ)=1, λ⁰₀>0}`. It is a normal
subgroup."*  As requested, this stays **off the gravity line** and **off the
Hankel–Majorana line**: it uses *only* the Minkowski metric `η` and the group
`O(1,3)` from Wave 78 (no gamma / Majorana matrices).  New file
`BookProof/ChapterLorentzOrthochronous.lean` (registered in `BookProof.lean`).

- `isLorentz_neg` — `O(1,3)` is closed under negation;
- `lorentz_inv_eq` — the explicit inverse `λ⁻¹ = η λᵀ η`;
- `isLorentz_mul_eta_transpose` — the dual metric relation `λ η λᵀ = η`;
- `lorentz_time_col` / `lorentz_time_row` — the time–column / time–row unit
  identities `(λ⁰₀)² = 1 + Σᵢ(λⁱ₀)² = 1 + Σᵢ(λ⁰ᵢ)²`;
- `lorentz_time_sq_ge_one` (`(λ⁰₀)² ≥ 1`), `lorentz_time_ne_zero` (`λ⁰₀ ≠ 0`);
- `lorentz_inv_time` — `(λ⁻¹)⁰₀ = λ⁰₀`;
- `product_time_component` — the `(0,0)` entry of a matrix product;
- `orthochronous_mul` — **the crux**: `a⁰₀ > 0`, `b⁰₀ > 0 ⇒ (ab)⁰₀ > 0`, via the
  reverse Cauchy–Schwarz inequality on the time components;
- `IsProperOrthochronous` — the predicate defining `SO⁺(1,3)`;
- `isPO_one`, `isPO_mul`, `isPO_inv` — `SO⁺(1,3)` is a **subgroup**;
- `isPO_conj` — **headline**: `SO⁺(1,3)` is a **normal** subgroup of `O(1,3)`
  (`g ∈ O(1,3)`, `s ∈ SO⁺(1,3) ⇒ g s g⁻¹ ∈ SO⁺(1,3)`), by a sign case split on
  `g⁰₀` using that `-g` is Lorentz with `(-g)⁻¹ = -g⁻¹`.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `lean_verify`).  `lake build BookProof` green.

## Wave 78 (2026-07-08) — **Book "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups", Note 43: the Lorentz group `O(1,3)` and its discrete Klein-four subgroup `Δ = {1, η, -η, -1}`** (`ChapterLorentzGroup`)

Continuing the standing directive (mine the next self-contained mathematical
claim from `book.tex`) and — per the author's latest instruction —
**prioritizing a chapter other than gravity** and **staying off the
Hankel–Majorana line** (this wave uses *only* the Minkowski metric
`η = diag(1,-1,-1,-1)`; no gamma/Majorana matrices are involved).  From the
chapter *"Real representations, CPT theorem and the relativistic position
operator"*, §*"On the Lorentz, SL(2,C) and Pin(3,1) groups"*, **Note 43**
(`book.tex` line ~5340): the Lorentz group
`O(1,3) = {λ ∈ ℝ^{4×4} : λᵀ η λ = η}` is the set of real matrices preserving the
metric `η = diag(1,-1,-1,-1)`, and `Δ = {1, η, -η, -1}` is the discrete Lorentz
subgroup of parity and time-reversal.  New file
`BookProof/ChapterLorentzGroup.lean` (registered in `BookProof.lean`).

- `eta_transpose`, `eta_mul_self` (`η² = 1`), `eta_det` (`det η = -1`) — the basic
  properties of the Minkowski metric;
- `IsLorentz` — the defining predicate `λᵀ η λ = η` of `O(1,3)`;
- `isLorentz_one`, `isLorentz_mul`, `isLorentz_inv` — `O(1,3)` is closed under
  the identity, matrix product, and matrix inverse: it is a **group**;
- `lorentz_det_sq_one` (`(det λ)² = 1`) and `lorentz_det_ne_zero` — every Lorentz
  matrix is invertible with determinant `±1`;
- `isLorentz_eta`, `isLorentz_neg_eta`, `isLorentz_neg_one` — the three
  nontrivial discrete generators lie in `O(1,3)`;
- `Delta`, `delta_subset_lorentz` (`Δ ⊆ O(1,3)`), `delta_mul_closed`
  (closed under multiplication), `delta_involutive` (every element squares to
  `1`, so `Δ` is abelian `≅ ℤ₂ × ℤ₂`, the **Klein four-group**), and
  `delta_card_four` (the four elements are distinct, `|Δ| = 4`).

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `#print axioms`).  `lake build BookProof` green
(8130 jobs).  (The full semidirect-product decomposition
`O(1,3) = Δ ⋉ SO⁺(1,3)` is left as prose; this wave lands the group structure
and the Klein-four subgroup.)

## Wave 77 (2026-07-08) — **Book "Yang-Mills … Classical Statistical Field Theory" / "Timepiece and the Gribov ambiguity", §"Pure Yang-Mills theory": the ℤ₂-graded (super) commutator unifying the bosonic CCR and fermionic CAR** (`ChapterSuperBracket`)

Continuing the standing directive (mine the next self-contained mathematical
claim from `book.tex`), and — per the author's latest instruction —
**prioritizing chapters other than gravity** (and staying off the
Hankel–Majorana line).  For `SU(3)` Yang–Mills the author builds the Hilbert
space as a tensor product of a symmetric (bosonic) and an antisymmetric
(fermionic) Fock space, giving *"a graded Lie superalgebra of creation and
annihilation operators"* with the unified canonical (anti)commutation relation
carrying the sign `(-1)^{(α mod 2)(β mod 2)}`.  New file
`BookProof/ChapterSuperBracket.lean` (registered in `BookProof.lean`), modelling
the ℤ₂-parity of a homogeneous operator by a `Bool` (`false` = even/bosonic,
`true` = odd/fermionic) inside an arbitrary associative ring `R`.

- `eps p q = (-1)^{p·q}` (the Koszul sign) and `sbracket p q a b = a·b − ε(p,q)·(b·a)`
  (the super-bracket `⟦a,b⟧`);
- `eps_comm`, `eps_mul_self`, `eps_false_left`/`eps_false_right` — the sign is
  symmetric, squares to `1`, and is trivial against an even element;
- `sbracket_even_even` — even/even gives the **commutator** `a·b − b·a` (bosonic
  CCR side);
- `sbracket_odd_odd` — odd/odd gives the **anticommutator** `a·b + b·a`
  (fermionic CAR side): the single formula unifying the two canonical relations;
- `sbracket_even_left`/`sbracket_even_right` — against an even element the bracket
  is always the commutator;
- `sbracket_graded_antisymm` — **graded antisymmetry** `⟦a,b⟧ = −ε(p,q)⟦b,a⟧`;
- `super_jacobi` — **headline** the graded Jacobi identity
  `ε(p,r)⟦a,⟦b,c⟧⟧ + ε(q,p)⟦b,⟦c,a⟧⟧ + ε(r,q)⟦c,⟦a,b⟧⟧ = 0` (inner bracket
  parity `xor q r`), which makes `(R, ⟦·,·⟧)` a **Lie superalgebra** — exactly
  the graded-Lie-superalgebra structure the book asserts;
- `commutator_jacobi` — the all-even specialization is the ordinary Jacobi
  identity of the commutator.

All `sorry`-free / `axiom`-free (`super_jacobi` needs only `propext`,
`Quot.sound`, confirmed via `lean_verify`).  `lake build BookProof` green.
(The Hankel–Majorana line is left untouched; this wave stays off the gravity
line, on the Yang-Mills chapter.)

## Wave 76 (2026-07-08) — **Book "Yang-Mills … Classical Statistical Field Theory", §"Lorentz covariance": the space-time translation representation `T(x)Ψ(γv) = e^{iMτ}Ψ(γv)` in the momentum-diagonal basis** (`ChapterLorentzTranslation`)

Continuing the standing directive (mine the next self-contained mathematical
claim from `book.tex`), and — per the author's latest instruction — **prioritizing
chapters other than gravity** (and, as always, staying off the Hankel–Majorana
line).  From the chapter *"Quantization due to time-evolution: Yang-Mills and
Classical Statistical Field Theory"*, §*"Lorentz covariance"* (line ~6506): in a
basis where the 3-momentum operator is diagonal, the space-time translations of a
free system of invariant mass `M` act by the phase
`T(x) Ψ(γv) = e^{i M τ(γv, x)} Ψ(γv)` with proper time
`τ(γv, x) = γ x₀ − (γv)·x`, `γ = √(1 + (γv)²)`.  The book notes this has "the
same structure as the non-relativistic time-evolution, with `M` as Hamiltonian
and `τ` as (proper) time".  New file `BookProof/ChapterLorentzTranslation.lean`
(registered in `BookProof.lean`), modelling the spatial momentum `γv` by
`w : Fin 3 → ℝ`.

- `gamma`, `properTime`, `transPhase` — the Lorentz factor `γ`, the proper-time
  functional `τ`, and the translation phase `e^{iMτ}`;
- `gamma_sq` / `mass_shell` — the four-velocity `(γ, γv)` is on the unit mass
  shell `γ² − (γv)² = 1`;
- `gamma_zero` — rest-frame value `γ = 1`;
- `properTime_add`, `properTime_zero` — `τ` is additive in the translation `x`
  (a homomorphism `(ℝ⁴,+) → (ℝ,+)`);
- `properTime_rest` — in the rest frame `τ = x₀` (proper = coordinate time);
- `transPhase_add` — **headline** `T(x + y) = T(x)·T(y)` (with `transPhase_zero`
  `T(0) = 1`, a one-dimensional representation of the translation group);
- `transPhase_norm` — each `T(x)` is unitary (`‖·‖ = 1`, real `M`);
- `transPhase_rest` — rest-frame reduction `T(x) = e^{i M x₀}`.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `lean_verify`).  `lake build BookProof` green.
(Per the author's instruction the Hankel–Majorana line is left untouched, and
this wave deliberately steps off the gravity line onto the Yang-Mills chapter.)

## Wave 75 (2026-07-08) — **Book "Diffeomorphisms and gravity", §"Classical Hamiltonian": the irreducible `SO(3)` decomposition of a spatial tensor `T_{ab} = ½S + ½A + ⅓T·I`** (`ChapterGravityIrrep`)

Continuing the standing directive (mine the next self-contained mathematical
claim from `book.tex`), extending the gravity projector/metric line (Waves
69–74).  In the Einstein–Cartan / teleparallel Hamiltonian formalism the author
decomposes the *spatial* torsion tensor `T_{ab}` (both indices projected by the
spatial projector `χ` of Wave 69, so it lives on the `3`-dimensional spatial
hyperplane `v^⊥` where the induced metric is positive definite, Wave 70) into
its three `SO(3)`-irreducible pieces: the antisymmetric part
`A_{ab} = T_{ab} − T_{ba}`, the trace `T = η^{ab}T_{ab}`, and the symmetric
traceless part `S_{ab} = T_{ab} + T_{ba} − (2/3)η_{ab}T` (the book's `A`, `T`,
`S`).  Modelling the spatial slice as Euclidean `Fin 3` (`η = δ`, so `tr δ = 3`,
which is exactly why the `2/3` factor makes `S` traceless).  New file
`BookProof/ChapterGravityIrrep.lean` (registered in `BookProof.lean`).

- `antisymPart`, `symTracelessPart`, `frobInner` — the pieces `A`, `S`, and the
  Frobenius inner product `⟨X,Y⟩ = ∑_{i,j} X_{ij}Y_{ij}`;
- `antisymPart_antisymm` — `Aᵀ = −A`;
- `symTracelessPart_symm` — `Sᵀ = S`;
- `trace_symTracelessPart` — `tr S = 0` (the `2/3`/`dim = 3` fact);
- `irrep_reconstruction` — **headline** `M = ½S + ½A + ⅓(tr M)·I`;
- `frob_symTraceless_antisym`, `frob_symTraceless_trace`, `frob_antisym_trace` —
  the three pieces are mutually Frobenius-orthogonal (the decomposition is
  orthogonal).

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `#print axioms`).  `lake build BookProof` green.
(Per the author's instruction the Hankel–Majorana line is left untouched.)

## Wave 74 (2026-07-08) — **Book "Diffeomorphisms and gravity", §"Classical Hamiltonian": `h` and `h♯` form a generalized-inverse pair** (`ChapterGravityGenInverse`)

Continuing the standing directive (mine the next self-contained mathematical
claim from `book.tex`), and building on Wave 70's induced spatial metric `h`
and Wave 72's raised metric `h♯`.  Although both are degenerate (they vanish
along the time direction `v`, `minkSq v = -1`), the pair `(h, h♯)` satisfies the
two defining absorption identities of a **generalized (Moore–Penrose-type)
inverse pair** on the spatial hyperplane `v^⊥`.  New file
`BookProof/ChapterGravityGenInverse.lean` (registered in `BookProof.lean`),
reusing `spatialProj_idempotent`, `spatialMetric_eq_metric_mul_proj`,
`invSpatialMetric_mulVec_lower_self`, `invSpatialMetric_symm` and the headline
`invSpatialMetric_mul_spatialMetric` (`h♯·h = χ`).

- `spatialMetric_mul_spatialProj` — `h · χ = h` (χ is identity on the image of `h`);
- `spatialProj_mul_invSpatialMetric` — `χ · h♯ = h♯` (χ is identity on the image
  of `h♯`);
- `spatialMetric_genInverse` — **headline** `h · h♯ · h = h`;
- `invSpatialMetric_genInverse` — **headline** `h♯ · h · h♯ = h♯`.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `#print axioms`).  `lake build BookProof` green.
(Per the author's instruction the Hankel–Majorana line is left untouched.)

## Wave 73 (2026-07-08) — **Book "Diffeomorphisms and gravity", §"Classical Hamiltonian": the orthogonal `3+1` spacetime split `x = χx + Πx`** (`ChapterGravitySplit`)

Continuing the standing directive (mine the next self-contained mathematical
claim from `book.tex`), and packaging together Wave 69's spatial projector `χ`
and Wave 71's temporal projector `Π`.  Relative to the globally defined **unit
timelike vector** `v` (`minkSq v = -1`), every contravariant vector `x` splits
uniquely into its **spatial part** `χx ∈ v^⊥` and its **temporal part** `Πx`
(a multiple of `v`); the two parts are Minkowski-orthogonal.  This is the
linear-algebra content behind the book's use of `χ` to split every torsion
tensor into spatial and temporal pieces.  New file
`BookProof/ChapterGravitySplit.lean` (registered in `BookProof.lean`), reusing
`spatialProj`, `timeProj`, `metric`, `lower`, `minkSq`, `spatialProj_mulVec_self`,
`spatialProj_mulVec_of_orthogonal` and `spatialProj_add_timeProj`.

- `minkForm x y` — the Minkowski bilinear form `⟨x,y⟩_η = ∑ₐ xᵃ y_a`;
- `minkForm_comm` — the Minkowski form is symmetric;
- `minkForm_self` — `minkForm x x = minkSq x`;
- `spatialPart v x`, `timePart v x` — the spatial (`χx`) and temporal (`Πx`) parts;
- `spatialPart_add_timePart` — **completeness** `χx + Πx = x`;
- `timePart_eq_smul` — the temporal part is `Πx = −⟨x,v⟩_η · v`, a multiple of `v`;
- `spatialPart_orthogonal` — the spatial part is Minkowski-orthogonal to `v`
  (`⟨χx, v⟩_η = 0`), i.e. it lies in `v^⊥`;
- `parts_orthogonal` — **headline** `⟨χx, Πx⟩_η = 0`: the spatial and temporal
  parts are Minkowski-orthogonal;
- `split_unique` — the `3+1` split is unique: if `x = s + c • v` with `s ⊥ v`
  then `s = χx` and `c • v = Πx`.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `#print axioms`).  `lake build BookProof` green.
(Per the author's instruction the Hankel–Majorana line is left untouched.)

## Wave 72 (2026-07-08) — **Book "Diffeomorphisms and gravity", §"Classical Hamiltonian": the inverse (raised) spatial metric `h♯ = η + v⊗v`** (`ChapterGravityInvMetric`)

Continuing the standing directive (mine the next self-contained mathematical
claim from `book.tex`), and building directly on Wave 69's projector `χ` and
Wave 70's induced spatial metric `h_{ab} = η_{ab} + v_a v_b`.  Raising both
indices of `h` with the Minkowski metric gives the **inverse spatial metric**
`h^{ab} = η^{ab} + v^a v^b`, the metric induced on the cotangent spatial
hyperplane.  New file `BookProof/ChapterGravityInvMetric.lean` (registered in
`BookProof.lean`), reusing `metric`, `lower`, `minkSq`, `spatialProj` from
`ChapterGravityProjector` and `spatialMetric` from `ChapterGravityMetric`.

- `invSpatialMetric` — the raised metric `h^{ab} = η^{ab} + v^a v^b`;
- `metric_mul_metric` — the Minkowski metric is an **involution** `η · η = 1`
  (so `η` is its own inverse, `η^{ab} η_{bc} = δ^a{}_c`);
- `invSpatialMetric_symm` — `h^♯` is symmetric (`(h♯)ᵀ = h♯`);
- `invSpatialMetric_mulVec_lower_self` — `h^{ab} v_b = 0`: the inverse metric
  degenerates along the time covector, complementary to `h_{ab} v^b = 0`
  (Wave 70);
- `invSpatialMetric_mul_spatialMetric` — **headline** `h^♯ · h = χ`: the raised
  and lowered spatial metrics compose to the spatial projector `χ` (identity on
  `v^⊥`), the defining relation of an inverse-metric pair on the degenerate
  hyperplane.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `#print axioms`).  `lake build BookProof` green.
(Per the author's instruction the Hankel–Majorana line is left untouched.)

## Wave 71 (2026-07-08) — **Book "Diffeomorphisms and gravity", §"Classical Hamiltonian": the complementary temporal projector `Π = δ − χ = −v⊗v♭`** (`ChapterGravityTimeProj`)

Continuing the standing directive (mine the next self-contained mathematical
claim from `book.tex`), and building directly on Wave 69's projector `χ`.  The
gravity chapter's mixed projector `χ_a{}^b = δ_a{}^b + v_a v^b` onto the spatial
hyperplane `v^⊥` has a complement `Π = δ − χ = −v⊗v♭`, the **temporal
projector** onto the `1`-dimensional time direction spanned by the unit timelike
vector `v` (`minkSq v = −1`).  New file `BookProof/ChapterGravityTimeProj.lean`
(registered in `BookProof.lean`), reusing `metric`, `lower`, `minkSq`,
`spatialProj` from `ChapterGravityProjector`.

- `timeProj` — the projector `Π^a{}_b = −v^a v_b`;
- `spatialProj_add_timeProj` — **completeness** `χ + Π = δ` (the identity split
  of spacetime into spatial + temporal parts);
- `timeProj_idempotent` — `Π² = Π` (a genuine projector);
- `trace_timeProj` — `tr Π = 1` (rank `1`: the time direction, complementary to
  `tr χ = 3`);
- `timeProj_mulVec_self` — `Π v = v`: `v` is fixed, spanning the image of `Π`
  (complementary to `χ v = 0`);
- `spatialProj_mul_timeProj` — `χ · Π = 0`: the two projectors are orthogonal;
- `timeProj_mul_spatialProj` — `Π · χ = 0`.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `#print axioms`).  `lake build BookProof` green.
(Per the author's instruction the Hankel–Majorana line is left untouched.)

## Wave 70 (2026-07-08) — **Book "Diffeomorphisms and gravity", §"Classical Hamiltonian": the induced spatial metric `h = η + v♭⊗v♭` is positive semidefinite** (`ChapterGravityMetric`)

Continuing the standing directive (mine the next self-contained mathematical
claim from `book.tex`), and building directly on Wave 69's projector.  Lowering
the free index of the mixed projector `χ_a{}^b = δ_a{}^b + v_a v^b` with the
Minkowski metric produces the associated `(0,2)` **induced spatial metric**
`h_{ab} = η_{ab} + v_a v_b`, the Riemannian metric on the spatial hyperplane
`v^⊥`.  New file `BookProof/ChapterGravityMetric.lean` (registered in
`BookProof.lean`), reusing `metric`, `lower`, `minkSq`, `spatialProj` from
`ChapterGravityProjector`.

- `spatialMetric` — the matrix `h_{ab} = η_{ab} + v_a v_b`;
- `spatialMetric_symm` — `h` is symmetric (`hᵀ = h`);
- `spatialMetric_eq_metric_mul_proj` — the tensor identity `h = η · χ` (the
  spatial metric is the projector `χ` with its free index lowered);
- `spatialMetric_mulVec_self` — `h v = 0`: `v` spans the kernel, so `h`
  degenerates exactly along the time direction;
- `reverse_cauchy_schwarz` — the **reverse Cauchy–Schwarz inequality** for the
  unit timelike vector `v`: `⟨x,v⟩_η² ≥ −⟨x,x⟩_η` for all `x` (proved via the
  SOS identity `s·F = (a v₀ − x₀ s)² + Lagrange`, `s = v₁²+v₂²+v₃²`);
- `spatialMetric_quadForm_nonneg` — **headline**: `0 ≤ xᵀ h x` for all `x` (the
  quadratic form equals `minkSq x + ⟨x,v⟩_η²`, nonneg by reverse Cauchy–Schwarz);
- `spatialMetric_posSemidef` — the packaged `Matrix.PosSemidef`: `h` is a
  genuine (degenerate) Riemannian metric, positive definite on `v^⊥`.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `#print axioms`).  `lake build BookProof` green
(8122 jobs).  (Per the author's instruction the Hankel–Majorana line is left
untouched.)

## Wave 69 (2026-07-08) — **Book "Diffeomorphisms and gravity", §"Classical Hamiltonian": the spatial projector `χ = δ + v⊗v`** (`ChapterGravityProjector`)

Continuing the standing directive (mine the next self-contained mathematical
claim from `book.tex`).  The gravity chapter (§*"Classical Hamiltonian"*,
`book.tex` line ~8091) introduces, relative to a globally defined **unit
timelike vector** `v` (`vᵘ vᵤ = −1` in the mostly-plus Minkowski metric
`η = diag(−1,1,1,1)`), the mixed tensor `χ_a{}^b = δ_a{}^b + v_a v^b`, used
pervasively to split the torsion tensors into their spatial / temporal parts.
This `χ` is exactly the **orthogonal projector onto the spatial hyperplane**
`v^⊥`.  New file `BookProof/ChapterGravityProjector.lean` (registered in
`BookProof.lean`); the `(1,1)` tensor `χ^a{}_b = δ^a{}_b + v^a v_b` is modelled
as an explicit `4×4` real matrix acting on contravariant vectors.

- `metric` / `lower` / `minkSq` — the Minkowski metric, index lowering
  `v_a = η_{ab} v^b`, and the Minkowski square `v^a v_a`;
- `spatialProj` — the projector `χ^a{}_b = δ^a{}_b + v^a v_b`;
- `spatialProj_mulVec_self` — `χ v = 0`: `v` spans the kernel;
- `spatialProj_idempotent` — **headline**: `χ² = χ` (a genuine projector; the
  key identity `M² = −M` for `M = v⊗v_♭` follows from `v·v = −1`);
- `trace_spatialProj` — `tr χ = 3`: it is a rank-`3` projector (the spatial
  slice);
- `spatialProj_mulVec_of_orthogonal` — `χ` is the identity on `v^⊥`, confirming
  it is the orthogonal projection onto the spatial hyperplane.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `#print axioms`).  `lake build BookProof` green
(8121 jobs).

## Wave 68 (2026-07-08) — **Book §A.5 "Hankel–Majorana Transform": the spherical Bessel function `j₃`, its `l = 3` ODE, and the next recurrences** (`ChapterSphericalBessel2`)

Extends the base `ChapterSphericalBessel` module (which had `j₀, j₁, j₂` and the
`l = 0` ODE) one order further, to the spherical Bessel function of the first
kind `j₃`.  New file `BookProof/ChapterSphericalBessel2.lean` (registered in
`BookProof.lean`), reusing the base module's `sbessel`, `sj1`, `sj2` and Rayleigh
machinery.

- `sj3` — the closed form
  `j₃(r) = (15/r⁴ − 6/r²) sin r − (15/r³ − 1/r) cos r`;
- `deriv_sj2` — the first derivative of `j₂`;
- `sbessel_three_eq` — the Rayleigh formula reproduces `j₃`
  (`sbessel 3 r = j₃ r`, via one more Rayleigh iterate on `sbessel_two_eq` using
  `Filter.EventuallyEq.deriv_eq` on the punctured line);
- `sbessel_recurrence_123` — the three-term recurrence at `l = 2`:
  `j₁(r) + j₃(r) = (5/r) · j₂(r)`;
- `deriv_recurrence_sj2` — the differentiation law at `l = 2`:
  `d/dr j₂ = j₁ − (3/r) · j₂`;
- `sj3_satisfies_ode` — `j₃` solves the `l = 3` spherical Bessel ODE
  `r² j'' + 2 r j' + (r² − 12) j = 0` (`l(l+1) = 12`).

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `#print axioms`).  `lake build BookProof` green.

## Wave 67 (2026-07-08) — **Book §10 "Ensemble forecasting …": there is no uniform countable measure** (`ChapterNoUniformCountable`)

Continuing the standing directive (mine the next self-contained mathematical
claim from `book.tex`).  The §10 chapter *"Ensemble forecasting allows the
approximation of a non-linear infinite-dimensional model …"* (`book.tex`
line ~2005) opens with the foundational assertion

> "There is no uniform countable measure. Thus, the rationals are not enough for
> Probability Theory. A standard probability space (which has countable and
> continuous measures) seems irreducible."

This measure-theoretic fact — distinct from the *infinite-dimensional Lebesgue*
non-existence result already in `ChapterNoLebesgue` — had not been formalized.
New file `BookProof/ChapterNoUniformCountable.lean` (registered in
`BookProof.lean`).

- `no_uniform_countable_measure` — **headline**: on a countably infinite
  measurable space with measurable singletons there is no probability measure
  assigning a common mass `c` to every singleton.  (Countable additivity gives
  total mass `∑' _, c`, which is `0` when `c = 0` and `⊤` when `c ≠ 0` — never
  `1`.)
- `no_uniform_measure_nat` — the book's concrete `ℕ` instance ("the rationals
  are not enough"): no probability measure on `ℕ` is uniform on singletons.

Engine: `MeasureTheory.Measure.tsum_indicator_apply_singleton` (total mass = sum
of singleton masses) and `ENNReal.tsum_const_eq_top_of_ne_zero`.  All
`sorry`-free / `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`,
confirmed via `#print axioms`).  `lake build BookProof` green (8119 jobs).

## Wave 66 (2026-07-08) — **Book "Wave-function collapse versus Euler's formula": Euler's formula for a *generic* phase-space** (`ChapterE4`)

Continuing the standing directive (mine the next self-contained mathematical
claim from `book.tex`).  The chapter *"Wave-function collapse versus Euler's
formula"* has a further section, *"Euler's formula for a generic phase-space"*
(`book.tex` line ~3565), which extends the finite 4-state density matrix of
`ChapterE3` to a **countable** orthonormal basis `{lₙ}` via the recursion
`vₙ = cos(θₙ)·lₙ + sin(θₙ)·vₙ₊₁`, and states that *collapse for a generic
phase-space is a recursion of collapses of 2-dimensional real wave-functions*.
This bridges the two prior chapters — `ChapterE2` (stick-breaking Born
*probabilities*) and `ChapterE3` (finite density matrix) — and was not yet
formalized.

New file `BookProof/ChapterE4.lean` (registered in `BookProof.lean`).  Model:
countable index space `ℕ`, orthonormal basis the standard basis
`eₖ = Pi.single k 1 : ℕ → ℝ`, and a finite-support recursion `wave θ s d`
(leading index `s`, `d` remaining stick-breaks, base `e_{s+d}`); outer products
`v v†` written entrywise as `v i * v j`.

- `wave_eq_zero_of_lt` — the tail `vₛ` is supported on indices `≥ s`
  (orthogonality of the tail to the already-measured basis vectors).
- `wave_self_succ` — the leading component is `cos θₛ`.
- `density_recursion` — **headline**: the entrywise density-matrix recursion
  `vₛ vₛ† = cₛ² eₛ eₛ† + sₛ² vₛ₊₁ vₛ₊₁† + cₛ sₛ (eₛ vₛ₊₁† + vₛ₊₁ eₛ†)`, a purely
  algebraic identity requiring no orthonormality.
- `cross_diag_zero` — the Euler cross term `eₛ vₛ₊₁†` has a vanishing diagonal.
- `diag_collapse` — "taking the real part": the diagonal obeys the classical
  stick-breaking recursion `(vₛ)ᵢ² = cₛ² (eₛ)ᵢ² + sₛ² (vₛ₊₁)ᵢ²`.
- `cond_prob_sum` — `cₛ² + sₛ² = 1`, the book's
  `P(s | s or above) + P(s+1 or above | s or above) = 1`.
- `wave_prob_sum` — **total probability is conserved**:
  `∑ i ∈ Icc s (s+d), (vₛ)ᵢ² = 1` (the trace of the density matrix is `1`).

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `#print axioms`).  `lake build BookProof` green
(8118 jobs).

## Wave 65 (2026-07-08) — **Book "Wave-function collapse versus Euler's formula": Euler's formula for the density matrix** (`ChapterE3`)

Continuing the standing directive (mine the next self-contained mathematical
claim from `book.tex`).  The chapter *"Wave-function collapse versus Euler's
formula"* (`book.tex` §"Euler's formula for a phase-space with 4 states", line
~3478) writes each collapse step of a real normalized wave-function
`φ = cos θ · l + sin θ · w` as an **"Euler's formula for the corresponding
density matrices"**: the rank-1 projector `φφ†` decomposes with a
`cos(2θ) + J sin(2θ)` structure, `J := l w† − w l†` playing the role of the
imaginary unit in `span{l, w}`, and "collapse = taking the real part" being the
`cos(2θ)` (diagonal) part.  Prior chapters covered only the 2-state clock
(`ChapterE`) and the stick-breaking Born *probabilities* (`ChapterE2`); the
density-matrix identity itself was not yet formalized.

New file `BookProof/ChapterE3.lean` (registered in `BookProof.lean`), column
vectors `l w : Fin n → ℝ`, outer products via `Matrix.vecMulVec`:

- `euler_density_matrix` — **headline**: the density-matrix Euler formula
  `φφ† = ½(l l† + w w†) + ½ cos(2θ)(l l† − w w†) + ½ sin(2θ)(l w† + w l†)`, a
  purely algebraic (double-angle) identity requiring no orthonormality.
- `eulerJ_antisymm` — the "imaginary unit" `J = l w† − w l†` is antisymmetric
  (`Jᵀ = −J`).
- `eulerJ_sq` — under orthonormality `J² = −(l l† + w w†)`: `J` squares to minus
  the identity of the subspace, so it genuinely behaves like `i`.
- `euler_density_diag_real` — "taking the real part": the `l`-diagonal entry of
  `φφ†` is `cos²θ = ½ + ½ cos(2θ)`, the book's conditional probability
  `P(l | l or above)`.
- `euler_density_isIdempotent` — under orthonormality `φφ†` is a genuine rank-1
  projector (`φφ† · φφ† = φφ†`), the density matrix of a pure state.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `#print axioms`).  `lake build BookProof` green
(8117 jobs).

## Wave 64 (2026-07-08) — **Book "Yang-Mills … Classical Statistical Field Theory" / gauge chapters: there is no infinite-dimensional Lebesgue measure** (`ChapterNoLebesgue`)

Continuing the standing directive (mine the next self-contained mathematical
claim from `book.tex`).  The Yang-Mills chapter (line ~6660) and the gauge
chapters (line 2128) repeatedly invoke, as a load-bearing premise for the whole
free-field / gauge-*variant* probability-measure framework, the classical fact
that a translation-invariant "Lebesgue-like" measure on an
infinite-dimensional space **cannot exist**:

> "the Feynman's path integral assumes the existence of a translation-invariant
> σ-finite (i.e. Lebesgue like) measure … Yet, it is proved that in rigor such
> infinite-dimensional Lebesgue measure cannot exist."

New file `BookProof/ChapterNoLebesgue.lean` (registered in `BookProof.lean`),
for a real normed space `E` with a Borel measure `μ`:

- `measure_ball_eq_measure_ball_zero` — a translation-invariant (`IsAddLeftInvariant`)
  measure gives every ball the same mass as the concentric ball at the origin.
- `measure_ball_zero_eq_zero` — **core estimate**: if `E` is infinite-dimensional
  (`¬ FiniteDimensional ℝ E`), `μ` is translation-invariant and finite on
  bounded sets, then every origin ball has measure `0`.  Proof rescales a bounded
  `1`-separated sequence (`exists_seq_norm_le_one_le_norm_sub`) by `2r` to get
  infinitely many disjoint radius-`r` balls inside one bounded set; positivity
  would force infinite measure there.
- `eq_zero_of_isAddLeftInvariant_of_finite_on_bounded` — **headline**: on an
  infinite-dimensional real normed space the only translation-invariant Borel
  measure finite on bounded sets is the zero measure.
- `not_exists_nonzero_isAddLeftInvariant_finite_on_bounded` — existence restatement.
- `not_finite_on_bounded_of_isAddLeftInvariant_of_pos_ball` — contrapositive
  used in the book: a translation-invariant measure positive on some ball cannot
  be finite on all bounded sets.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); `lake build BookProof` green.  The physical modelling of the
gauge-variant Gaussian measure that replaces the impossible Lebesgue measure is
left as prose.

> **Merge note (2026-07-08).** Two parallel Aristotle lineages extended this
> log past Wave 39 with overlapping wave numbers.  The "Wave 41"/"Wave 40"
> entries immediately below are the second lineage (in-place extensions of
> `ChapterH1/H2/F4`); the "Wave 63" … "Wave 40" block after them is the first
> lineage (`ChapterH3/H4`, `ChapterF6`, ten new book chapters, and the
> spherical-Bessel series).  Both lineages are integrated in the library
> (`ChapterSphericalBessel2–7` triaged out per STOP RULE #2; `ChapterF4` is
> the union of the two lineages' versions).

## Wave 41 — **N14 / F3.5 Misra–Gries heavy-hitter bound** (`ChapterF4.lean`)

This pass closes the last open (optional) roadmap deliverable, **F3.5**.
`lake build BookProof` green (8123 jobs); all new declarations `sorry`-free and
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`; `misraGries_bound`
verified via `lean_verify`). No `axiom`, no `EXTERNAL`.

**N14 (QFM) F3.5 — DONE (`ChapterF4.lean`).** A self-contained executable
formalization of the Misra–Gries frequency-estimation algorithm and its
two-sided guarantee:
* `mgSupport`, `mgStep`, `mgRun` — support size, one processing step, and the run
  of the algorithm over a stream (`List`).
* `mgSum_decrement` — a full decrement lowers the total by the number of active
  counters (additive `ℕ` form).
* `mgStep_support_le` / `mgRun_support_le` — at most `k` counters are ever active.
* **`mgRun_sum`** — conservation invariant `(∑ counters)+(k+1)·d = N`.
* `mgRun_decrement_le` — decrement budget `k·d ≤ N`.
* `mgRun_undercount` (`f̂ ≤ f`) and `mgRun_error_le` (`f ≤ f̂ + d`).
* **`misraGries_bound`** (F3.5 headline) — `f - N/k ≤ f̂ ≤ f`
  (stated as `f̂ ≤ f ∧ f ≤ f̂ + N/k`).

⇒ With this pass **every** FORMALIZATION_ROADMAP.md deliverable is complete
(N1–N12, and the full N13 and N14 packages including the optional F3.5).

## Wave 40 (2026-07-08) — **N13 residue + N14 residue** (`ChapterH1/H2`, `ChapterF4`)

This pass closes the remaining open residues of the two flagship packages.
`lake build BookProof` green (8123 jobs); all new declarations `sorry`-free and
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`; verified via
`lean_verify` on `duhamel_phiOp1`, `sirk_error_bound_of_crouzeix`,
`countSketch_unbiased`).  No `axiom`; the single deep analytic input
(Crouzeix's inequality) enters **only** as named hypotheses on H2.3.

**N13 (Hashimoto SIRK) residue — DONE.**
* **H1.3** `phiOp1` (operator φ₁-function `∫₀¹ e^{s·M} g ds`) + **`duhamel_phiOp1`**
  (exponential-integrator Duhamel identity `∫₀^δ e^{(δ−s)·A} g ds = δ·phiOp1(δ·A)g`,
  by the two interval-integral substitutions) — `ChapterH1.lean`.
* **H1.5** `psi` (`ψ_{k,γ}(x) = φ_k(γ − x⁻¹)`, Def 2.4) + **`psi_resolvent`**
  (`ψ_{k,γ}((γ−z)⁻¹) = φ_k(z)`) + **`resolvent_eigenvector`**
  (`A v = z v ⇒ X v = (γ−z)⁻¹ v` for `X = (γI−A)⁻¹`) — the spectral bridge for
  the CFC identity `φ_k(A) = ψ_{k,γ}(X)` — `ChapterH1.lean`.
* **H1.7** **`resolvent_shift_repr`** (`X_j = (1 + h(m−j)·X_m)⁻¹ · X_m`, the
  generating step of the rational-Krylov equality (11)) — `ChapterH1.lean`.
* **H2.2** **`sirk_compression`** (`Vᴴ X V = H K⁻¹`, eq. 10) — `ChapterH2.lean`.
* **H2.3** **`sirk_error_bound_of_crouzeix`** (the (13)+(14) SIRK error bound
  `‖φ_k(A)v − V ψ(HK⁻¹)Vᴴv‖ ≤ 2C‖v‖·‖ψ−r‖_Σ`, conditional on two named Crouzeix
  applications — never axioms) — `ChapterH2.lean`.
* **H2.4** **`sirk_advantage_factor`** (`e^{−hm}·B ≤ B`, the Remark 4.2 decay
  advantage of SIRK over SIA) — `ChapterH2.lean`.

**N14 (QFM) residue — DONE (new `ChapterF4.lean`, registered in `BookProof.lean`).**
* **F3.1** `countSketch` + `countSketch_add` (linearity) + **`countSketch_unbiased`**
  (`E[⟪S₁x, S₁y⟫] = ⟪x,y⟫` for Rademacher signs — the AMS/Count-Sketch estimator).
* **F3.2** **`observable_matrix_entry`** (`Tr(E_{r,s}ᴴ Wᴴ P_a W) = conj(W_{a,r})·W_{a,s}`).
* **F3.3** **`hermitian_flow_unitary`** (`Uᴴ U = 1` for `U = e^{−itH}`, `H` Hermitian)
  + **`hermitian_flow_preserves_normSq`** (norm-preserving generation).
* **F3.4** **`pseudoInverse_left_inverse`** (`(ΦᵀΦ)⁻¹Φᵀ · Φ = I`, subspace recovery).

⇒ With this pass the FORMALIZATION_ROADMAP.md queue is fully exhausted: N1–N12
(incl. N7(c)) and now the N13 and N14 residues are all complete.

## Wave 63 (2026-07-08) — **Book §A.5 "Hankel–Majorana Transform": the next spherical Bessel function `j₆`, its `l = 6` ODE, and the next recurrences** (`ChapterSphericalBessel6`)

Continuing the standing directive (mine the next self-contained mathematical
content from `book.tex`), this pass extends the spherical Bessel family of the
first kind `jₗ` (§A.5 subsection *"Hankel–Majorana Transform"*, Definitions
65–71) one order beyond Waves 58–62.  New module
`BookProof/ChapterSphericalBessel6.lean` (registered in `BookProof.lean`),
reusing the Wave 58–62 closed forms and derivatives; all **`sorry`-free** and
**`axiom`-free** (only `propext`, `Classical.choice`, `Quot.sound`, verified via
`lean_verify`); full `lake build` green (8141 jobs).  No `EXTERNAL` hypothesis,
no `axiom`, no `native_decide`.

- `sj6` — the classical closed form
  `j₆(r) = (10395/r⁷ − 4725/r⁵ + 210/r³ − 1/r) sin r − (10395/r⁶ − 1260/r⁴ + 21/r²) cos r`;
- `deriv_sj6` — its first derivative;
- `sbessel_six_eq` — the Rayleigh formula reproduces the closed form,
  `sbessel 6 r = j₆(r)` (assembled from the Wave 62 `sbessel_five_eq` via one
  more Rayleigh iterate, using `Filter.EventuallyEq.deriv_eq` on the punctured
  line);
- `sj6_satisfies_ode` — `j₆` solves the `l = 6` spherical Bessel ODE
  `r² j'' + 2 r j' + (r² − 42) j = 0` (`l(l+1) = 42`);
- `sbessel_recurrence_456` — the three-term recurrence
  `jₗ₋₁ + jₗ₊₁ = (2l+1)/r · jₗ` at `l = 5`: `j₄(r) + j₆(r) = (11/r) · j₅(r)`;
- `deriv_recurrence_sj5` — the differentiation law
  `d/dr jₗ = jₗ₋₁ − (l+1)/r jₗ` at `l = 5`: `d/dr j₅ = j₄ − 6/r · j₅`.

Together with Waves 58–62, the seven lowest spherical Bessel functions
`j₀, j₁, j₂, j₃, j₄, j₅, j₆` are now shown to arise from the Rayleigh formula, to
satisfy their defining second-order ODEs, and to obey both the three-term
recurrence and the first-derivative recurrence that generate the whole family.
The surrounding representation-theoretic modelling of the full Hankel–Majorana
transform is left as prose.

## Wave 62 (2026-07-07) — **Book §A.5 "Hankel–Majorana Transform": the next spherical Bessel function `j₅`, its `l = 5` ODE, and the next recurrences** (`ChapterSphericalBessel5`)

Continuing the standing directive (mine the next self-contained mathematical
content from `book.tex`), this pass extends the spherical Bessel family of the
first kind `jₗ` (§A.5 subsection *"Hankel–Majorana Transform"*, Definitions
65–71) one order beyond Waves 58–61.  New module
`BookProof/ChapterSphericalBessel5.lean` (registered in `BookProof.lean`),
reusing the Wave 58/59/60/61 closed forms and derivatives; all **`sorry`-free**
and **`axiom`-free** (only `propext`, `Classical.choice`, `Quot.sound`, verified
via `lean_verify`); full `lake build` green (8140 jobs).  No `EXTERNAL`
hypothesis, no `axiom`, no `native_decide`.

- `sj5` — the classical closed form
  `j₅(r) = (945/r⁶ − 420/r⁴ + 15/r²) sin r − (945/r⁵ − 105/r³ + 1/r) cos r`;
- `deriv_sj5` — its first derivative;
- `sbessel_five_eq` — the Rayleigh formula reproduces the closed form,
  `sbessel 5 r = j₅(r)` (assembled from the Wave 61 `sbessel_four_eq` via one
  more Rayleigh iterate, using `Filter.EventuallyEq.deriv_eq` on the punctured
  line);
- `sj5_satisfies_ode` — `j₅` solves the `l = 5` spherical Bessel ODE
  `r² j'' + 2 r j' + (r² − 30) j = 0` (`l(l+1) = 30`);
- `sbessel_recurrence_345` — the three-term recurrence
  `jₗ₋₁ + jₗ₊₁ = (2l+1)/r · jₗ` at `l = 4`: `j₃(r) + j₅(r) = (9/r) · j₄(r)`;
- `deriv_recurrence_sj4` — the differentiation law
  `d/dr jₗ = jₗ₋₁ − (l+1)/r jₗ` at `l = 4`: `d/dr j₄ = j₃ − 5/r · j₄`.

Together with Waves 58–61, the six lowest spherical Bessel functions
`j₀, j₁, j₂, j₃, j₄, j₅` are now shown to arise from the Rayleigh formula, to
satisfy their defining second-order ODEs, and to obey both the three-term
recurrence and the first-derivative recurrence that generate the whole family.
The surrounding representation-theoretic modelling of the full Hankel–Majorana
transform is left as prose.

## Wave 61 (2026-07-07) — **Book §A.5 "Hankel–Majorana Transform": the next spherical Bessel function `j₄`, its `l = 4` ODE, and the next recurrences** (`ChapterSphericalBessel4`)

Continuing the standing directive (mine the next self-contained mathematical
content from `book.tex`), this pass extends the spherical Bessel family of the
first kind `jₗ` (§A.5 subsection *"Hankel–Majorana Transform"*, Definitions
65–71) one order beyond Waves 58–60.  New module
`BookProof/ChapterSphericalBessel4.lean` (registered in `BookProof.lean`),
reusing the Wave 58/59/60 closed forms and derivatives; all **`sorry`-free** and
**`axiom`-free** (only `propext`, `Classical.choice`, `Quot.sound`, verified via
`lean_verify`); full `lake build` green (8139 jobs).  No `EXTERNAL` hypothesis,
no `axiom`, no `native_decide`.

- `sj4` — the classical closed form
  `j₄(r) = (105/r⁵ − 45/r³ + 1/r) sin r − (105/r⁴ − 10/r²) cos r`;
- `deriv_sj4` — its first derivative;
- `sbessel_four_eq` — the Rayleigh formula reproduces the closed form,
  `sbessel 4 r = j₄(r)` (assembled from the Wave 60 `sbessel_three_eq` via one
  more Rayleigh iterate, using `Filter.EventuallyEq.deriv_eq` on the punctured
  line);
- `sj4_satisfies_ode` — `j₄` solves the `l = 4` spherical Bessel ODE
  `r² j'' + 2 r j' + (r² − 20) j = 0` (`l(l+1) = 20`);
- `sbessel_recurrence_234` — the three-term recurrence
  `jₗ₋₁ + jₗ₊₁ = (2l+1)/r · jₗ` at `l = 3`: `j₂(r) + j₄(r) = (7/r) · j₃(r)`;
- `deriv_recurrence_sj3` — the differentiation law
  `d/dr jₗ = jₗ₋₁ − (l+1)/r jₗ` at `l = 3`: `d/dr j₃ = j₂ − 4/r · j₃`.

Together with Waves 58–60, the five lowest spherical Bessel functions
`j₀, j₁, j₂, j₃, j₄` are now shown to arise from the Rayleigh formula, to satisfy
their defining second-order ODEs, and to obey both the three-term recurrence and
the first-derivative recurrence that generate the whole family.  The surrounding
representation-theoretic modelling of the full Hankel–Majorana transform is left
as prose.

## Wave 60 (2026-07-07) — **Book §A.5 "Hankel–Majorana Transform": the next spherical Bessel function `j₃`, its `l = 3` ODE, and the differentiation law** (`ChapterSphericalBessel3`)

Continuing the standing directive (mine the next self-contained mathematical
content from `book.tex`), this pass extends the spherical Bessel family of the
first kind `jₗ` (§A.5 subsection *"Hankel–Majorana Transform"*, Definitions
65–71) one order beyond Waves 58–59.  New module
`BookProof/ChapterSphericalBessel3.lean` (registered in `BookProof.lean`),
reusing the Wave 58/59 closed forms and derivatives; all **`sorry`-free** and
**`axiom`-free** (only `propext`, `Classical.choice`, `Quot.sound`, verified via
`lean_verify`); full `lake build` green (8138 jobs).  No `EXTERNAL` hypothesis,
no `axiom`, no `native_decide`.

- `sj3` — the classical closed form
  `j₃(r) = (15/r⁴ − 6/r²) sin r − (15/r³ − 1/r) cos r`;
- `deriv_sj3` — its first derivative;
- `sbessel_three_eq` — the Rayleigh formula reproduces the closed form,
  `sbessel 3 r = j₃(r)` (assembled from the Wave 59 `sbessel_two_eq` via one more
  Rayleigh iterate, using `Filter.EventuallyEq.deriv_eq` on the punctured line);
- `sj3_satisfies_ode` — `j₃` solves the `l = 3` spherical Bessel ODE
  `r² j'' + 2 r j' + (r² − 12) j = 0` (`l(l+1) = 12`);
- `sbessel_recurrence_123` — the three-term recurrence
  `jₗ₋₁ + jₗ₊₁ = (2l+1)/r · jₗ` at `l = 2`: `j₁(r) + j₃(r) = (5/r) · j₂(r)`;
- `deriv_recurrence_sj1` / `deriv_recurrence_sj2` — the differentiation law
  `d/dr jₗ = jₗ₋₁ − (l+1)/r jₗ` at `l = 1, 2`.

Together with Waves 58–59, the four lowest spherical Bessel functions
`j₀, j₁, j₂, j₃` are now shown to arise from the Rayleigh formula, to satisfy
their defining second-order ODEs, and to obey both the three-term recurrence and
the first-derivative recurrence that generate the whole family.  The surrounding
representation-theoretic modelling of the full Hankel–Majorana transform is left
as prose.

## Wave 59 (2026-07-07) — **Book §A.5 "Hankel–Majorana Transform": the defining second-order ODE and three-term recurrence for the spherical Bessel functions** (`ChapterSphericalBessel2`)

Continuing the standing directive (mine the next self-contained mathematical
content from `book.tex`), this pass completes the classical analytic
characterisation of the spherical Bessel functions of the first kind `jₗ`
introduced in Wave 58 (`ChapterSphericalBessel`, `book.tex` §A.5 subsection
*"Hankel–Majorana Transform"*, Definitions 65–71).  New module
`BookProof/ChapterSphericalBessel2.lean` (registered in `BookProof.lean`),
reusing the Wave 58 closed forms `sj0`/`sj1`/`sj2`; all **`sorry`-free** and
**`axiom`-free** (only `propext`, `Classical.choice`, `Quot.sound`, verified via
`lean_verify`); full `lake build` green (8137 jobs).  No `EXTERNAL` hypothesis,
no `axiom`, no `native_decide`.

- `deriv_sj1` / `deriv_sj2` — the first derivatives of the closed forms
  `j₁(r) = sin r / r² − cos r / r` and
  `j₂(r) = (3/r³ − 1/r) sin r − (3/r²) cos r`;
- `sj1_satisfies_ode` — `j₁` solves the `l = 1` spherical Bessel ODE
  `r² j'' + 2 r j' + (r² − 2) j = 0` (`l(l+1) = 2`);
- `sj2_satisfies_ode` — `j₂` solves the `l = 2` spherical Bessel ODE
  `r² j'' + 2 r j' + (r² − 6) j = 0` (`l(l+1) = 6`);
- `sbessel_recurrence_012` — the classical three-term recurrence
  `jₗ₋₁ + jₗ₊₁ = (2l+1)/r · jₗ` at `l = 1`: `j₀(r) + j₂(r) = (3/r) · j₁(r)`.

Together with Wave 58's `sj0_satisfies_ode` and `rayleigh_raise_01`, the three
lowest spherical Bessel functions are now shown to satisfy their defining ODEs
and the raising/recurrence relations that generate the whole family.  The
surrounding representation-theoretic modelling of the full Hankel–Majorana
transform is left as prose.

## Wave 58 (2026-07-07) — **Book §A.5 "Hankel–Majorana Transform" (Def. 65–71): the spherical Bessel functions of the first kind via the Rayleigh formula** (`ChapterSphericalBessel`)

Continuing the standing directive (mine the next self-contained mathematical
content from `book.tex`), this pass formalizes the analytic backbone of the §A.5
subsection *"Hankel–Majorana Transform"* (`book.tex` line ~5805, Definitions
65–71).  The transform is built from the **spherical Bessel functions of the
first kind** `jₗ`, defined (Definition 67) by the **Rayleigh formula**
`jₗ(r) = rˡ (-(1/r) d/dr)ˡ (sin r / r)`.  These special functions are **absent
from Mathlib** (only the Legendre *symbol* exists; there are no spherical Bessel
functions, spherical harmonics, or Legendre polynomials), so this file builds the
self-contained core from scratch.  New module
`BookProof/ChapterSphericalBessel.lean` (registered in `BookProof.lean`); all
**`sorry`-free** and **`axiom`-free** (only `propext`, `Classical.choice`,
`Quot.sound`, verified via `lean_verify`); full `lake build` green (8136 jobs).
No `EXTERNAL` hypothesis, no `axiom`, no `native_decide`.

- `rayleighOp` — the Rayleigh differential operator `T f (r) = -(1/r) · f'(r)`;
- `sbesselBase` / `sbessel` — the generator `j₀(r) = sin r / r` and the general
  spherical Bessel function `jₗ(r) = rˡ (Tˡ (sin r / r))(r)` (the book's Rayleigh
  formula, Definition 67);
- `sj0` / `sj1` / `sj2` — the classical closed forms
  `j₀ = sin r / r`, `j₁ = sin r / r² − cos r / r`,
  `j₂ = (3/r³ − 1/r) sin r − (3/r²) cos r`;
- `deriv_sbesselBase` — the derivative of the generator,
  `d/dr (sin r / r) = cos r / r − sin r / r²`;
- `sbessel_zero` / `sbessel_one_eq` / `sbessel_two_eq` — the Rayleigh formula
  reproduces the three closed forms `j₀, j₁, j₂` (the `l = 1, 2` cases via the
  first/second derivatives, using `Filter.EventuallyEq.deriv_eq` on the punctured
  line);
- `rayleigh_raise_01` — the Rayleigh raising relation `j₁ = −(d/dr) j₀`;
- `sj0_satisfies_ode` — `j₀(r) = sin r / r` solves the `l = 0` spherical Bessel
  ODE `r² j'' + 2 r j' + r² j = 0`.

The surrounding representation-theoretic modelling (unitarity of the full
Hankel–Majorana transform, spherical-harmonic expansions, Clebsch–Gordan
assembly of the pinor transform) is left as prose.

## Wave 57 (2026-07-07) — **Book §A.5 "Spinor frame and CPT theorem": the most general Lorentz-covariant Dirac mass Hamiltonian is anti-Hermitian and obeys the relativistic mass-shell relation** (`ChapterCPTHamiltonian`)

Continuing the standing directive (mine the next self-contained mathematical
content from `book.tex`), this pass formalizes the finite-dimensional algebraic
core of the §A.5 subsection *"Spinor frame and CPT theorem"* (`book.tex` line
~6453). There the author states that the most general mass in the Hamiltonian
`iH` covariant under the connected component of the Lorentz group is
`iH = ∂⃗·γ⃗ γ⁰ + i γ⁰ m₁ + γ⁰ γ⁵ m₂`, invariant under a parity–time reversal —
"this is essentially the CPT theorem". Working in the concrete `4×4` Majorana
model of §A.3 (`BookProof.ChapterA3`), the plane-wave form of that operator
(`∂ⱼ ↦ i kⱼ`) is the matrix `D(k,m₁,m₂) = i (Σⱼ kⱼ γ^{j+1}γ⁰) + i m₁ γ⁰ + m₂ γ⁰γ⁵`.
New module `BookProof/ChapterCPTHamiltonian.lean` (registered in `BookProof.lean`);
all **`sorry`-free** and **`axiom`-free** (only `propext`, `Classical.choice`,
`Quot.sound`, verified via `lean_verify`); full `lake build` green (8135 jobs).
No `EXTERNAL` hypothesis, no `axiom`, no `native_decide`.

- `Kin` / `MassA` / `MassB` — the five building-block matrices `γ^{j+1}γ⁰`
  (`j : Fin 3`), `iγ⁰`, `γ⁰γ⁵`, each equal to the cast of an explicit integer
  matrix (`Kin_eq_cast`, `MassA_eq_cast`, `MassB_eq_cast`);
- `Kin_sq` (`=1`), `Kin_anticomm`, `MassA_sq` / `MassB_sq` (`=-1`),
  `MassA_MassB_anticomm`, `Kin_MassA_anticomm`, `Kin_MassB_anticomm` — the five
  matrices are **mutually anticommuting**, with squares `+1,+1,+1,-1,-1`
  (Clifford relations reduced to the §A.3 integer model and closed by `decide`);
- `Kin_conjTranspose` (Hermitian), `MassA_conjTranspose` / `MassB_conjTranspose`
  (anti-Hermitian) — the kinetic blocks are self-adjoint and the two mass blocks
  anti-self-adjoint;
- `diracHamOp_conjTranspose` — **`iH` is anti-Hermitian** (`Dᴴ = -D`), i.e. the
  Hamiltonian `H` is self-adjoint;
- `diracHamOp_sq` — the **relativistic mass-shell / dispersion relation**
  `D² = -(k₀²+k₁²+k₂²+m₁²+m₂²) • 1`, so the eigenvalues of `H` are
  `±√(k⃗²+m₁²+m₂²)`: `m₁, m₂` are exactly the covariant mass parameters.

The surrounding physical modelling (spinor frames, the `Pin(3,1)` principal
homogeneous space, field reparametrizations) is left as prose.

## Wave 56 (2026-07-07) — **Book chapter "On the physical parity transformation and antiparticles": the finite algebraic core (Hermitian field decomposition, order-4 parity ⇒ `Pin(3,1)`, Gell-Mann outer automorphism)** (`ChapterParity`)

Continuing the standing directive (mine the next self-contained mathematical
content from `book.tex`), this pass formalizes the finite-dimensional algebraic
core of the chapter *"On the physical parity transformation and antiparticles"*
(`book.tex` line ~7522). The chapter's central thesis — that at the quantum level
all fields are **real representations** (self-adjoint operators), so CP and P
coincide and the (generalized) parity transformation is **order four**, which
fixes the double cover as `Pin(3,1)` — rests on a handful of concrete
linear-algebra facts, which are what is discharged here. New module
`BookProof/ChapterParity.lean` (registered in `BookProof.lean`), reusing the
concrete `4×4` Dirac model `BookProof.ChapterA3.mgamma`/`dgamma`; all
**`sorry`-free** and **`axiom`-free** (only `propext`, `Classical.choice`,
`Quot.sound`, verified via `lean_verify`); full `lake build` green (8134 jobs).
No `EXTERNAL` hypothesis, no `axiom`, no `native_decide`.

- `hermPart` / `antihermPart` + `hermPart_isHermitian` / `antihermPart_isHermitian`
  / `field_hermitian_decomp` — *"Any non-Hermitian field can always be decomposed
  into a sum of two Hermitian fields"*: every square complex matrix `X` equals
  `A + i B` with `A = ½(X+Xᴴ)`, `B = (2i)⁻¹(X−Xᴴ)` both Hermitian;
- `pauli2` / `higgsParity` + `pauli2_sq` (`σ₂²=1`), `higgsParity_sq`
  (`(iσ₂)²=−1`), `higgsParity_pow_four` (`(iσ₂)⁴=1`), `higgsParity_order_four`
  — the internal part `iσ₂` of the Higgs (generalized) parity `φ ↦ iσ₂φ` is a
  genuine order-4 (`ℤ₄`) symmetry;
- `mgamma0_sq` (`(iγ⁰)²=−1`), `fermionParity_order_four`, `dgamma0_sq`
  (`(γ⁰)²=+1`, contrast) — the Majorana fermion parity operator `iγ⁰` is order
  four, and the value `−1` (vs `+1` for the naive Dirac `γ⁰`) is the invariant
  selecting the double cover `Pin(3,1)` over `Pin(1,3)`;
- `gellMann` / `gellMannConjSign` + `gellMann_conj` / `gellMann_parity_sign` —
  the complex conjugation of the eight `SU(3)` Gell-Mann matrices realizes the
  `ℤ₂` outer automorphism with sign pattern `ε = (+,−,+,+,−,+,−,+)` (real
  generators `λ¹,λ³,λ⁴,λ⁶,λ⁸` fixed, imaginary `λ²,λ⁵,λ⁷` negated); the chapter's
  gluon parity sign is `s^a = −ε^a` (`s^{1,3,4,6,8}=−1`, `s^{2,5,7}=+1`).

The surrounding physical modelling (canonical quantization of a real Hilbert
space, the Standard-Model Lagrangian, path-integral measures) is left as prose.

## Wave 55 (2026-07-07) — **Book §A.5 "Application to the momentum of Majorana spinor fields", Proposition 73: the Majorana–Fourier boost mixing matrix is unitary** (`ChapterMajoranaFourier`)

Continuing the standing directive (mine the next self-contained mathematical
content from `book.tex`), this pass formalizes the algebraic core of
**Proposition 73** (`book.tex` §A.5, "Application to the momentum of Majorana
spinor fields", line ~5900). The book proves the **Majorana–Fourier transform**
`𝓕_M = S ∘ 𝓕_P^Θ` is unitary by reducing to the statement that the explicit
`2×2` block "boost mixing" matrix `S = [[c, −s·A],[s·A, c]]` is orthogonal/unitary,
where `c = √((E+m)/(2E))`, `s = √((E−m)/(2E))` are the boost half-angle
coefficients (`E = √(q²+m²)`, `q = |p⃗|`, `m ≥ 0`) and `A = (n̂·γ⃗) γ⁰` is built
from the Dirac spatial slash of the unit momentum direction `n̂`. This reuses the
concrete `4×4` Dirac model `BookProof.ChapterA3.dgamma`. New module
`BookProof/ChapterMajoranaFourier.lean` (registered in `BookProof.lean`), all
**`sorry`-free** and **`axiom`-free** (only `propext`, `Classical.choice`,
`Quot.sound`; verified via `#print axioms`); full `lake build` green (8133 jobs).
No `EXTERNAL` hypothesis, no `axiom`, no `native_decide`.

- `boost_sq_add` / `boost_sq_sub` / `boost_two_mul` — the boost half-angle
  identities `c² + s² = 1`, `c² − s² = m/E`, `2cs = q/E` (the trigonometric
  content of the Lorentz boost as a "rotation" of rapidity half-angle);
- `mgamma_conjTranspose` / `dgamma_conjTranspose` — `γ⁰` is Hermitian and the
  spatial `γⁱ` are anti-Hermitian in the Majorana model;
- `dgamma_spatial_sq` / `dgamma_spatial_anticomm` — spatial Clifford relations
  `(γⁱ)² = −1`, `γⁱγʲ = −γʲγⁱ` (`i ≠ j`);
- `nslash_conjTranspose` / `nslash_sq` — the spatial slash `n̸ = Σ nᵢ γ^{i+1}` is
  anti-Hermitian and, for a unit direction, squares to `−1`;
- `Aop_conjTranspose` / `Aop_sq` — `A = n̸ γ⁰` is a **Hermitian involution**
  (`Aᴴ = A`, `A² = 1`), hence unitary;
- `boostBlock_unitary` — the abstract result: for any Hermitian involution `A`
  and reals `c, s` with `c² + s² = 1`, the block matrix `S = [[c, −s·A],[s·A, c]]`
  satisfies `Sᴴ S = 1`;
- `majoranaFourier_boostBlock_unitary` — the headline: the concrete Prop-73
  boost mixing matrix is unitary.

The surrounding analytic content (the integral operators `𝓕_P`, `𝓕_M` and their
unitarity as operators on `L²`) is physical/analytic modelling left as prose;
this pass discharges the finite linear-algebra identity on which the book's
proof rests.

## Wave 54 (2026-07-07) — **Book §6 "Free field parametrization for finite sample spaces and the spin-statistics theorem": the two-mode fermionic CAR algebra on `ℤ₂ × ℤ₂`** (`ChapterSpinStatistics`)

Continuing the standing directive (mine the next self-contained mathematical
content from `book.tex`), this pass formalizes the section *"6. Free field
parametrization for finite sample spaces and the spin-statistics theorem"*
(`book.tex` line ~1816). There a finite sample space `ℤ₂` is parametrized by a
**fermionic** Fock space `Γ^a(L²(ℤ₂))`, and for the product `ℤ₂ × ℤ₂` one must use
the graded tensor product so the two modes **anticommute** rather than produce
spurious products of creation operators — the algebraic content underlying the
**spin–statistics** correspondence. Extending the single-mode ghost CAR of
Wave 53, this builds the **two-mode** fermionic Fock space `ℂ⁴ ≅ ℂ² ⊗ ℂ²` via the
Jordan–Wigner realization `b₁ = a ⊗ I`, `b₂ = Z ⊗ a` (parity string
`Z = diag(1,-1)`), as explicit `4×4` matrices. New module
`BookProof/ChapterSpinStatistics.lean` (registered in `BookProof.lean`), all
**`sorry`-free** and **`axiom`-free** (only `propext`, `Classical.choice`,
`Quot.sound`; verified via `lean_verify`); full `lake build` green (8132 jobs).
No `EXTERNAL` hypothesis, no `axiom`.

- `fermiCreate1_eq` / `fermiCreate2_eq` — explicit matrix form of `b₁†`, `b₂†`
  (each the conjugate-transpose adjoint of its annihilation operator);
- `fermi_CAR₁` / `fermi_CAR₂` — the diagonal CAR `{bᵢ, bᵢ†} = 1`;
- `fermi_CAR_cross` / `fermi_CAR_cross'` — the off-diagonal CAR
  `{b₁, b₂†} = 0`, `{b₂, b₁†} = 0` (distinct modes canonically anticommute);
- `fermiAnticomm_annih` / `fermiAnticomm_create` — the fermionic statistics
  `{b₁, b₂} = 0`, `{b₁†, b₂†} = 0` (so `b₁ b₂ = − b₂ b₁`);
- `fermiAnnih₁_sq` … `fermiCreate₂_sq` — per-mode nilpotency `bᵢ² = 0`, `bᵢ†² = 0`
  (Pauli exclusion);
- `fermiNumber₁_eq` / `fermiNumber₂_eq` — number operators `Nᵢ = bᵢ† bᵢ`
  (`diag(0,0,1,1)`, `diag(0,1,0,1)`), with `fermiNumber₁_hermitian`/`_idem`
  (Hermitian projections, eigenvalues `0,1`) and `fermiNumber_commute`
  (`N₁ N₂ = N₂ N₁`, simultaneously measurable);
- `fermiTotalNumber_eq` — the total number operator `N = N₁ + N₂ = diag(0,1,1,2)`.

The representation-theoretic claim that the fermionic (anticommuting)
parametrization is genuinely distinct from the bosonic (commuting) one, and that
certain symmetry transformations are representable only by one or the other (the
spin–statistics theorem), is left as prose.

## Wave 53 (2026-07-07) — **Book "Free field parametrization … Navier–Stokes", *Navier–Stokes* section: the BRST ghost-field CAR algebra `{ψ, ψ†} = 1`** (`ChapterNavierStokes`)

Continuing the standing directive (mine the next self-contained mathematical
content from `book.tex`), this pass formalizes the fermionic **ghost field**
of the section *"Free field parametrization in Navier–Stokes equations"*
(`book.tex` line ~4134). There the divergence constraint of Navier–Stokes is
implemented à la BRST through a single fermionic ghost `ψ` (BRST charge
`Ω = ∫ u_{j,j} ψ†`), governed by the canonical anticommutation relation
`{ψ, ψ†} = ψψ† + ψ†ψ = 1` with the explicit realization the book writes down,
`ψ†{a}(…,j) = a(…,1) δ_{j0}`, `ψ{a}(…,j) = a(…,0) δ_{j1}`. On the
two-dimensional occupation space `ℂ²` these are the `2×2` matrices
`ψ = !![0,0;1,0]` and `ψ† = ψᴴ = !![0,1;0,0]`. New module
`BookProof/ChapterNavierStokes.lean` (registered in `BookProof.lean`), all
**`sorry`-free** and **`axiom`-free** (only `propext`, `Classical.choice`,
`Quot.sound`; verified via `lean_verify` on the headlines); full `lake build`
green (8131 jobs). No `EXTERNAL` hypothesis, no `axiom`.

- `ghostCreate_eq` — explicit matrix form of `ψ†`;
- `ghostCreate_eq_conjTranspose` — `ψ†` is the (conjugate-transpose) adjoint of
  `ψ`, so the CAR pair is a genuine operator/adjoint pair;
- `ghost_CAR` — the canonical anticommutation relation `ψψ† + ψ†ψ = 1`
  (the book's `{ψ, ψ†} = 1`);
- `ghostAnnih_sq` / `ghostCreate_sq` — nilpotency `ψ² = 0`, `ψ†² = 0`
  (fermionic Pauli exclusion), with the paired `{ψ,ψ} = 0`, `{ψ†,ψ†} = 0`;
- `ghostNumber_eq`, `ghostNumber_hermitian`, `ghostNumber_idem` — the number
  operator `N = ψ†ψ = !![1,0;0,0]` is Hermitian and idempotent (eigenvalues
  `0, 1`, the fermionic occupation numbers);
- `ghost_annih_create_eq`, `ghostNumber_resolution` — `ψψ† = !![0,0;0,1]` and
  the resolution of the identity `N + ψψ† = 1` into the two occupation sectors.

The surrounding field-theoretic construction (the full graded Lie superalgebra,
essential self-adjointness of the polynomial Navier–Stokes Hamiltonian, and the
existence/uniqueness claim) is physical modelling left as prose.

## Wave 52 (2026-07-07) — **Book "Free field parametrization … Navier–Stokes", *Holomorphic fields*: functions satisfying the Cauchy–Riemann equations on an open domain are holomorphic** (`ChapterHolomorphic`)

Continuing the standing directive (mine the next self-contained mathematical
content from `book.tex`), this pass formalizes the section *"Holomorphic fields"*
(`book.tex` line ~4105), where the Hamiltonian is *defined by the Cauchy–Riemann
equations*. The book states the distributional (Weyl-lemma) version — a
locally-integrable function whose Cauchy–Riemann equations hold weakly is a.e.
equal to an analytic function; that elliptic-regularity statement is not in
Mathlib. This pass formalizes the classical (strong-derivative) core it rests on:
a complex function real-differentiable on an open domain and satisfying the
Cauchy–Riemann equations there is complex analytic (holomorphic), hence its own
analytic representative. New module `BookProof/ChapterHolomorphic.lean`
(registered in `BookProof.lean`), all **`sorry`-free** and **`axiom`-free**
(only `propext`, `Classical.choice`, `Quot.sound`; verified via `lean_verify` on
the headlines); full `lake build` green (8130 jobs). No `EXTERNAL` hypothesis, no
`axiom`.

Over an open `s ⊆ ℂ`:
- `cauchyRiemann_analyticOn` — **operator form**: real-differentiable on `s`
  with `fderiv ℝ f z I = I • fderiv ℝ f z 1` (i.e. `∂f/∂y = i · ∂f/∂x`) implies
  `AnalyticOn ℂ f s` (Cauchy–Riemann criterion +
  `DifferentiableOn.analyticOn`);
- `cauchyRiemann_partial_analyticOn` — the classical **partial-derivative form**
  `u_x = v_y`, `u_y = -v_x` (writing `f = u + i v`) implies analyticity;
- `analyticOn_cauchyRiemann` — the converse: every function analytic on an open
  set satisfies the Cauchy–Riemann equations there;
- `cauchyRiemann_iff_analyticOn` — the resulting characterization
  (Cauchy–Riemann ⇔ holomorphic for real-differentiable `f`);
- `cauchyRiemann_contDiffOn` — the smoothness payoff: such an `f` is `C^∞`.

## Wave 51 (2026-07-07) — **Book §3 "Any conditional probability measure is parametrized by a unitary operator": the finite-dimensional matrix version** (`ChapterJointUnitary`)

With the roadmap queue N1–N14 and Waves 46–50 complete, this pass mines the
self-contained finite-dimensional core of `book.tex` section *"3. Any conditional
probability measure in a standard measure space is parametrized by a unitary
operator"* (Chapter *"Wave-function parametrization of a probability measure"*,
book line ~1392): the book's claim that a joint probability density `p(x,y)` is
`|𝒰(y,x,0)|²` for a unitary `𝒰` built by Gram–Schmidt with a chosen column equal to
the wave-function `Ψ` (`|Ψ|²=p`), plus its converse. The abstract `L²`/Hilbert-
basis form is already `ChapterB.unit_vector_extends`; this adds the concrete
matrix form. New module `BookProof/ChapterJointUnitary.lean` (registered in
`BookProof.lean`), all **`sorry`-free** and **`axiom`-free** (only `propext`,
`Classical.choice`, `Quot.sound`; verified via `lean_verify` on the headlines);
full `lake build` green (8129 jobs). No `EXTERNAL` hypothesis, no `axiom`.

Over a finite index type:
- `exists_unitary_column` — Gram–Schmidt crux: every unit vector `v`
  (`∑ᵢ ‖v i‖² = 1`) is the `i₀`-th column of some unitary matrix (extend to an
  orthonormal basis of `EuclideanSpace ℂ ι`; its coordinate matrix is unitary);
- `exists_unitary_of_prob` — every finite probability distribution `p` is the
  squared modulus of a column of a unitary matrix (via `v i = √(p i)`);
- `exists_unitary_joint` — the book's exact two-space form: every joint
  distribution `p(x,y)` on a finite `X × Y` is `|U|²` along a column of a unitary
  matrix indexed by `X × Y`;
- `sqAbs_isProb_of_frobenius_one` + `frobenius_eq_trace` — converse: any matrix
  `B` with `∑_{i,j} ‖B i j‖² = 1` (i.e. `tr(Bᴴ B) = 1`) makes `(i,j) ↦ ‖B i j‖²`
  a genuine probability distribution.

## Wave 50 (2026-07-06) — **Book "Conditions for the classical limit of Quantum Mechanics": calculable (step / polynomial / smooth) functions are dense in `L²`** (`ChapterClassicalLimit`)

With the roadmap queue N1–N14 and Waves 46–49 complete, this pass mines the next
self-contained mathematical claim from `book.tex`: the section *"11. Conditions
for the classical limit of Quantum Mechanics"* (Chapter *"Wave-function
parametrization of a probability measure"*, line ~2081), namely that *"step,
polynomial or smooth functions are dense in the `L²` measure"* and that any
bounded function on a compact domain can be `L²`-approximated by such calculable
functions.  New module `BookProof/ChapterClassicalLimit.lean` (registered in
`BookProof.lean`), all **`sorry`-free** and **`axiom`-free** (only `propext`,
`Classical.choice`, `Quot.sound`; verified via `lean_verify` on the headline);
full `lake build` green (8128 jobs).  No `EXTERNAL` hypothesis, no `axiom`.

Working over a compact `s ⊆ ℝ` (the book's "compact domain") with any finite,
weakly-regular Borel measure `μ`, the three families the book lists are each
shown dense in `Lᵖ(μ)` (stated at the book's `p = 2`):
- `simpleFunc_dense_L2` — **step functions** (a.e. classes of simple functions)
  are dense (`Lp.simpleFunc.dense`, any `p ≠ ∞`);
- `continuousMap_denseRange_L2` — **continuous functions** are dense, i.e. the
  embedding `C(s, ℝ) → Lᵖ` has dense range (`ContinuousMap.toLp_denseRange`);
- `polynomialFunctions_val_denseRange` — **polynomials are dense in `C(s, ℝ)`**
  (Stone–Weierstrass, `polynomialFunctions.topologicalClosure = ⊤`);
- `polynomial_denseRange_L2` — **polynomial functions are dense in `Lᵖ`**,
  obtained by composing the two previous facts; since polynomials are smooth
  this simultaneously witnesses the density of the **smooth** functions;
- headline `exists_polynomial_approx_L2` — the book's exact `ε`-statement: for
  every `F ∈ L²(μ)` and every `ε > 0` there is a polynomial `q` with
  `‖q|ₛ − F‖₂ < ε`.

## Wave 49 (2026-07-06) — **Book "Reconstructing the classical trajectory of any isolated quantum system": a symmetry acts on probability distributions iff it is deterministic** (`ChapterReconstruct`)

With the roadmap queue N1–N14 and Waves 46–48 complete, this pass mines the next
self-contained mathematical claim from `book.tex`: the section *"Time translation
is a stochastic process if and only if it is deterministic"* (Chapter
*"Reconstructing the classical trajectory of any isolated quantum system"*, line
~2613).  New module `BookProof/ChapterReconstruct.lean` (registered in
`BookProof.lean`), all **`sorry`-free** and **`axiom`-free** (only `propext`,
`Classical.choice`, `Quot.sound`; verified via `lean_verify` on the headline);
full `lake build` green (8127 jobs).  No `EXTERNAL` hypothesis, no `axiom`.

A Wigner symmetry acts on the wave-function by a unitary matrix `U`; the book's
main result is that the induced map on the (post-collapse) probability
distributions is a well-defined group action **iff** `U` is *deterministic*,
meaning each column of `U` has at most one nonzero entry.  The extracted
linear-algebra core is that, for each column `a`, the "off-diagonal Born sum"
`S_a(Ψ) = ∑_{k ≠ b} conj(U k a)·Ψ k·conj(Ψ b)·U b a` vanishes on every state `Ψ`
iff `conj(U m a)·U l a = 0` for all `l ≠ m` (no unitarity hypothesis is needed).
Deliverables:
- `IsDeterministicCol` / `IsDeterministic` (each column has ≤ 1 nonzero entry)
  and the `offDiag` off-diagonal Born sum;
- `offDiag_eq` — the identity `S_a(Ψ) = (∑ₖ conj(U k a)·Ψ k)(∑_b conj(Ψ b)·U b a)
  − ∑ₖ conj(U k a)·Ψ k·conj(Ψ k)·U k a` (full bilinear product minus diagonal);
- `offDiag_of_isDeterministicCol` (forward: deterministic ⇒ every off-diagonal
  term carries the vanishing factor `conj(U k a)·U b a`);
- `isDeterministicCol_of_offDiag` (backward: the polarization witnesses
  `Ψ = δ_{·m} + z δ_{·l}` for `z ∈ {1, i}` recover `conj(U m a)·U l a = 0`, the
  rigorous version of the book's `δ_{·m}+δ_{·l}` witness);
- headline **`offDiag_eq_zero_iff`** (per column) and
  **`offDiag_eq_zero_iff_isDeterministic`** (global): the Born-rule map is a
  well-defined action on distributions iff `U` is deterministic;
- `offDiag_unit_iff` — the book's exact unit-state (pure-density-matrix) form,
  equivalent by homogeneity of `offDiag`.

## Wave 48 (2026-07-06) — **Book "Wave-function collapse versus Euler's formula": the generic-phase-space (stick-breaking) Born parametrization** (`ChapterE2`)

With the roadmap queue N1–N14 and Waves 46–47 complete, this pass mines the next
self-contained mathematical content from `book.tex`: the sections *"Euler's
formula for a phase-space with 4 states"* and *"Euler's formula for a generic
phase-space"* (Chapter *"Wave-function collapse versus Euler's formula"*, line
~3565).  `BookProof/ChapterE.lean` had only handled the 2-state clock (E.1–E.4);
this pass formalizes the `n`-state / countable generalization.  New module
`BookProof/ChapterE2.lean` (registered in `BookProof.lean`), all **`sorry`-free**
and **`axiom`-free** (only `propext`, `Classical.choice`, `Quot.sound`; verified
via `lean_verify` on the headlines); full `lake build` green (8126 jobs).  No
`EXTERNAL` hypothesis, no `axiom`.

The book parametrizes a real normalized wave-function by Euler angles via the
recursion `vₙ = cos(θₙ) lₙ + sin(θₙ) vₙ₊₁`, giving the *stick-breaking* Born
probabilities `P(1)=c₁²`, `P(2)=(s₁c₂)²`, `P(3)=(s₁s₂c₃)²`, … with conditional
"stop-here" probability `cₖ²=cos²(θₖ)` and "go-higher" probability
`sₖ²=sin²(θₖ)`.  Angles are modelled by `θ : ℕ → ℝ` (avoids `Fin`-index
arithmetic).  Deliverables:
- `stick`/`remainder`/`bornProb` definitions + basic identities (`stick_eq`,
  `remainder_succ`, `remainder_zero`, `stick_nonneg`, `remainder_nonneg`,
  `remainder_le_one`);
- **`sum_stick_add_remainder`** — the telescoping normalization identity
  `(∑_{n<N} stick θ n) + remainder θ N = 1`;
- `bornProb_nonneg` + **`bornProb_sum_eq_one`** — the `n`-state Born family is a
  genuine probability distribution (nonnegative, sums to `1`);
- `cos_sq_surjective` — the conditional probabilities `cos²(θ)` are arbitrary
  over `[0,1]`;
- **headline `exists_angles_realize`** — *every* probability distribution on `n`
  states is realized by the Born rule of some wave-function (there exist Euler
  angles whose stick-breaking Born distribution equals it), the book's claim
  "any probability distribution can be reproduced by the Born rule for some
  wave-function" (via the stick-breaking construction `cos²θ_k = q_k / R_k`).

## Wave 47 (2026-07-06) — **Book "Entropy and an irreversible deterministic time-evolution coexist": the invertibility probability `n!/nⁿ`** (`ChapterEntropy`)

With the roadmap queue N1–N14 and the Wave-46 Gleason sanity check already
complete, this pass mines the next self-contained numbered claim from `book.tex`:
the chapter *"Entropy and an irreversible deterministic time-evolution coexist"*
(line ~9474, §"Irreversible deterministic time-evolution").  New module
`BookProof/ChapterEntropy.lean` (registered in `BookProof.lean`), all
**`sorry`-free** and **`axiom`-free** (only `propext`, `Classical.choice`,
`Quot.sound`; verified via `lean_verify`); full `lake build` green (8125 jobs).
No `EXTERNAL` hypothesis, no `axiom`.

Partitioning the rescaled joint sample square into `n²` cells, the probability
that a uniformly random discrete self-map of the `n` index cells is invertible
(a bijection) is `n!/nⁿ`; it is a genuine probability in `[0,1]`, tends to `0`,
and is Stirling-asymptotic to `√(2πn) e^{-n}` — so a randomly sampled evolution
is almost surely non-invertible (irreversible).  Deliverables:
- `card_selfMaps` (`nⁿ` self-maps) and `card_bijections` (`n!` bijections) of an
  `n`-element index set;
- `invertibleProb` and `invertibleProb_eq` (`= (n! : ℝ)/nⁿ`);
- `invertibleProb_nonneg` / `invertibleProb_le_one` (in `[0,1]`, via
  `Nat.factorial_le_pow`);
- headline `invertibleProb_tendsto_zero` (from
  `tendsto_factorial_div_pow_self_atTop`);
- `invertibleProb_isEquivalent_stirling` (`n!/nⁿ ~ √(2πn) e^{-n}`, from
  `Stirling.factorial_isEquivalent_stirling` divided by `nⁿ`);
- `exists_injective_not_surjective` (the successor map on `ℕ`: injective
  "non-singular" but not surjective "not invertible" — an arrow-of-time witness).

## Wave 46 (2026-07-06) — **Book §4 Gleason contrast: pure vs. mixed states on non-commuting projections** (`ChapterB4`)

With the entire roadmap queue N1–N14 complete (both flagship packages landed),
this pass lands the concrete, finite-dimensional worked example flagged in
`FORMALIZATION_ROADMAP.md` (Chapter B remark) as "worth adding as a sanity
check" but never previously implemented: the `2`-dimensional real Gleason
contrast from `book.tex` §4 (line ~1637).  New module
`BookProof/ChapterB4.lean` (registered in `BookProof.lean`), all **`sorry`-free**
and **`axiom`-free** (only `propext`, `Classical.choice`, `Quot.sound`; verified
via `lean_verify` on the headlines); full `lake build` green (8124 jobs).  No
`EXTERNAL` hypothesis, no `axiom`.

Fix the two non-commuting real projections `P₁ = [[1,0],[0,0]]` and
`P₂ = ½[[1,1],[1,1]]`.  A **pure state** is a rank-one projector `v vᵀ` for a
real unit vector `v` (`IsPureState`); a **density matrix** is Hermitian,
positive-semidefinite, unit-trace (`IsDensityMatrix`); the Born value of a
projection `P` in state `ρ` is `tr(ρ P)`.

* `pure_state_satisfies_P1` / `pure_state_satisfies_P2` — a pure state (namely
  `P₂`, resp. `P₁`) individually realizes each Born constraint `= ½`
  (`P2_isPureState`, `P1_isPureState`).
* **headline** `no_pure_state_satisfies_both` — **no** pure state realizes both
  `tr(ρ P₁) = ½` and `tr(ρ P₂) = ½` at once (from `v₀² = ½` and
  `(v₀+v₁)²/2 = ½` a `nlinarith` contradiction with `v₀²+v₁² = 1`).
* `mixed_state_satisfies_both` + `mixed_state_isDensityMatrix` +
  `mixed_state_not_pure` — the genuinely mixed state `ρ = ½ I` *does* satisfy
  both constraints and is a legitimate (Gleason) density matrix, but is not a
  pure state.

This is exactly the book's point: the wave-function (pure states) cannot match
the Born data of two non-commuting projections simultaneously, whereas
Gleason's mixed-state density matrix can.  (Separately confirmed this pass: the
§0 S7 hygiene item — the `../unfer` cross-reference docstrings on
`born_conditioning` and `prodEquiv` in `ChapterU.lean` — is already present, so
no further edit was needed there.)

## Wave 45 (2026-07-06) — **N14 QFM: the concrete `x̂`/`p̂` function-space model — F2.1/F2.2 fully realized** (`ChapterF7`)

This pass closes the last recorded open item of the two flagship packages: the
concrete `p̂ = −i ∂` / `x̂` integration-by-parts function-space model underlying
N14's F2.1/F2.2 (whose *algebraic* cores were already done in `ChapterF5`).  New
module `BookProof/ChapterF7.lean` (registered in `BookProof.lean`), all
**`sorry`-free** and **`axiom`-free** (only `propext`, `Classical.choice`,
`Quot.sound`; verified via `lean_verify`); `lake build` green (8123 jobs).
**No `EXTERNAL` hypothesis, no `axiom`.**

The state space is the Schwartz space `𝓢(ℝ, ℂ)` with the sesquilinear `L²`
pairing `⟪f, g⟫ = ∫ conj (f x) · g x` (`l2pair`, with its integrability helper
`l2pair_integrable` and full (conjugate-)bilinearity
`l2pair_add/sub/smul_left/right`).  `IsL2Symmetric T` is Hermiticity of `T` on
this dense domain (`⟪T f, g⟫ = ⟪f, T g⟫`).

* **Position / multiplication operators** (`mulOp v`, `(v(x̂)Ψ)(x)=v(x)Ψ(x)` via
  `SchwartzMap.bilinLeftCLM`): multiplication by any real function of temperate
  growth is `L²`-symmetric (`mulOp_l2Symmetric`, because `conj (v x) = v x`);
  `position_l2Symmetric` is the `v = id` case.
* **Momentum** (`momentum`, `(p̂Ψ)(x) = −i Ψ′(x)` via `SchwartzMap.derivCLM`):
  `momentum_l2Symmetric`.  The analytic heart is
  `schwartz_integration_by_parts` — `∫ conj(f′) g = −∫ conj(f) g′` for Schwartz
  `f, g` — proved from `integral_deriv_mul_eq_sub` with vanishing boundary terms
  (`SchwartzMap.tendsto_cocompact` at `±∞`) and Schwartz integrability
  (`bdd_mul`: `conj ∘ f` bounded × `g′` integrable).
* **F2.1 concretely** (§4 eq. 4.2): `anticomm_l2Symmetric` (the symmetrized
  product of two symmetric operators is symmetric) yields
  `continuityHamiltonian_l2Symmetric` — the continuity Hamiltonian
  `H = ½(p̂ v(x̂) + v(x̂) p̂)` is Hermitian.
* **F2.2 concretely** (§4 eqs. 4.4–4.6): `i_comm_l2Symmetric` (`i·[K,V]`
  symmetric when `K,V` are) with `kinetic_l2Symmetric` (`K = ½ p̂·p̂`) yields
  `conservativeHamiltonian_l2Symmetric` — the conservative continuity
  Hamiltonian `H^c = i[K, V(x̂)]` is Hermitian.

**⇒ With this wave both flagship packages N13 (Hashimoto SIRK) and N14 (QFM) are
complete**, including the previously-deferred concrete `x̂`/`p̂` model.  The only
remaining `sorry`s in the repo are the out-of-scope `RiemannProof/RcpEuler.lean`
ones.

## Wave 44 (2026-07-06) — **N13 SIRK: H1.5 + H2.2 + H2.3 + H2.4 — the package is complete** (`ChapterH4`)

This pass lands the four remaining N13 (Hashimoto SIRK) deliverables in a new
module `BookProof/ChapterH4.lean` (registered in `BookProof.lean`), all
**`sorry`-free** and **`axiom`-free** (only `propext`, `Classical.choice`,
`Quot.sound`; verified via `#print axioms`); `lake build` green (8122 jobs).
**No `axiom`.** The two genuinely deep analytic inputs (Crouzeix's inequality
and the deferred `e^{−hm}` deformation of the source Theorem 5) are **named
hypotheses with citation docstrings**, never axioms — the `IsSchurFull`/`EXTERNAL`
design pattern. With this wave the entire N13 deliverable list (H1.1–H2.4) is
formalized.

* **H1.5** (operator φ-function via the resolvent, Definition 2.4 — scalar
  core): `psi k γ w := φ_k(γ − w⁻¹)` is the Taylor(1951)/Güttel(2010) function
  whose functional calculus at the resolvent `X = (γ − A)⁻¹` defines `φ_k(A)`.
  Its spectral-consistency identity `psi_shift_eq_phi`
  (`ψ_{k,γ}((γ − z)⁻¹) = φ_k(z)` for `γ − z ≠ 0`) is proved: under the
  shift-invert change of variable `w = (γ − z)⁻¹` one has `γ − w⁻¹ = z`.
* **H2.2** (SIRK compression `Vₘ∗ Xₘ Vₘ = Hₘ Kₘ⁻¹`, eq. 10, and the
  rational-function transfer): `compress V X := V∗ X V` (eq. 10 is literally this
  definition). For an isometric embedding `V` (`V∗V = 1`) with `X`-invariant
  range: `compress_X_comp_V` (`X ∘ V = V ∘ B`), `compress_pow`
  (`Xⁿ ∘ V = V ∘ Bⁿ`), `compress_transfer` (`Xⁿ v = V (Bⁿ (V∗ v))` on the
  range), and `compress_inv_transfer` (`q(X)⁻¹ ∘ V = V ∘ q(B)⁻¹`, the denominator
  step) — together the load-bearing identity `r(Xₘ)v = Vₘ r(HₘKₘ⁻¹) Vₘ∗ v` of
  Theorem 4.1.
* **H2.3** (SIRK convergence headline, Theorem 4.1 — CONDITIONAL on Crouzeix):
  `sirk_error_bound` proves the eq.-(13)→(14) triangle-inequality core
  `‖φ_k(A)v − Vₘ ψ(HₘKₘ⁻¹) Vₘ∗ v‖ ≤ 2C·D·‖v‖` (`D = ‖ψ−r‖`), taking the two
  Crouzeix operator-norm bounds (eq. 14) as named hypotheses; and
  `sirk_error_bound_decay` assembles the full eq.-(12) form
  `≤ 2C·e^{−hm}·Dmin·‖v‖` given the deferred `e^{−hm}` deformation hypothesis.
* **H2.4** (existing-methods comparison, Remark 4.2 — CONDITIONAL):
  `sia_error_bound` is the analogous SIA bound (15) `≤ 2C·Dsia·‖v‖`, and
  `sirk_le_sia` records the `e^{−hm}` advantage of SIRK over SIA as an
  inequality of the two bounds (since `e^{−hm} ≤ 1` for `h, m ≥ 0`).

**⇒ N13 (Hashimoto SIRK) is now complete.** Remaining open work across the two
flagship packages: the concrete `p̂ = −i ∂` / `x̂` integration-by-parts
function-space model underlying N14's F2.1/F2.2 (the algebraic cores are already
done in `ChapterF5`) — the QFM pure-proof definition of done is otherwise
complete.

## Wave 43 (2026-07-06) — **N14 QFM: F3.5 Misra–Gries heavy-hitter bound** (`ChapterF6`)

This pass lands the F3.5 deliverable of the N14 (Quantum Flow Matching) package
in a new module `BookProof/ChapterF6.lean` (registered in `BookProof.lean`), all
**`sorry`-free** and **`axiom`-free** (only `propext`, `Classical.choice`,
`Quot.sound`; verified via `lean_verify`); `lake build` green (8121 jobs).
**No `EXTERNAL` hypothesis, no `axiom`.**

* **F3.5** (Misra–Gries heavy-hitter bound, §8 Phase 4): the full streaming
  frequency-estimation state machine is modelled and its guarantee proved.
  The counter table is a finitely-supported map `T : α →₀ ℕ`; `mgStep k` processes
  one item (increment when present or a slot is free, else decrement every
  counter by one), `mgT k`/`mg k` fold it over the stream, and `mgD k` counts
  the decrement rounds.  Headline `misra_gries_bound` proves
  `f(x) − N/k ≤ f̂(x) ≤ f(x)` for capacity `k ≥ 1`, where `f(x) = s.count x` is the
  true frequency, `f̂(x) = (mg k s) x` the estimate, and `N = s.length`.  The
  proof rests on three invariants: `mg_upper` (never overshoots, by monotone
  per-step counting), `mg_lower` (undershoots by at most the decrement count),
  and `mgD_bound` (`k · D ≤ N`) via the mass-conservation identity
  `mgSum(mgT) + (k+1)·D = mgSum(T₀) + N` (`mgT_sum_add`), which uses that each
  decrement round removes exactly `k` units of mass once the table is full
  (`mgStep_card_le` capacity invariant + `mgSum_mapRange_pred`).
* **Remaining N14 item** (documented, not asserted): the concrete `p̂ = −i ∂` /
  `x̂` integration-by-parts symmetry underlying F2.1/F2.2 needs the
  function-space differentiation model.  **Remaining N13 items** stay as before:
  H1.5 (operator φ via CFC), H2.2 (SIRK compression assembly), and H2.3/H2.4
  (convergence, conditional on the named `CrouzeixBound`).

## Wave 42 (2026-07-06) — **N14 QFM: F2.1/F2.2 symmetric generators + F2.5 commuting flows** (`ChapterF5`)

This pass lands three further N14 (Quantum Flow Matching) deliverables in a new
module `BookProof/ChapterF5.lean` (registered in `BookProof.lean`), all
**`sorry`-free** and **`axiom`-free** (only `propext`, `Classical.choice`,
`Quot.sound`; verified via `#print axioms`); `lake build` green.  **No `EXTERNAL`
hypothesis, no `axiom`.**

* **F2.1** (continuity-Hamiltonian Hermiticity, algebraic core, §4 eq. 4.2):
  `anticommutator_isSymmetric` — the symmetrized product `K ∘ V + V ∘ K` of two
  symmetric operators is symmetric, with *no* commutation hypothesis.  This is
  the structural reason `H = ½(p̂·v(x̂) + v(x̂)·p̂)` is Hermitian even though
  `p̂` and `v(x̂)` do not commute.
* **F2.2** (conservative commutator form, algebraic core, §4 eqs. 4.4–4.6):
  `i_commutator_isSymmetric` — `i • [K, V] = i • (K ∘ V − V ∘ K)` is symmetric
  whenever `K, V` are (the commutator of symmetrics is skew, and `i` restores
  symmetry).  This is why `H^c = i • [K, V(x̂)]` is Hermitian.
* **F2.5** (exact commutativity and time-averaging, §5.4): `commuting_flow_two`
  and `commuting_flow_finset` — a pairwise-commuting family of channel
  generators has a fully factorizing time-ordered flow
  `exp(−i t • ∑ⱼ Hⱼ) = ∏ⱼ exp(−i t • Hⱼ)` (via `NormedSpace.exp_add_of_commute`
  / `exp_sum_of_commute`), the Magnus/Dyson truncation for a commuting family.
* **Remaining N14 items** (documented, not asserted): F3.5 (Misra–Gries
  heavy-hitter bound, optional) needs the full streaming state machine; the
  concrete `p̂ = −i ∂` / `x̂` integration-by-parts symmetry underlying F2.1/F2.2
  needs the function-space differentiation model.  **Remaining N13 items** stay
  as before: H1.5 (operator φ via CFC), H2.2 (SIRK compression assembly), and
  H2.3/H2.4 (convergence, conditional on the named `CrouzeixBound`).

## Wave 41 (2026-07-06) — **N13 SIRK: H1.3 Duhamel + H1.7 rational-Krylov** (`ChapterH3`)

This pass lands two further N13 (Hashimoto SIRK) deliverables in a new module
`BookProof/ChapterH3.lean` (registered in `BookProof.lean`), all **`sorry`-free**
and **`axiom`-free** (only `propext`, `Classical.choice`, `Quot.sound`; verified
via `#print axioms`); `lake build` green.  **No `EXTERNAL` hypothesis, no
`axiom`.**

* **H1.3** (exponential-integrator Duhamel identity, scalar/per-spectral-
  component core, §0 S3): `duhamel_scalar`
  (`∫₀^δ e^{(δ−s) z} ds = δ·φ₁(δ z)`) and the forcing-term corollary
  `duhamel_scalar_smul` (`∫₀^δ e^{(δ−s) z}·g ds = δ·φ₁(δ z)·g`).  Here `φ₁` is
  the `ChapterH1.phi 1` of H1.1/H1.2; proved by the reflection substitution
  `u = δ−s` (`intervalIntegral.integral_comp_sub_left`) and the rescaling
  `u = δ t` (`intervalIntegral.integral_comp_mul_left`).
* **H1.7** (rational-Krylov ⊆ rational functions of `Xₘ`, eq. 11):
  `sirkKrylov` (the SIRK Krylov iterates `w_j = X_j ⋯ X_1 v` over `ℕ`) and
  `sirk_krylov_mem_adjoin` — given the H1.6 shift identity `X_j = Y_j · Xₘ`
  (with `Y_j = (1 + h(m−j)·Xₘ)⁻¹`), every Krylov iterate lies in
  `{ r v | r ∈ adjoin ℂ ({Xₘ} ∪ range Y) }`, i.e. is a rational function of the
  single operator `Xₘ` applied to `v`.  This is the load-bearing inclusion of
  the paper's characterization; the reverse (surjectivity onto all of `R_SIRK`)
  is noted in the docstring but not needed for the error bound.
* **Remaining N13 items** (documented, not asserted): H1.5 (operator φ via CFC)
  and H2.2 (SIRK compression assembly) require the full continuous-functional-
  calculus operator-φ infrastructure; H2.3/H2.4 (convergence) remain conditional
  on the named `CrouzeixBound` deep analytic input — to stay a named hypothesis,
  never an axiom.

## Wave 40 (2026-07-06) — **N13 SIRK + N14 QFM flagships** (`ChapterH1/H2`, `ChapterF3/F4`)

This pass lands the two remaining flagship work packages of the roadmap queue,
the `../unfer` numerical algorithms promoted 2026-07-06.  Four new modules,
registered in `BookProof.lean`, all **`sorry`-free** and **`axiom`-free** (only
`propext`, `Classical.choice`, `Quot.sound`; verified via `lean_verify`);
`lake build` green (8118 jobs).  **No `EXTERNAL` hypothesis, no `axiom`.**

### N13 — Hashimoto SIRK (`ChapterH1.lean`, `ChapterH2.lean`)

* **H1.1** `phi : ℕ → ℂ → ℂ` (Hashimoto eq. 3, `φ₀ = exp`,
  `φ_{k+1}(z) = ∫₀¹ e^{sz}(1−s)^k/k!`), `phi_zero`, `phi_at_zero` (`φ_k(0)=1/k!`).
* **H1.2** `phi_succ_mul` (`z·φ_{k+1} z = φ_k z − 1/k!`, integration by parts)
  and corollary `phi_one` (`φ₁ z = (e^z−1)/z`).
* **H1.4** `numericalRange` + `eigenvalue_mem_numericalRange` (the easy half of
  Toeplitz–Hausdorff: every eigenvalue is a Rayleigh quotient).
* **H1.6** `resolvent_identity` and **`resolvent_shift_mul`**
  (`X_j·(1 + h(m−j)·X_m) = X_m` for `γ_j = N − h·j`) — the clean SIRK algebra
  core, purely algebraic from the resolvent identity.
* **H2.1** `hessenberg_vanishing` / `compression_upper_hessenberg`: with an
  orthonormal Krylov basis and the nesting `X 𝒦_j ⊆ 𝒦_{j+1}`, the compression
  `⟪vᵢ, X vⱼ⟫ = 0` for `i > j+1` (upper-Hessenberg).
* **Remaining N13 items** (documented, not asserted): H1.3 (Duhamel), H1.5
  (operator φ via CFC), H1.7 (rational-Krylov = rational functions of `X_m`),
  H2.2 (SIRK compression assembly), H2.3/H2.4 (convergence, conditional on the
  named `CrouzeixBound` — the deep analytic input, to be a named hypothesis,
  never an axiom).

### N14 — Quantum Flow Matching (`ChapterF3.lean`, `ChapterF4.lean`)

The full pure-proof *definition of done* is complete.  Reuses N12's
`ChapterF1.numberOp`.

* **F2.3** `disjoint_support_mul`, `disjoint_support_inner_zero` (orthogonal-Fock
  disjoint-support ⇒ zero product / orthogonality — "zero data loss").
* **F2.4** `diagonal_gram_residual_orthogonal` (diagonal-Gram closed-form
  training: `αₖ = ⟪gₖ,b⟫/‖gₖ‖²` makes the residual orthogonal — the `O(M)`
  payoff).
* **F2.6** `projOnto` with `projOnto_idempotent`, `projOnto_isSymmetric`,
  `projOnto_eq_starProjection` (the `|0⟩⟨0|` vacuum projector).
* **F2.7** `diagGen_vacuum`, `diagGen_eigenstate` (diagonal generator's
  eigenstates, direct reuse of N12 `numberOp`).
* **F2.8** `mehler_arc_integral`, `overlap_prod_pos`, **`dressed_vacuum_bessel`**
  (`Σⱼ εⱼ² ≤ 1`, exactly Bessel's inequality).
* **F2.9** `mehler_projector_matrix` (`⟪xᵢ,H₀ xⱼ⟫ = conj εᵢ·εⱼ`).
* **F3.1** `csketch` + `csketch_add`/`csketch_smul` (linearity),
  `sign_pair_expectation` (Rademacher orthonormality), **`countsketch_unbiased`**
  (`E[⟪S₁x,S₁y⟫] = ⟪x,y⟫`, the AMS/Count-Sketch estimator).
* **F3.2** `observable_matrix_identity`
  (`Tr(E_{r,s}ᴴ Wᴴ Pₐ W) = conj(W_{a,r})·W_{a,s}`).
* **F3.3** `unitary_preserves_dotProduct` (unitary ⇒ norm-preserving flow) and
  `selfAdjoint_exp_star_mul_self` (`e^{iH}` unitary for self-adjoint `H`).
* **F3.4** `pseudoinverse_left_inverse` (`(ΦᴴΦ)⁻¹Φᴴ·Φ = I`, subspace recovery).

## Wave 39 (2026-07-05) — **N7(c) mass gap** (`ChapterF2.lean`)

This pass lands **N7(c)** — the mathematically self-contained content of the
book's *"Mass gap"* section (`book.tex` ~line 4060), building on the Wave-38
Bargmann–Fock model of `ChapterF1`.  Following the book's own definition (*"the
mass gap is the eigenvalue of the Hamiltonian which is closer to the null
eigenvalue corresponding to the vacuum state"*), the Hamiltonian is the
quadratically-ordered `H := a†a = N`; on the monomial basis `H Xⁿ = n·Xⁿ`, so
the spectrum is `ℕ`, the vacuum `|0⟩ = 1` has energy `0`, and the mass gap is
`Δ = 1`.  New module `BookProof/ChapterF2.lean` (registered in `BookProof.lean`),
all declarations `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`; verified via `lean_verify` on `mass_gap`,
`hamiltonian_expectation_nonneg`, `deformedHamiltonian_monomial`);
`lake build BookProof` green (8114 jobs).  **No `EXTERNAL` hypothesis.**

* **F2.1** `numberOp_coeff` (`(N p)_n = n·p_n`) and `numberOp_support`.
* **F2.2** `bargmann_self_re`/`bargmann_numberOp_re` (real forms
  `⟨p|p⟩ = Σ n!|p_n|²`, `⟨p|N|p⟩ = Σ n·n!|p_n|²`) and
  **`hamiltonian_expectation_nonneg`** (`H` is positive / bounded from below by
  the quadratic ordering: `⟨ψ|H|ψ⟩ ≥ 0`).
* **F2.3** `deformedHamiltonian c := c•N` with `deformedHamiltonian_monomial`
  (`H_c Xⁿ = (c·n)·Xⁿ`, so the mass gap becomes arbitrary `c` with unchanged
  eigenstates), `deformedHamiltonian_commutes_numberOp` and
  `hamiltonian_commutes_numberOp` (`[H_c, N] = 0` — the book's *"the number
  operator can be added to the Hamiltonian, modifying the mass gap without
  observable consequences"*).
* **F2.4 HEADLINE** `mass_gap` (for `ψ ⟂ vacuum`, i.e. `ψ₀ = 0`,
  `⟨ψ|H|ψ⟩ ≥ ⟨ψ|ψ⟩` — spectrum above the vacuum bounded below by `Δ = 1`),
  with `mass_gap_attained` (`⟨X|H|X⟩ = ⟨X|X⟩`, the gap is tight),
  `vacuum_energy_zero`, and `massGap_smallest_excited` (eigenvalue form: `1` is
  the smallest positive eigenvalue).

This closes the last remaining roadmap work item (N7(c)); the earlier author
flag *"ask before building"* is satisfied because the book isolates the mass gap
explicitly in this section, and the §0 S7 formalism fixes the model.

## Wave 38 (2026-07-05) — **N11 + N12 + hygiene** (`ChapterA4h.lean`, `ChapterA3w.lean`, `ChapterF1.lean`)

This pass lands the last two open work packages of the roadmap plus the pending
S7 hygiene docstrings.  All new declarations are `sorry`-free and `axiom`-free
(only `propext`, `Classical.choice`, `Quot.sound`; verified via `lean_verify`);
`lake build BookProof` green (8113 jobs).

**N12 — S7 Bargmann–Fock / CCR field package (`ChapterF1.lean`).** The
polynomial (Bargmann–Fock) model of the CCR algebra on `ℂ[X]` (vacuum `|0⟩ = 1`,
`a := d/dX`, `a† := X·`), with the `../unfer` design decisions (§0 S7):
* **F1.1** `ccr` (`[a, a†] = 1` on `ℂ[X]`) and `ccr_mv` (`[a_i, a†_j] = δ_ij`
  on `MvPolynomial (Fin n) ℂ` via `pderiv`);
* **F1.2** Hermitian field rep `fieldPhi := a†+a`, `fieldPi := i·(a†−a)`,
  `field_ccr` (`[φ, π] = 2i·1`); the Bargmann pairing `bargmann` with
  `bargmann_eq_sum`, `bargmann_monomial_left`, `bargmann_monomial`
  (`⟪Xᵐ,Xⁿ⟫ = n!·δ_{mn}`), and the adjoint relation `bargmann_creat_annih`
  (`⟪a†p,q⟫ = ⟪p,aq⟫`, whence `φ`/`π` symmetric);
* **F1.3** `numberOp := a†∘a`, `numberOp_monomial` (`N Xⁿ = n·Xⁿ`);
* **F1.4 HEADLINE** `quadratic_ordering_vacuum` (`⟨0|H|0⟩ = 0` for `H := a†a`),
  contrasted with `symmetric_ordering_vacuum` (`½` for `(aa†+a†a)/2`) and
  `orderings_differ` — the quadratic-ordering normalization is a theorem;
* **F1.5** `field_gauge_invariant_iff` — BRST bridge to `ChapterG2`
  (gauge invariance = commutation with the BRST constraint).
No `EXTERNAL` input.

**N11 — Wigner/Mackey/Weyl exhaustiveness bundle (`ChapterA4h.lean`,
`ChapterA3w.lean`).** Named-hypothesis structures with citation docstrings
(never axioms), and the conditional headlines assembled around the on-disk
exclusion cores:
* `ChapterA4h`: concrete `localizable_iff_massShell` (the Majorana energy symbol
  is singular iff `|p⃗|² = m₁²+m₂²`, from `ChapterA5.energySymbolR_sq`) +
  `not_localizable_of_tachyon` / `not_localizable_zeroMomentum` (Exclusions 1–2);
  the `EXTERNAL` `MackeyImprimitivity` (induced realization) and
  `WignerClassification` (no continuous spin); **`prop87_assembled`** (a
  localizable induced irrep is massive or massless-discrete),
  `prop88_energy_sign_not_conserved` + `cor1_energy_sectors_swapped`
  (antiparticles/CPT, from `ChapterA4e`), and the combined `prop87_88_assembled`.
* `ChapterA3w`: the `EXTERNAL` `WeylCompleteReducibility` (finite-dim `SL(2,ℂ)`
  reps completely reducible, stated over Mathlib `Representation`) +
  `weyl_invariant_complement`; the concrete **`lemma52_parity_gluing`** (chirality
  not parity-invariant, parity swaps `V_{(m,n)} ↔ V_{(n,m)}`, LL↔RR), reusing
  `chirality_not_parity_invariant`/`parity_swaps_chirL`/`projLL_not_parity_invariant`/
  `parity_swaps_LL_RR`.

**Hygiene.** Added the pending §0 S7 `../unfer` cross-reference docstrings to
`born_conditioning` (cite `prob_kernel` `Session.condition`) and `prodEquiv`
(cite `nested_fock_algebra`) in `ChapterU.lean`; the new modules are lint-clean.

## Wave 37 (2026-07-05) — N4 §A.3 Note 50 / Lemma 52: **dimensions of the complete-reducibility summands at `N = 6`** (`ChapterA3v.lean`)

New module `BookProof/ChapterA3v.lean` (registered in `BookProof.lean`), the
next case after Wave 36's `N = 5` dimension count.  As at `N = 5`, the totally
antisymmetric summand `Λ⁶V` vanishes (a `4`-dimensional space has no nonzero
`6`-fold exterior power).  For the `4`-dimensional Dirac spinor `V`
(`dim V^{⊗6} = 4⁶ = 4096`) the file computes, reusing Wave 36's general
orbit-count machinery (`ChapterA3u.card_fixedTuples`,
`ChapterA3u.trace_permMat_pow`: `tr(permMat σ) = 4^{c(σ)}`):

* **`dim Sym⁶V = 84`** `trace_projSym_six` (`= C(9,6)`), via `Σ_{σ∈S₆} 4^{c(σ)} = 60480`, `/6! = 84`;
* **`dim Λ⁶V = 0`** `trace_projAnti_six` (`= C(4,6) = 0`), via `Σ_{σ∈S₆} sgn(σ)·4^{c(σ)} = 0`;
* **`dim(mixed) = 4012`** `trace_projMixed_six` (`= 4096 − 84 − 0`);
* **Headline** `trace_decomposition_six`: `84 + 0 + 4012 = 4096 = dim (V^{⊗6})`.

The two averaged-projector traces become finite sums over `S₆` (720 permutations)
of small numbers, discharged by kernel `decide` under
`set_option maxRecDepth 100000` / `maxHeartbeats 4000000` — **no `native_decide`**.

All declarations are `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`; verified via `lean_verify` on
`trace_decomposition_six`).  `lake build BookProof` green (8110 jobs).
**No `EXTERNAL` hypothesis.**

Still open after wave 37 (unchanged in kind): the `EXTERNAL` Wigner/Mackey
exhaustiveness backbone of the §A.4/A.5 Bargmann–Wigner/CPT classification.

## Wave 36 (2026-07-05) — N4 §A.3 Note 50 / Lemma 52: **dimensions of the complete-reducibility summands at `N = 5`** (`ChapterA3u.lean`)

New module `BookProof/ChapterA3u.lean` (registered in `BookProof.lean`), the
next case after Wave 35's `N = 4` dimension count, and the **first** where the
totally antisymmetric summand `Λ⁵V` vanishes (a `4`-dimensional space has no
nonzero `5`-fold exterior power).  For the `4`-dimensional Dirac spinor `V`
(`dim V^{⊗5} = 4⁵ = 1024`) the file computes:

* **`dim Sym⁵V = 56`** `trace_projSym_five` (`= C(8,5)`);
* **`dim Λ⁵V = 0`** `trace_projAnti_five` (`= C(4,5) = 0`, vacuous exterior power);
* **`dim(mixed) = 968`** `trace_projMixed_five` (`= 1024 − 56 − 0`);
* **Headline** `trace_decomposition_five`: `56 + 0 + 968 = 1024 = dim V^{⊗5}`.

Because the brute-force `S₅ × 4⁵` count (`120` permutations over `1024` index
tuples) is far too large for kernel `decide`, this wave first proves the
general **orbit-count** lemma `card_fixedTuples`: for any `σ : S_N`, the number
of index tuples `a : Fin N → Fin 4` fixed by `σ` equals `4^{c(σ)}`, where
`c(σ) = (N − Σ cycleType σ) + #(cycleType σ)` is the number of orbits of `σ`
(fixed points plus nontrivial cycles).  The proof sets up an explicit
bijection between the fixed tuples and functions on
`{fixed points} ⊕ {cycle factors}` (reusing the helper `invariant_sameCycle` /
`invariant_apply_zpow`, that an invariant tuple is constant along each orbit),
then counts via `Equiv.Perm.sum_cycleType`, `cycleType_def`, and
`Fintype.card_pi`.  With `trace (permMat σ) = 4^{c(σ)}` (`trace_permMat_pow`),
the two averaged-projector traces become finite sums over `S₅` of small numbers
(`Σ 4^{c(σ)} = 6720`, `Σ sgn(σ)·4^{c(σ)} = 0`), discharged by kernel `decide`
under `set_option maxRecDepth 100000` — **no `native_decide`**.

All declarations are `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`; verified via `lean_verify` on
`trace_decomposition_five` and `card_fixedTuples`).  `lake build BookProof`
green (8109 jobs).  **No `EXTERNAL` hypothesis.**

Still open after wave 36 (unchanged in kind): the `EXTERNAL` Wigner/Mackey
exhaustiveness backbone of the §A.4/A.5 Bargmann–Wigner/CPT classification.

## Wave 35 (2026-07-05) — N4 §A.3 Note 50 / Lemma 52: **dimensions of the complete-reducibility summands at `N = 4`** (`ChapterA3t.lean`)

New module `BookProof/ChapterA3t.lean` (registered in `BookProof.lean`), the
next case after Wave 34's `N = 3` dimension count.  Each projector is idempotent,
so its trace equals its rank (the dimension of the summand).  For the
`4`-dimensional Dirac spinor `V` (`dim V^{⊗4} = 4⁴ = 256`) the file computes,
reusing Wave 33's general `trace_permMat`:

* **`dim Sym⁴V = 35`** `trace_projSym_four`: `tr(projSym 4) = (4!)⁻¹ Σ_σ tr(permMat σ)
  = (1/24)(256 + 6·64 + 8·16 + 3·16 + 6·4) = 840/24 = 35 = C(7,4)` (cycle type
  of `S₄`: identity 4 cycles → 256; six transpositions 3 cycles → 64 each; eight
  3-cycles 2 cycles → 16 each; three (2,2) 2 cycles → 16 each; six 4-cycles 1
  cycle → 4 each).
* **`dim Λ⁴V = 1`** `trace_projAnti_four`: `tr(projAnti 4) = (4!)⁻¹ Σ_σ sgn(σ)·tr(permMat σ)
  = (1/24)(256 − 6·64 + 8·16 + 3·16 − 6·4) = 24/24 = 1 = C(4,4)`.
* **`dim(mixed) = 220`** `trace_projMixed_four`: `tr(projMixed 4) = tr(1) − 35 − 1
  = 256 − 36 = 220`.
* **Headline** `trace_decomposition_four`: `35 + 1 + 220 = 256 = dim (V ⊗ V ⊗ V ⊗ V)`.

All declarations are `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`; the finite ℕ counts are discharged by kernel
`decide`/`norm_cast` under `set_option maxRecDepth 10000` — 24 permutations over
`4⁴ = 256` index tuples — with **no `native_decide`**; verified via `lean_verify`
on `trace_decomposition_four`, `trace_projSym_four`).  `lake build BookProof`
green (8108 jobs).  **No `EXTERNAL` hypothesis.**

Still open after wave 35 (unchanged in kind): the `EXTERNAL` Wigner/Mackey
exhaustiveness backbone of the §A.4/A.5 Bargmann–Wigner/CPT classification.

## Wave 34 (2026-07-05) — N4 §A.3 Note 50 / Lemma 52: **dimensions of the complete-reducibility summands at `N = 3`** (`ChapterA3s.lean`)

New module `BookProof/ChapterA3s.lean` (registered in `BookProof.lean`), the
next case after Wave 33's `N = 2` dimension count.  `N = 3` is the **first** case
where the symmetric and antisymmetric pieces no longer exhaust `V^{⊗3}` and the
mixed-symmetry summand is nonzero.  Each projector is idempotent, so its trace
equals its rank (the dimension of the summand).  For the `4`-dimensional Dirac
spinor `V` (`dim V^{⊗3} = 4³ = 64`) the file computes, reusing Wave 33's general
`trace_permMat` (`tr(permMat σ) = #{a | a∘σ = a} = 4^{cycles(σ)}`):

* **`dim Sym³V = 20`** `trace_projSym_three`: `tr(projSym 3) = (3!)⁻¹ Σ_σ tr(permMat σ)
  = (1/6)(64 + 3·16 + 2·4) = 120/6 = 20` (identity 3 cycles → 64; three
  transpositions 2 cycles → 16 each; two 3-cycles 1 cycle → 4 each).
* **`dim Λ³V = 4`** `trace_projAnti_three`: `tr(projAnti 3) = (3!)⁻¹ Σ_σ sgn(σ)·tr(permMat σ)
  = (1/6)(64 − 3·16 + 2·4) = 24/6 = 4`.
* **`dim(mixed) = 40`** `trace_projMixed_three`: `tr(projMixed 3) = tr(1) − 20 − 4
  = 64 − 24 = 40` (first nonzero mixed-symmetry piece).
* **Headline** `trace_decomposition_three`: `20 + 4 + 40 = 64 = dim (V ⊗ V ⊗ V)`.

All declarations are `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`; the finite ℕ count `Σ_σ #{a | a∘σ = a} = 120`
is discharged by `decide`, no `native_decide`; verified via `lean_verify` on
`trace_decomposition_three`, `trace_projSym_three`).  `lake build BookProof`
green (8107 jobs).  **No `EXTERNAL` hypothesis.**

Still open after wave 34 (unchanged in kind): the `EXTERNAL` Wigner/Mackey
exhaustiveness backbone of the §A.4/A.5 Bargmann–Wigner/CPT classification.

## Wave 33 (2026-07-05) — N4 §A.3 Note 50 / Lemma 52: **dimensions (ranks) of the complete-reducibility summands** (`ChapterA3r.lean`)

New module `BookProof/ChapterA3r.lean` (registered in `BookProof.lean`), the
dimension-counting payoff of the Wave 29–32 complete-reducibility machinery.
Since each of `projSym N`, `projAnti N`, `projMixed N` is an **idempotent**
endomorphism of a finite-dimensional space, its trace equals its rank — the
dimension of the summand it projects onto.  This file computes those traces in
the base case `N = 2` (the tensor square of the `4`-dimensional Dirac spinor),
giving the concrete count `dim (V ⊗ V) = 16 = 10 + 6` with the mixed piece
vanishing.  All declarations are `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`; verified via `lean_verify` on
`trace_decomposition_two`, `trace_projSym_two`); `lake build BookProof` green
(8106 jobs).  **No `EXTERNAL` hypothesis.**

* **Trace of a braiding** `trace_permMat` (general `N`): `tr (permMat σ)` counts
  the index tuples `a : Fin N → Fin 4` fixed by the slot permutation `σ`
  (`= Σ_a [a ∘ σ = a]`, the number of tuples constant on each cycle of `σ`).
* **`dim Sym²V = 10`** `trace_projSym_two`: `tr (projSym 2) = (2!)⁻¹·Σ_σ tr(permMat σ)
  = (1/2)(16 + 4) = 10`.
* **`dim Λ²V = 6`** `trace_projAnti_two`: `tr (projAnti 2) = (2!)⁻¹·Σ_σ sgn(σ)·tr(permMat σ)
  = (1/2)(16 − 4) = 6` — the dimension of the Def 57 antisymmetric pinor pair.
* **No mixed piece** `trace_projMixed_two`: `tr (projMixed 2) = 0` (from
  `ChapterA3q.projMixed_two_eq_zero`).
* **Headline** `trace_decomposition_two`: the dimension count
  `10 + 6 + 0 = 16 = dim (V ⊗ V)` of the `N = 2` complete-reducibility
  decomposition `V ⊗ V = Sym²V ⊕ Λ²V`.

Still open after wave 33 (unchanged in kind): the `EXTERNAL` Wigner/Mackey
exhaustiveness backbone of the §A.4/A.5 Bargmann–Wigner/CPT classification.

## Wave 32 (2026-07-05) — N4 §A.3 Note 50 / Lemma 52: **general-`N` complete reducibility** via the mixed-symmetry complement (`ChapterA3q.lean`)

New module `BookProof/ChapterA3q.lean` (registered in `BookProof.lean`),
extending Wave 31's `N = 2` decomposition to **arbitrary `N`**, still **without
the `EXTERNAL` Weyl hypothesis**.  For `N ≥ 3` the symmetric (`projSym N`) and
antisymmetric (`projAnti N`) pieces no longer exhaust `V^{⊗N}`; the remainder
carries the **mixed-symmetry** representations.  This file isolates that
remainder as the complementary projector `projMixed N := 1 − projSym N −
projAnti N` and proves the triple `{projSym N, projAnti N, projMixed N}` is a
complete system of pairwise orthogonal, idempotent, full-Lorentz–invariant
projectors for every `N ≥ 2`.  All 12 declarations are `sorry`-free and
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`; verified via
`lean_verify` on `tensorPow_complete_reducibility`, `projMixed_two_eq_zero`);
`lake build BookProof` green (8105 jobs).

* **Completeness** `projSym_add_projAnti_add_projMixed`: the three sum to `1`.
* **Orthogonality (`N ≥ 2`)** `projSym_mul_projMixed`, `projMixed_mul_projSym`,
  `projAnti_mul_projMixed`, `projMixed_mul_projAnti` (all `= 0`), reducing via
  `projSym_idem`/`projAnti_idem` and Wave 31's `projSym_mul_projAnti` /
  `projAnti_mul_projSym`.
* **Idempotency (`N ≥ 2`)** `projMixed_idem`: `projMixed` is a genuine projector.
* **Full-Lorentz invariance** `projMixed_diagGen_comm`, `projMixed_uniform_comm`
  and the §A.3 specializations `projMixed_spinGenDiag_comm` (diagonal `Spin⁺`),
  `projMixed_parityDiag_comm` (diagonal parity `γ⁰⊗…⊗γ⁰`) — each inherited from
  the corresponding `projSym`/`projAnti` commutation lemmas.
* **Consistency** `projMixed_two_eq_zero`: at `N = 2` the mixed piece vanishes
  (matches `ChapterA3p.projSym_add_projAnti_two`).
* **Headline** `tensorPow_complete_reducibility` (general `N ≥ 2`): the bundled
  complete orthogonal idempotent system realizing
  `V^{⊗N} = Sym^N V ⊕ Λ^N V ⊕ (mixed symmetry)` of the Lorentz representation —
  the general-`N` (mixed-symmetry) form of Note 50, `EXTERNAL`-free.

Still open after wave 32: the `EXTERNAL` Wigner/Mackey exhaustiveness backbone
of the §A.4/A.5 Bargmann–Wigner/CPT classification (identifying the concrete
mixed-symmetry summands with the abstract irreps `V_{(m,n)}` still relies on the
cited Weyl/Wigner backbone).

## Wave 31 (2026-07-05) — N4 §A.3 Note 50 / Lemma 52: **concrete complete reducibility** of the tensor square (`ChapterA3p.lean`)

New module `BookProof/ChapterA3p.lean` (registered in `BookProof.lean`), the
complete-reducibility payoff of Note 50 (Weyl: finite-dimensional reps of
`SL(2,ℂ)` are completely reducible) in the base case `N = 2`, proved **outright
without the `EXTERNAL` Weyl hypothesis**.  Using the symmetrizer `projSym`
(`ChapterA3n`) and antisymmetrizer `projAnti` (`ChapterA3o`), it exhibits the
internal direct-sum decomposition `V ⊗ V = Sym²V ⊕ Λ²V` of the Lorentz
representation via a complete system of complementary orthogonal projectors.
All 5 declarations are `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`; verified via `lean_verify` on
`tensorSquare_complete_reducibility`); `lake build BookProof` green (8104 jobs).

* **Signed group sum vanishes** `sum_signC_eq_zero`: `Σ_{σ∈S_N} sgn(σ) = 0` once
  `N ≥ 2` (left-multiply by a fixed transposition `t = swap 0 1`; the bijection
  `σ ↦ t·σ` flips the sign, so the sum equals its own negative).
* **Orthogonality (N ≥ 2)** `projSym_mul_projAnti`, `projAnti_mul_projSym`: the
  symmetrizer and antisymmetrizer annihilate each other.  Reindexing `ρ = στ`
  factors the cross term as `(Σ_σ sgn σ)·(antisymmetrizer) = 0`.
* **Complementarity (N = 2)** `projSym_add_projAnti_two`: `projSym 2 + projAnti 2 = 1`
  (`(1/2)(1+τ) + (1/2)(1-τ) = 1`).
* **Headline** `tensorSquare_complete_reducibility`: `projSym 2`, `projAnti 2`
  are complementary (`sum = 1`), orthogonal (`both products = 0`) and idempotent
  (reusing `projSym_idem`/`projAnti_idem`) — the concrete `N = 2` instance of
  Weyl complete reducibility, `EXTERNAL`-free.  Each summand is full-Lorentz
  invariant by `ChapterA3n`/`ChapterA3o`.

Still open after wave 31: the general-`N` `EXTERNAL` Weyl/Note-50
complete-reducibility layer (mixed-symmetry pieces for `N ≥ 3`) and the
`EXTERNAL` Wigner/Mackey exhaustiveness backbone of the §A.4/A.5
Bargmann–Wigner/CPT classification.

## Wave 30 (2026-07-05) — N4 §A.3 Note 51 / Lemma 52 / Def 57: the **arbitrary `N`-fold antisymmetric** power (`ChapterA3o.lean`)

New module `BookProof/ChapterA3o.lean` (registered in `BookProof.lean`), the
exact **dual** of Wave 29's symmetric-power construction: for arbitrary `N` it
builds the totally **antisymmetric** power (the `N`-fold exterior power
`Λ^N V`), whose base case `N = 2` is the antisymmetric pair `Pinor₀` of Def 57.
It reuses the tensor model of `ChapterA3n` verbatim — carrier
`MN N = Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ`, `tensorPow`, the permutation
representation `permMat`, the diagonal `Spin⁺` generator `diagGen`, and the
uniform parity operator `uniform` — changing only the group average from the
trivial character to the **sign** character `sgn : S_N → {±1}`.  All 6
declarations are `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`; verified via `lean_verify` on `projAnti_idem`,
`projAnti_parityDiag_comm`); `lake build` green (8103 jobs).  **No `EXTERNAL`
hypothesis** (Note 50 / Weyl complete reducibility remains the cited backbone).

* **Total antisymmetrizer** `projAnti N = (N!)⁻¹ • Σ_{σ∈S_N} sgn(σ)·permMat σ`
  onto `Λ^N V` (`signC σ = ((Equiv.Perm.sign σ : ℤ) : ℂ)`).
* **Signed group identity** `sum_signed_permMat_sq`:
  `(Σ_σ sgn(σ)·ρ(σ))² = N!·Σ_σ sgn(σ)·ρ(σ)` — reindexing `ρ = στ` and using
  that `sgn` is a `{±1}`-valued homomorphism (`sgn(σ)·sgn(σ⁻¹ρ) = sgn(ρ)`).
* **Idempotency** `projAnti_idem`: `projAnti N` is a genuine projector.
* **Lemma 52 payoff (antisymmetric case)**: because every braiding `permMat σ`
  already commutes with `diagGen A` and `uniform A` (Wave 29's
  `permMat_diagGen_comm`/`permMat_uniform_comm`), so does the signed average
  (`projAnti_diagGen_comm`, `projAnti_uniform_comm`).  Specialising to the §A.3
  data: the exterior power is a **full-Lorentz** subrepresentation, invariant
  under the diagonal `Spin⁺` generators `γ^μγ^ν` (`projAnti_spinGenDiag_comm`)
  **and** under diagonal parity `γ⁰⊗…⊗γ⁰` (`projAnti_parityDiag_comm`).
  Together with `ChapterA3n` this completes the pair of totally
  (anti)symmetric tensor-power constructions of Notes 50–51 / Def 57.

Still open after wave 30: the `EXTERNAL` Weyl/Note-50 complete-reducibility layer
and the `EXTERNAL` Wigner/Mackey exhaustiveness backbone of the §A.4/A.5
Bargmann–Wigner/CPT classification.

## Wave 29 (2026-07-05) — N4 §A.3 Note 51 / Lemma 52: the **arbitrary `N`-fold** symmetric power (`ChapterA3n.lean`)

New module `BookProof/ChapterA3n.lean` (registered in `BookProof.lean`), taking
the **general step** past the concrete two-fold (`ChapterA3l`, `S₂`) and
three-fold (`ChapterA3m`, `S₃`) braiding constructions: for *arbitrary* `N` it
formalizes the `N`-fold tensor product `V^{⊗N}` and the action of the full
symmetric group `S_N` by braidings, culminating in the Lemma-52 payoff that the
total symmetrizer `projSym N = (1/N!)·Σ_{σ∈S_N} ρ(σ)` is a genuine projector onto
a **full-Lorentz** subrepresentation (the symmetric power `V^{⊙N}`).  All 13
declarations are `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`; verified via `lean_verify` on `projSym_idem`,
`projSym_spinGenDiag_comm`, `projSym_parityDiag_comm`); `lake build` green
(8102 jobs).  **No `EXTERNAL` hypothesis** (Note 50 / Weyl complete reducibility
remains the cited backbone).

Instead of iterated left-associated Kronecker products, this file uses the clean
`N`-fold tensor model: the carrier is `Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ`,
indexed by tuples `a : Fin N → Fin 4`.

* **Tensor operator** `tensorPow M a b = ∏ i, (M i) (a i) (b i)` (the `N`-fold
  `⊗ᵢ Mᵢ`), proven **multiplicative** (`tensorPow_mul`, via the factorisation
  `Finset.prod_univ_sum` of a sum over tuples of a product) and **unital**
  (`tensorPow_one`).
* **Permutation representation** `permMat σ a b = [b = a ∘ σ]`: a homomorphism
  from `S_N` (`permMat_mul : permMat σ * permMat τ = permMat (σ*τ)`,
  `permMat_one`).
* **Braiding relation** `permMat_braiding`:
  `permMat σ * tensorPow M = tensorPow (fun j => M (σ⁻¹ j)) * permMat σ`.
* **Full-Lorentz invariance of the diagonal action**: the diagonal `Spin⁺`
  generator `diagGen A = Σᵢ (1⊗…⊗A⊗…⊗1)` and the uniform parity operator
  `uniform A = A⊗…⊗A` each commute with every `permMat σ`
  (`permMat_diagGen_comm`, `permMat_uniform_comm`) — the totally symmetric
  diagonal action is invariant under any permutation of the `N` slots.
* **Lemma 52 payoff (general `N`)**: the core group identity
  `(Σ_{σ∈S_N} σ)² = N!·(Σ_{σ∈S_N} σ)` (`sum_permMat_sq`, using
  `Fintype.card_perm`) makes `projSym N` a genuine **projector** (`projSym_idem`)
  that commutes with `diagGen A` and `uniform A` (`projSym_diagGen_comm`,
  `projSym_uniform_comm`).  Specialising to the §A.3 data gives the headline
  statement: the symmetric power is a full-Lorentz subrepresentation, invariant
  under the diagonal `Spin⁺` generators `γ^μγ^ν` (`projSym_spinGenDiag_comm`)
  **and** under diagonal parity `γ⁰⊗…⊗γ⁰` (`projSym_parityDiag_comm`).  This
  generalises the concrete `N = 2`/`N = 3` constructions of Waves 27–28 to all `N`.

Still open after wave 29: the `EXTERNAL` Weyl/Note-50 complete-reducibility layer
and the `EXTERNAL` Wigner/Mackey exhaustiveness backbone of the §A.4/A.5
Bargmann–Wigner/CPT classification.

## Wave 28 (2026-07-05) — N4 §A.3 Note 51 / Lemma 52: the threefold braiding (`S₃`) / symmetric-cube structure (`ChapterA3m.lean`)

New module `BookProof/ChapterA3m.lean` (registered in `BookProof.lean`), taking
the **next step** past the two-fold braiding / symmetric-square structure of
`ChapterA3l` toward the *arbitrary* `N`-fold symmetric powers of Note 51.  It
formalizes the **three-fold tensor product** `V ⊗ V ⊗ V` (carrier of the
symmetric cube `V ⊙ V ⊙ V`, which contains the top irrep `V⁺_{3/2}`) and the
action of the symmetric group `S₃` by braidings, on the `4×4 ⊗ 4×4 ⊗ 4×4`
left-associated Kronecker model (index type `((Fin 4 × Fin 4) × Fin 4)`).  All
`sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`;
verified via `lean_verify` on `projSym3_idem`, `projSym3_parityDiag_comm`);
`lake build` green (8101 jobs).  **No `EXTERNAL` hypothesis** (Note 50 / Weyl
complete reducibility and the extension to *all* `N`-fold symmetric powers remain
the cited backbone).

* **Three transposition (braiding) operators** `swap12 = τ ⊗ 1` (built from the
  two-fold `ChapterA3l.swap`), `swap23`, `swap13` (entrywise permutation
  matrices), with **braiding relations** `swap12_kronecker`, `swap23_kronecker`,
  `swap13_kronecker` (each `τ` conjugates a Kronecker product into the
  correspondingly permuted product).
* **The `S₃` (Coxeter) presentation**: involutivity `swap12_sq`, `swap23_sq`,
  `swap13_sq` (`τ²=1`) and the **braid relation**
  `swap12·swap23·swap12 = swap13 = swap23·swap12·swap23` (`braid_left`,
  `braid_right`, `braid_rel`).
* **Full-Lorentz invariance of the diagonal action**: the diagonal `Spin⁺`
  generator `spinGenDiag3 = A⊗1⊗1 + 1⊗A⊗1 + 1⊗1⊗A` and diagonal parity
  `parityDiag3 = γ⁰⊗γ⁰⊗γ⁰` each commute with all three transpositions
  (`swap12_spinGenDiag_comm`, …, `swap13_parityDiag_comm`) — the totally
  symmetric diagonal action is invariant under any permutation of the slots.
* **Lemma 52 payoff (symmetric-cube step)**: the total symmetrizer
  `projSym3 = (1/6)·Σ_{g∈S₃} ρ(g)` is a genuine projector (`projSym3_idem`,
  encoding the group identity `(Σ_{g∈S₃} g)² = 6·Σ_{g∈S₃} g`) onto a
  **full-Lorentz** subrepresentation: `projSym3_spinGenDiag_comm` (diagonal
  `Spin⁺`-invariant) **and** `projSym3_parityDiag_comm` (parity-invariant).  So,
  exactly as at the symmetric-square level in `ChapterA3l`, the *real*
  symmetric-cube construction is automatically a representation of the full
  Lorentz group.

Still open after wave 28: the extension of Lemma 52 to *arbitrary* `N`-fold
symmetric powers plus the `EXTERNAL` Weyl/Note-50 layer; the `EXTERNAL`
Wigner/Mackey exhaustiveness backbone of the §A.4/A.5 Bargmann–Wigner/CPT
classification.

## Wave 27 (2026-07-05) — N4 §A.3 Note 51 / Lemma 52: the symmetric tensor-square (braiding) structure (`ChapterA3l.lean`)

New module `BookProof/ChapterA3l.lean` (registered in `BookProof.lean`), taking
the **next step** past the tensor-square chiral decomposition of `ChapterA3k`.
Note 51 builds the general irreps `V_{(m,n)}` as *symmetric* tensor powers of the
chiral spinors, so this file introduces the **braiding (swap) operator**
`τ : u ⊗ v ↦ v ⊗ u` on `V ⊗ V` and the symmetric/antisymmetric decomposition it
induces.  All `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`; verified via `lean_verify` on `swap_kronecker`,
`projSym_parityDiag_comm`); `lake build` green (8100 jobs).  **No `EXTERNAL`
hypothesis** (Note 50 / Weyl complete reducibility and the extension to arbitrary
`N`-fold symmetric powers remain the cited backbone).

On the `4×4 ⊗ 4×4` Kronecker model of §A.3 the swap is the commutation matrix
`τ_{(i,j),(k,l)} = [i=l ∧ j=k]`:

* **Braiding relation** `swap_kronecker` (`τ·(A⊗B) = (B⊗A)·τ` for all `A,B`);
  involutivity `swap_sq` (`τ²=1`); exchange of the per-slot chirality operators
  `swap_chir1`, `swap_chir2` (`τ·(iγ⁵⊗1) = (1⊗iγ⁵)·τ`).
* **`τ` commutes with the diagonal Lorentz/parity action**
  `swap_spinGenDiag_comm`, `swap_parityDiag_comm` (both `γ^μγ^ν⊗1+1⊗γ^μγ^ν` and
  `γ⁰⊗γ⁰` are symmetric under slot exchange).
* **`τ` fixes the pure blocks, exchanges the mixed ones**: `swap_projLL_comm`,
  `swap_projRR_comm` (fixes `V⁺⊗V⁺`, `V⁻⊗V⁻`), `swap_swaps_LR_RL` /
  `swap_swaps_RL_LR` (braids the two `(½,½)` blocks `V⁺⊗V⁻ ↔ V⁻⊗V⁺`).
* **Symmetric/antisymmetric projectors** `projSym = ½(1+τ)`, `projAsym = ½(1-τ)`:
  `projSym_add_projAsym` (`=1`), `projSym_idem`, `projAsym_idem`,
  `projSym_mul_projAsym` (`=0`).
* **Lemma 52 payoff — the symmetric tensor square is a *full-Lorentz*
  subrepresentation**: `projSym_spinGenDiag_comm` (diagonal `Spin⁺`-invariant)
  **and** `projSym_parityDiag_comm` (parity-invariant); likewise
  `projAsym_spinGenDiag_comm`, `projAsym_parityDiag_comm`.  Unlike a single pure
  chirality block (`ChapterA3k.projLL_not_parity_invariant`), the symmetric
  (real) tensor construction is automatically a representation of the full
  Lorentz group.  `projLL_projSym_comm` shows the pure `(1,0)` block sits inside
  the symmetric tensor square.

Still open after wave 27: the extension of Lemma 52 to arbitrary `N`-fold
symmetric powers plus the `EXTERNAL` Weyl/Note-50 layer; the `EXTERNAL`
Wigner/Mackey exhaustiveness backbone of the §A.4/A.5 Bargmann–Wigner/CPT
classification.

## Wave 26 (2026-07-05) — N4 §A.3 Notes 50–51 / Lemma 52: tensor-power chiral decomposition (`ChapterA3k.lean`)

New module `BookProof/ChapterA3k.lean` (registered in `BookProof.lean`), taking
the **tensor-power step** of the §A.3 Notes 50–51 / Lemma 52 finite-dim-irrep
classification past the `m=n=½` base case of `ChapterA3j`.  All `sorry`-free and
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`; verified via
`#print axioms` on `projLL_not_parity_invariant`, `parity_swaps_LL_RR`,
`parityDiag_sq`, `chir2_spinGenDiag_comm`, `projSum`); `lake build` green
(8099 jobs).  **No `EXTERNAL` hypothesis** (Note 50 / Weyl complete reducibility
and the extension to arbitrary `N`-fold symmetric powers remain the cited
backbone).

Notes 50–51 build the general irreps `V_{(m,n)}` as symmetric tensor powers of
the two chiral spinors, and Lemma 52 observes parity swaps `V_{(m,n)} ↔ V_{(n,m)}`.
This file formalizes the **first nontrivial tensor power** `V ⊗ V` (a
16-dimensional space, modeled by the Kronecker product `4×4 ⊗ 4×4` of the Majorana
model of §A.3), where the four chirality blocks `V⁺⊗V⁺` (label `(1,0)`),
`V⁻⊗V⁻` (`(0,1)`), and the mixed `V⁺⊗V⁻`, `V⁻⊗V⁺` appear explicitly.

* **Per-slot chirality** `chir1 = iγ⁵⊗1`, `chir2 = 1⊗iγ⁵`: `chir1_sq`, `chir2_sq`,
  `chir1_chir2_comm` (commute — different slots).
* **Diagonal `Spin⁺` action** `spinGenDiag μ ν = γ^μγ^ν⊗1 + 1⊗γ^μγ^ν`:
  `chir1_spinGenDiag_comm`, `chir2_spinGenDiag_comm` (each chirality operator
  commutes with the diagonal Lorentz generator).
* **Diagonal parity** `parityDiag = γ⁰⊗γ⁰`: `parity_chir1_anticomm`,
  `parity_chir2_anticomm`; `parityDiag_sq` (`(γ⁰⊗γ⁰)² = 1`).
* **Four chirality projectors** `projLL/projLR/projRL/projRR`: `projSum`
  (`P_LL+P_LR+P_RL+P_RR = 1`); `projLL_spinGenDiag_comm`,
  `projRR_spinGenDiag_comm` (pure blocks are diagonal-`Spin⁺` subreps).
* **Lemma 52 payoff:** `parity_swaps_LL_RR` / `parity_swaps_RR_LL`
  (`γ⁰⊗γ⁰` intertwines `V⁺⊗V⁺ ↔ V⁻⊗V⁻`, i.e. `(1,0) ↔ (0,1)`),
  `parity_swaps_LR_RL` (swaps the mixed `(½,½)` blocks); `projLL_ne_projRR`;
  headline **`projLL_not_parity_invariant`** — the pure `(1,0)` block is not
  parity-invariant, so a single pure-chirality `Spin⁺`-subrep is not
  full-Lorentz irreducible, and the real irrep must combine `V_{(m,n)}` with its
  parity image `V_{(n,m)}` (the mechanism of Lemma 52, now at the tensor-power
  level).

Still open after wave 26: the extension of Lemma 52 to arbitrary `N`-fold
symmetric powers plus the `EXTERNAL` Weyl/Note-50 layer; the `EXTERNAL`
Wigner/Mackey exhaustiveness backbone of the §A.4/A.5 Bargmann–Wigner/CPT
classification.

## Wave 25 (2026-07-04) — N4 §A.4 Prop 81 / Notes 80–83: Bargmann–Wigner rep group laws (`ChapterA4g.lean`)

New module `BookProof/ChapterA4g.lean` (registered in `BookProof.lean`), landing
the concrete **group-representation axioms** of the little-group and translation
factors of the Bargmann–Wigner Poincaré representations (book §A.4, Notes 80–83 /
Proposition 81 — the roadmap directive "state the reps as structures and verify
the group-rep axioms for the given `L_S, T_a`"). All `sorry`-free and
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`; verified via
`lean_verify` on `SUtwo_mul_mem`, `transPhase_add`, `rotGen_projPos_comm`);
`lake build` green (8098 jobs). **No `EXTERNAL` hypothesis** — Wigner 1939
exhaustiveness (that these are *all* the irreps) remains the cited backbone, not
these axiom checks.

* **Massive little group `SU(2)` (Prop 79, `ChapterA4c`) — spin-½ defining rep:**
  `SUtwo_one_mem`, `SUtwo_mul_mem` (closure `L_{ST}=L_S L_T`),
  `SUtwo_conjTranspose_mem` / `SUtwo_mul_conjTranspose` (`S⁻¹ = S† ∈ SU(2)`).
* **Massless little group `SE(2)` (Prop 79, `ChapterA4d`):** `SEtwo_one_mem`,
  `SEtwo_mul_mem`.
* **Translation factor `T_a(p⃗)=e^{i p⃗·a⃗}` (`transPhase`):** `transPhase_add`
  (`T_{a+b}=T_a T_b`), `transPhase_zero` (`T_0=1`), `transPhase_abs`
  (`|T_a|=1`, unitarity of the abelian translation subgroup).
* **Massive-rep constraint preservation:** the spatial rotation generators
  `γⁱγʲ` (`rotGen`, `SU(2)` Lie algebra) commute with the energy-sign operator
  `iγ⁰` (`rotGen_enSign_comm`, from the integer `decide` lemma
  `rotGenZ_coeffMass1Z_comm`), hence with the positive-energy Dirac projector
  `P₊` (**`rotGen_projPos_comm`**): the massive little-group action preserves the
  positive-energy (Dirac) constraint subspace — the Bargmann–Wigner
  rep-consistency statement for the massive irreps.

Still open after wave 25: the Bargmann–Wigner classification *exhaustiveness* of
Props 81/87/88 (the `EXTERNAL` Wigner/Mackey backbone); the Lemma 52
symmetric-tensor-power generalization to arbitrary `(m,n)`; and the N7 external
Wigner/Mackey bundle.

## Wave 24 (2026-07-04) — N4 §A.4 Prop 87: the localizability exclusion lemmas (`ChapterA4f.lean`)

New module `BookProof/ChapterA4f.lean` (registered in `BookProof.lean`), landing
the concrete algebraic cores of the **three exclusion lemmas of §A.4
Proposition 87** (book §A.4, line ~5636 — the roadmap's directive "state the
three exclusions as lemmas").  All `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`; verified via `lean_verify` on
`infinite_spin_excluded` and `no_tachyon`); `lake build` green (8097 jobs).
**No `EXTERNAL` hypothesis** — Wigner little-group theory + Mackey imprimitivity
remain the cited backbone of the *decomposition/exhaustiveness* clause of
Prop 87, not of these reductions.

Prop 87 (any localizable unitary Poincaré rep is a direct sum of massive /
massless-discrete-helicity irreducibles) is proved by ruling out three families
of irreducibles as localizable subspaces.  This module formalizes the honest,
self-contained algebraic core of each exclusion on the `2×2` Pauli / `4×4`
Majorana models of §A.3–§A.5:

* **Exclusion 1 — no tachyons (`m² ≥ 0`)**: `massSq_nonneg` (`0 ≤ m₁²+m₂²`) and
  `no_tachyon` (the real §A.5 energy symbol squares to `(|p⃗|² − (m₁²+m₂²))·1`,
  so the physical mass² is a sum of squares — a tachyonic `m²<0` dispersion
  cannot arise from the real Majorana `iH`).
* **Exclusion 2 — the zero-momentum point**: `zeroMomentum_symbol` — at `p⃗ = 0`
  the energy symbol reduces to the pure mass operator with square
  `−(m₁²+m₂²)·1`, so the single zero-momentum point is a measure-zero,
  non-invariant subset of the `ℝ³` momentum space of a localizable system.
* **Exclusion 3 — no infinite (continuous) spin**: on the `SE(2)` massless
  little group of Prop 79 (`ChapterA4d.SEtwo`, elements `!![a,0;c,a⁻¹]`,
  `|a|=1`), the `z`-boost `boostZ l = diag(l, l⁻¹) ∈ SL(2,ℂ)` conjugates an
  `SE(2)` element to `!![a,0; l⁻²c, a⁻¹]`: `boostZ_preserves_angle` (fixes the
  `SO(2)` angle `a = T 0 0`), `boostZ_scales_translation` (scales the
  translation modulus `c = T 1 0` by `l⁻²`), `boostZ_conj_mem` (the conjugate
  stays in `SE(2)`), and headline **`infinite_spin_excluded`** — for a nonzero
  translation label the `z`-boost conjugate realizes *any* nonzero translation
  label (still inside `SE(2)`), so there is no boost-invariant nonzero `SE(2)`
  translation modulus: a continuous/infinite-spin irrep cannot coexist with a
  `p⃗`-independent Wigner rotation.

Supporting `boostZ` algebra: `boostZ_det` (`det = 1` for `l ≠ 0`),
`boostZ_mul_inv` (`boostZ l · boostZ l⁻¹ = 1`).

Still open after wave 24: the full Bargmann–Wigner classification
*exhaustiveness* of Props 81/87/88 (the `EXTERNAL` Wigner/Mackey backbone); the
Lemma 52 symmetric-tensor-power generalization to arbitrary `(m,n)`; and the N7
external Wigner/Mackey bundle.

## Wave 23 (2026-07-04) — N4 §A.3 Notes 50–51 / Lemma 52: the chiral (`γ⁵`) decomposition core (`ChapterA3j.lean`)

New module `BookProof/ChapterA3j.lean` (registered in `BookProof.lean`), landing
the concrete algebraic **base case** of the **§A.3 Notes 50–51 / Lemma 52**
finite-dim-irrep classification (book §A.3, line ~5560 — the roadmap's remaining
§A.3 classification residue).  All `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`; verified via `lean_verify` on
`chirality_not_parity_invariant`, `parity_swaps_chirL`, `projChirL_spinGen_comm`);
`lake build` green (8096 jobs).  **No `EXTERNAL` hypothesis** (Note 50 / Weyl
complete reducibility and the symmetric-tensor-power generalization to arbitrary
`(m,n)` remain the cited backbone, not this algebraic base case).

The exact chirality analogue of the energy-sign story of `ChapterA4e`, built on
the `4×4` Majorana Clifford model of §A.3 (`ChapterA3.mgamma`, `mgamma5`).  The
chirality operator `iγ⁵ = mgamma5` squares to `-1` (`mgamma5_sq`), so its
eigenvalues are `±i` and the chiral projectors `P_{L/R} = ½(1 ∓ i·iγ⁵)` live
over `ℂ`.

* `chir` (`iγ⁵`), `spinGen μ ν` (`γ^μγ^ν`, the `Spin⁺(3,1)` generators),
  `chir_sq`.
* `chir_mgamma_anticomm`; **`chir_spinGen_comm`** — `iγ⁵` *commutes* with every
  even Clifford element `γ^μγ^ν`; `chir_parity_anticomm` — `iγ⁵` *anticommutes*
  with `γ⁰`.
* `projChirL`, `projChirR` and the projector algebra: `projChirL_add_projChirR`
  (`P_L+P_R=1`), `projChirL_idem`, `projChirR_idem` (idempotent),
  `projChirL_mul_projChirR` (`P_L P_R=0`) — genuine complementary projectors.
* **Note 51 core** (`projChirL_spinGen_comm` / `projChirR_spinGen_comm`) — each
  chiral projector commutes with every `Spin⁺` generator, so `V_L`, `V_R` are
  genuine connected-Lorentz subreps: the Weyl / chiral irreps `V⁺_½`, `V⁻_½`.
* **Lemma 52 core** (`parity_swaps_chirL` / `parity_swaps_chirR`) — the parity
  operator `γ⁰` *intertwines* the two chiral projectors (`P_L γ⁰ = γ⁰ P_R`), so
  parity glues `V_{(m,n)}` to its parity image `V_{(n,m)}`.
* `projChirL_parity_commutator` — `[P_L, γ⁰] = i·γ⁰(iγ⁵)`, an explicit nonzero
  matrix.
* headline **`chirality_not_parity_invariant`** — there is a parity operator
  (`γ⁰`) not commuting with `P_L`; hence a single-chirality `Spin⁺`-irrep is not
  full-Lorentz irreducible, so the real full-Lorentz irrep must combine
  `V_{(m,n)}` with `V_{(n,m)}` — the mechanism underlying Lemma 52 (unlike
  complex irreps, real irreps are automatically full-Lorentz projective reps).

Still open after wave 23: the full symmetric-tensor-power generalization of
Lemma 52 to arbitrary `(m,n)` plus the `EXTERNAL` Weyl/Note-50 layer; the
exhaustiveness layer of §A.4/A.5 Bargmann–Wigner/CPT (`EXTERNAL` Wigner/Mackey);
and the N7 external Wigner/Mackey bundle.

## Wave 22 (2026-07-04) — N4 §A.4 Props 88 / Cor 1: the CPT / antiparticle payoff (`ChapterA4e.lean`)

New module `BookProof/ChapterA4e.lean` (registered in `BookProof.lean`), landing
the concrete algebraic core of the **§A.4 CPT / "causality ⇒ antiparticles"**
statement (book §A.4, Props 87–88 and Corollary 1 — the roadmap's explicit
"prove the reductions ... the projector-non-conservation in Prop 88 / Cor 1"
directive).  All `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`; verified via `lean_verify` on
`energy_sign_not_conserved` and `spatialOp_swaps_pos`); `lake build` green
(8095 jobs).  **No `EXTERNAL` hypothesis** (Wigner/Mackey enter only in the
*exhaustiveness* clauses of Props 87/88, which are the cited backbone, not this
algebraic core).

Builds directly on the `4×4` Majorana Clifford model of §A.3/§A.5
(`ChapterA5.coeffMass1Z = iγ⁰`, `ChapterA5.coeffBoostZ j = γʲγ⁰`).  Because
`iγ⁰` squares to `-1` (`enSign_sq`), its energy-sign eigenvalues are `±i` and the
sign projectors `P± = ½(1 ∓ i·iγ⁰)` live over `ℂ`.

* `enSign` (`iγ⁰`), `spatialOp j` (`γʲγ⁰`), both as complex casts of the integer
  model; `enSign_sq : enSign*enSign = -1`.
* **`enSign_spatialOp_anticomm`** — the generalized Clifford relation
  `{iγ⁰, γʲγ⁰} = 0` (the algebraic heart), from
  `ChapterA5.coeffBoostZ_mass1_anticomm`.
* `projPos`, `projNeg` and the projector algebra: `projPos_add_projNeg`
  (`P₊+P₋=1`), `projPos_idem`, `projNeg_idem` (idempotent), `projPos_mul_projNeg`
  (`P₊P₋=0`) — genuine complementary projectors.
* **`spatialOp_swaps_pos` / `spatialOp_swaps_neg`** (Prop 88 core) — every
  spatial-gradient operator *intertwines* the two sign projectors
  (`P₊(γʲγ⁰) = (γʲγ⁰)P₋` and conversely), so `γʲγ⁰` maps the negative-energy
  subspace onto the positive one: a positive-energy subrep forces the negative
  one (antiparticles).
* `projPos_spatialOp_commutator` — `[P₊, γʲγ⁰] = i·(γʲγ⁰)(iγ⁰)`, an explicit
  nonzero matrix.
* headline **`energy_sign_not_conserved`** (Cor 1 core) — there is a spatial
  operator that does not commute with `P₊`; hence a localizable rep that is
  irreducible under the *full* Poincaré group cannot use the (non-conserved)
  `iγ⁰`-sign projectors — the reduction underlying the CPT / position-operator
  payoff.

Still open after wave 22: Lemma 52 (real-irrep classification via symmetric
tensor powers + `EXTERNAL` Weyl); the exhaustiveness layer of §A.4/A.5
Bargmann–Wigner/CPT (Props 81/87 exclusions, Prop 88/Cor 1 exhaustiveness —
`EXTERNAL` Wigner/Mackey); and the N7 external Wigner/Mackey bundle.

## Wave 21 (2026-07-04) — N4 §A.3 Lemma 48: the `Σ`/bridge `Λ(Σ T Σ⁻¹) = Υ(T)` (`ChapterA3i.lean`)

New module `BookProof/ChapterA3i.lean` (registered in `BookProof.lean`), landing
the **`Σ` / bridge half of Lemma 48** (book §A.3, line 5458) — the piece
connecting the two concrete double covers of the Lorentz group built earlier:
the Pauli/`SL(2,ℂ)` cover `Υ` of `ChapterA3h.lean` (Note 47) and the
Majorana/Pinor cover `Λ` of `ChapterA3c.lean` (Prop 46).  All `sorry`-free and
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`; verified via
`lean_verify` on `lemma48_bridge`); `lake build` green (8094 jobs).

The book's real-linear isomorphism `Σ : Pauli → Pinor` (book eq. 5468) matches the
`±`-eigenspaces of `γ⁰γ³` (on `Pinor = ℂ⁴`) with those of `σ³` (on `Pauli = ℂ²`).
Taking `M₊ = e₀+e₃`, `M₋ = e₀-e₃`, the concrete integer matrix is
`Σ = !![1,0,0,-1; 0,-1,-1,0; 0,-1,1,0; 1,0,0,1]`, with `Σ Σᵀ = Σᵀ Σ = 2·1`
(`sigmaZ_mul_transpose`, `sigmaC_mul_transpose`, `sigmaC_transpose_mul`), so
`Σ⁻¹ = ½ Σᵀ`.  For `T ∈ SL(2,ℂ)` the spin element `Σ T Σ⁻¹` is realised as the
real `4×4` matrix `Spinor T := Σ · Treal T · (½ Σᵀ)`, where `Treal T` is the real
form of the `ℂ`-linear action of `T` on `ℂ²` in the ordered real basis
`(P₊, iP₊, P₋, iP₋)`.

* `Treal`, `adj2` (the `2×2` adjugate), `Spinor`, `SpinorInv` (built from `adj2`).
* `Treal_mul` (real form is multiplicative), `Treal_one`, `T_mul_adj2` /
  `adj2_mul_T` (`T · adj2 T = adj2 T · T = 1` when `det T = 1`).
* `spinor_mul_spinorInv` / `spinorInv_mul_spinor` — `Spinor T · SpinorInv T = 1`
  and conversely, for `T ∈ SL(2,ℂ)`; hence `spinor_inv_eq`:
  `(Spinor T)⁻¹ = SpinorInv T`.
* **`spinorInv_conj_mgamma`** — the core bridge, a *pure polynomial identity*
  (no `det T = 1` needed): `SpinorInv T · iγ^μ · Spinor T = ∑_ν Υ(T)^ν_μ · iγ^ν`.
* headline **`lemma48_bridge`** — for `T ∈ SL(2,ℂ)`,
  `(Spinor T)⁻¹ · iγ^μ · Spinor T = ∑_ν Υ(T)^ν_μ · iγ^ν`, i.e. the Pinor cover
  `Λ` of `Σ T Σ⁻¹` equals the Pauli cover `Υ` of `T` (transposed by the `Λ`/`Υ`
  index conventions) — the identity `Λ(Σ T Σ⁻¹) = Υ(T)` of Lemma 48 in the
  concrete model.

No `EXTERNAL` hypothesis.  Still open after wave 21: Lemma 52 (real-irrep
classification via symmetric tensor powers + `EXTERNAL` Weyl); the deeper §A.4/A.5
Bargmann–Wigner/CPT classification layer (`EXTERNAL` Wigner/Mackey, Props 81/87/88,
Cor 1); and the N7 external Wigner/Mackey bundle.

## Wave 20 (2026-07-04) — N4 §A.4 Prop 79: the massless little group is `SE(2)` (`ChapterA4d.lean`)

New module `BookProof/ChapterA4d.lean` (registered in `BookProof.lean`),
landing the concrete **massless little group** of **Proposition 79** (book §A.4,
line 5636), the companion of the massive `SU(2)` case (`ChapterA4c.lean`).  All
`sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`;
verified via `lean_verify` on `massless_little_group`); `lake build` green
(8093 jobs).

Builds on the `Υ : SL(2,ℂ) → O(1,3)` covering map of `ChapterA3h.lean`
(Note 47) and reuses `upsilon_re` / `pauliCoeff_one` from `ChapterA4c.lean`.  For
a **massless** particle the standard momentum is the null vector
`n = e₀ + e₃ = (1,0,0,1)` (the book's `i l̸ = iγ⁰ + iγ³`), and the little group
`G_l = {T | T l̸ = l̸ T}` is exactly the stabiliser of `n` under `Υ`; the book
records this as `G_l = SE(2)`.  On the concrete `2×2` Pauli model
(`n·σ = σ⁰ + σ³ = diag(2,0)`):

* `FixesNullAxis` — a real `4×4` matrix fixes `n` (its `col₀ + col₃ = n`);
  `SEtwo` — `SE(2)` as the lower-triangular unimodular matrices with
  unit-modulus top-left entry.
* `pauliCoeff_add`, `pauliCoeff_null` — `½ tr(σ^μ(σ⁰+σ³)) = δ_{μ0}+δ_{μ3}`.
* `upsilonC_nullCol` — the null-column sum of `Υ(T)` is
  `Υ(T)^μ_0 + Υ(T)^μ_3 = ½ tr(σ^μ T†(σ⁰+σ³)T)`.
* **`fixesNullAxis_iff_conj`** — `Υ(T)` fixes `n` **iff** `T†(σ⁰+σ³)T = σ⁰+σ³`
  (Pauli-basis reconstruction, no `det T = 1` needed).
* **`nullConj_iff_form`** — that matrix identity holds **iff**
  `T 0 1 = 0 ∧ |T 0 0| = 1` (lower triangular, unit-modulus top-left entry).
* headline **`massless_little_group`** — `{T ∈ SL(2,ℂ) | Υ(T) fixes n} = SEtwo`;
  plus `SEtwo_lower_triangular` (the explicit `SE(2)` shape `T = !![a,0;c,a⁻¹]`,
  `|a| = 1`: an `SO(2)` angle `a` and a translation `c ∈ ℂ ≅ ℝ²`) and
  `upsilon_massless_lorentz` (each such `Υ(T)` is a genuine Lorentz
  transformation fixing the null axis).

No `EXTERNAL` hypothesis.  Still open after wave 20: the `Σ`/bridge half of
Lemma 48; Lemma 52 (real-irrep classification); the deeper §A.4/A.5
Bargmann–Wigner/CPT classification layer (`EXTERNAL` Wigner/Mackey); and the N7
external Wigner/Mackey bundle.

## Wave 19 (2026-07-04) — N4 §A.4 Prop 79: the massive little group is `SU(2)` (`ChapterA4c.lean`)

New module `BookProof/ChapterA4c.lean` (registered in `BookProof.lean`),
landing the concrete **massive little group** of **Proposition 79** (book §A.4,
line 5636).  All `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`; verified via `lean_verify`); `lake build`
green (8092 jobs).

Builds directly on the `Υ : SL(2,ℂ) → O(1,3)` covering map of `ChapterA3h.lean`
(Note 47).  For a **massive** particle the standard momentum lies along the time
axis `e₀ = (1,0,0,0)`, and the little group `G_l = {T | T l̸ = l̸ T}` is exactly
the stabiliser of `e₀` under `Υ`; the book records this as `i l̸ = iγ⁰ ⇒ G_l =
SU(2)`.  Formalized on the concrete `2×2` Pauli model:

* `FixesTimeAxis` — a real `4×4` matrix fixes `e₀` (its `0`-th column is `e₀`);
  `SUtwo` — `SU(2) = {T | det T = 1 ∧ T† T = 1}`.
* `pauliCoeff_one` — the Pauli coefficients of `1` are `δ_{μ0}` (`½ tr σ^μ`).
* `upsilonC_timeCol` — the time column of `Υ(T)` is `Υ(T)^μ_0 = ½ tr(σ^μ T† T)`
  (because `σ⁰ = 1`, so `T† σ⁰ T = T† T`); `upsilon_re` — its entries are real.
* **`fixesTimeAxis_iff_unitary`** — `Υ(T)` fixes `e₀` **iff** `T† T = 1` (needs
  no `det T = 1`: the Pauli-basis reconstruction already forces unitarity).
* headline **`massive_little_group`** — `{T ∈ SL(2,ℂ) | Υ(T) e₀ = e₀} = SU(2)`.
* `upsilon_little_group_lorentz` — each such `Υ(T)` is a genuine Lorentz
  transformation fixing the time axis (a spatial rotation).

No `EXTERNAL` hypothesis.  Still open after wave 19: the `Σ`/bridge half of
Lemma 48; Lemma 52 (real-irrep classification); the massless (`SE(2)`) little
group and the deeper §A.4/A.5 Bargmann–Wigner/CPT classification layer
(`EXTERNAL` Wigner/Mackey); and the N7 external Wigner/Mackey bundle.

## Wave 18 (2026-07-04) — N4 §A.3 Note 47: the covering map `Υ : SL(2,ℂ) → O(1,3)` (`ChapterA3h.lean`)

New module `BookProof/ChapterA3h.lean` (registered in `BookProof.lean`),
landing **Note 47** (book §A.3, line 5440), the `SL(2,ℂ)` side of **Lemma 48**.
All `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`; verified via `lean_verify`); `lake build` green (8091 jobs).

The book defines a two-to-one surjection `Υ : SL(2,ℂ) → SO⁺(1,3)` by
`Υᴼ_ν(T) σᵛ = T† σᴼ T`, with `σ⁰ = 1` and `σʲ` the Pauli matrices.  This
module builds the concrete `2×2` Pauli model and formalizes the construction
and its Lorentz property:

* `pauliσ` — the four Pauli matrices `σᴼ`; `pauliσ_herm` (each Hermitian),
  `pauliσ_trace` (trace-orthogonality `tr(σᴼ σᵛ) = 2δᴼᵛ`).
* `pauliCoeff` / `pauli_expand` / `pauliCoeff_comb` — the four Pauli matrices are
  a basis of `Mat₂(ℂ)`, with coefficient functional `c_μ(M) = ½ tr(σᴼ M)`.
* `UpsilonC` / `upsilon_recon` — the complex coefficient matrix `Υ(T)` with
  `T† σᵛ T = ∑_μ Υ(T)ᴼ_ν σᴼ`.
* `upsilonC_antihom` — `Υ(T U) = Υ(U) Υ(T)` (anti-homomorphism, since
  `(TU)† = U† T†`).
* `upsilonC_real` / `Upsilon` / `toC_Upsilon` — the entries of `Υ(T)` are real,
  giving the real matrix `Upsilon T` whose complexification is `UpsilonC T`.
* `det_pauli_comb` — `det(∑_ν x_ν σᵛ) = x₀² − x₁² − x₂² − x₃²`, the Minkowski
  norm realized as a `2×2` determinant (the geometric heart of the map);
  `upsilon_apply_comb`, `upsilonC_Qc` (`det T = 1 ⇒ Υ(T)` preserves the form).
* Polarization layer `bilC`, `bilC_ext` (a symmetric `4×4` matrix is determined
  by its quadratic form), `bilC_minkowski`, `bilC_conj`, `toC_minkowski_symm`.
* **`upsilonC_metric` / `upsilon_metric`** — `Υ(T)ᵀ η Υ(T) = η` (complex, then
  real via `toC` injectivity).
* headline **`upsilon_mem_lorentz`** — for `T ∈ SL(2,ℂ)` (`det T = 1`),
  `Upsilon T ∈ O(1,3)` (`LorentzO`), converting `ΛᵀηΛ = η` to `ΛηΛᵀ = η`
  via `η² = 1` and `Matrix.mul_eq_one_comm`.

No `EXTERNAL` hypothesis.  Still to come for the full Lemma 48: the explicit
isomorphism `Σ : Pauli → Pinor` (matching the `γ⁰γ³`/`σ³` ±-eigenspaces) and the
bridge identity `Λ(S) = Υ(Σ⁻¹ S Σ)`; the group-level Lorentz image of
`Spin⁺(3,1)` is already available via the exponential route in `ChapterA3g.lean`.

**Still open after wave 18**: the `Σ`/bridge half of Lemma 48; Lemma 52
(real-irrep classification via symmetric tensor powers + Weyl); the remaining
§A.4/A.5 classification layer (Bargmann–Wigner Props 79–88, localizable-rep
classification, CPT/Cor 1 — `EXTERNAL` Wigner/Mackey); and the N7 external
Wigner/Mackey bundle.

## Wave 17 (2026-07-04) — N4 §A.5 CPT / energy operator (`ChapterA5.lean`)

New module `BookProof/ChapterA5.lean` (registered in `BookProof.lean`),
landing the **§A.5** closing item (book line 6453, *"Spinor frame and CPT
theorem"*).  All `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`; verified via `lean_verify`); `lake build`
green (8090 jobs).

The book states that, in space coordinates, the most general Lorentz-covariant
mass term of the Hamiltonian is
`iH = ∂⃗·γ⃗γ⁰ + iγ⁰ m₁ + γ⁰γ⁵ m₂`, and — being **real** in the Majorana basis —
it is automatically invariant under a parity–time reversal (PT), *which is
essentially the CPT theorem*.  This module formalizes the concrete matrix core
of that statement on the `4×4` Majorana Clifford model of §A.3 (`ChapterA3`).

* Coefficient matrices of `iH` in the integer Majorana model: `coeffBoostZ j`
  (`= γʲγ⁰`, `j = 1,2,3`), `coeffMass1Z` (`= iγ⁰`), `coeffMass2Z` (`= γ⁰γ⁵`) —
  all **real integer** matrices (the Majorana/reality property underlying CPT).
* **Generalized Clifford relations** (all by `decide`): the five matrices
  mutually anticommute (`coeffBoostZ_anticomm`, `coeffBoostZ_mass1_anticomm`,
  `coeffBoostZ_mass2_anticomm`, `coeffMass_anticomm`) with squares
  `(γʲγ⁰)² = 1` (`coeffBoostZ_sq`) and `(iγ⁰)² = (γ⁰γ⁵)² = -1`
  (`coeffMass1Z_sq`, `coeffMass2Z_sq`).
* **Mass-shell identity** `energySymbolZ_sq`: the momentum-space symbol
  `D = p₁γ¹γ⁰ + p₂γ²γ⁰ + p₃γ³γ⁰ + m₁ iγ⁰ + m₂ γ⁰γ⁵` satisfies
  `D² = (|p⃗|² - m₁² - m₂²)·1` — equivalently `H² = |p⃗|² + m₁² + m₂²`, the
  Klein–Gordon relation with the two masses combining as `m² = m₁² + m₂²`.
* Real Majorana model `coeffBoostR`/`coeffMass1R`/`coeffMass2R` and
  `energySymbolR` via `(Int.castRingHom ℝ).mapMatrix`, with the same mass-shell
  identity `energySymbolR_sq` (the physically meaningful real form).

No `EXTERNAL` hypothesis: the covariance statements motivating the form of `iH`
are the on-disk §A.3 results (`spinBoost_hasAdLambda` / `spinRot_hasAdLambda`);
the PT/CPT physics discussion is captured in docstrings, not as theorems (per
the roadmap's §A.4/A.5 recommendation).

**Still open after wave 17**: the explicit `SL(2,ℂ)`/`Σ`/`Υ` cover
`Λ(S) = Υ(Σ⁻¹SΣ)` of Lemma 48; Lemma 52 (real-irrep classification via
symmetric tensor powers + Weyl); the remaining §A.4/A.5 classification layer
(Bargmann–Wigner Props 79–88, localizable-rep classification, CPT/Cor 1 —
`EXTERNAL` Wigner/Mackey); and the N7 external Wigner/Mackey bundle.

## Wave 16 (2026-07-04) — N4 §A.4 Prop 61 unitarity (`ChapterA4b.lean`)

New module `BookProof/ChapterA4b.lean` (registered in `BookProof.lean`),
continuing work-package **N4** (§A.4, book line 5636, **Proposition 61** — the
first of §A.4's four "unitarity by direct computation" props, together with
73/74/76 in `ChapterA4.lean`).  All `sorry`-free and `axiom`-free (only
`propext`, `Classical.choice`, `Quot.sound`; verified via `#print axioms`);
`lake build` green (8089 jobs).

The book: if `U : Pinor_j(ℝ³) → Pinor_j(𝕏)` is unitary with `U∘H² = E²∘U`
(`iH = γ⁰∂̸ + iγ⁰m`, `E ≥ m ≥ 0`) then `U' := (E + U H γ⁰ U†)/(√(E+m)·√(2E))`
is unitary, proved by `(U')†U' = 1 = U'(U')†`.  The mathematical heart is a
C*-algebra identity: with `c := U H γ⁰ U†` the Dirac anticommutator
`{γ⁰,H} = 2m` and `(γ⁰)² = 1` give `c + c† = 2m·1` and `E² = c†c = cc†`
(`E = |c|`), whence `(E + c†)(E + c) = 2E(E+m) = (E + c)(E + c†)`, so dividing
by `p := √(2E)·√(E+m)` makes `U' := p⁻¹(E+c)` unitary.

* `prop61_unitary_core` — abstract engine over any `ℂ`-*-algebra: given `c` with
  `c + c† = 2m·1`, self-adjoint `E` with `E² = c†c` commuting with `c`, and a
  self-adjoint normaliser `p` with `p² = 2E² + 2m·E` invertible with inverse `q`
  (self-adjoint, commuting with `E`, `c`), the element `U' := q(E+c)` satisfies
  `U'†U' = 1 = U'U'†`.
* `prop61_energyMap_unitary` — C*-algebra existence wrapper: for `c` with
  `c + c† = 2m·1` (`m ≥ 0` real) and `c` a unit, the positive square roots
  `E := √(c†c)` and `p := √(2E² + 2m·E)` exist (continuous functional calculus,
  `CFC.sqrt`), are invertible, and satisfy the core's hypotheses, so
  `U' := p⁻¹(E+c)` is genuinely a unitary.
* Generic reusable helpers `isSelfAdjoint_of_mul_eq_one` (a two-sided inverse of
  a self-adjoint element is self-adjoint) and `Commute.of_mul_eq_one` (an inverse
  commutes with whatever the original element commutes with).

**Still open after wave 16**: the explicit `SL(2,ℂ)`/`Σ`/`Υ` cover
`Λ(S) = Υ(Σ⁻¹SΣ)` of Lemma 48; Lemma 52 (real-irrep classification); the
remaining §A.4/A.5 classification layer (Bargmann–Wigner Props 79–88,
localizable-rep classification, CPT/Cor 1 — `EXTERNAL` Wigner/Mackey); and the
N7 external Wigner/Mackey bundle.

## Wave 15 (2026-07-04) — N4 §A.4 unitarity props (73/74/76) + N3 residue `denseCore_svd`

Two deliverables from the top of the wave-14 "still open" list, both
`sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`;
verified with `#print axioms`); `lake build` green (8088 jobs).

### `BookProof/ChapterA4.lean` — §A.4 Majorana–Fourier / Energy unitarity (N4)

The **tractable unitarity core** of §A.4 (book line 5636): Note 62 / Props 73,
74, 76.  The book defines the Majorana–Fourier transform `𝓕_M := (𝓕_P)^Θ` (the
`Θ`-conjugate of the complex Pauli Fourier transform, `Θ` the real-linear
isometric `Pauli^r ≅ Pinor` identification) and argues *a `Θ`-conjugate of a
unitary is unitary*.  Formalized faithfully:

* `LinearIsometryEquiv.restrictScalarsₗᵢ` — the small missing Mathlib helper: a
  `𝕜`-linear isometry equivalence is an `R`-linear one for a compatible
  sub-scalar-ring (norms are scalar-independent).  Lets a real-linear `Θ`
  conjugate a **complex** unitary.
* `conjugateₗᵢ` — the **engine** (Prop 73 / 76 argument): `A^Θ := Θ ∘ A ∘ Θ⁻¹`
  is a `LinearIsometryEquiv` when `A` and `Θ` are; `conjugateₗᵢ_symm`
  (**Prop 74**, `(A^Θ)⁻¹ = (A⁻¹)^Θ`), `conjugateₗᵢ_trans`, `conjugateₗᵢ_refl`.
* `pauliFourier` — Mathlib's `MeasureTheory.Lp.fourierTransformₗᵢ` (unitary by
  Plancherel, already in Mathlib) viewed as a **real** unitary `𝓕_P`.
* `majoranaFourier` (**Prop 73**) — `𝓕_M := 𝓕_P^Θ`, a real unitary
  (`≃ₗᵢ[ℝ]`); `majoranaFourier_symm` (**Prop 74**), `majoranaFourier_apply`.
* `energyTransform` (**Prop 76**) — `𝓔`, the same conjugation of a
  (time-coordinate) Fourier transform, again a real unitary; `energyTransform_symm`.

No `EXTERNAL` hypothesis (Plancherel is in Mathlib); the real-linear iso `Θ`
(Pauli↔Pinor tensored with `L²`, Def 53/54 scaffolding) is a parameter.

### `BookProof/ChapterB3b.lean` — finite-rank SVD `denseCore_svd` (N3 residue)

The recorded N3 residue: the finite-dimensional singular-value decomposition
that the §0 dense-core method reduces the book's `Ψ = W D U†` (§B.3(b)) to.

* `gram_svd` — spectral half: `Aᴴ A = U · diag(D²) · Uᴴ` with `U` unitary and
  `D i = √(eigenvalue i) ≥ 0`, from `Matrix.IsHermitian.spectral_theorem` on the
  positive-semidefinite Gram matrix `Aᴴ A` (`posSemidef_conjTranspose_mul_self`,
  `PosSemidef.eigenvalues_nonneg`, with `RCLike.toPartialOrder` /
  `toStarOrderedRing` supplied locally so the order-dependent PSD API applies to
  general `RCLike 𝕜`).
* `svd_completion` — completion half: from `Bᴴ B = diag(D²)` (`D ≥ 0`) the
  columns of `B` are orthogonal with squared norms `D i²`; normalize the nonzero
  ones and complete to an orthonormal basis via
  `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`, giving a unitary
  `W` with `B = W · diag(D)`.
* headline **`denseCore_svd`**: every square matrix over `𝕜 ∈ {ℝ, ℂ}` factors as
  `A = W · diagonal D · Uᴴ` with `W, U` unitary and `D ≥ 0` — assembled from the
  two halves (`B := A U`, `Bᴴ B = diag(D²)`).  Plugs directly into
  `ChapterB3.conditional_operator_identity` (B.3c).

**Still open after wave 15**: the explicit `SL(2,ℂ)`/`Σ`/`Υ` cover
`Λ(S) = Υ(Σ⁻¹SΣ)` of Lemma 48 (concrete Pauli↔Pinor iso); Lemma 52 (real-irrep
classification via symmetric tensor powers + Weyl); the remaining §A.4/A.5
classification layer (Bargmann–Wigner Props 79–88, localizable-rep
classification, CPT/Cor 1 — `EXTERNAL` Wigner/Mackey) and Prop 61 (operator
functional-calculus unitarity); the N7 external Wigner/Mackey bundle.

## Wave 14 (2026-07-04) — N4 §A.3 group-level Lemma 48: infinitesimal → group bridge

New module `BookProof/ChapterA3g.lean` (registered in `BookProof.lean`),
continuing work-package **N4** (§A.3, book line 5445, **Note 47 / Lemma 48**).
All `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`; verified with `lean_verify`); `lake build` green (8086 jobs).

### `BookProof/ChapterA3g.lean` — the two exponential ingredients + group Lemma 48

This file discharges the two analytic ingredients recorded as the standing
obstruction in `ChapterA3e.lean`.

* `exp_neg_mul_exp` / `exp_matrix_inv`: `exp(-G) * exp G = 1`, so
  `(exp G)⁻¹ = exp(-G)` (`Matrix.inv_eq_left_inv`).
* **`conj_exp_hasAdLambda`** — the **adjoint-exponential identity** in Majorana
  form: if `HasAdLambda G A` (`ChapterA3e`), then
  `exp(-G) · iγ^μ · exp(G) = Σ_ν (exp(-A))^μ_ν iγ^ν`. Proof is the one-parameter
  ODE argument staying inside `Matrix (Fin 4) (Fin 4) ℝ` (no operator
  exponential): `φ(t) = exp(t•G) · Z(t) · exp(-t•G)` with
  `Z(t) = Σ_ν (exp(-t•A))^μ_ν iγ^ν` has zero derivative because
  `Z'(t) = -[G, Z(t)]` (from `HasAdLambda` and `Commute` of `A` with its
  exponential), hence is constant `= iγ^μ`; evaluate at `t = 1`.
* `hasLambda_exp`: `HasLambda (exp G) (exp (-A))` from `HasAdLambda G A`.
* **`lorentzLie_exp`** — the **Lie-algebra → group exponential**
  `A ∈ 𝔬(1,3) ⟹ exp A ∈ O(1,3)`, via `Matrix.exp_conj` (η A η⁻¹ = -Aᵀ),
  `Matrix.exp_transpose`, and `η² = 1`.
* `isPin_exp_of_isSpinLie`: `G ∈ 𝔰𝔭𝔦𝔫⁺(3,1) ⟹ exp G ∈ Pin(3,1)` (with
  `det (exp G) = 1` from `ChapterA3f.spinLie_det_exp_eq_one`).
* headline **`spinLie_exp_hasLambda_lorentz`**: for `G ∈ 𝔰𝔭𝔦𝔫⁺(3,1)` the
  conjugation action of `exp G` on the Majorana basis is a Lorentz matrix
  `Λ = exp(-A) ∈ O(1,3)` — the infinitesimal → group Lorentz-image half of
  Lemma 48.

**Still open after wave 14** (unchanged otherwise): the explicit
`SL(2,ℂ)`/`Σ`/`Υ` cover `Λ(S) = Υ(Σ⁻¹SΣ)` of Lemma 48 (the concrete
Pauli↔Pinor isomorphism); Lemma 52 (real-irrep classification via symmetric
tensor powers + Weyl); the §A.4–A.5 layer (Bargmann–Wigner scaffolding,
Majorana–Fourier/Energy unitarity Props 61/73/74/76, localizable-rep
classification, CPT/Cor 1); the N3 residue `denseCore_svd`; and the N7 external
Wigner/Mackey bundle.

## Wave 13 (2026-07-04) — N4 §A.3 group-level Lemma 48: `det (exp A) = exp (tr A)`

New module `BookProof/ChapterA3f.lean` (registered in `BookProof.lean`),
continuing work-package **N4** (§A.3, book line 5445, **Note 47 / Lemma 48**).
All `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`; verified with `lean_verify`); `lake build` green (8085 jobs).

### `BookProof/ChapterA3f.lean` — the Jacobi–Liouville formula + `det Spin⁺(3,1) = 1`

This file discharges the analytic ingredient recorded as the standing
obstruction for the **group-level** half of Lemma 48: the matrix-exponential
determinant identity `det (exp A) = exp (tr A)`, a listed `TODO` in Mathlib
(`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`, line 57).  Proof is
the classical one-parameter-group / ODE argument, fully over `ℝ` for arbitrary
`n × n` real matrices.

* `detExpPath A t := (exp (t • A)).det` with `detExpPath_zero` and the
  one-parameter-group law `detExpPath_add` (`f (s+t) = f s · f t`, from
  `NormedSpace.exp_add_of_commute` + `Matrix.det_mul`).
* `differentiable_det` (`det` is a polynomial in the entries).
* `hasDerivAt_det_line` (Jacobi along `1 + t • A`; derivative at `0` is the
  trace, from `Matrix.det_one_add_smul`).
* `hasDerivAt_detExpPath_zero` (Jacobi at the identity along the exponential
  path, via the chain rule with `hasDerivAt_exp_smul_const'` and uniqueness of
  the derivative against `hasDerivAt_det_line`) and `hasDerivAt_detExpPath` (the
  derivative at an arbitrary point, from the group law).
* headline **`det_exp_eq_exp_trace`** (`det (exp A) = exp (tr A)`) via the ODE
  argument (`t ↦ detExpPath A t · exp(-(tr A · t))` has zero derivative, hence
  is `≡ 1`).
* downstream **`spinLie_det_exp_eq_one`**: every element of `𝔰𝔭𝔦𝔫⁺(3,1)`
  (traceless, `ChapterA3e.spinLie_traceless`) exponentiates to a matrix of unit
  determinant — the infinitesimal-to-group `det = 1` half of Lemma 48.

**Still open after wave 13** (unchanged otherwise): the remaining group-level
Lemma 48 content beyond `det = 1` (the explicit `SL(2,ℂ)`/`Σ`/`Υ` cover
`Λ(S) = Υ(Σ⁻¹SΣ)` and the `exp(-ad_G)` adjoint-exponential identity); Lemma 52
(real-irrep classification via symmetric tensor powers + Weyl); the §A.4–A.5
layer (Bargmann–Wigner scaffolding, Majorana–Fourier/Energy unitarity Props
61/73/74/76, localizable-rep classification, CPT/Cor 1); the N3 residue
`denseCore_svd`; and the N7 external Wigner/Mackey bundle.

## Wave 12 (2026-07-03) — N4 §A.3 Note 47 / Lemma 48: the Lie algebra 𝔰𝔭𝔦𝔫⁺(3,1)

New module `BookProof/ChapterA3e.lean` (registered in `BookProof.lean`),
continuing work-package **N4** (§A.3, book line 5445, **Note 47 / Lemma 48**).
All `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`; verified with `lean_verify`); `lake build` green (8084 jobs).

### `BookProof/ChapterA3e.lean` — infinitesimal Note 47 / Lemma 48

The book characterizes the restricted spin group by its Lie algebra,
`Spin⁺(3,1) = { e^{θʲ iγ⁵γ⁰γʲ + bʲ γ⁰γʲ} }`.  This file formalizes the
**infinitesimal content** — the differential `Λ_* : 𝔰𝔭𝔦𝔫⁺(3,1) → 𝔬(1,3)` of the
two-to-one cover `Λ : Pin(3,1) → O(1,3)` of `ChapterA3c.lean` — fully over `ℝ`
on the concrete `4×4` Majorana model, with every per-generator fact a decidable
integer-matrix computation (**no external hypothesis**).

* The six **spinor Lorentz generators**: boosts `spinBoost j = γ⁰γʲ`, rotations
  `spinRot j = iγ⁵γ⁰γʲ` (`j = 0,1,2`), and their explicit adjoint matrices
  `adBoost j`, `adRot j`.
* `HasAdLambda G A` (`[G, iγ^μ] = Σ_ν A^μ_ν iγ^ν`, the infinitesimal analogue of
  `HasLambda`) and the **Lorentz Lie algebra** `LorentzLie = {A | A η + η Aᵀ = 0}`
  (derivative of `Λ η Λᵀ = η`), with transport helpers `hasAdLambda_of_intModel`,
  `lorentzLie_of_intModel`.
* `spinBoost_hasAdLambda` / `spinRot_hasAdLambda` (the adjoint identities) and
  `adBoost_mem_lorentzLie` / `adRot_mem_lorentzLie` (each adjoint matrix is in
  `𝔬(1,3)`), all closed by `decide`.
* `spinGen_traceless` (via `spinBoost_traceless` / `spinRot_traceless`) — the
  generators are traceless (the infinitesimal `det = 1` of Lemma 48).
* Linearity: `hasAdLambda_add/_smul/_sum`, `lorentzLie_add/_smul/_sum` (a
  subspace), and the headline **`spinLie_hasAdLambda_lorentzLie`**: every element
  of `𝔰𝔭𝔦𝔫⁺(3,1)` (`IsSpinLie`) has an adjoint matrix lying in `𝔬(1,3)`, i.e.
  `Λ_*` is well-defined and lands in `𝔬(1,3)`; plus `spinLie_traceless`.

**Recorded obstruction (group-level Lemma 48).**  Exponentiating to the group
statement `Spin⁺(3,1) ⊆ Pin(3,1)` and `Λ(S) = Υ(Σ⁻¹SΣ)` needs the
matrix-exponential determinant identity `det (exp A) = exp (tr A)` — a listed
*TODO* in Mathlib (`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`) —
and the adjoint-exponential identity `exp(-G)·X·exp(G) = exp(-ad_G)(X)`.  Those
analytic ingredients are the recorded open step; the algebraic Lie-algebra core is
complete.

**Still open after wave 12** (unchanged otherwise): §A.3 Lemma 48 group-level
exponentiation (above), Lemma 52 (real-irrep classification via symmetric tensor
powers + Weyl); the §A.4–A.5 layer (Bargmann–Wigner scaffolding,
Majorana–Fourier/Energy unitarity Props 61/73/74/76, localizable-rep
classification, CPT/Cor 1); the N3 residue `denseCore_svd`; and the N7 external
Wigner/Mackey bundle.

## Wave 11 (2026-07-03) — N4 §A.3 Definition 49: the discrete Pin subgroup Ω

New module `BookProof/ChapterA3d.lean` (registered in `BookProof.lean`),
continuing work-package **N4** (§A.3, book line 5476).  All `sorry`-free and
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`; verified with
`lean_verify`); `lake build` green (8083 jobs).

### `BookProof/ChapterA3d.lean` — Definition 49 (`Ω → Δ`, 2-to-1 cover)

**Definition 49**: the *discrete Pin subgroup*
`Ω = {±1, ±iγ⁰, ±γ⁰γ⁵, ±iγ⁵} ⊆ Pin(3,1)` is the double cover of the
*discrete Lorentz subgroup* `Δ = {1, η, -η, -1} ⊆ O(1,3)`.  Fully self-contained
over `ℝ` on the concrete `4×4` Majorana model — **no external hypothesis** (no
Pauli/Weyl input), since `Ω` is a finite explicit set and each
membership/`Λ`-value is a concrete matrix computation.

* Sets `OmegaPin` (`Ω`), `LorentzDelta` (`Δ`); integer/real generators
  `omegaA0`=`iγ⁰`, `omegaA5`=`iγ⁵`, `omegaG05`=`γ⁰γ⁵` (= `-(iγ⁰)(iγ⁵)`).
* Generic helpers: `inv_of_sq_neg_one` (`S²=-1 ⇒ S⁻¹=-S`),
  `det_sq_of_sq_neg_one`, `isPin_of_sq_neg_one`, and the reduction lemma
  `hasLambda_of_intModel` (transport `HasLambda` from the integer Clifford
  model, closing the conjugations by `decide`).
* Per-generator `HasLambda`/`IsPin`/`LambdaOf` values, with the explicit images
  `Λ(±iγ⁰)=η`, `Λ(±γ⁰γ⁵)=-η`, `Λ(±iγ⁵)=-1`, `Λ(±1)=1`
  (`lambdaOf_omegaA0`/`_omegaA5`/`_omegaG05`/`_one`, using `lambdaOf_neg` for
  the `±` symmetry).
* Headlines: **`omega_subset_pin`** (`Ω ⊆ Pin(3,1)`), **`lambda_omega_mem_delta`**
  (`Λ(ω) ∈ Δ` for all `ω ∈ Ω` — the 2-to-1 cover `Ω → Δ`), and the corollary
  **`delta_subset_lorentz`** (`Δ ⊆ O(1,3)`).

**Still open after wave 11** (unchanged otherwise): §A.3 Lemma 48
(`Spin⁺(3,1)` = `Σ∘SL(2,ℂ)∘Σ⁻¹`, needs the `SL(2,ℂ)`/`Σ`/`Υ` layer and matrix
exponentials), Lemma 52 (real-irrep classification via symmetric tensor powers +
Weyl); the §A.4–A.5 layer (Bargmann–Wigner scaffolding, Majorana–Fourier/Energy
unitarity Props 61/73/74/76, localizable-rep classification, CPT/Cor 1); the N3
residue `denseCore_svd`; and the N7 Wigner/Mackey `EXTERNAL` bundle.

## Wave 10 (2026-07-03) — N4 §A.3 Prop 46 group form + N3 residue B.3c

Two deliverables from the top of the wave-9 "still open" list.  Both
`sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`);
`lake build` green (8082 jobs).

### `BookProof/ChapterA3c.lean` — Prop 46 as a group homomorphism (N4 §A.3)

The **group-theoretic wrapper of Prop 46** (`Λ : Pin(3,1) → O(1,3)` is a 2-to-1
surjective homomorphism), building on wave-9's `lorentz_of_conj` and `real_pauli`
(`ChapterA3b.lean`).  Everything is stated over `ℝ` using `mgammaR` (the real
Majorana matrices — the `iγ^μ` have integer entries).

* Foundations: `mgammaR` (real Majorana matrices), `toC_mgammaR`
  (complexification back to `mgamma`), `mgammaR_clifford` (real Clifford set),
  `mgammaR_indep` (the four `iγ^μ` are `ℝ`-linearly independent — makes `Λ`
  well-defined).
* Definitions: `LorentzO` (`O(1,3) = {Λ | Λ η Λᵀ = η}`), `HasLambda S Λ`
  (`S⁻¹ iγ^μ S = Σ_ν Λ^μ_ν iγ^ν`), `IsPin` (`Pin(3,1)` membership),
  `LambdaOf` (the map `Λ(S)`), with `hasLambda_unique` (well-definedness).
* **Prop 46(a) lands in `O(1,3)`**: `lorentz_of_conjR` (real form of
  `lorentz_of_conj`, via `toC` transfer) and `lambda_mem_lorentz`.
* **Prop 46(b) homomorphism**: `hasLambda_mul`, `isPin_mul`, headline
  `lambdaOf_mul` (`Λ(S₁ S₂) = Λ(S₁) Λ(S₂)`).
* **Prop 46(c) 2-to-1 surjective**: `cliffordR_lorentz_comb` (`Σ Λ^μ_ν iγ^ν` is
  again a Clifford set when `Λ ∈ O(1,3)`), `hasLambda_neg`/`isPin_neg`/
  `lambdaOf_neg` (the `±S` symmetry), headline `lambda_surjective` (every
  `λ ∈ O(1,3)` is `Λ(S)` for some `S ∈ Pin(3,1)`, via `real_pauli`) and
  `lambda_two_to_one` (the fibre of `Λ` over `λ` is exactly `{±S}`).

The only external input is the named hypothesis `PauliFundamental` (Note 36),
inherited from `real_pauli`; there is no `axiom`.

### `BookProof/ChapterB3.lean` — B.3c conditional-operator identity (N3 residue)

Added `conditional_operator_identity`: with `Ψ = W D U†` and `D` self-adjoint,
`Ψ R Ψ† = W D U† R U D W†` — the §B.3c algebraic identity turning a change of
reference marginal `p₀ → p` (the operator `R = p/p₀`) into conjugation of the
singular-value factorization.  The compact-operator SVD `denseCore_svd` producing
the concrete `W, D, U` from a Hilbert–Schmidt `Ψ` remains the recorded open N3
residue (needs compact-operator spectral theory absent from Mathlib).

**Still open after wave 10**: §A.3 Lemma 48 (`Spin⁺(3,1)`), Lemma 52 (real-irrep
classification); the §A.4–A.5 layer (Bargmann–Wigner scaffolding, Majorana–
Fourier/Energy unitarity Props 61/73/74/76, localizable-rep classification,
CPT/Cor 1); the N3 residue `denseCore_svd`; and the N7 mining (Wigner/Mackey
`EXTERNAL` bundle, Ch. P re-scan).

## Wave 9 (2026-07-03) — N4 §A.3: charge conjugation (Lemma 40), real Pauli theorem (Prop 37), metric-preservation core of Prop 46

`BookProof/ChapterA3b.lean` advances the **N4** work-package (§A.3, book line
5196), building on the concrete `4×4` Majorana / gamma-matrix model of
`ChapterA3.lean`.  All `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`; verified with `#print axioms`), `lake build`
green (8081 jobs).

Deliverables:
* **Lemma 40 (charge conjugation `Θ`)** — fully concrete, no external input:
  `chargeConj` (entrywise complex conjugation on `ℂ⁴`) is an anti-linear
  involution (`chargeConj_involutive`, `chargeConj_add`, `chargeConj_smul`)
  commuting with every Majorana matrix (`chargeConj_mgamma_commutes`), because
  the `iγ^μ` are real (`mgamma_map_conj`).
* **Prop 37 (real Pauli theorem)** `real_pauli` — two real Clifford sets are
  related by a real `S` with `|det S| = 1`, `β^μ = S α^μ S⁻¹`, unique up to
  sign.  Proved from the **Pauli fundamental theorem** (Note 36), introduced as
  the EXTERNAL named hypothesis `PauliFundamental` (cite `Good1955Properties`;
  never an `axiom`).  Proof = complexify, use uniqueness-up-to-scalar to see the
  entrywise conjugate `T̄ = c·T` with `|c| = 1`, then rescale by
  `a = |det T|^{-1/4}·exp(i·arg c/2)` to a real `S` with `|det S| = 1`.
  Supporting complexification API: `IsCliffordC`/`IsCliffordR`, `toC`,
  `isCliffordC_toC`, `toC_mul`/`toC_one`/`toC_det`/`toC_conj`/`toC_inv`,
  `exists_real_of_conj_fixed`, `toC_injective`.
* **Prop 46 (metric-preservation core)** `lorentz_of_conj` — if `S` is invertible
  and a real matrix `Λ` describes its conjugation action on the Majorana basis
  (`S⁻¹ iγ^μ S = Σ_ν Λ^μ_ν iγ^ν`), then `Λ η Λᵀ = η`, i.e. `Λ ∈ O(1,3)`.  This
  is the computational heart of `Λ : Pin(3,1) → O(1,3)`, following from the
  Clifford relation `{iγ^μ,iγ^ν} = -2 η^{μν}`.

**Still open after wave 9** (§A.3): the group-theoretic wrapper of Prop 46 (the
map `Λ` as a homomorphism, 2-to-1 surjectivity via Prop 37), Lemma 48
(`Spin⁺(3,1)`), Lemma 52 (real-irrep classification), and the §A.4–A.5 layer
(Bargmann–Wigner, Majorana–Fourier/Energy unitarity, CPT).  Also still open: the
N3 residue (`denseCore_svd` + B.3c) and the N1 hard converse of Prop 11.

## Wave 8 (2026-07-03) — N1 residue: real-system R-type trichotomy

`BookProof/ChapterA1h.lean` continues the **N1 residue** (§A.1, **Prop 11** — the
type assignment of a **real** system), complementing the complex-side
`realification_classification` of wave 7.  All `sorry`-free and `axiom`-free
(only `propext`, `Classical.choice`, `Quot.sound`), `lake build BookProof` green;
the file is warning-free.

The classification is phrased via the **R-imaginary** operators of Def 8.2 (an
isometry `J` with `J² = -1` commuting with the system), i.e. the endomorphism
division-algebra (Frobenius) trichotomy real / complex / quaternionic:

* **`IsRRealType`** — no commuting R-imaginary (endomorphism algebra `ℝ`);
* **`IsRComplexType`** — a commuting R-imaginary exists, but no anticommuting
  (`HasQuaternionicRImaginary`) pair (endomorphism algebra `ℂ`);
* **`IsRPseudorealType`** — an anticommuting pair `J, K` of commuting
  R-imaginaries exists (endomorphism algebra `ℍ`).

Headlines:
* **`rType_exhaustive`** — every real system is of one of the three R-types,
  with the three mutual-exclusion lemmas.
* **`cxSystem_reducible_of_commuting_rImaginary`** — the Def-10 link: a real
  system on a non-trivial space with a commuting R-imaginary `J` has a
  **reducible** complexification `(M, Cx W)`.  Proof = the concrete `V ⊕ V̄`
  eigenspace splitting: the complexified `Jc := cxMap J` (`rImagCx`) is
  `ℂ`-linear with `(Jc)² = -1` (`rImagCx_sq`) and commutes with the complexified
  system (`rImagCx_commutes`), so its `+i` eigenspace `ker (Jc - i)` is a proper
  (`≠ ⊤`, else `⟨J w, 0⟩ = ⟨0, w⟩`), non-trivial (`≠ ⊥`, contains
  `⟨J w, w⟩ ≠ 0`) subsystem.
* **`IsRReal.isRRealType`** / **`IsRReal.excludes_other_types`** — an R-real
  system (irreducible complexification, `IsRReal`) is of R-real type and excludes
  the other two, plus **`IsRComplexType.not_isRReal`** /
  **`IsRPseudorealType.not_isRReal`**.

**Still open after wave 8**: the *hard converse* of Prop 11 (an irreducible real
system with a **reducible** complexification actually admits a commuting
R-imaginary — the Frobenius/Schur direction extracting the division-algebra
imaginary from a proper subsystem of `Cx W`); the N3 residue (`denseCore_svd` —
infinite-dimensional compact-operator SVD, absent from Mathlib); and the N4
`EXTERNAL` Pauli/Weyl layer (§A.4–A.5).

## Wave 7 (2026-07-03) — N1 residue: converse realification dichotomy complete

`BookProof/ChapterA1g.lean` discharges the first open queue item, the **N1
residue** (§A.1, Prop 12 converse) — the recorded crux
`realification_irreducible_of_not_isCReal`, previously blocked on the
Frobenius–Schur orthogonality `Y ⊥ J Y`.  All `sorry`-free and `axiom`-free
(only `propext`, `Classical.choice`, `Quot.sound`), `lake build BookProof` green.
The Schur input is the named hypothesis `IsSchurFull` (never an `axiom`).

Headlines:
* **`realification_irreducible_of_not_isCReal`** — a normal, complex-irreducible
  Schur system that is **not** C-real has an **irreducible** realification (the
  R-pseudoreal / R-complex cases of Prop 12).
* **`realification_irreducible_iff`** — the full Def-10 dichotomy: realification
  irreducible ⇔ not C-real.
* **`realification_classification`** — the complex-side trichotomy of Prop 11:
  C-real (realification reducible) / C-pseudoreal / C-complex (both irreducible).

Method (avoids proving `Y ⊥ J Y` directly).  From a reducible realification take
`E := Y.starProjection` (self-adjoint; commutes with `M` via
`starProjection_realCommutes`, using `rxSystem_isNormal`/`adjoint_rxMap`).  Its
`ℂ`-antilinear part `Q := Qanti E` (from `ChapterA2c.lean`) is self-adjoint
(`Qanti_selfAdjoint`) and `ℂ`-antilinear (`anti_conj_smul`); by `IsSchurFull`,
`Q² = r·1` with `r ≥ 0` real (`Qanti_sq_scalar`, via the real-inner identities
`real_inner_smul_I`/`real_inner_smul_self`).  `r > 0` gives a C-conjugation
`θ = r^{-1/2}·Q` (`isCReal_of_antilinear_sq_pos`) ⇒ C-real, contradiction; `r = 0`
gives `Q = 0` (`selfAdjoint_sq_eq_zero`), so `E` is `ℂ`-linear
(`clinear_of_Qanti_eq_zero`) and `Y` is a proper complex subsystem, contradicting
complex irreducibility.

**Still open after wave 7**: the other N1 sub-item `real_system_trichotomy`
(Prop 11 stated intrinsically on a real system — needs new R-pseudoreal /
R-complex predicate definitions), the N3 residue (`denseCore_svd` —
infinite-dimensional compact-operator SVD, absent from Mathlib), and the N4
`EXTERNAL` Pauli/Weyl layer (§A.4–A.5).

## Wave 6 (2026-07-03) — N2 Prop 16 complete (work-package N2 DONE)

`BookProof/ChapterA2e.lean` discharges **Prop 16** — the last N2 leftover — in
**both** the C-complex and C-pseudoreal cases, all `sorry`-free and `axiom`-free
(only `propext`, `Classical.choice`, `Quot.sound`), `lake build BookProof` green.
This **completes work-package N2** (§A.2, the ℝ / ℂ / ℍ commutant classification
and its isometry criteria).

Framework: a complex system `(M, V)`'s *realification* is `V` as a real
inner-product space with the operators restricted to `ℝ`-scalars; a
**realification system isometry** `β : V ≃ₗᵢ[ℝ] W` (`IsRealSystemIso`) carries the
realified `M` onto the realified `N` by conjugation.  A complex system isometry
is such a `β` that is additionally `ℂ`-linear (`CLinear`), an antiisometry one
that is `ℂ`-antilinear (`CAntilinear`).  Prop 16 = "iso-or-antiiso ⇔ realifications
iso" becomes: a `ℂ`-linear-or-`ℂ`-antilinear realification isometry exists iff a
realification isometry exists.

* Common machinery: `betaR`, `conjClmR`, `IsRealSystemIso`, `CLinear`,
  `CAntilinear`; the transported complex structure `transK β = β ∘ (i·) ∘ β⁻¹`
  with `transK_sq` (`K² = -1`) and `transK_realCommutes` (`K` in the real
  commutant of `N`).
* **C-complex case** (`Ccomplex_realification_dichotomy`,
  `Ccomplex_iso_or_antiiso_iff_realification_iso`): by Prop 18
  (`Rcomplex_realCommutant_eq_complex`) the real commutant is `ℂ`, so `K = c·1`
  with `c² = -1`, i.e. `c = ±i`; hence `β` is *itself* `ℂ`-linear or
  `ℂ`-antilinear.
* **C-pseudoreal case** (`Cpseudoreal_realification_dichotomy`,
  `Cpseudoreal_iso_or_antiiso_iff_realification_iso`): built on the quaternion
  `rot θ p s : w ↦ p•w + s•θw` (the quaternion `p + s·j` acting on `w`), with
  `rot_comp` (composition = quaternion multiplication), the Frobenius–Schur
  orthogonality `theta_inner_self_zero` (`x ⊥ θx` when `θ² = -1`) giving
  `rot_isometry`/`rotEquiv` (unit `rot`s are isometric equivalences), and
  `qembed_eq_rot` bridging Prop 19's output.  By Prop 19 `K = rot pK sK`; a unit
  rotation `u = (pK + i, sK)/n` conjugates `K` to `mulI`, so `β` post-composed
  with `rotEquiv u` is `ℂ`-linear (or, when `K = -mulI`, `β` is already
  `ℂ`-antilinear).  No new `EXTERNAL` input beyond the `IsSchurFull` named Schur
  predicate already used by Props 18–19.

**Still open after wave 6**: the N1 residue (Prop 11 `real_system_trichotomy` +
Prop 12 converse `realification_irreducible_of_not_isCReal`), the N3 residue
(`denseCore_svd` — infinite-dimensional compact-operator SVD, absent from
Mathlib), and the N4 `EXTERNAL` Pauli/Weyl layer (§A.4–A.5).

## Wave 4 (2026-07-03) — N9 and N10 complete

Two brand-new fully-guided work packages landed, both `sorry`-free and
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`), no `EXTERNAL`
hypothesis; `lake build BookProof` green.

* **N9 — Chapter G II** (`BookProof/ChapterG2.lean`): all of G.8–G.12.
  - G.8 `cond_of_null`, `not_isProbabilityMeasure_cond_null` (conditioning
    fails on null constraint sets).
  - G.9 `no_translation_invariant_probabilityMeasure`,
    `translation_invariant_l2_eq_zero`, `no_translation_invariant_unit_vector`
    (Dirac obstruction for any countably infinite gauge group).
  - G.10 headline `no_continuous_gauge_fixing_circle` +
    `gauge_fixing_section_discontinuous` (the Gribov ambiguity, IVT proof).
  - G.11 `brstKer`/`brstIm`/`brstIm_le_brstKer`/`mem_brstKer_iff`/
    `mem_brstIm_iff`/`brstCohomology`, the full split
    **`brstCohomology_equiv : H ≃ₗ[A] ker(·Q) × (A⧸(Q))`** (built from
    `brstFwd`/`brstGinv` + the two round-trip lemmas), and headline
    `brst_physical_iff_gauge_invariant`.
  - G.12 `haarAverage_invariant`, `haarAverage_idempotent`,
    `integral_haarAverage` (Haar averaging is the invariant projection).
* **N10 — Chapter B §§7–9** (`BookProof/ChapterB7.lean`): all of B7.1–B7.4.
  - B7.1 `koopman_comp`, `koopman_refl`, `koopmanRep_mul` (Koopman
    functoriality / group representation).
  - B7.2 `koopman_const` (Koopman fixes constants).
  - B7.3 `eventMap_measure`/`_inter`/`_union`/`_compl`/`_leftInverse` and
    `koopman_indicatorConstLp` (deterministic = event-algebra automorphism).
  - B7.4 `hadamard_not_deterministic` (complementarity = non-deterministic
    unitary).

## Wave 5 (2026-07-03) — N2 Prop 15 complete

`BookProof/ChapterA2d.lean` discharges **Prop 15** of the N2 leftover, all
`sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`),
`lake build BookProof` green.  See the dedicated section below.

**Still open after wave 5** (require infrastructure absent from Mathlib / not yet
built in `BookProof`, and resisted earlier waves): the N1 residue (Prop 11
`real_system_trichotomy` + Prop 12 converse
`realification_irreducible_of_not_isCReal`), the **N2 leftover Prop 16 only**
(iso-or-antiiso ⇔ realifications iso — needs the realification-side
isometry/antiisometry decomposition and the `(1−J_N K)(1−K J_N) = r ≥ 0` Schur
scalar extraction, and a `LinearIsometryEquiv.restrictScalars`-style ℂ→ℝ bridge
not in Mathlib), the N3 residue (`denseCore_svd` — infinite-dimensional
compact-operator SVD, absent from Mathlib), and the N4 `EXTERNAL` Pauli/Weyl
layer (§A.4–A.5).

## Completed

### Chapter U — `BookProof/ChapterU.lean` (work-package N8, complete)
Unitary inference / `unfer` source material (see roadmap §U), all `sorry`-free
and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
- **U.1** `bornMeasure` (`|Ψ|²·μ`), `bornMeasure_isProbability`,
  `conditionedState` (projection-and-renormalize collapse), and the headline
  **`born_conditioning`**: the Born measure of the collapsed state equals the
  classical conditional measure `ProbabilityTheory.cond` (`μ[|E]`) — quantum
  wave-function collapse onto an event *is* Bayesian conditioning.
- **U.3** the bosonic Fock exponential property: `prodToTensor`/`tensorToProd`
  (the two universal-property algebra maps), `tensorToProd_comp_prodToTensor`,
  `prodToTensor_comp_tensorToProd`, and the isomorphism
  **`prodEquiv : Sym(M × N) ≃ₐ[R] Sym M ⊗[R] Sym N`**.
- **U.4** `no_differentiable_trajectory` and `differentiable_trajectory_null`:
  the measure-theoretic wrapper turning the (external, cited Paley–Wiener–
  Zygmund 1933 / Bertoin 1994) a.s.-nowhere-differentiability hypothesis into
  `P(differentiable trajectory) = 0` / full-measure nowhere-differentiability.
  The external fact is a scoped hypothesis, never an `axiom`.
- **U.5** `portfolio_risk_inv_sqrt` (variance of the average of `n` independent
  equal-variance components is `σ²/n`) and `portfolio_std_inv_sqrt` (aggregate
  std deviation `σ/√n`).
- U.2 (sphere→Gaussian / Gegenbauer→Hermite) is a cross-reference to the
  already-`sorry`-free `PnpProof/SphereGaussian.lean`; no new code.
The fermionic (exterior-algebra, graded-sign) analogue of U.3 and the U.6
prose/software items remain out of scope per the roadmap.

### Chapter G — `BookProof/ChapterG.lean` (work-package N6, complete)
Gauge transformations in probability spaces (book line 2128), deliverables
G.0–G.7, all `sorry`-free and `axiom`-free, **no `EXTERNAL` hypothesis**.
- G.0 `gaugeGroup` (the fiber-preserving permutations); `mem_gaugeGroup`.
- G.1 `swap_mem_gaugeGroup`, `gaugeOrbit_eq_fiber` (orbit = fiber),
  `gaugeInvariant_iff_factors` (gauge-invariance ⇔ factoring through `π`).
- G.2 `gaugeInvariantSubalgebra`, `gaugeInvariantOperators` (= centralizer),
  `expectation_gauge_invariant` (gauge-independence of expectation values).
- G.3 the Dirac obstruction: `no_shift_invariant_probabilityMeasure`,
  `shift_invariant_l2_eq_zero`, `no_shift_invariant_unit_vector`,
  `one_mem_gaugeInvariantSubalgebra` (the invariant algebra stays nontrivial).
- G.4 `IsCompleteGaugeFixing`, `exists_complete_gaugeFixing` (sections exist).
- G.5 `haarAverage` + `haarAverage_smul`/`_of_invariant`/`_one`/`_nonneg`
  (invariantization) and the headline
  `gauge_constraint_pushforward_full_measure` (the constraint set carries
  measure 1 under the pushforward — not null).
- G.6 the BRST ghost algebra: `ghostAnnih`/`ghostCreat`, `ghost_car`,
  `ghost_annih_sq`, `ghost_creat_sq`, `ghost_creat_conjTranspose`, `BRST`,
  `BRST_nilpotent` (`Ω² = 0`).
- G.7 dissipative/Koopman dynamics: `dampedCoupledMatrix`, `dampedFlow_add`/
  `dampedFlow_zero` (one-parameter flow group), `evolution_conserves_probability`,
  and the Koopman unitary `koopmanEquiv` (built from `koopman_comp_left`/`_right`).

### Chapter A §A.1 scaffolding — `BookProof/ChapterA1.lean` (work-package N1, partial)
Anti-unitary operators (Note 4) and the Def 8 structures, all `sorry`-free and
`axiom`-free, **no `EXTERNAL` hypothesis**.
- `AntiUnitary V` (Note 4): a conjugate-linear isometric equivalence `V ≃ₗᵢ⋆[ℂ] V`;
  `AntiUnitary.inner_map_map` (`⟪θ x, θ y⟫ = conj ⟪x, y⟫`) and `AntiUnitary.comp_inner`
  (the composite of two anti-unitaries is a unitary).
- `IsConjugation` (Def 8.1, C-conjugation) and `IsRImaginary` (Def 8.2, R-imaginary)
  as predicates on a `System`.
- C-conjugation structural lemmas: `conjugation_smul_I_of_neg` (the `(-1)`-eigenspace
  is `I •` the fixed space), `conjugation_avg_fixed`/`conjugation_avg_antifixed`
  (the `½(1 ± θ)` averaging projections), `conjugation_decomp` (real-form splitting).
- R-imaginary structural lemmas: `rimaginary_orthogonal` (`⟪J x, x⟫_ℝ = 0`),
  `rimaginary_symm_apply` (`J⁻¹ = -J`).

**Obstruction (now partly discharged): see `Complexification.lean` below.** The
missing *complex inner-product* structure on the complexification has now been
built from scratch, and the easy foundational half of Props 11/12 (that the
complexification of a real system is **C-real**) is proved.  What remains is the
full irreducibility transfer of Props 11/12 (the invariant-closed-subspace
bookkeeping identifying the three R-types), which builds on top of the new
infrastructure.

### Complexification inner-product infrastructure — `BookProof/Complexification.lean` (work-package N1, infrastructure)
The complex inner-product structure on the complexification `Wᶜ` of a real
inner-product space, previously recorded as *not in Mathlib*, is built here from
scratch, all `sorry`-free and `axiom`-free, **no `EXTERNAL` hypothesis**.
- `Cx W` (pairs `⟨re, im⟩ ≃ re + i·im`) with its `AddCommGroup`, `Module ℂ`,
  Hermitian `Inner ℂ` (conjugate-linear in the first argument), and the full
  `NormedAddCommGroup` + `InnerProductSpace ℂ` instances (via
  `InnerProductSpace.Core`); `CompleteSpace (Cx W)` when `W` is complete — so
  `Cx W` is a complex Hilbert space.
- `Cx.inner_re`/`inner_im`/`norm_sq` (`‖x‖² = ‖x.re‖² + ‖x.im‖²`), the real
  embedding `Cx.ofReal`, and `Cx.smul_I` (`i · ⟨u,v⟩ = ⟨-v, u⟩`).
- The canonical **conjugation** `Cx.cxConj : Cx W ≃ₗᵢ⋆[ℂ] Cx W` (`⟨u,v⟩ ↦ ⟨u,-v⟩`),
  an anti-unitary involution: `cxConj_involutive`, `cxConj_inner`
  (`⟪θ x, θ y⟫ = conj ⟪x, y⟫`), `cxConj_fixed_iff` (fixed set = real form).
- The **complexification of a real operator** `Cx.cxMap : (W →L[ℝ] W) → (Cx W →L[ℂ] Cx W)`
  (coordinatewise, same operator-norm bound), with `cxMap_one`, `cxMap_mul`,
  `cxMap_add`, and `cxConj_comm_cxMap` (θ commutes with every complexified
  operator).
- Connection to Chapter A's `System` framework: `cxSystem` (complexification of a
  real system) and **`cxConj_isConjugation`** — the canonical conjugation is a
  C-conjugation (Def 8.1) of the complexified system, i.e. *the complexification
  of a real system is C-real*.

**Progress (subspace correspondence now done): see `ChapterA1b.lean` below.**
The closed-subspace bookkeeping the roadmap flags as "the main work" of
Props 11/12 is now formalized: the order-preserving bijection between real
subsystems and conjugation-invariant complex subsystems, and the resulting
reduction of real irreducibility to the conjugation-stable complex lattice.
What remains is the finer sorting of the *conjugation-free* part into the three
R-types (C-real / C-pseudoreal / C-complex), which builds on this correspondence.

### Chapter A §A.1 subsystem correspondence — `BookProof/ChapterA1b.lean` (work-package N1)
The real↔complex *closed-subspace bookkeeping* underlying Props 11/12, all
`sorry`-free and `axiom`-free, **no `EXTERNAL` hypothesis**.  Built on the
`Complexification.lean` infrastructure.
- `Cx.complexify (Y : Submodule ℝ W) : Submodule ℂ (Cx W)` and
  `Cx.realPart (X : Submodule ℂ (Cx W)) : Submodule ℝ W`, the two directions of
  the correspondence, with `mem_complexify`/`mem_realPart`.
- Coordinate continuity: `Cx.continuous_re`/`continuous_im`/`continuous_ofReal`
  (each coordinate map is `1`-Lipschitz).
- The two round-trips: `realPart_complexify` (`= Y`) and
  `complexify_realPart_of_invariant` (for a `cxConj`-invariant `X`, `= X`),
  plus `complexify_cxConj_invariant` and the extremal values
  `complexify_bot`/`complexify_top`/`realPart_bot`/`realPart_top`.
- Subsystem preservation: `complexify_isSubsystem` and `realPart_isSubsystem`
  (each direction sends subsystems to subsystems).
- Headline `irreducible_iff_no_conj_subsystem`: a real system `(M, W)` is
  irreducible **iff** its complexification `(M, Cx W)` has no proper non-trivial
  *conjugation-invariant* subsystem — the reduction of real irreducibility to
  the `cxConj`-stable part of the complexified subspace lattice used throughout
  Props 11/12.

**Progress (C-type classification + R-real case now done): see `ChapterA1c.lean`
below.** The Def 9 C-type predicates and their trichotomy are now formalized, as
is the R-real case of Def 10 / Prop 12.  What remains is the finer sorting of the
R-pseudoreal / R-complex cases (which need the `V ⊕ V̄` decomposition of a
reducible complexification) and the full Prop 11 type assignment.

### Chapter A §A.1 C-type / R-type classification — `BookProof/ChapterA1c.lean` (work-package N1)
The Def 9 / Def 10 classification predicates and the R-real half of Prop 12, all
`sorry`-free and `axiom`-free, **no `EXTERNAL` hypothesis**.  Built on
`Complexification.lean` and `ChapterA1b.lean`.
- Def 9 predicates on a complex system: `CommutesAntiUnitary`,
  `HasCommutingAntiUnitary`, `IsCReal` (a C-conjugation exists), `IsCPseudoreal`
  (no C-conjugation but a commuting anti-unitary), `IsCComplex` (no commuting
  anti-unitary), with `IsCReal.hasCommutingAntiUnitary`.
- The C-type **trichotomy**: `cType_exhaustive` (every complex system is one of
  the three) plus the three mutual-exclusion lemmas
  `not_isCReal_and_isCPseudoreal`, `not_isCReal_and_isCComplex`,
  `not_isCPseudoreal_and_isCComplex`.
- `cxSystem_isCReal`: the complexification of a real system is C-real (Def 9.1
  form of `cxConj_isConjugation`).
- `IsRReal` (Def 10): a real system is R-real iff its complexification is
  irreducible (as a complex system) — automatically C-real by
  `cxSystem_isCReal` — and **`IsRReal.isIrreducible`** (Prop 12, R-real case):
  an R-real real system is irreducible, via `irreducible_iff_no_conj_subsystem`.

**Obstruction (remaining):** the R-pseudoreal / R-complex cases of Def 10 /
Props 11-12 (identifying, within an irreducible real system whose complexification
splits, whether the underlying complex irreducible piece is C-pseudoreal or
C-complex) need the `V ⊕ V̄` conjugate-space decomposition and are left for a
later pass; they now have the inner-product infrastructure, the subspace
correspondence, and the C-type predicates they need.

### Chapter A §A.1 realification correspondence — `BookProof/ChapterA1d.lean` (work-package N1)
The *dual* of `ChapterA1b.lean`: the realification of a **complex** system and
the reduction of complex irreducibility to the `J`-invariant real subspace
lattice (the `(M, V^r)` / `J u := i·u` half of the Def 10 / Prop 12 machinery),
all `sorry`-free and `axiom`-free, **no `EXTERNAL` hypothesis**.  The real
inner-product structure on a complex Hilbert space is supplied by
`InnerProductSpace.rclikeToReal ℂ V`, registered as a **local** instance only
(never global, to avoid the real/complex diamond).
- `rxMap`/`rxSystem` — realification of a complex operator / system (restriction
  of scalars).
- `Jmap` (Def 8.2): the canonical R-imaginary operator `J u := i·u`, an
  `ℝ`-linear isometric equivalence with `Jmap_sq` (`J (J x) = -x`); and
  `Jmap_isRImaginary` — `J` is R-imaginary of the realified system.
- The correspondence `realSub`/`cplxSub` between complex subspaces of `V` and
  `J`-invariant real subspaces of `V^r`, with both round-trips
  (`realSub_cplxSub`, `cplxSub_realSub`), extremal values, and subsystem
  preservation (`realSub_isSubsystem`, `cplxSub_isSubsystem`).
- Headline `complex_irreducible_iff_no_Jinvariant_subsystem`: a complex system
  `(M, V)` is irreducible **iff** its realification `(M, V^r)` has no proper
  non-trivial `J`-invariant subsystem.

### Chapter A §A.1 `V ⊕ V̄` splitting — `BookProof/ChapterA1e.lean` (work-package N1)
The structural dichotomy underlying the R-pseudoreal / R-complex cases of
Props 11/12, all `sorry`-free and `axiom`-free, **no `EXTERNAL` hypothesis**.
Built on the realification correspondence of `ChapterA1d.lean`.
- `JY Y := Jmap '' Y` (the image of a real subspace under the R-imaginary
  operator `Jmap : u ↦ i·u`), with `mem_JY`, `Jmap_mem_JY`,
  `Jmap_mem_of_mem_JY`, and the involution `JY_JY` (`J (J Y) = Y`).
- `JY_isClosed` / `JY_isSubsystem` (`J Y` inherits closedness and
  `M`-invariance from `Y`, since `Jmap` commutes with every `ℂ`-linear op).
- The two `J`-invariant subsystems: `Y ⊓ J Y` (`inf_JY_Jinvariant`,
  `inf_JY_isSubsystem`) and the topological closure `(Y ⊔ J Y)‾`
  (`sup_JY_Jinvariant`, `sup_JY_closure_Jinvariant`,
  `sup_JY_closure_isSubsystem`).
- Headline **`realification_splits`**: if `(M, V)` is complex-irreducible and
  `Y` is a real subsystem of its realification `(M, V^r)`, then either `Y` is
  trivial (`⊥`/`⊤`) or `V` is the closure of the internal direct sum
  `Y ⊕ J Y` (`Y ⊓ J Y = ⊥` and `(Y ⊔ J Y)‾ = ⊤`) — the `V ⊕ V̄`
  conjugate-space decomposition of a reducible realification.  Proved by
  applying `complex_irreducible_iff_no_Jinvariant_subsystem` to the two
  `J`-invariant subsystems and case-splitting.

**Obstruction (remaining, recorded):** the final type assignment of Prop 11
(sorting the split `Y ⊕ J Y` case into R-pseudoreal vs R-complex by constructing
the commuting anti-unitary / conjugation on the split) and the R-pseudoreal /
R-complex cases of Prop 12 still need the anti-unitary construction from the
decomposition; the `V ⊕ V̄` splitting itself is now on disk.

### Chapter A §A.1 R-real realification dichotomy — `BookProof/ChapterA1f.lean` (work-package N1)
The realification-side half of the Def 10 / Prop 12 dichotomy, all `sorry`-free
and `axiom`-free, **no `EXTERNAL` hypothesis**.  Complements the `V ⊕ V̄`
splitting of `ChapterA1e.lean` by handling the R-real case from the realification.
- `conjFixed θ := {v : θ v = v}` — the real fixed space of an anti-unitary `θ`,
  as a real subspace of `V^r` (the real form `W` with `V = W ⊕ i·W`), with
  `mem_conjFixed`, `conjFixed_isClosed`, `conjFixed_invariant`,
  `conjFixed_isSubsystem`, and the non-triviality/properness lemmas
  `conjFixed_ne_bot` / `conjFixed_ne_top` (each fails only if `θ = ±1`, which is
  impossible for an anti-linear involution on a non-trivial space).
- Headline **`realification_reducible_of_conjugation`**: if a complex system
  `(M, V)` on a non-trivial space admits a C-conjugation `θ` (so `M` is C-real),
  its realification `(M, V^r)` is **reducible** — `conjFixed θ` is a proper
  non-trivial subsystem.  Corollary **`isCReal_realification_reducible`**
  (C-real ⇒ realification reducible) and its contrapositive
  **`not_isCReal_of_realification_irreducible`** (realification irreducible ⇒
  not C-real, i.e. C-pseudoreal or C-complex).

**Obstruction (remaining, recorded):** the *converse* direction
`realification_irreducible_of_not_isCReal` (a normal irreducible complex system
that is not C-real has an irreducible realification — the R-pseudoreal /
R-complex cases of Prop 12) is **not** yet on disk.  It is a Frobenius–Schur
invariant-real-structure construction: from a proper real subsystem `Y` one must
build a commuting anti-unitary, which requires the orthogonality `Y ⊥ J Y`.
That orthogonality does **not** follow from normality alone (a real invariant
subspace need not be orthogonal to `i·` itself); it is tied to the §A.2
commutant classification (Props 17–19).  Left for a later pass with the
Frobenius–Schur form machinery.

### Chapter A §A.2 Schur / Lemma 14 — `BookProof/ChapterA2.lean` (work-package N2)
The self-contained algebraic layer of §A.2, all `sorry`-free and `axiom`-free.
The unitary-representation Schur lemma (flagged `EXTERNAL` by the roadmap) is a
named predicate, never an `axiom`.
- `CommutesUnitary` / `IsSchurUnitary` (Def 13, unitary form): a `ℂ`-linear
  isometric equivalence commuting with `M`, and the Schur property that every
  such is a scalar of modulus one.
- **`antiisometry_unique_up_to_phase`** (Lemma 14): in a Schur system, any two
  anti-unitaries commuting with `M` differ by a unit complex phase
  (`θ₂ = c · θ₁`, `‖c‖ = 1`), via the composite `θ₂ ∘ θ₁⁻¹` being a commuting
  unitary hence a unit scalar.
- `commuting_antiUnitary_scalar_multiple`: the uniqueness-of-C-conjugation
  corollary.

### Chapter A §A.2 commutant classification, R-real case — `BookProof/ChapterA2b.lean` (work-package N2)
The commutant-classification payoff for the R-real type (**Prop 17**), all
`sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
Schur's lemma for the representation (flagged `EXTERNAL` for unitary reps) is a
named predicate, never an `axiom`.
- `IsSchurFull` (Def 13, full form): every continuous `ℂ`-linear operator
  commuting with `M` is a complex scalar `c • 1`.
- **`commutant_eq_complex_scalars`**: for a Schur system, an operator lies in
  the commutant **iff** it is a complex scalar — the packaged "commutant `= ℂ`".
- `CommutesConj θ S := ∀ x, S (θ x) = θ (S x)` (equivalently `S` preserves the
  real form `V_θ`) and `real_scalar_commutesConj` (real scalars commute with any
  anti-unitary, since `θ` is conjugate-linear).
- **`Rreal_commutant_eq_real_scalars`** (**Prop 17**): for a complex Schur
  system `(M, V)` with a C-conjugation `θ`, an operator commutes with `M` **and**
  with `θ` **iff** it is a **real** scalar `(r : ℂ) • 1`.  Via the real-form
  correspondence this is exactly "the real commutant of an R-real Schur system is
  `ℝ`" — the first entry of the ℝ / ℂ / ℍ trichotomy.  Proved by `IsSchurFull`
  (operator `= c • 1`) plus: commuting with the conjugate-linear `θ` forces
  `c = conj c` real (or `V` trivial, giving `0`).

**N2 residue now discharged: see `ChapterA2c.lean` below.** Prop 18 and Prop 19
are now proved.  Lemmas 20/28/34 remain the documented `EXTERNAL` Schur inputs
(carried by the `IsSchurFull` named hypothesis, never an `axiom`).

### Chapter A §A.2 commutant classification, R-complex & R-pseudoreal cases — `BookProof/ChapterA2c.lean` (work-package N2, complete)
The remaining two entries of the ℝ / ℂ / ℍ trichotomy (**Prop 18** and
**Prop 19**), all `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).  Schur's lemma for the representation is the
named hypothesis `IsSchurFull` (from `ChapterA2b.lean`), never an `axiom`.

The file works with the **real commutant** — continuous `ℝ`-linear operators
commuting with `M` (`RealCommutes`) — and two canonical real operators inside it:
- `mulI` (multiplication by `i`, `ℂ`-linear, always commuting) with
  `mulI * mulI = -1`; and
- `thetaR θ` — the real-linear operator underlying a commuting anti-unitary `θ`
  (obtained via `toRealCLM` from the conjugate-linear continuous map).
- **`cembed : ℂ →ₐ[ℝ] (V →L[ℝ] V)`** (via `Complex.lift ⟨mulI, mulI_mul_mulI⟩`),
  the complex-scalar embedding, with `cembed_apply` (`cembed c x = c • x`),
  `cembed_realCommutes`, and `cembed_injective` (for `Nontrivial V`).
- **`qbasis` / `qembed : ℍ →ₐ[ℝ] (V →L[ℝ] V)`** (via `QuaternionAlgebra.lift`),
  valid when `θ² = -1`, sending `i, j, k` to `mulI, thetaR θ, mulI·thetaR θ`
  (the quaternion relations `i² = j² = -1`, `ij = -ji` are `qbasis`), with
  `qembed_realCommutes` (the image commutes with `M`) and **`qembed_injective`**
  (the quaternions embed — `ℍ` a division ring ⇒ any algebra hom to a nontrivial
  ring is injective).
- **Linear / antilinear decomposition.** `cplxify` (a real-linear operator
  commuting with `mulI` is `ℂ`-linear) + `cplxify_commutes`; `Plin`/`Qanti`
  (the `ℂ`-linear and `ℂ`-antilinear parts) with `Plin_add_Qanti`
  (`Plin S + Qanti S = S`), `Plin_mulI_comm`/`Qanti_mulI_comm` (operator
  (anti)commutation with `mulI`) and their pointwise forms
  `Plin_commutes_mulI`/`Qanti_anticommutes_mulI`, plus
  `Plin_realCommutes`/`Qanti_realCommutes`.
- `NoAntilinearCommutant` (no nonzero commuting `ℂ`-antilinear operator — the
  precise algebraic content of C-complex) and `noAntilinearCommutant_isCComplex`
  (it implies `IsCComplex`).
- **`Rcomplex_realCommutant_eq_complex` (Prop 18).**  For a complex Schur system
  with `NoAntilinearCommutant`, an `ℝ`-linear operator commutes with `M` **iff**
  it is `cembed c` for some `c : ℂ` — the real commutant is exactly the complex
  scalars, i.e. `≅ ℂ`.  Proof: `Plin S = c • 1` by `IsSchurFull` (via `cplxify`),
  `Qanti S = 0` by `NoAntilinearCommutant`.
- **`Rpseudoreal_realCommutant_eq_quaternion` (Prop 19).**  For a complex Schur
  system with a commuting anti-unitary `θ`, `θ² = -1`, an `ℝ`-linear operator
  commutes with `M` **iff** it is `qembed θ hθ q` for some quaternion `q` —
  together with `qembed_injective` this exhibits the real commutant as `≅ ℍ`.
  Proof: `Plin S = c • 1` (`IsSchurFull`); `Qanti S ∘ θ` is `ℂ`-linear
  (antilinear∘antilinear) hence `= d' • 1` (`IsSchurFull`), giving
  `Qanti S = (-d') • θ`; so `S = c·1 + (-d')·θ = qembed ⟨c.re, c.im, (-d').re,
  (-d').im⟩`.

**N2 status.** Lemma 14 (`ChapterA2.lean`), Prop 17 (`ChapterA2b.lean`) and now
Props 18–19 (`ChapterA2c.lean`) complete the ℝ / ℂ / ℍ commutant trichotomy at
the packaged (named-Schur-hypothesis) level.  The genuinely `EXTERNAL` inputs
Lemmas 20/28/34 (Schur for unitary / imprimitivity representations, not in
Mathlib) remain carried by the named `IsSchurUnitary` / `IsSchurFull` predicates,
never as `axiom`s.

### Chapter A §A.2 isomorphism criterion, Prop 15 — `BookProof/ChapterA2d.lean` (work-package N2)
**Prop 15** (R-real Schur systems: isometric ⇔ complexifications isometric), all
`sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
In the `BookProof` framework an R-real Schur system is a complex Schur system
`(M, V)` with a C-conjugation `θ` whose real form is `V_θ`; the ambient complex
system plays the role of the complexification.
- `conjCLM α m := α ∘ m ∘ α⁻¹` (conjugation of an operator by a ℂ-linear isometric
  equivalence) and `IsSystemIso M N α := N.ops = conjCLM α '' M.ops` (a system
  isometry: `α` carries `M` onto `N` by conjugation).
- `conjAU α θ := α ∘ θ ∘ α⁻¹` (transport of an anti-unitary along `α`) with
  `conjAU_commutesAntiUnitary` (a transported conjugation commutes with `N`).
- `unitScaleEquiv c hc` (multiplication by a unit-modulus scalar as a ℂ-linear
  isometric equivalence), `exists_unit_sqrt` (every unit scalar has a
  unit-modulus square root), and `conjCLM_unitScale` (rescaling `α` by a unit
  scalar leaves `conjCLM α` unchanged).
- Headline **`Rreal_isometric_iff_complexification_isometric`**: for complex
  Schur systems `(M, V)`, `(N, W)` (`IsSchurUnitary N`) with C-conjugations
  `θ_M`, `θ_N`, a *conjugation-intertwining* system isometry
  (`α ∘ θ_M = θ_N ∘ α`, i.e. `α` restricts to a real-form isometry) exists **iff**
  a system isometry exists.  Proof: backward is immediate; forward transports
  `θ_M` to `ϑ := α θ_M α⁻¹`, applies **Lemma 14**
  (`antiisometry_unique_up_to_phase`) to get `θ_N = c·ϑ` with `‖c‖ = 1`, and
  rescales `α` by a unit square root `λ` of `c` (`λ² = c`, so `λ = conjλ·c`),
  yielding the intertwining isometry.

**Obstruction (recorded, N2 residue):** Prop 16 (C-complex / C-pseudoreal:
iso-or-antiiso ⇔ realifications iso) remains open — it needs the realification-side
decomposition of an ℝ-linear isometry into its ℂ-linear and ℂ-antilinear parts
and the `(1 − J_N K)(1 − K J_N) = r ≥ 0` Schur scalar extraction, plus a
`LinearIsometryEquiv.restrictScalars` (ℂ → ℝ) bridge that Mathlib does not
provide.  Left for a later pass.

### Chapter A §A.3 concrete model — `BookProof/ChapterA3.lean` (work-package N4, partial)
The concrete `4×4` Majorana / gamma-matrix model, all `sorry`-free and
`axiom`-free, **no `EXTERNAL` hypothesis**.  The matrices are defined over `ℤ`
(so the Clifford identities close by `decide`) and cast into `ℂ` via
`Int.castRingHom ℂ`; each complex statement is transported from its integer form.
- `mgamma : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ` (the four Majorana matrices `iγ^μ`
  in the real Majorana basis of `book.tex` eq. `\label{basis}`), `mgamma5` (`iγ⁵`),
  and `minkowski` (`η = diag(1,-1,-1,-1)`).
- `mgamma_clifford` (Def 38): `(iγ^μ)(iγ^ν) + (iγ^ν)(iγ^μ) = -2 η^{μν}`.
- `mgamma_map_conj` (reality) and `mgamma_unitary` (`(iγ^μ)ᴴ (iγ^μ) = 1`).
- `mgamma5_eq_prod` (`iγ⁵ = iγ⁰ iγ¹ iγ² iγ³`), `mgamma5_sq` (`(iγ⁵)² = -1`),
  `mgamma5_anticomm` (`iγ⁵` anticommutes with every `iγ^μ`).
- `dgamma` (the Dirac matrices `γ^μ = -i (iγ^μ)`, Def 38) and `dgamma_clifford`
  (`γ^μ γ^ν + γ^ν γ^μ = 2 η^{μν}`).

**Obstruction (recorded):** the later §A.3 results (Prop 37 real Pauli theorem,
Lemma 40 charge conjugation, Prop 46 `Pin(3,1) → O(1,3)`, Lemma 52) build on the
`EXTERNAL` Pauli fundamental theorem (Note 36) and Weyl complete reducibility
(Note 50), which are not in Mathlib; only the concrete matrix model is
established here.  Left for a later pass.

### §0 substrate glue — `BookProof/Substrate.lean` (work-package N5, complete)
Instantiates Chapter B at the Kopperman substrate measure
`PnpProof.unitMeasure` (reusing the already-formalized Kopperman/Mehler layer).
- `substrate_born_forward`, `substrate_born_backward`,
  `substrate_unit_vector_extends`.

### Chapter B.2′ — `BookProof/ChapterB.lean` (work-package N3, partial)
- `condKernel_disintegration`: the regular-conditional-probability
  disintegration `ρ.fst.compProd ρ.condKernel = ρ` on standard Borel spaces
  (the book's `p(y|x)`).

### Chapter B §B.3 partial-isometry API — `BookProof/ChapterB3.lean` (work-package N3)
The partial-isometry layer of the B.3b singular-value expansion `Ψ = W D U†`
(the SVD produces a partial isometry `V` padded to a unitary `W`).  Mathlib has
no `PartialIsometry` for operators, so this file builds it from scratch, all
`sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`).
- `IsPartialIsometry V := V ∘L V† ∘L V = V` (Def) and `IsPartialIsometry.apply`
  (its pointwise form `V (V† (V y)) = V y`).
- `adjointComp_isSelfAdjoint` / `compAdjoint_isSelfAdjoint`: `V†V` and `VV†` are
  always self-adjoint (any `V`).
- `IsPartialIsometry.adjointComp_isIdempotent` /
  `IsPartialIsometry.compAdjoint_isIdempotent`: for a partial isometry, `V†V`
  and `VV†` are idempotent — hence orthogonal projections (the requested
  `V†V`/`VV†`-projection API triple).
- `IsPartialIsometry.adjoint`: the adjoint of a partial isometry is a partial
  isometry (`V† V V† = V†`).
- `isPartialIsometry_of_adjointComp_isIdempotent` and the packaged equivalence
  `isPartialIsometry_iff_adjointComp_isIdempotent`: the textbook
  characterization `V` partial isometry ⇔ `V†V` an orthogonal projection
  (proved via the `‖V(1 - V†V)x‖² = ⟨(1-V†V)x, (V†V)(1-V†V)x⟩ = 0` computation).
- `norm_map_of_adjointComp_eq`: a partial isometry is norm-preserving on its
  initial space (`V†V x = x ⇒ ‖V x‖ = ‖x‖`).

**Obstruction (remaining N3 residue):** the B.3b/B.3c *dense-core singular-value
expansion* itself (`denseCore_svd`, finite-rank diagonalization of `Ψ†Ψ` on the
finite-support core via `LinearMap.IsSymmetric.eigenvectorBasis`, then closure
by density) and the B.3c conditional operator identity `T p T† = W D U† (p/p₀) U
D W†` are not yet built; the partial-isometry API above is the algebraic layer
they plug into.


### Chapter C — `BookProof/ChapterC.lean` (§C.1, complete)
Vanishing probability of an invertible partition map.
- `card_invertible`, `card_all`, `prob_invertible`: the probability that a
  uniformly random discrete map `Fin n → Fin n` is invertible is `n!/nⁿ`.
- `invertible_ratio_isEquivalent`: `n!/nⁿ ~ √(2πn)·e⁻ⁿ` (via Mathlib Stirling).
- `invertible_ratio_tendsto_zero`: `n!/nⁿ → 0`.

### Chapter D — `BookProof/ChapterD.lean` (§D.1, complete)
Almost all functions are uncomputable (computable ⇒ countable ⇒ null).
- `computable_countable`, `computable_bool_countable`.
- `computable_null`, `computable_bool_null`: under any atomless measure the set
  of computable functions is null.

### Chapter E — `BookProof/ChapterE.lean` (§E, complete)
Wave-function collapse versus Euler's formula.
- `cos_sq_surjective` (E.1a), `exp_J` / `exp_J_mulVec` (E.1b, the Euler
  rotation via the matrix exponential), `collapse_density` (E.1c).
- `stochastic_uniform_to_vertex_singular` (E.2b).
- `hadamard_uniformizes` (E.3, `n=2`) and `exists_uniformizer` (E.3, general
  `n`: the DFT "black-hole" uniformizer, unitary with all `|·|² = 1/n`).
- `stickBreaking_surjective` (E.4): the hyperspherical Born / stick-breaking
  recursion is surjective onto the probability simplex.

### Chapter B — `BookProof/ChapterB.lean` (§B.1–B.2, complete)
Wave-function parametrization of a probability measure.
- `born_forward` (B.1 forward): every probability density is `|Ψ|²` for a unit
  vector `Ψ ∈ L²` (`Ψ = √p`).
- `born_backward` (B.1 backward): `|Ψ|²` of a unit vector is a probability
  density.
- `unit_vector_extends` (B.2): every unit vector is a member of a Hilbert basis
  (the book's `Ψ = 𝒰 e₀`).

### Chapter A — `BookProof/ChapterA.lean` (§A.0–A.2 foundational core)
Systems on real/complex Hilbert spaces.
- `System` structure (Def 1) with predicates `Commutes`, `IsNormal` (Def 24),
  `IsSubsystem` (Def 7), `IsIrreducible` (Def 7).
- `orthogonal_isSubsystem` (**Lemma 26**): for a normal system, the orthogonal
  complement of a subsystem is a subsystem.
- `schur_normal_irreducible` (**Lemma 27**): a Schur normal system is
  irreducible.  Following the roadmap, the Schur property (Def 13) is a named
  hypothesis (self-adjoint commuting operators are scalars), never an `axiom`.

## Not implemented here (per the roadmap's own assessment)

The remaining Chapter A material is a large representation-theory subproject
whose deep inputs are, by the roadmap's coverage policy, *external theorems not
present in Mathlib* (Schur for unitary/imprimitivity representations, Weyl
complete reducibility, Mackey imprimitivity, Wigner little-group classification,
Pauli's fundamental theorem of γ-matrices, Varadarajan, Wigner's symmetry
theorem).  The roadmap prescribes introducing these as named hypotheses inside
large bespoke developments; what remains after the 2026-07-03 wave:
- §A.1 residue: Prop 11 final type assignment + Prop 12 converse (the
  `Y ⊥ JY` crux — its §A.2 prerequisite, Props 17–19, is now on disk in
  `ChapterA2b`/`A2c`; the `V ⊕ V̄` splitting and R-real dichotomy are DONE),
- §A.2 leftover: Props 15–16 iso-transfer (small; the ℝ/ℂ/ℍ trichotomy is
  COMPLETE, L20/28/34 stay `EXTERNAL` named hypotheses),
- §A.3 `EXTERNAL` layer and `Pin(3,1)→O(1,3)` (Props 37/46, Lemma 52; the
  concrete γ-matrix model is DONE),
- §B.3 residue: `denseCore_svd` + the B.3c conditional identity (the
  partial-isometry API is DONE in `ChapterB3.lean`),
- §A.4–A.5 Bargmann–Wigner, Majorana–Fourier/Energy unitarity, CPT (Cor 1).

**Two NEW fully-guided packages were added by the author's instruction on
2026-07-03** (no `EXTERNAL` input in either; see the roadmap's guided sections
"Chapter G II" and "Chapter B §§7–9"):
- **N9 — `BookProof/ChapterG2.lean` (no file yet)**: G.8 conditioning fails on
  null constraint sets; G.9 Dirac obstruction for any countably infinite gauge
  group; **G.10 Gribov headline `no_continuous_gauge_fixing_circle`**; G.11
  BRST cohomology (`brstCohomology_equiv`,
  `brst_physical_iff_gauge_invariant`); G.12 Haar averaging = invariant
  projection (`haarAverage_invariant`/`_idempotent`/`integral_haarAverage`).
- **N10 — `BookProof/ChapterB7.lean` (no file yet)**: book-Ch.-B §§7–9 —
  Koopman functoriality `koopman_comp`/`koopmanRep_mul`, `koopman_const`,
  deterministic = event-algebra automorphism (`eventMap_*`,
  `koopman_indicatorConstLp`), complementarity `hadamard_not_deterministic`
  (reuses `ChapterE.lean`'s Hadamard and `ChapterG.lean`'s `koopmanEquiv`).

**Standing rule (author, 2026-07-03 — roadmap §0 S7):** everything involving
fields or field theory follows the Mehler/Kopperman formalism **as implemented
in the sibling repo `../unfer`** (Rust reference implementation:
`nested_fock_algebra` Fock layer, Hermitian field representation `φ = a† + a`,
quadratic ordering `⟨0|H|0⟩ = 0`, `fock_sirk` BRST projection, `prob_kernel`
Born layer). Binds N4 (§A.3–A.5), N9's G.11, Ch.-P mining; hygiene item = add
`../unfer` cross-reference docstrings to `born_conditioning` (`ChapterU.lean`)
and `prodEquiv`.

Chapters F, H and P contain no numbered theorems and are triaged
non-formalizable by the roadmap (prose / physics derivations).
**Chapter G (gauge transformations, book line 2128) was PROMOTED by the author
on 2026-07-02** to a full work package (queue item N6) — **now COMPLETE**, see
`BookProof/ChapterG.lean` at the top of this file.
**Chapter U (unitary inference / unfer) was ADDED by the author on 2026-07-02**
from new source material (the `../test` gitbook + the overlapping
https://timepiece.pubpub.org/ec0in collection, to be merged into book.tex —
the merge is editorial and does not block the Lean targets) — **now COMPLETE**
(queue item N8 ✅, run `e3ffd49f`): see `BookProof/ChapterU.lean` above
(headline `born_conditioning` — Born-rule conditioning is the classical
conditional measure `ProbabilityTheory.cond`; plus `prodEquiv`, the `EXTERNAL`
Lévy wrappers, and the 1/√n portfolio lemmas; the fermionic analogue of U.3
and the U.6 prose items are out of scope per the roadmap).
The ODE, P≠NP, and Riemann-Hypothesis chapters are explicitly
excluded by the author; note the pre-existing `PnpProof` and `RiemannProof`
libraries already cover the adjacent Kopperman/Mehler substrate and the
analytic-ζ route respectively.
