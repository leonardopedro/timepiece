import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Appendix: Proof Plans" =>
%%%
tag := "proof-plans"
number := false
%%%

This appendix collects the precise statements that are *mathematically relevant to
the book but not yet proved* in the repository, together with a plan for proving
them in Lean 4. It is addressed to an LLM Lean specialist (e.g. Aristotle). A more
detailed, machine-oriented version lives in `BOOK_PROOF_PLAN.md` at the repository
root.

Every plan targets the project's pinned toolchain (*Lean v4.28.0, Mathlib
v4.28.0*), so that the work stays compatible with the existing `sorry`-free
`BookProof` library and with the automated prover.

# A. The ODE Chapter

The `Singularity` library and `BookProof` are both `sorry`-free. All three
headline ODE results are proved: `weyl_symmetrization_self_adjoint` and
`nelson_essential_self_adjoint` in `Singularity/`, and
`ae_no_real_singular_time` in `BookProof/ChapterOdeComplexification.lean`.

## A.1 Self-adjointness of the Weyl Hamiltonian

*Status: PROVED.* `weyl_symmetrization_self_adjoint` (in
`Singularity/Hamiltonian.lean:102`) proves `adj (odeToHamiltonian sys) =
  odeToHamiltonian sys` by `simp` + `ext`. The Wick symmetrization
$`(A + A^\dagger)/2` is therefore self-adjoint at the algebraic level.

## A.2 Nelson's essential-self-adjointness theorem

*Status: PROVED.* `nelson_essential_self_adjoint` (in
`Singularity/Esa.lean:44`) proves the equivalence by `simp` from the certificate
definitions: vanishing deficiency indices iff the classical flow is complete. The
forward direction (flow complete => ESA) is the one needed for the ODE resolution.

## A.3 The complexification resolution

*Status: PROVED.* `ae_no_real_singular_time` (in
`BookProof/ChapterOdeComplexification.lean:70`) proves that for almost every
initial condition, the singular time is non-real. Uses
`MeasureTheory.Measure.addHaar_submodule` for the null-measure argument.

*Goal.* Prove that the flow of $`\dot z = z^2` on $`L^2(\mathbb{R}^2)` has *no
finite-time singularity for almost every initial condition*, because the singular
time $`t = 1/z(0)` is real only when $`\operatorname{Im} z(0) = 0`, a null set.

*Plan.* Work in `Singularity` or a new `BookProof` module. Formalize: the explicit
solution $`z(t) = z(0)/(1 - t z(0))`; the singular-time condition
$`1 - t z(0) = 0 \Rightarrow t = 1/z(0)`; that $`1/z(0) \in \mathbb{R}`
$`\Leftrightarrow \operatorname{Im} z(0) = 0`; and that the line
$`\{y = 0\} \subset \mathbb{R}^2` has Lebesgue measure zero (use
`MeasureTheory` — cf. `ConsciousnessNullMeasure.countable_volume_zero` for the
measure-theoretic style). Conclude the set of initial data with a real singular time
is null.

## A.4 Energy-bounded initial conditions

*Status: PROVED* (in the spectral representation).
`BookProof/ChapterSpectralEnergyBound.lean` works where the spectral theorem has
already been applied, i.e. with $`H` the multiplication operator attached to a real
eigenvalue function $`f`, and proves the whole chain: the spectral-projection bound
$`\|H\psi\| \le E_{\max}\|\psi\|` for $`\psi` supported on $`\{|f| \le E_{\max}\}`
(`norm_diagOp_le`); unitarity of the evolution (`norm_evolve`); the Schrödinger
equation $`\psi'(t) = -iH\psi(t)` (`hasDerivAt_evolve`); the uniform bound
$`\|\partial_t\psi(t)\| \le E_{\max}\|\psi(0)\|` (`norm_deriv_evolve_le`); and hence
global Lipschitz continuity in time (`evolve_lipschitz`) — no finite-time
singularity.

```
#check @ChapterSpectralEnergyBound.norm_diagOp_le
#check @ChapterSpectralEnergyBound.norm_deriv_evolve_le
#check @ChapterSpectralEnergyBound.evolve_lipschitz
```

# B. The PA-Free Chapter

## B.1 The verifiable analytic core (proved)

The Riesz–Fischer characterization `completeSpace_iff_summable_norm` and the
completeness of `UniformSpace.Completion` are in Mathlib. The analytic core is
now fully instantiated in `BookProof.ChapterRieszFischer`: $`\ell^2(\mathbb{N})`
is complete (`ell2_completeSpace`), every vector is the unconditional sum of its
coordinate atoms (`riesz_fischer_hasSum`), the finitely-supported core is dense
(`finSupport_dense`) and proper (`finSupport_ne_univ`), and the rational fragment
is a countable dense subset (`BookProof.ChapterEll2Separable.ell2_separable`), so
the completion is separable.

## B.2 Definability / conservativity (the hard, partly informal part)

*Status.* The claim "the completion does not leak Peano Arithmetic" is a
metamathematical statement about definability in the base language, *not* an
internal theorem of analysis.

*What is formalizable.* The precise, provable fragment is now proved in
`BookProof.ChapterDefinabilityFragment`: inside $`\ell^2(\mathbb{N})` the image of
the term-denotable fragment $`\mathbb{N} \to_0 \mathbb{R}` is *exactly* the set of
finitely-supported vectors, that set is dense, and it is a proper subset
(`completion_conservative_over_core`). The remaining, purely *proof-theoretic*
reading — that the completion is a conservative extension of the base theory —
would require formalizing a first-order language of Hilbert spaces and a
definability predicate, a research-scale task that is not claimed here.

# C. Book Tooling

## C.1 Inline-elaborated Lean blocks

*Current state.* The Lean statements in this book are shown as *plain
(non-elaborated) code blocks*, and verification is anchored on
`lake build BookProof`. The blocks are not yet elaborated inside the book build.

*Goal.* Make the `#check` blocks elaborate (and syntax-highlight with hovers)
during the book build.

*Plan.* Verso elaborates a code block against the module's *exported* interface,
so the chapter modules must re-export the `BookProof` names. This needs
`public import BookProof.<Module>`, which in turn requires Lean's
`experimental.module` feature to be enabled for the `Book` targets. Concretely:
enable `experimental.module` for the `Book` library and `book` executable in
`lakefile.toml`, change each chapter's `BookProof` import to `public import`, and
re-add the imports. Verify a chapter at a time. (This re-introduces Mathlib
elaboration into the book build, so it is slower; it does *not* rebuild Mathlib.)

## C.2 Migration to verso-blueprint

*Current state.* The book is a Verso *manual* on Lean v4.28.0.

*Goal.* Adopt [`verso-blueprint`](https://github.com/leanprover/verso-blueprint)
to sync the exposition with the Lean declarations (proof-status tracking, dependency
graphs, progress summaries).

*Blocker.* verso-blueprint requires Lean *≥ v4.29.0*; this project is on
*v4.28.0* (with Mathlib v4.28.0 and the 198-module `BookProof`). verso-blueprint
elaborates the declarations it documents (it detects `sorry` and builds dependency
graphs), so it must run on the same toolchain as the code.

*Plan (execute only when compatible with the automated prover).*
 1. Bump `lean-toolchain` to a version that is *both* supported by
    verso-blueprint *and* by the automated prover.
 2. Bump Mathlib to the matching version and re-fetch its build cache
    (`lake exe cache get`); re-verify `BookProof` (watch for API drift — the library
    has drifted once before).
 3. Choose a stable *label scheme* mirroring the chapter structure (e.g.
    `dutch_book_coherent_iff`, `euler_sum_one`, `total_variance`).
 4. Tag the featured `BookProof` theorems with `@[blueprint "label"]` (use
    `autoDeps := true` where appropriate).
 5. Port the exposition written here into blueprint blocks
    (`:::theorem "label" (uses := ...)`, `:::proof`, with `{uses ...}` /
    `{bpref ...}` edges), reusing the existing prose and sketch proofs.
 6. Build with `lake exe vbp build` and inspect the progress and dependency views.

The Verso markup already written ports to blueprint blocks with modest edits, so the
prose work in this book is not wasted by the migration.

# D. Weak Measurements and Weak Values

*Current state.* The post-selection / ABL reconstruction that underlies the
trajectory chapter and the double-slit discussion is proved
(`BookProof.ChapterTrajectory`): the three-instant collapsed Born process
(`midProb`, `transProb`, `jointProb`, `finalProb`, `condProb`), the reconstruction
consistency (`jointProb_sum_final_eq_midProb`), and the double-slit capstone
(`dslit_finalProb`, `dslit_condProb`, `dslit_coherentFinal`, `dslit_interference`).
What is *not* yet formalized is the *weak value* itself.

*What is formalizable.* The weak value of an observable $`A` given a pre-selection
$`\langle i|` and a post-selection $`|f\rangle`,

$$`\langle A \rangle_w = \frac{\langle f | A | i \rangle}{\langle f | i \rangle},`

is a well-defined complex number whenever $`\langle f | i \rangle \neq 0`. A natural
formalization (new module, e.g. `BookProof.ChapterWeakValue`) would prove, on a
finite complex Hilbert space $`\mathrm{Fin}\, n \to \mathbb{C}`:

 * `weakValue i f A = (inner f (A • i)) / inner f i` — the definition, with the
   claimed values of the inner products well-formed;
 * `weakValue_wellDefined` — if $`\langle f | i \rangle \neq 0`, the weak value is
   finite and well-defined;
 * `weakValue_diag` — when $`i = f` (the post-selection is the pre-selection), the
   weak value collapses to the ordinary expectation
   $`\langle A \rangle_w = \langle i | A | i \rangle`;
 * `weakValue_linear` — linearity of the pre-selection in $`A` (after the
   post-selection is fixed), the algebraic core of "weak measurements are linear in
   the observable";
 * a double-slit capstone `dslit_weakValue` — the weak value of the position
   observable through the Hadamard evolution, tying the abstract definition to the
   `ChapterTrajectory` machinery already in place.

*Boundary.* The *physical* claim that weak measurements do not disturb the
intermediate state is about the measurement interaction, not about the mathematical
ratio; it is not claimed here. The formal content is the ratio, its well-definedness,
and its agreement with the ordinary expectation in the diagonal case.

*Where it lives.* `BookProof.ChapterWeakValue`, registered in `BookProof.lean`,
certified in `BookProof/ChapterRoadmapAudit.lean`, and `#check`-ed from the
double-slit chapter's "Weak Measurements" section.

# E. The Dynamics-Based Unitary (from a function / conditional probability)

*Current state.* The `ConditionalUnitary` chapter builds the unitary that
parametrizes a conditional probability by *Gram–Schmidt* completion of the
wave-function `Ψ = √p` (`BookProof.ChapterJointUnitary.exists_unitary_column`),
and reads the marginal/conditional back off the operator's Gram matrix
(`BookProof.ChapterConditional`). That construction is correct but *arbitrary*:
the columns after the first are chosen by the completion, not fixed by the
probability data.

*The less arbitrary alternative.* The manuscript's field-theoretic thread (QFM.tex)
defines the unitary from the *dynamics* rather than from a basis choice: a function
(a velocity field `v_t(x)`, or a potential `V(x,z)`) determines a Hermitian
generator by the continuity (Weyl-symmetrized) prescription

$$`\mathbf{H}_t = \tfrac12\bigl[\hat p\cdot v_t(\hat x) + v_t(\hat x)\cdot\hat p\bigr],`

and hence a unitary $`\mathbf{U} = e^{i\mathbf{H}t}` — pinned down by the function,
with no free choice of extra columns. For a conditional probability $`p(y|x)` the
construction needs no Bochner-space machinery: via the tensor–product
identification $`L^2(X,\mu)\otimes L^2(Z,\nu) \cong L^2(X\times Z,\mu\times\nu)`,
$`\mathbf{H}` is a standard Hermitian operator on the scalar space
$`L^2(X\times Z)` (e.g. $`\mathbf{H} = -\tfrac12\Delta_z + V(x,z)`), and the
conditional is recovered by the ordinary Born rule $`P(x,B) = \int_B
|\Psi_1(x,z)|^2\,d\nu(z)`.

*What is formalizable.* A new module (e.g. `BookProof.ChapterContinuityUnitary`)
would prove, on the finite (discretized) model that the rest of `BookProof` uses:

 * `continuityHamiltonian` — the Weyl-symmetrized generator
   $`\mathbf{H} = \tfrac12(p\,v + v\,p)` for a velocity vector $`v` on a finite
   lattice, and its Hermiticity (`continuityHamiltonian_hermitian`);
 * `continuityUnitary` — $`\mathbf{U} = e^{i\mathbf{H}}` is a unitary matrix
   (`continuityUnitary_unitary`), the "function → unitary" translation;
 * `bornRecover` — for a product wave-function $`\Psi_0(x,z) = f(x)\,e_0(z)` and
   $`\Psi_1 = e^{i\mathbf{H}}\Psi_0`, the map $`B \mapsto \int_B
   |\Psi_1(x,z)|^2\,d\nu(z)` is a genuine probability measure on $`Z` for each
   $`x` (the Born recovery of the conditional);
 * `tensorIsom` — the finite index-level statement of the tensor–product
   identification (the scalar `L²(X×Z)` is the same object); and, as a capstone,
 * `condProb_of_continuity` — instantiating the recovered $`P(x,B)` as a regular
   conditional probability, tying the dynamics-based unitary back to the
   `ChapterConditional`/`ChapterJointUnitary` Gram-matrix reading.

*Boundary.* The analytic integrability of $`\int_B |\Psi_1|^2\,d\nu` and the
unboundedness of $`-\tfrac12\Delta_z` are handled at the finite/discretized level,
as throughout `BookProof`; the infinite-dimensional analytic realization is the
same open layer as the rest of the book. The *physical* claim that the dynamics
"is" the transition is about the choice of $`\mathbf{H}`; the formal content is
that a Hermitian $`\mathbf{H}` yields a unitary and that the Born rule recovers a
probability law.

*Where it lives.* `BookProof.ChapterContinuityUnitary`, registered in
`BookProof.lean`, certified in `BookProof/ChapterRoadmapAudit.lean`, and `#check`-ed
from the `ConditionalUnitary` chapter's "A Less Arbitrary Construction" section.
