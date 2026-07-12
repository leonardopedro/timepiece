# Summary of changes for run 26fe4498-cd99-4bba-9c81-482a89a42090
Continued the `book.tex` formalization on the main-conclusion thread (as in the recent waves), taking the natural next step after the previous run's Wave 138. The entire roadmap queue (N1–N14) was already complete, so this run added the next mined result on the free-field/uniform-sphere thread of §5 "Free field parametrization in Bayesian inference and Statistical Mechanics".

New file `BookProof/ChapterFreeFieldSphereSupport.lean` (sorry-free, axiom-clean — only `propext`, `Classical.choice`, `Quot.sound`), registered in `BookProof.lean`:
- `normalize_mem_sphere`: radial normalization sends any nonzero vector to the unit sphere;
- `stdGaussian_singleton`: for `n ≥ 1` the standard Gaussian prior is atomless (`stdGaussian n {x} = 0`);
- headline `sphereGaussian_sphere_eq_one`: for `n ≥ 1`, `sphereGaussian n (Metric.sphere 0 1) = 1` — the Gaussian-built uniform measure really is concentrated on the unit sphere (the preimage of the sphere under normalization is the complement of `{0}`, which carries full Gaussian mass).

This confirms that the construction of Waves 137/138 (`stdGaussian`, `sphereGaussian`) genuinely produces a measure supported on the sphere.

Verification: `lake build BookProof` is green, the new file contains no `sorry`, and `#print axioms` on the headline reports only the standard axioms. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, which was left untouched.

Documentation updated as requested: a new Wave 139 section in `BookProof/STATUS.md` and a prepended summary in `ARISTOTLE_SUMMARY.md`. All changes committed and pushed.

# Summary of changes (latest run) — Book main-conclusion thread: the Gaussian-built uniform measure really lives on the unit sphere

Continued the `book.tex` formalization on the main-conclusion thread (staying off Gravity and the Bell/CHSH comparison results; no Hankel transform; Majorana content fine), building on the previous run's Wave 138. Added one new `sorry`-free, axiom-clean (`propext`, `Classical.choice`, `Quot.sound`) file, registered in `BookProof.lean`; `lake build BookProof` is green. (The only repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched.)

New file — `BookProof/ChapterFreeFieldSphereSupport.lean`: the natural next step after Waves 137/138 in §5 "Free field parametrization in Bayesian inference and Statistical Mechanics" ("Wave-function parametrization of a probability measure", `book.tex` ~line 1706). Wave 137's `ChapterFreeFieldGaussian` built the rotation-invariant standard Gaussian prior `stdGaussian n`; Wave 138's `ChapterFreeFieldSphere` defined `sphereGaussian n` (the Gaussian pushed to the sphere by radial normalization `x ↦ ‖x‖⁻¹•x`) and proved it rotation-invariant. This run verifies that the construction genuinely yields a measure *on the sphere*:

- `normalize_mem_sphere`: for `x ≠ 0`, `normalize x` lies on the unit sphere;
- `stdGaussian_singleton`: for `n ≥ 1` the Gaussian prior is atomless, `stdGaussian n {x} = 0` (via `noAtoms_gaussianReal` and `Measure.pi_pi`);
- headline `sphereGaussian_sphere_eq_one`: for `n ≥ 1`, `sphereGaussian n (Metric.sphere 0 1) = 1` — since the Gaussian has no atom at the origin, the preimage of the sphere under normalization is `{0}ᶜ`, which has full Gaussian mass, so all the mass lands on the unit sphere.

Axioms on the headline theorem were verified to be only `propext`, `Classical.choice`, `Quot.sound`. Documentation updated: a new Wave 139 section in `BookProof/STATUS.md` and this prepended summary in `ARISTOTLE_SUMMARY.md`. All changes committed and pushed.

# Summary of changes for run 9a1bc29f-d7ba-422f-850f-b4e6297f4601
Continued the `book.tex` formalization on the main-conclusion thread (staying off Gravity and the Bell/CHSH comparison results; no Hankel transform, Majorana content fine), building on the previous run's Wave 137. Added two new `sorry`-free, axiom-clean (`propext`, `Classical.choice`, `Quot.sound`) files, both registered in `BookProof.lean`; `lake build BookProof` is green. (The only repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched.)

New file 1 — `BookProof/ChapterBornPhaseFiber.lean`: the gauge ambiguity (exact fiber) of the Born-rule wave-function parametrization. The book states the wave-function is a surjective parametrization of probability distributions from the hypersphere and that "two wave-functions are always related by a rotation of the hypersphere"; surjectivity was already formalized, so this file supplies the complementary statement of exactly when two wave-functions give the same distribution:
- `Complex.normSq_eq_iff_exists_phase` and headline `born_fiber_complex` (two complex wave-functions give equal Born probabilities iff they differ by a coordinate-wise phase e^{iθₖ}, a diagonal unitary);
- `sq_eq_iff_exists_sign` and headline `born_fiber_real` (real case: a coordinate-wise sign ±1).

New file 2 — `BookProof/ChapterFreeFieldSphere.lean`: the explicit next step after Wave 137's `ChapterFreeFieldGaussian`. §5 of "Wave-function parametrization of a probability measure" builds a uniform (Lebesgue-like) prior on the sphere from the Gaussian measure. This file pushes the standard Gaussian to the unit sphere by radial normalization x ↦ ‖x‖⁻¹•x and proves the resulting uniform sphere measure is itself rotation-invariant:
- `normalize`, `measurable_normalize`, `normalize_comm` (normalization commutes with norm-preserving orthogonal maps);
- `sphereGaussian` + `instIsProbabilityMeasure_sphereGaussian`;
- headline `sphereGaussian_map_linearIsometryEquiv`: `(sphereGaussian n).map L = sphereGaussian n` for every orthogonal L.

Axioms on the headline theorems were verified to be only `propext`, `Classical.choice`, `Quot.sound`. Documentation updated: a new Wave 138 section in `BookProof/STATUS.md` and a prepended summary in `ARISTOTLE_SUMMARY.md` (as requested). All changes committed and pushed.

# Summary of changes (latest run) — Book main-conclusion thread: the Born-rule parametrization fiber, and the uniform sphere measure from the Gaussian

Continued the `book.tex` formalization on the **main-conclusion** thread (author
instruction: prioritize chapters other than Gravity and off the Bell/CHSH
comparison results; no Hankel transform, Majorana content fine). Two new
`sorry`-free, axiom-clean (`propext`, `Classical.choice`, `Quot.sound`) files,
both registered in `BookProof.lean`; `lake build BookProof` green (the only
repository build failure is the pre-existing, out-of-scope
`RiemannProof/RandomMap.lean`, left untouched).

New deliverable 1 — `BookProof/ChapterBornPhaseFiber.lean` — the **gauge
ambiguity of the Born-rule parametrization**. The book (Introduction,
§"Wave-function collapse versus Euler's formula", `book.tex` ~line 805) states
that the wave-function is a surjective parametrization of probability
distributions from the hypersphere, and that *"two wave-functions are always
related by a rotation of the hypersphere."* Surjectivity was already formalized
(`ChapterB.born_forward`, `ChapterE.stickBreaking_surjective`,
`ChapterEulerNState.euler_reproduces`); this file supplies the complementary
statement — the exact **fiber** of the Born map, i.e. precisely when two
wave-functions give the same probability distribution:
- `Complex.normSq_eq_iff_exists_phase` and headline `born_fiber_complex`: two
  complex wave-functions `u, v : Fin n → ℂ` reproduce equal Born probabilities
  iff they differ by a coordinate-wise phase `e^{iθₖ}` (a diagonal unitary);
- `sq_eq_iff_exists_sign` and headline `born_fiber_real`: two real
  wave-functions differ by a coordinate-wise sign `±1`.

New deliverable 2 — `BookProof/ChapterFreeFieldSphere.lean` — the explicit
**next step** after Wave 137's `ChapterFreeFieldGaussian`. §5 of "Wave-function
parametrization of a probability measure" (`book.tex` ~line 1706) builds a
uniform (Lebesgue-like) prior on the sphere out of the Gaussian measure. Wave
137 proved the standard Gaussian on `EuclideanSpace ℝ (Fin n)` is invariant
under every orthogonal map. This file pushes the Gaussian to the unit sphere by
radial normalization `x ↦ ‖x‖⁻¹ • x` and proves the resulting *uniform measure
on the sphere from the Gaussian* is itself rotation-invariant:
- `normalize`, `measurable_normalize`, `normalize_comm` (normalization commutes
  with orthogonal maps, which preserve the norm);
- `sphereGaussian` + `instIsProbabilityMeasure_sphereGaussian`;
- headline `sphereGaussian_map_linearIsometryEquiv`: `(sphereGaussian n).map L =
  sphereGaussian n` for every orthogonal `L`.

Documentation updated: a new Wave 138 section in `BookProof/STATUS.md` and this
prepended summary in `ARISTOTLE_SUMMARY.md`. All changes committed and pushed.

# Summary of changes for run f60a711a-bf51-4a85-a0f9-2382f55563cf
Continued the `book.tex` formalization on the main-conclusion thread (staying off Gravity and the Bell/CHSH comparison results, no Hankel transform; Majorana content fine).

New deliverable — `BookProof/ChapterFreeFieldGaussian.lean` — formalizing the self-contained finite-dimensional heart of §5 "Free field parametrization in Bayesian inference and Statistical Mechanics" of the chapter "Wave-function parametrization of a probability measure" (`book.tex` ~line 1706): the book's claim that a uniform (Lebesgue-like) prior on the sphere can be built from the Gaussian measure. Since there is no infinite-dimensional Lebesgue measure (already covered in `ChapterNoLebesgue`), the free-field / uniform-on-sphere prior is built from the Gaussian, and the fact that makes this work is that the standard Gaussian is rotationally symmetric.

Over `EuclideanSpace ℝ (Fin n)` the file:
- defines `stdGaussian n` (the standard n-dimensional Gaussian: the product of n copies of the 1-D standard normal `gaussianReal 0 1`, transported to the L² inner-product structure);
- proves it is a probability measure (`instIsProbabilityMeasure_stdGaussian`);
- proves its characteristic function is the standard form `t ↦ exp(-‖t‖²/2)`, depending only on `‖t‖` (`charFun_stdGaussian`);
- proves the headline `stdGaussian_map_linearIsometryEquiv`: for every orthogonal map (linear isometry equivalence) `L`, `(stdGaussian n).map L = stdGaussian n` — the free-field Gaussian prior is rotation-invariant. This is the positive companion to the existing `ChapterNoLebesgue` and `ChapterNoUniformCountable`.

The new file is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified with `#print axioms` on the headline theorems), is registered in `BookProof.lean`, and `lake build BookProof` completes successfully. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

Documentation updated: a new Wave 137 section in `BookProof/STATUS.md` and a prepended Wave 137 summary in `ARISTOTLE_SUMMARY.md` (the new prompt explicitly requested updating it). Before adding the file I checked that nearby §5 material was not duplicated (`ChapterDensitySpectral` covers only §5's last, density-matrix paragraph). All changes committed and pushed.

# Summary of changes (Wave 137) — Book "Wave-function parametrization of a probability measure", §5: the standard Gaussian prior is rotation-invariant (free-field / uniform-on-sphere construction)

Continued the `book.tex` formalization on the main-conclusion thread — staying off Gravity and the Bell/CHSH comparison results, and using no Hankel transform (Majorana content fine), per your instructions.

**New deliverable — `BookProof/ChapterFreeFieldGaussian.lean` (Wave 137)**, `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`; verified with `#print axioms` on the two headline theorems). Registered in `BookProof.lean`; `lake build BookProof` completes successfully. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, which I left untouched.

It formalizes the self-contained finite-dimensional heart of the subsection "5. Free field parametrization in Bayesian inference and Statistical Mechanics" (chapter "Wave-function parametrization of a probability measure", `book.tex` line ~1706): *"a uniform (Lebesgue-like) measure of an infinite-dimensional sphere can be defined using the Gaussian measure and the Fock-space."* Since there is no infinite-dimensional Lebesgue measure (already formalized in `ChapterNoLebesgue`), the book builds its free-field / uniform-on-sphere prior out of the Gaussian measure; the mathematical fact that makes this work is that the standard Gaussian is rotationally symmetric, so after radial normalization it induces the uniform measure on the sphere.

Over `EuclideanSpace ℝ (Fin n)` it defines `stdGaussian n` (the standard `n`-dimensional Gaussian, the product of `n` copies of the one-dimensional standard normal `gaussianReal 0 1` transported to the L² inner-product structure by `WithLp.toLp 2`) and proves: `instIsProbabilityMeasure_stdGaussian` (it is a probability measure — a legitimate Bayesian prior), `charFun_stdGaussian` (its characteristic function is the standard Gaussian form `t ↦ exp(-‖t‖²/2)`, depending only on `‖t‖`), and the headline `stdGaussian_map_linearIsometryEquiv` (for every orthogonal map — a linear isometry equivalence — `L`, the pushforward `(stdGaussian n).map L` equals `stdGaussian n`: the free-field Gaussian prior is rotation-invariant). This is the positive companion to the existing `ChapterNoLebesgue` (no infinite-dimensional Lebesgue measure) and `ChapterNoUniformCountable` (no uniform countable measure).

Before writing it, I checked nearby §5 material was not duplicated: `ChapterDensitySpectral` covers only §5's last paragraph (the density matrix as a diagonal probability operator rotated by a unitary), and the Gaussian rotation-invariance / uniform-on-sphere claim was not yet formalized.

Documentation updated: new Wave 137 section in `BookProof/STATUS.md` and prepended here in `ARISTOTLE_SUMMARY.md`. All changes committed and pushed.

---

# Summary of changes for run 04f865e0-549b-4e91-8f06-ab0ded3e5511
Continued the `book.tex` formalization on the main-conclusion thread — staying off Gravity and the Bell/CHSH comparison results, and using no Hankel transform (Majorana content fine), per your instructions.

**New deliverable — `BookProof/ChapterEulerComplexQuat.lean` (Wave 136)**, `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`; verified with `#print axioms` on the headline theorems). Registered in `BookProof.lean`; the module builds green (`lake build BookProof.ChapterEulerComplexQuat` and `BookProof` complete successfully). The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, which I left untouched.

It formalizes the self-contained claim of the subsection "Complex and Quaternionic Hilbert spaces" (chapter "Wave-function collapse versus Euler's formula", §"Euler's formula for a generic phase-space"): a complex (resp. quaternionic) wave-function is the realification of a real wave-function on a state space with twice (resp. four times) as many outcomes, and the complex/quaternionic Born probability P(n)=|vₙ|² is exactly the sum of the 2 (resp. 4) real Born probabilities of its real coordinates — the book's `P(n)=∑_{m=1}^4 P(n,m)` and "the union of 2 identical spaces". This justifies using complex/quaternionic Hilbert spaces while keeping the real Euler-angle parametrization of the earlier `ChapterEulerNState`.

Over `Fin n → ℂ` and `Fin n → ℍ[ℝ]` it defines `cbornProb`/`qbornProb` (= `normSq (v k)`) and proves: `complex_born_split` (P(k)=(Re vₖ)²+(Im vₖ)²), `quat_born_split` (P(k)=re²+imI²+imJ²+imK²), `complex_realification_norm`/`quat_realification_norm` (realification preserves total probability), and the headlines `complex_reproduces`/`quat_reproduces` (every probability distribution is reproduced by the Born rule of a complex, resp. quaternionic, unit wave-function).

Before writing it, I verified several nearby candidates were already done so as not to duplicate: the Stern-Gerlach/"black-hole" uniformizer (`ChapterE.exists_uniformizer`), the n!/nⁿ→0 invertible-map probability with Stirling asymptotics (`ChapterC`), and the density-matrix Euler-formula projector with J as imaginary unit (`ChapterE3`).

Documentation updated: new Wave 136 sections in `BookProof/STATUS.md` and prepended in `ARISTOTLE_SUMMARY.md`. All changes committed and pushed.

# Summary of latest changes (Wave 136) — Book "Wave-function collapse versus Euler's formula", §"Complex and Quaternionic Hilbert spaces"

Continued the `book.tex` formalization on the main-conclusion thread, staying off Gravity and the Bell/CHSH comparison results and using no Hankel transform (Majorana content is fine), per your instructions.

**New deliverable — `BookProof/ChapterEulerComplexQuat.lean` (Wave 136), `sorry`-free and axiom-clean** (only `propext`, `Classical.choice`, `Quot.sound`; verified with `#print axioms` on the headline theorems). Registered in `BookProof.lean`; `lake build BookProof` completes green (the only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, untouched here).

It formalizes the self-contained claim of the subsection "Complex and Quaternionic Hilbert spaces" (book line ~3639): a complex (resp. quaternionic) wave-function is the **realification** of a real wave-function on a state space with twice (resp. four times) as many outcomes, and the complex/quaternionic Born probability `P(n)=|vₙ|²` is exactly the sum of the 2 (resp. 4) real Born probabilities of its real coordinates — the book's `P(n)=∑_{m=1}^4 P(n,m)`, and the complex case as "the union of 2 identical spaces". This is the book's justification for using complex/quaternionic Hilbert spaces while keeping the real Euler-angle parametrization of `ChapterEulerNState` (Wave 135).

Over `Fin n → ℂ` and `Fin n → ℍ[ℝ]` it defines `cbornProb v k = Complex.normSq (v k)` and `qbornProb v k = Quaternion.normSq (v k)` and proves:
- `complex_born_split` — `P(k) = (Re vₖ)² + (Im vₖ)²`;
- `quat_born_split` — `P(k) = re² + imI² + imJ² + imK²` (the book's `P(n)=∑_{m=1}^4 P(n,m)`);
- `complex_realification_norm` / `quat_realification_norm` — the realification preserves total probability;
- `complex_reproduces` / `quat_reproduces` (headlines) — every probability distribution on `{0,…,n-1}` is reproduced by the Born rule of a complex (resp. quaternionic) unit wave-function.

Before writing this file I confirmed several nearby candidates were already done (so as not to duplicate): the Stern-Gerlach/"black-hole" DFT uniformizer (`ChapterE.exists_uniformizer`), the `n!/nⁿ→0` invertible-map probability with Stirling asymptotics (`ChapterC`), and the density-matrix Euler-formula projector with `J` as imaginary unit (`ChapterE3`). I updated `BookProof/STATUS.md` (new Wave 136 section) and prepended this Wave 136 summary. All changes are committed and pushed.

---

# Summary of changes for run de3c47ed-c9d9-4655-b3d8-0223a0c52237
Continued the `book.tex` formalization on the main-conclusion thread, staying off Gravity and the Bell/CHSH comparison results and using no Hankel transform (Majorana content is fine), per your instructions.

**New deliverable — `BookProof/ChapterEulerNState.lean` (Wave 135), `sorry`-free and axiom-clean** (only `propext`, `Classical.choice`, `Quot.sound`; verified with `#print axioms` on the headline theorems).

It formalizes the self-contained claim of the chapter "Wave-function collapse versus Euler's formula", sections "Euler's formula for a phase-space with 4 states" and "Euler's formula for a generic phase-space": **any probability distribution over `n` states can be reproduced by the Born rule for some wave-function**, via the Euler-angle (hyper-spherical / stick-breaking) parametrization P(1)=c₁², P(2)=(s₁c₂)², P(3)=(s₁s₂c₃)², P(4)=(s₁s₂s₃)² with cₙ=cos θₙ, sₙ=sin θₙ — because for any probability p there is an angle θₙ with cₙ²=p. This generalizes the 2-state result of Wave 134 (`ChapterEulerStochastic`) to arbitrarily many states.

Working with real coordinates in the book's orthonormal `l`-basis (indexed over ℕ for a fixed number of states `n`), the file defines `tailProd θ m = ∏_{i<m} sin²(θ i)` (the remainder weight "P(m or above)"), the Euler wave-function coordinate `eulerWave θ n k`, and the Born probability `bornProb θ n k = P(k) = |φₖ|²`. It proves:
- `eulerWave_sq` — the Born rule `bornProb = (eulerWave)²`;
- `euler_sum_one` (headline) — any angles give a probability distribution: ∑_{k<n} bornProb θ n k = 1;
- `euler_wave_unit` — the Euler wave-function is a unit vector;
- `euler_reproduces` (headline) — for any probability distribution p on {0,…,n-1} there exist Euler angles whose Born probabilities equal p (every distribution is reproduced by the Born rule), via the tail-sum construction `exists_theta_tailProd`.

The file is registered in `BookProof.lean`; `lake build BookProof` completes green with no warnings in the new module. I updated `BookProof/STATUS.md` (new Wave 135 section) and prepended a Wave 135 summary to `ARISTOTLE_SUMMARY.md`. All changes are committed and pushed.

Note: the only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, an unrelated thread that already had errors before this work and was left untouched.

# Summary of latest changes (Wave 135) — Book "Wave-function collapse versus Euler's formula", §§"Euler's formula for a phase-space with 4 states" / "Euler's formula for a generic phase-space"

Continued the `book.tex` formalization on the main-conclusion thread, staying off Gravity and the Bell/CHSH comparison results and using no Hankel transform (Majorana content is fine), per your instructions.

**New deliverable — `BookProof/ChapterEulerNState.lean` (Wave 135), `sorry`-free and axiom-clean** (only `propext`, `Classical.choice`, `Quot.sound`; verified with `#print axioms` on the headline theorems).

It formalizes the self-contained claim of the chapter *"Wave-function collapse versus Euler's formula"*, sections *"Euler's formula for a phase-space with 4 states"* and *"Euler's formula for a generic phase-space"*: **any probability distribution for `n` states can be reproduced by the Born rule for some wave-function**, via the Euler-angle (hyper-spherical / stick-breaking) parametrization `P(1)=c₁², P(2)=(s₁c₂)², P(3)=(s₁s₂c₃)², P(4)=(s₁s₂s₃)²` with `cₙ=cos θₙ`, `sₙ=sin θₙ` — because for any probability `p` there is an angle `θₙ` with `cₙ²=p`. This generalizes the 2-state result of Wave 134 (`ChapterEulerStochastic`) to arbitrarily many states.

Working with real coordinates in the book's orthonormal `l`-basis (indexed over `ℕ` for a fixed number of states `n`), the file defines `tailProd θ m = ∏_{i<m} sin²(θ i)` (the remainder weight `P(m or above)`), the Euler wave-function coordinate `eulerWave θ n k` (`(∏_{i<k} sin θᵢ)·cos θₖ`, cosine-free on the last coordinate), and the Born probability `bornProb θ n k = P(k) = |φₖ|²`. It proves:
- `eulerWave_sq` — the Born rule `bornProb = (eulerWave)²`;
- `euler_sum_one` (headline) — **any** angles give a probability distribution: `∑_{k<n} bornProb θ n k = 1`;
- `euler_wave_unit` — the Euler wave-function is a unit vector;
- `euler_reproduces` (headline) — for **any** probability distribution `p` on `{0,…,n-1}` there exist Euler angles whose Born probabilities equal `p` (every distribution is reproduced by the Born rule), via the tail-sum construction `exists_theta_tailProd`.

The file is registered in `BookProof.lean`; `lake build BookProof` completes green with no warnings in the new module. I updated `BookProof/STATUS.md` (new Wave 135 section) and prepended this Wave 135 summary. All changes are committed and pushed.

Note: the only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, an unrelated thread that already had errors before this work and was left untouched.

---

# Summary of changes for run 59badb12-7342-457e-94f4-be01316a8c34
Continued the `book.tex` formalization on the main-conclusion thread, staying off Gravity and the Bell/CHSH comparison results and using no Hankel transform (Majorana content is fine), per your instructions.

**New deliverable — `BookProof/ChapterEulerStochastic.lean` (Wave 134), `sorry`-free and axiom-clean** (axioms limited to `propext`, `Classical.choice`, `Quot.sound`, verified with `lean_verify` on the two headline theorems).

It formalizes the self-contained finite-dimensional claim of the chapter *"Wave-function collapse versus Euler's formula"*, section *"Euler's formula for the probability clock"*: *"the most general linear transformation of a probability distribution that preserves the space of probability distributions is `M(a,b) = [[cos²a, cos²b],[sin²a, sin²b]]` … the matrix `M` such that `M·½(1,1)=(1,0)` is necessarily singular and so it is not suitable to represent a symmetry group."* This is the book's contrast between the invertible rotations acting on the wave-function and the fact that on the probability simplex the only linear symmetries are column-stochastic matrices.

Over `Matrix (Fin 2) (Fin 2) ℝ`, defining `IsProbVec` (a 2-state probability vector), `PreservesProb` (a matrix mapping every probability vector to a probability vector) and `Mmat a b` (= `M(a,b)`), it proves:
- `Mmat_preservesProb` — every `M(a,b)` preserves probability distributions;
- `preservesProb_iff_columnStochastic` — a linear map preserves the probability simplex iff each column is a probability vector;
- `preservesProb_iff_exists_angles` (headline) — a linear map preserves the space of probability distributions iff it equals `M(a,b)` for some real angles `a,b`;
- `uniform_to_vertex_singular` (headline) — any probability-preserving `M` with `M·½(1,1)=(1,0)` has `det = 0`, so it cannot represent a symmetry group.

The file is registered in `BookProof.lean`; `lake build BookProof` completes green with no warnings in the new module. I updated `BookProof/STATUS.md` (new Wave 134 section) and `ARISTOTLE_SUMMARY.md` (prepended a Wave 134 summary). All changes are committed and pushed.

Note: the only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, an unrelated thread that already had errors before this work and was left untouched.

# Summary of latest changes (Wave 134) — Book "Wave-function collapse versus Euler's formula", §"Euler's formula for the probability clock": the most general probability-preserving linear map on 2 states is `M(a,b)`, and the collapse-to-vertex map is singular

Continued the `book.tex` formalization on the main-conclusion thread, staying off Gravity and the Bell/CHSH comparison results and using no Hankel transform (Majorana content is fine), per your instructions.

**New deliverable — `BookProof/ChapterEulerStochastic.lean` (Wave 134), `sorry`-free and axiom-clean** (axioms limited to `propext`, `Classical.choice`, `Quot.sound`, verified via `#print axioms`/`lean_verify` on the two headline theorems).

It formalizes the self-contained finite-dimensional claim of the chapter *"Wave-function collapse versus Euler's formula"*, section *"Euler's formula for the probability clock"* (`book.tex` line ~3310): *"the most general linear transformation of a probability distribution that preserves the space of probability distributions is `M(a,b) = [[cos²a, cos²b],[sin²a, sin²b]]` … the matrix `M` such that `M·½(1,1)=(1,0)` is necessarily singular and so it is not suitable to represent a symmetry group."* The book uses this to contrast the invertible rotations acting on the wave-function with the fact that on the probability simplex the only linear symmetries are column-stochastic matrices (the collapse-to-vertex one being singular) — motivating the wave-function parametrization. Over `Matrix (Fin 2) (Fin 2) ℝ` it defines `IsProbVec` (a 2-state probability vector), `PreservesProb` (a matrix mapping every probability vector to a probability vector) and `Mmat a b` (the book's `M(a,b)`), and proves:
- `Mmat_preservesProb` — every `M(a,b)` preserves probability distributions;
- `preservesProb_iff_columnStochastic` — a linear map preserves the probability simplex iff each of its columns is a probability vector;
- `preservesProb_iff_exists_angles` — the headline: a linear map preserves the space of probability distributions iff it equals `M(a,b)` for some real angles `a,b` (the book's "most general" claim), using `exists_cos_sq` (every `p ∈ [0,1]` equals `cos² a`);
- `uniform_to_vertex_singular` — the headline: any probability-preserving `M` with `M·½(1,1)=(1,0)` has `det = 0`, so it cannot represent a symmetry group.

The file is registered in `BookProof.lean`; `lake build BookProof` completes green, and the new module compiles with no warnings. I updated `BookProof/STATUS.md` (new Wave 134 section) and this file, as requested. All changes are committed and pushed.

Note: the only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, an unrelated thread that already had errors before this work and was left untouched.

# Summary of changes for run 0f70460d-9737-4bb9-bccb-f161c3bc3259
Continued the `book.tex` formalization on the main-conclusion thread (chapter *"Wave-function parametrization of a probability measure"*), staying off Gravity and the Bell/CHSH comparison results and using no Hankel transform (Majorana content is fine), per your instructions.

**New deliverable — `BookProof/ChapterMeasurementLLN.lean` (Wave 133), `sorry`-free and axiom-clean** (axioms limited to `propext`, `Classical.choice`, `Quot.sound`, verified via `#print axioms` on all three headline theorems).

It formalizes the self-contained mathematical content of §10 *"Ensemble forecasting …"* (`book.tex` line ~2005): *"a measurement … reproduc[es] the probability distribution in the limit of infinite measurements … not different from an unbiased sampling process taken over infinite time."* Mathematically this is the strong law of large numbers for a finite-outcome measurement. Over a probability space `(Ω, μ)` and an i.i.d. sequence of `Fin k`-valued measurements `M : ℕ → Ω → Fin k` (each measurable, pairwise independent, identically distributed to `M 0`), it proves:
- `outcomeIndicator_integral` — the expectation of the `{0,1}` indicator of the event "`Mᵢ = a`" equals the outcome probability `(μ {ω | M 0 ω = a}).toReal`;
- `measurement_average_tendsto` — the general observable version: the running average of any observable `f ∘ Mᵢ` converges almost surely to its expectation `∫ f (M 0 ω) ∂μ` (the "unbiased sampling over infinite time" statement);
- `measurement_frequency_tendsto` — the headline: for every outcome `a`, the empirical frequency `(∑_{i<n} 𝟙[Mᵢ = a]) / n` converges almost surely to the true outcome probability `(μ {ω | M 0 ω = a}).toReal` — so infinitely many measurements reproduce the distribution.

The file is registered in `BookProof.lean`; `lake build BookProof` completes green, and the new module compiles with no warnings. I updated `BookProof/STATUS.md` (new Wave 133 section) and `ARISTOTLE_SUMMARY.md` (prepended a Wave 133 summary), as requested. All changes are committed and pushed.

Note: the only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, an unrelated thread that already had errors before this work and was left untouched.

# Summary of latest changes (Wave 133) — §10 "Ensemble forecasting": measurements reproduce the probability distribution in the infinite-measurement limit (strong law of large numbers)

Continued the `book.tex` formalization on the main-conclusion thread (chapter
*"Wave-function parametrization of a probability measure"*), staying off Gravity
and the Bell/CHSH comparison results and using no Hankel transform (Majorana
content is fine), per your instructions. Landed **Wave 133** with one new,
self-contained, `sorry`-free and `axiom`-clean file (axioms limited to `propext`,
`Classical.choice`, `Quot.sound`, verified on the headline theorems via
`#print axioms`):

- `BookProof/ChapterMeasurementLLN.lean` formalizes the self-contained
  mathematical claim of §10 *"Ensemble forecasting …"* (`book.tex` line ~2005):
  *"a measurement … reproduc[es] the probability distribution in the limit of
  infinite measurements … not different from an unbiased sampling process taken
  over infinite time."* Mathematically this is the **strong law of large
  numbers** for a finite-outcome measurement. Over a probability space `(Ω, μ)`
  and an i.i.d. sequence of `Fin k`-valued measurements
  `M : ℕ → Ω → Fin k` (each measurable, pairwise independent, identically
  distributed to `M 0`), it proves:
  - `outcomeIndicator_integral` — the expectation of the `{0,1}` indicator of the
    event "`Mᵢ = a`" is the outcome probability `(μ {ω | M 0 ω = a}).toReal`;
  - `measurement_average_tendsto` — the general observable version: the running
    average of any observable `f ∘ Mᵢ` converges almost surely to its expectation
    `∫ f (M 0 ω) ∂μ` (the "unbiased sampling over infinite time" statement);
  - `measurement_frequency_tendsto` — the headline: for every outcome `a`, the
    empirical frequency `(∑_{i<n} 𝟙[Mᵢ = a]) / n` converges almost surely to the
    true outcome probability `(μ {ω | M 0 ω = a}).toReal`, so infinitely many
    measurements reproduce the distribution.

  The file is registered in `BookProof.lean`; `lake build BookProof` completes
  green. Updated `BookProof/STATUS.md` (new Wave 133 section). All changes
  committed and pushed. The only remaining repository build failure is the
  pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, an unrelated thread
  that already had errors before this work.

---

# Summary of changes for run 78e28403-805a-4ad5-8c3e-454a1329d01f
Continued the `book.tex` formalization on the main-conclusion thread (chapter *"Wave-function parametrization of a probability measure"*), staying off Gravity and the Bell/CHSH comparison results and using no Hankel transform (Majorana content is fine), per your instructions.

**Wave 132 — one new, self-contained, `sorry`-free and axiom-clean file** (axioms limited to `propext`, `Classical.choice`, `Quot.sound`, verified on the headline theorems via `#print axioms`):

- `BookProof/ChapterDensitySpectral.lean` formalizes the last paragraph of §5 *"Free field parametrization in Bayesian inference and Statistical Mechanics"* (`book.tex` line ~1706): *"We can always define the density matrix through a diagonal operator rotated by a unitary operator, with the diagonal operator defining the marginal probability of the initial state and the unitary operator defining the conditioned probability of the final state conditioned by the initial state."* Mathematically this is the spectral decomposition of a density matrix. Over `Matrix n n ℂ` (finite `n`), with `IsDensityMatrix ρ` = Hermitian ∧ positive semidefinite ∧ `trace ρ = 1`, it proves:
  - `density_eigenvalues_nonneg` — eigenvalues ≥ 0;
  - `density_eigenvalues_sum_one` — eigenvalues sum to 1 (so the eigenvalue vector is a probability distribution — the book's "marginal probability of the initial state");
  - `density_spectral` — the decomposition `ρ = U · diag(eigenvalues) · U†` (the "diagonal operator rotated by a unitary");
  - `isDensityMatrix_of_unitary_diagonal` — the converse: for any unitary `U` and probability distribution `d`, `U · diag(d) · U†` is a density matrix;
  - `density_iff_exists_unitary_diagonal` — the headline: a matrix is a density matrix iff it is a probability-diagonal operator rotated by a unitary.

The file is registered in `BookProof.lean`; `lake build BookProof` completes green. Updated `ARISTOTLE_SUMMARY.md` (new Wave 132 block prepended) and `BookProof/STATUS.md` (new Wave 132 section). All changes committed and pushed.

Note: the only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, an unrelated thread that already had errors before this work.

# Summary of changes — Wave 132 (density matrix = diagonal probability operator rotated by a unitary)

Continued the `book.tex` formalization on the main-conclusion thread (chapter
*"Wave-function parametrization of a probability measure"*), staying off Gravity
and the Bell/CHSH comparison results and using no Hankel transform (Majorana
content fine), per instructions. Landed **Wave 132** with one new,
self-contained, `sorry`-free and axiom-clean deliverable (axioms limited to
`propext`, `Classical.choice`, `Quot.sound`, verified on the headline theorems):

- `BookProof/ChapterDensitySpectral.lean` — formalizes the last paragraph of §5
  *"Free field parametrization in Bayesian inference and Statistical Mechanics"*
  (`book.tex` line ~1706): *"We can always define the density matrix through a
  diagonal operator rotated by a unitary operator, with the diagonal operator
  defining the marginal probability of the initial state and the unitary operator
  defining the conditioned probability of the final state conditioned by the
  initial state."* Mathematically this is the spectral decomposition of a density
  matrix. Over `Matrix n n ℂ` (finite `n`), `IsDensityMatrix ρ` = Hermitian ∧
  positive semidefinite ∧ `trace ρ = 1`. Proves `density_eigenvalues_nonneg`
  (eigenvalues ≥ 0), `density_eigenvalues_sum_one` (eigenvalues sum to 1 — so the
  eigenvalue vector is a probability distribution, the "marginal probability"),
  `density_spectral` (the decomposition `ρ = U · diag(eigenvalues) · U†`, the
  "diagonal operator rotated by a unitary"), the converse
  `isDensityMatrix_of_unitary_diagonal` (for any unitary `U` and probability
  distribution `d`, `U · diag(d) · U†` is a density matrix), and the headline
  `density_iff_exists_unitary_diagonal` (a matrix is a density matrix iff it is a
  probability-diagonal operator rotated by a unitary).

Registered in `BookProof.lean`; `lake build BookProof` completes green.
`ARISTOTLE_SUMMARY.md` (this block) and `BookProof/STATUS.md` (new Wave 132
section) were updated. All changes are committed and pushed.

Note: the only remaining repository build failure is the pre-existing,
out-of-scope `RiemannProof/RandomMap.lean`, an unrelated thread that already had
errors before this work.

---

# Summary of changes for run 68726ac7-a443-476b-adbc-8f882aeee8f5
Continued the `book.tex` formalization on the main-conclusion thread (chapter *"Wave-function parametrization of a probability measure"*), staying off Gravity and the Bell/CHSH comparison results and using no Hankel transform (Majorana content fine), per your instructions. Landed **Wave 131** with two new, self-contained, `sorry`-free and axiom-clean deliverables (axioms limited to `propext`, `Classical.choice`, `Quot.sound`, verified on the headline theorems), both formalizing the finite-dimensional core of §4 "Quantum Mechanics versus a non-commutative generalization of probability theory" (`book.tex` line ~1550):

- `BookProof/ChapterGleasonPureMixed.lean` — the book's explicit 2-dimensional real example contrasting its wave-function (pure-state) parametrization with Gleason's theorem (mixed states). Over `Matrix (Fin 2) (Fin 2) ℝ` with `E ρ A = tr(ρ A)`, the two non-commuting projections `P0 = [[1,0],[0,0]]` and `Q = ½[[1,1],[1,1]]` (`P0_Q_not_commute`). Proves both projections are pure states, that each individually admits a pure state giving expectation ½, the headline `no_pure_state_both` (no pure state realizes both `tr(ρ P0)=½` and `tr(ρ Q)=½`), and the headline `exists_mixed_state_both` (the maximally mixed `½·I` does — exactly the density matrix Gleason provides), plus the summary `pure_vs_mixed_gleason_contrast`. The docstring records that the real-field restriction is the book's own ("the 2-dimensional real case"): over ℂ the state `[[½,i/2],[-i/2,½]]` is pure and satisfies both, so the impossibility is a genuinely real-field phenomenon.

- `BookProof/ChapterCollapseDiagonal.lean` — the collapse mechanism underlying §4's claim that the wave-function collapse keeps Quantum Mechanics inside Kolmogorov probability theory. Over an arbitrary finite index set, complex matrices: `trace_diagonal_mul` and the headline `trace_diag_nullDiag_zero` (a diagonal state assigns zero expectation to every null-diagonal operator — the post-collapse condition `E(O)=0`).

Both files are registered in `BookProof.lean`; `lake build BookProof` completes green. `ARISTOTLE_SUMMARY.md` (prepended a Wave 131 summary) and `BookProof/STATUS.md` (new Wave 131 section) were updated. All changes are committed and pushed.

Note: the only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, an unrelated thread that already had errors before this work.

# Summary of latest changes (Wave 131) — §4 "Quantum Mechanics versus a non-commutative generalization of probability theory": the pure- vs. mixed-state (Gleason) contrast and the collapse mechanism

Continued the `book.tex` formalization on the main-conclusion thread (chapter *"Wave-function parametrization of a probability measure"*), staying off Gravity and the Bell/CHSH comparison results and using no Hankel transform (Majorana content fine), per your instructions. Landed **Wave 131** with two new, self-contained, `sorry`-free and axiom-clean deliverables (axioms limited to `propext`, `Classical.choice`, `Quot.sound`, verified on the headline theorems). Both formalize the self-contained finite-dimensional core of the book's §4 (`book.tex` line ~1550), which contrasts the book's own wave-function (pure-state) parametrization with Gleason's theorem (general density / mixed states).

- `BookProof/ChapterGleasonPureMixed.lean` — the book's explicit **2-dimensional real** example. Over `Matrix (Fin 2) (Fin 2) ℝ` with expectation `E ρ A = tr(ρ A)`, the two non-commuting projections `P0 = [[1,0],[0,0]]` and `Q = ½[[1,1],[1,1]]` (`P0_Q_not_commute`). A *pure state* `IsPureState` is a real symmetric idempotent of unit trace (an orthogonal projection onto a line); a *mixed state* `IsMixedState` is a positive-semidefinite matrix of unit trace. Proves `P0_isPure`/`Q_isPure`, `E_Q_P0`/`E_P0_Q` (`= ½`), `exists_pure_expP0`/`exists_pure_expQ` (there **is** a pure state giving `tr(ρ P0)=½`, resp. `tr(ρ Q)=½`), the headline **`no_pure_state_both`** (there is **no** pure state satisfying both `tr(ρ P0)=½` and `tr(ρ Q)=½`), `halfI_isMixed`/`halfI_not_pure`, the headline **`exists_mixed_state_both`** (but the mixed state `½·I` does satisfy both, as Gleason provides), and the summary `pure_vs_mixed_gleason_contrast`. The docstring records that the restriction to the *real* field is the book's own ("the 2-dimensional real case"): over `ℂ` the state `[[½, i/2],[-i/2, ½]]` is pure and satisfies both, so `no_pure_state_both` is a genuinely real-field phenomenon.

- `BookProof/ChapterCollapseDiagonal.lean` — the collapse mechanism underlying §4's claim that the wave-function collapse keeps Quantum Mechanics inside Kolmogorov probability theory. Over an arbitrary finite index set `Fin n`, complex matrices, with `IsDiagonal ρ` (off-diagonal entries vanish): `trace_diagonal_mul` (`tr(ρ O) = ∑ i, ρ i i · O i i` for diagonal `ρ`), the headline **`trace_diag_nullDiag_zero`** (the book's *"if an operator `O` has null diagonal … then `tr(ρ O)=0` for any diagonal `ρ`"* — the post-collapse condition `E(O)=0`), and `trace_diagonal_mul_diag` for the surviving diagonal part.

Both files are registered in `BookProof.lean`; `lake build BookProof` completes green (the only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, an unrelated thread that already had errors). A new Wave 131 section was recorded in `BookProof/STATUS.md`. All changes are committed and pushed.

# Summary of changes for run 80608ed8-655c-4b81-940f-867d470a91c5
Continued the `book.tex` formalization on the main-conclusion thread (chapter *"Wave-function parametrization of a probability measure"*), staying off Gravity and the Bell/CHSH comparison results and using no Hankel transform, per your instructions. Landed Wave 130 with two new, self-contained, `sorry`-free and axiom-clean deliverables (axioms limited to `propext`, `Classical.choice`, `Quot.sound`, verified on the headline theorems):

- `BookProof/ChapterConservative.lean` — §8 "Conservative transformations". Models the book's unitary time-evolution `U(t) = e^{iHt}` for a self-adjoint Hamiltonian `H` (over a finite index set, complex matrices) and proves it is a conservative/measure-preserving transformation: `timeEvo_zero` (`U(0)=1`), `timeEvo_add` (one-parameter group law `U(s)·U(t)=U(s+t)`), `timeEvo_unitary`/`timeEvo_unitary'` (`U(t)` is unitary), `timeEvo_mem_unitaryGroup`, `timeEvo_inv` (`U(t)·U(-t)=1`), and the headline `timeEvo_conj_trace` (conjugating a density operator `ρ` by `U(t)` preserves its trace, `tr(U(t) ρ U(t)ᴴ)=tr ρ`, so total probability is conserved).

- `BookProof/ChapterSymmetryRep.lean` — §7 "Symmetries and unitary representations". Building on the previous file, it proves `timeEvoU_one` and `timeEvoU_mul` inside the unitary group and bundles them into `timeEvoRep`: a group homomorphism (`MonoidHom`) from `Multiplicative ℝ` into `Matrix.unitaryGroup n ℂ`, `t ↦ e^{iHt}` — the concrete one-parameter unitary representation of the time-translation symmetry group `ℝ`, with `timeEvoRep_apply` identifying its underlying matrix with `timeEvo H t`.

Both files are registered in `BookProof.lean`, and `lake build BookProof` (and building the two new modules explicitly) completes green with no linter warnings. I recorded a new Wave 130 section in `BookProof/STATUS.md` and updated `ARISTOTLE_SUMMARY.md` (prepended a Wave 130 summary). All changes are committed and pushed.

Note: the only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, a separate thread that already had errors and is unrelated to this work.

# Summary of latest changes (Wave 130) — conservative transformations and one-parameter unitary representations: `U(t)=e^{iHt}`

Continued the `book.tex` formalization on the main-conclusion thread (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform, Majorana content fine).

**New deliverable — `BookProof/ChapterConservative.lean` (Wave 130).** Formalized the self-contained finite-dimensional core of the book's section *"8. Conservative transformations"* (chapter *"Wave-function parametrization of a probability measure"*, `book.tex` line ~1917): a conservative (canonical) transformation preserving the measure is realized by a **unitary time-evolution** `U(t) = e^{iHt}` for a self-adjoint Hamiltonian `H` (*"any unitary automorphism can be defined as a time-evolution, for some Hamiltonian and time"*), and such a transformation *preserves the measure* (total probability).

Over a finite index set `n` and complex matrices, with `timeEvo H t = NormedSpace.exp ((t : ℂ) • (Complex.I • H))` modelling the book's `e^{iHt}`, the file proves:
- `timeEvo_zero` — `U(0) = 1`;
- `timeEvo_commute` — the exponents at two times commute;
- `timeEvo_add` — the one-parameter group law `U(s)·U(t) = U(s+t)`;
- `timeEvo_unitary` / `timeEvo_unitary'` — `U(t)` is unitary (`U(t)ᴴ U(t) = 1` and `U(t) U(t)ᴴ = 1`), via `Matrix.exp_conjTranspose` and the skew-Hermiticity of `iH`;
- `timeEvo_mem_unitaryGroup` — hence `U(t) ∈ unitaryGroup n ℂ`;
- `timeEvo_inv` — the inverse is the time-reversed evolution, `U(t)·U(-t) = 1`;
- headline `timeEvo_conj_trace` — the conservative property: conjugating a density operator `ρ` by `U(t)` preserves its trace, `tr(U(t) ρ U(t)ᴴ) = tr ρ`, so total probability `tr ρ = 1` is preserved.

**Companion deliverable — `BookProof/ChapterSymmetryRep.lean` (Wave 130).** Formalized the self-contained core of the book's section *"7. Symmetries and unitary representations"* (`book.tex` line ~1857): *"When a subset of canonical transformations forms a group, such subset is always a linear unitary representation of a group which is then called symmetry group."* The concrete self-contained instance is the one-parameter **time-translation group**. Building on `ChapterConservative`, the file proves `timeEvoU_one` (`U(0)=1` in the unitary group) and `timeEvoU_mul` (`U(s+t)=U(s)·U(t)`), and bundles them into `timeEvoRep`: a `MonoidHom` from `Multiplicative ℝ` (the additive reals viewed multiplicatively) into `Matrix.unitaryGroup n ℂ`, `t ↦ e^{iHt}` — a genuine one-parameter unitary representation of the symmetry group `ℝ`; `timeEvoRep_apply` identifies its underlying matrix with `timeEvo H t`.

Both files are `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified on the headlines), are registered in `BookProof.lean`, and `lake build BookProof` completes green. Updated `BookProof/STATUS.md` (new Wave 130 section). The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean` (a separate thread that already had errors, unrelated to this work).

---

# Summary of changes for run aace1bff-fc3a-4c3c-bfd3-2d231db30d3d
Continued the `book.tex` formalization on the main-conclusion thread (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform, Majorana content fine).

**New deliverable — `BookProof/ChapterBayesInference.lean` (Wave 129).** Formalized the self-contained finite-dimensional core of the book's central §2 compatibility claim (chapter *"Wave-function parametrization of a probability measure"*, ~line 1338): *"given a Bayesian model, a prior probability and data that produce a posterior through Bayesian inference, there is a reversible model that produces the same posterior as a function of the prior."*

A finite Bayesian model is a prior `prior : X → ℝ` plus a likelihood/Markov kernel `L : X → Y → ℝ` (each row a distribution on the data `Y`). The file defines the joint density `joint = prior x · L x y`, the evidence `evidence y = ∑_x prior x · L x y`, and the Bayes `posterior y x = prior x · L x y / evidence y`, and proves:
- `joint_nonneg` / `joint_sum_one` — the joint is a probability distribution on `X × Y`;
- `evidence_eq_marginal` / `evidence_nonneg`; `posterior_nonneg` / `posterior_sum_one` (posterior is a distribution on `X` for data with positive evidence);
- `posterior_eq_joint_div_evidence` — the Bayes chain rule;
- headline `posterior_eq_born_conditional` — with the wave-function `Ψ = √p`, the Bayes posterior equals the Born-rule conditional `|Ψ(x,y)|² / ∑_{x'} |Ψ(x',y)|²`;
- headline `exists_unitary_reproduces_posterior` — there is a *unitary* matrix `U` on `X × Y` and a column index `i₀` with `‖U(x,y) i₀‖² = p(x,y)` such that for every data point with positive evidence the Bayes posterior is reproduced by Born-rule conditioning of that column (the reversible/unitary model reproducing Bayesian inference). It reuses the §3 unitary parametrization `ChapterJointUnitary.exists_unitary_joint`.

The file is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified on the headline), registered in `BookProof.lean`, and `lake build BookProof` completes green. Updated `BookProof/STATUS.md` (new Wave 129 section) and `ARISTOTLE_SUMMARY.md`. All changes committed and pushed.

The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean` (a separate thread that already had errors, unrelated to this work).

# Summary of latest changes (Wave 129) — unitary inference reproduces Bayesian inference
Continued the `book.tex` formalization on the main-conclusion thread (per your instructions: chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform, Majorana content fine).

**New work — `BookProof/ChapterBayesInference.lean`.** Formalized the self-contained finite-dimensional core of the book's central §2 compatibility claim (chapter *"Wave-function parametrization of a probability measure"*, `book.tex` line ~1338): *"given a Bayesian model, a prior probability and data that allows to produce a posterior probability through Bayesian inference, there is a reversible model that produces the same posterior probability as a function of the prior probability."* A finite Bayesian model is a prior `prior : X → ℝ` together with a likelihood / Markov kernel `L : X → Y → ℝ` (each row a probability distribution on the data `Y`). The file defines the joint density `joint = prior x · L x y`, the evidence `evidence y = ∑_x prior x · L x y`, and the Bayes `posterior y x = prior x · L x y / evidence y`, and proves: `joint_nonneg` / `joint_sum_one` (the joint is a probability distribution on `X × Y`); `evidence_eq_marginal` / `evidence_nonneg`; `posterior_nonneg` / `posterior_sum_one` (for data with positive evidence the posterior is a distribution on `X`); `posterior_eq_joint_div_evidence` (the Bayes chain rule); the headline **`posterior_eq_born_conditional`** (with the wave-function `Ψ = √p`, the Bayes posterior equals the Born-rule conditional `|Ψ(x,y)|² / ∑_{x'} |Ψ(x',y)|²`); and the headline **`exists_unitary_reproduces_posterior`** (there is a *unitary* matrix `U` on `X × Y` and a column index `i₀` with `‖U (x,y) i₀‖² = p(x,y)` such that, for every data point `y` with positive evidence, the Bayes posterior is reproduced by Born-rule conditioning of that column of `U` — i.e. the reversible/unitary model reproduces Bayesian inference). It reuses the §3 unitary parametrization `ChapterJointUnitary.exists_unitary_joint`.

The file is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, verified on the headline theorem), is registered in `BookProof.lean`, and `lake build BookProof` completes green. I updated `BookProof/STATUS.md` (new Wave 129 section) and this file. All changes are committed and pushed. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, unrelated to this work.

# Summary of changes for run 13737a83-0439-4b91-a24e-1650ae0a427d
Continued the `book.tex` formalization on the main-conclusion thread (per your instructions: chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform, Majorana content fine).

**New work — `BookProof/ChapterConditional.lean`.** After surveying the existing coverage (the book is already extensively formalized across ~150 files), I found an uncovered self-contained piece of the book's central §3 theorem in *"Wave-function parametrization of a probability measure"* ("Any conditional probability measure in a standard measure space is parametrized by a unitary operator"). The joint-distribution half of the theorem's converse was already done (`ChapterJointUnitary`); this wave adds the **marginal / regular-conditional** layer of the converse:

> "Given a bounded operator B with tr(BB†)=1, then p(x,y)=|B(y,x)|² is a joint probability distribution; if p(x)={B†B}(x,x)>0 for all x, then p(y|x) is a regular conditional probability density."

Over finite index sets, `RCLike`-agnostic, with `pJoint = ‖B y x‖²`, `pMarg = ∑_y ‖B y x‖²`, `pCond = pJoint/pMarg`, the file proves: `pMarg_eq_diagBHB` (the marginal equals the diagonal of the Gram matrix BᴴB, i.e. the book's p(x)={B†B}(x,x)); `trace_gram_eq_one` (normalization tr(BᴴB)=tr(BB†)=1); `pJoint_sum_one`/`pMarg_sum_one` (joint on X×Y and marginal on X are genuine probability distributions); nonnegativity lemmas; `pCond_sum_one` (for every x with p(x)>0 the conditional p(y|x) sums to 1 — the regular conditional density); and `pJoint_eq_cond_mul_marg` (the chain rule p(x,y)=p(y|x)·p(x)).

The file is `sorry`-free and axiom-free (only `propext`, `Classical.choice`, `Quot.sound`, verified on the headline theorems), is registered in `BookProof.lean`, and `lake build BookProof` completes green. I updated `BookProof/STATUS.md` (new Wave 128 section) and `ARISTOTLE_SUMMARY.md` (new top section). All changes are committed and pushed.

The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, a separate thread that already had errors before this work and is unrelated to it.

# Summary of latest changes (Wave 128)
Executed the next step of the `book.tex` formalization, staying on the main-conclusion thread as instructed (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana content fine).

**New work — `BookProof/ChapterConditional.lean`.** Formalized the self-contained
finite-dimensional core of the **converse** direction of the book's central §3
theorem in *"Wave-function parametrization of a probability measure"* (book §3
*"Any conditional probability measure in a standard measure space is parametrized
by a unitary operator"*, `book.tex` line ~1478, paragraph *"The converse also
holds"*): *"Given a bounded operator `B`, such that `tr(BB†)=1`, then it defines a
joint probability distribution `p(x,y)=|B(y,x)|²`. From the joint probability, if
`p(x)={B†B}(x,x)>0` for all `x∈X`, then we can define a regular conditional
probability density."*

The joint-distribution half of the converse is already
`ChapterJointUnitary.sqAbs_isProb_of_frobenius_one`; this wave adds the **marginal
/ regular-conditional** layer. Over finite index sets `X, Y`, `RCLike`-agnostic,
with `pJoint B x y = ‖B y x‖²`, `pMarg B x = ∑_y ‖B y x‖²`, and
`pCond B x y = pJoint / pMarg`, the file proves:
- `pMarg_eq_diagBHB` (headline) — the book's `p(x) = {B†B}(x,x)`: the marginal is
  the diagonal of the Gram matrix `Bᴴ B`;
- `trace_gram_eq_one` — the normalization `tr(BᴴB) = tr(BB†) = 1` in trace form;
- `pJoint_sum_one` / `pMarg_sum_one` — the joint (on `X×Y`) and marginal (on `X`)
  are genuine probability distributions;
- `pJoint_nonneg` / `pMarg_nonneg` / `pCond_nonneg` — nonnegativity;
- `pCond_sum_one` (headline) — for every `x` with `p(x)>0`, the conditional
  `p(y|x)=p(x,y)/p(x)` is a probability distribution on `Y` (the regular
  conditional density);
- `pJoint_eq_cond_mul_marg` — the chain rule `p(x,y)=p(y|x)·p(x)`, reconstructing
  the joint from the marginal and the conditional.

The file is `sorry`-free and axiom-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed on the headline theorems), is registered in
`BookProof.lean`, and `lake build BookProof` completes green. Documentation
updated in `BookProof/STATUS.md` (new Wave 128 section). The only remaining
repository build failure is the pre-existing, out-of-scope
`RiemannProof/RandomMap.lean` (a separate thread that already had errors and is
unrelated to this work).

---

# Summary of changes for run 69977102-c289-4dd3-a2a8-e1d6a578f054
Executed the next step of the `book.tex` formalization, staying on the main-conclusion thread as instructed (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana content fine).

**New work — `BookProof/ChapterMarkovEntropy.lean`.** Formalized the self-contained finite-dimensional content of the book's §2 claim ("Probability updates, machine learning and Quantum Mechanics") in its central foundational chapter *"Wave-function parametrization of a probability measure"* (book §2, near line 1338), which motivates the book's reversible "Unitary inference" by contrasting it with ordinary Bayesian inference: *"Markov processes … there is an ordering (related with the concept of entropy) with respect to which all continuous-time Markov processes are monotonic. Thus, Bayesian inference is irreversible."*

The self-contained mathematical core is the discrete **H-theorem**: a doubly-stochastic (bistochastic) Markov transition cannot decrease Shannon entropy, with equality exactly on reversible (permutation) transitions. With `entropy p = ∑ a, negMulLog (p a)`, `applyMarkov M p j = ∑ i, M j i * p i`, and `IsDoublyStochastic M` (nonnegative entries, row and column sums both = 1), the file proves:
- `entropy_applyMarkov_ge` (headline) — `H(p) ≤ H(M p)` for a doubly-stochastic `M` and any nonnegative `p`, via row-wise concave Jensen on `negMulLog` (`Real.concaveOn_negMulLog`) using the row-sum constraint, then reindexing and the column-sum constraint;
- `permMatrix`, `permMatrix_doublyStochastic`, `applyMarkov_permMatrix` (`(M p) j = p (σ⁻¹ j)`);
- `entropy_applyMarkov_permMatrix` (headline, reversible boundary case) — a permutation (deterministic, invertible) transition preserves entropy exactly.

The contrast — permutation maps keep entropy fixed while a genuinely mixing doubly-stochastic step can only raise it — is precisely the irreversibility the book invokes.

The file is `sorry`-free and axiom-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed on the two headline theorems), builds with no warnings, is registered in `BookProof.lean`, and `lake build BookProof` completes green. Documentation updated in `BookProof/STATUS.md` (new Wave 127 section) and `ARISTOTLE_SUMMARY.md` (new top section). The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean` (a separate thread that already had errors and a `sorry`); it was left untouched. All changes committed and pushed.

# Summary of changes — Wave 127 (Markov entropy monotonicity / irreversibility)
Executed the next step of the `book.tex` formalization, staying on the main-conclusion thread as instructed (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana content is fine).

**New work — Wave 127: `BookProof/ChapterMarkovEntropy.lean`.** Formalized the self-contained finite-dimensional content of the book's §2 claim in its central foundational chapter *"Wave-function parametrization of a probability measure"* (§2 *"Probability updates, machine learning and Quantum Mechanics"*, `book.tex` line ~1338), which motivates the book's *reversible* "Unitary inference" by contrasting it with ordinary Bayesian inference: *"Markov processes cannot produce an arbitrary function of time, because there is an ordering (related with the concept of entropy) with respect to which all continuous-time Markov processes are monotonic. Thus, Bayesian inference is irreversible."* The self-contained mathematical core is the discrete **`H`-theorem** — a doubly-stochastic (bistochastic) Markov transition cannot decrease Shannon entropy, with equality exactly on the reversible (permutation) transitions. Consistently with the finite-dimensional models used throughout `BookProof`, it is stated over finite index sets `Fin n`.

With `entropy p = ∑ a, negMulLog (p a)`, `applyMarkov M p j = ∑ i, M j i * p i`, and `IsDoublyStochastic M` (nonnegative entries, row and column sums both `= 1`), the file proves:
- `entropy_applyMarkov_ge` (headline) — `H(p) ≤ H(M p)` for a doubly-stochastic `M` and any nonnegative `p` (row-wise concave Jensen on `negMulLog` using the row-sum constraint, then reindexing and the column-sum constraint);
- `permMatrix`, `permMatrix_doublyStochastic`, `applyMarkov_permMatrix` (`(M p) j = p (σ⁻¹ j)`);
- `entropy_applyMarkov_permMatrix` (headline, reversible boundary case) — a permutation (deterministic, invertible) transition preserves entropy exactly.

The contrast — permutation maps keep entropy fixed while a genuinely mixing doubly-stochastic step can only raise it — is precisely the irreversibility the book invokes. The file is `sorry`-free and axiom-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed on the two headline theorems), is registered in `BookProof.lean`, and `lake build BookProof` completes green. Documentation was updated in `BookProof/STATUS.md` (new Wave 127 section) and here. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean` (a separate thread that already had errors and a `sorry`); it was left untouched.

---

# Summary of changes for run 1afd916a-efb9-477d-bf60-96b576391a25
Executed the next step of the `book.tex` formalization, staying on the main-conclusion thread as instructed (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana content is fine).

**New work — Wave 126: `BookProof/ChapterKernelBound.lean`.** Formalized the self-contained analytic step used by the book's central §3 theorem *"Any conditional probability measure in a standard measure space is parametrized by a unitary operator"* (chapter *"Wave-function parametrization of a probability measure"*), which was not yet covered. On the way to the singular-value expansion `Ψ = W D U†` (already done in `ChapterB3`/`ChapterB3b`), the book views a normalized wave-function `Ψ ∈ L²(X×Y)` as an integral operator `Ψ{Φ}(y) = ∫ dx Ψ(x,y) Φ(x)` and remarks that "the Cauchy–Schwarz inequality implies … `Ψ(x,y)` is bounded when defined as an operator `Ψ : L²(X) → L²(Y)`." This is the classical Hilbert–Schmidt bound (operator norm ≤ the L²/Hilbert–Schmidt norm of the kernel). Consistently with the finite-dimensional models used throughout `BookProof`, it is stated for a discretized kernel over finite index sets, field-agnostic (`RCLike`).

With `kernelOp Ψ Φ y = ∑ x, Ψ y x * Φ x`, the file proves:
- `kernel_row_bound` — the row-wise Cauchy–Schwarz bound `‖Ψ{Φ}(y)‖² ≤ (∑ x ‖Ψ y x‖²)(∑ x ‖Φ x‖²)`;
- `kernel_hs_sq_bound` (headline) — the summed bound `∑ y ‖Ψ{Φ}(y)‖² ≤ (∑ y ∑ x ‖Ψ(y,x)‖²)(∑ x ‖Φ(x)‖²)`;
- `kernel_l2_bound` — the book's inequality in L² form, `‖Ψ{Φ}‖_{L²} ≤ ‖Ψ‖_{HS} · ‖Φ‖_{L²}`;
- `kernel_contraction` — the book's normalized conclusion: a normalized wave-function (`∑ y ∑ x ‖Ψ(y,x)‖² = 1`) yields a contraction, hence a bounded operator.

The file is `sorry`-free and axiom-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed on the two headline theorems), is registered in `BookProof.lean`, and `lake build BookProof` completes green. I also cleaned up the auto-generated proof (removed a leftover `exact?`, restored proper docstrings).

Documentation was updated in `BookProof/STATUS.md` (new Wave 126 section) and in `ARISTOTLE_SUMMARY.md` (new top section), as requested. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean` (a separate thread that already had errors and a `sorry`); it was left untouched. All changes have been committed and pushed.

# Summary of changes — Wave 126 (Cauchy–Schwarz / Hilbert–Schmidt boundedness of the kernel operator, Chapter B §3)
Executed the next step of the `book.tex` formalization, staying on the **main-conclusion** thread as instructed (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana content fine).

**New work — Wave 126: `BookProof/ChapterKernelBound.lean`.** Formalized the self-contained analytic step used by the book's central §3 theorem *"Any conditional probability measure in a standard measure space is parametrized by a unitary operator"* (chapter *"Wave-function parametrization of a probability measure"*, `book.tex` line ~1478), on the way to the singular-value expansion `Ψ = W D U†` already formalized in `ChapterB3`/`ChapterB3b`. Having written a joint density as `p(x,y) = |Ψ(x,y)|²` for a normalized wave-function `Ψ ∈ L²(X×Y)`, the book views `Ψ` as an integral operator `Ψ{Φ}(y) = ∫ dx Ψ(x,y) Φ(x)` and remarks that *"the Cauchy–Schwarz inequality implies … `Ψ(x,y)` is bounded when defined as an operator `Ψ : L²(X) → L²(Y)`"*. This is the classical **Hilbert–Schmidt bound**: an integral operator with an `L²` kernel is bounded, with operator norm at most the `L²` (Hilbert–Schmidt) norm of the kernel.

Consistently with the finite-dimensional models used throughout `BookProof` (e.g. the finite SVD in `ChapterB3b`), the kernel is discretized over finite index sets `ιx` (the sample space `X`) and `ιy` (`Y`), stated `RCLike`-field agnostically. With `kernelOp Ψ Φ y = ∑ x, Ψ y x * Φ x` (the book's `Ψ{Φ}(y)`), the file proves: `kernel_row_bound` (the row-wise Cauchy–Schwarz bound `‖Ψ{Φ}(y)‖² ≤ (∑ x ‖Ψ y x‖²)(∑ x ‖Φ x‖²)`); the headline **`kernel_hs_sq_bound`** (summing over outputs `y`: `∑ y ‖Ψ{Φ}(y)‖² ≤ (∑ y ∑ x ‖Ψ(y,x)‖²)(∑ x ‖Φ(x)‖²)`); **`kernel_l2_bound`** (the book's inequality verbatim in `L²` form, `‖Ψ{Φ}‖_{L²} ≤ ‖Ψ‖_{HS} · ‖Φ‖_{L²}`); and **`kernel_contraction`** (the book's normalized conclusion: for a normalized wave-function `∑ y ∑ x ‖Ψ(y,x)‖² = 1` the operator is a contraction `∑ y ‖Ψ{Φ}(y)‖² ≤ ∑ x ‖Φ(x)‖²`, hence bounded).

The file is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified via `lean_verify` on `kernel_l2_bound` and `kernel_contraction`), is registered in `BookProof.lean`, and `lake build BookProof` completes green. Documentation was updated in `BookProof/STATUS.md` (new Wave 126 section) and this file as requested. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean` (a separate thread with prior errors and a `sorry`), left untouched. All changes committed and pushed.

# Summary of changes for run 55480637-1909-4aa1-bbf2-b82f58c58f6b
Executed the next step of the `book.tex` formalization, staying on the main-conclusion thread as instructed (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana content fine).

**New work — Wave 125: `BookProof/ChapterQuantizationWeyl.lean`.** Formalized the self-contained algebraic content of the book's central **quantization** claim, from the section *"Quantization due to time evolution"* (in the chapter "Quantization due to time-evolution: Yang-Mills and Classical Statistical Field Theory"): that the canonical commutation relations of position and momentum — strictly, the **Weyl relations**, the exponentiated CCR — arise from a non-deterministic time-evolution acting by conjugation, via the Trotter/Baker–Campbell–Hausdorff formula `e^{εA} e^{B} e^{-εA} = e^{B - ε[A,B] + O(ε²)}` and the concrete `e^{iεp²} e^{ix} e^{-iεp²} = e^{i(x+εp)}`.

Since the full CCR `[x,p] = i·1` has no finite-dimensional representation, the honest finite model used is the **Heisenberg algebra / group** of 3×3 real matrices — `Xgen = e₁₂` (position), `Ygen = e₂₃` (momentum), `Zgen = e₁₃` (central `[X,Y]`), all nilpotent so the exponential series terminates and every BCH/Trotter identity becomes **exact** (no `O(ε²)` remainder). The file proves:
- `comm_XY` (`[X,Y] = Z`) and `comm_scaled` (`[aX, bY] = (ab)Z`);
- `Zgen_central` and `Zgen_sq` (Z is central and squares to zero);
- `Heis_mul` — the Heisenberg group law `H(a,b,c)·H(a',b',c') = H(a+a', b+b', c+c'+a·b')`;
- `exp_Ngen` — the exponential map `exp(aX+bY+cZ) = H(a, b, c + ab/2)` (via three-step nilpotency and the `exp` power series);
- **`weyl`** — the Weyl relation `exp(aX)·exp(bY) = exp(aX + bY + (ab/2)Z)` (the exponentiated CCR / exact BCH product formula, the `(ab/2)Z` correction being `½[aX,bY]`); and
- **`weyl_shift`** — the conjugation/quantization identity `exp(aX)·exp(bY)·exp(-aX) = exp(bY + (ab)Z) = exp(bY + a[X,Y])`, the exact finite-dimensional model of the book's `e^{εA}e^{B}e^{-εA}=e^{B-ε[A,B]}` and `e^{iεp²}e^{ix}e^{-iεp²}=e^{i(x+εp)}`.

The file is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified via the axiom check on the two headline theorems `weyl` and `weyl_shift`), is registered in `BookProof.lean`, and `lake build BookProof` completes green.

Documentation updated in `BookProof/STATUS.md` (new Wave 125 section). The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean` (a separate thread with prior errors and `sorry`s), left untouched. All changes committed and pushed.

# Summary of changes for run 2ae1c62a-b82f-413c-b2bf-c5c914b6ee39
Executed the next step of the `book.tex` formalization, staying on the main-conclusion thread as instructed (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana content fine).

**New work — Wave 124: `BookProof/ChapterGleason2D.lean`.** Formalized the concrete 2-dimensional real example from §4 of the foundational chapter *"Wave-function parametrization of a probability measure"* ("Quantum Mechanics versus a non-commutative generalization of probability theory"), which contrasts the book's wave-function parametrization (only *commuting* projections, i.e. **pure states**) with **Gleason's theorem** (which needs *non-commuting* projections and **mixed states**).

Using the two non-commuting rank-one projections on `ℝ²` — `P₁ = !![1,0;0,0]` and `Q = ½!![1,1;1,1]` — with pure states modelled as `ρ = v vᵀ` and expectation `tr(ρ A)`, the file proves:
- `P1_Q_noncomm` (P₁Q ≠ QP₁);
- `P1_isProjection` / `Q_isProjection` (each a symmetric idempotent of trace one);
- the expectation formulas `expec_pure_P1` (= v₀²) and `expec_pure_Q` (= (v₀+v₁)²/2);
- `pure_realizes_P1` and `pure_realizes_Q` (a pure state achieves each constraint tr(ρ·)=½ separately);
- **`no_pure_state_both`** — no pure state realizes both tr(ρP₁)=½ and tr(ρQ)=½ at once; and
- **`mixed_state_both`** — the maximally mixed state ρ=½·I is a density matrix realizing both, exactly as Gleason's theorem predicts.

The file is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified via `#print axioms` on the two headline theorems), is registered in `BookProof.lean`, and `lake build BookProof` completes green.

Documentation updated in `BookProof/STATUS.md` (new Wave 124 section) and `ARISTOTLE_SUMMARY.md` (new top section), as requested. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean` (a separate thread with prior errors and a `sorry`), left untouched. All changes committed and pushed.

# Summary of changes — Wave 124 (2D Gleason comparison: pure vs. mixed states)
Executed the next step of the `book.tex` formalization, staying on the main-conclusion thread as instructed (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana content fine).

**New work — Wave 124: `BookProof/ChapterGleason2D.lean`.** Formalized the concrete **2-dimensional real** example the book uses in §4 of the foundational chapter *"Wave-function parametrization of a probability measure"* (`book.tex` line ~1550), *"Quantum Mechanics versus a non-commutative generalization of probability theory"*. There the book contrasts its own wave-function parametrization — which uses only **commuting** projections and hence **pure states** — with **Gleason's theorem**, which handles **non-commuting** projections and requires **mixed states**.

Using the two non-commuting rank-one projections on `ℝ²`, `P₁ = !![1,0;0,0]` (first axis) and `Q = ½!![1,1;1,1]` (diagonal `(1,1)` direction), and modelling a real pure state by `ρ = v vᵀ` (`pure`) for a unit vector `v` with expectation `expec ρ A = tr(ρ A)`, the file proves: `P1_Q_noncomm` (`P₁Q ≠ QP₁`); `P1_isProjection` / `Q_isProjection` (each is a symmetric idempotent of trace one); the expectation formulas `expec_pure_P1` (`tr(v vᵀ P₁) = v₀²`) and `expec_pure_Q` (`tr(v vᵀ Q) = (v₀+v₁)²/2`); `pure_realizes_P1` and `pure_realizes_Q` (a pure state achieves each constraint `tr(ρ·)=½` separately); the headline **`no_pure_state_both`** (**no** pure state realizes both `tr(ρ P₁)=½` and `tr(ρ Q)=½` at once — the constraints force `v₀²=v₁²=½` yet `v₀v₁=0`, a contradiction); and **`mixed_state_both`** (the maximally mixed state `ρ=½·I` is a density matrix and realizes **both** constraints, exactly as Gleason's theorem predicts).

The file is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified via `lean_verify`/`#print axioms` on `no_pure_state_both` and `mixed_state_both`), is registered in `BookProof.lean`, and `lake build BookProof` completes green. Documentation was updated in `BookProof/STATUS.md` (new Wave 124 section) and this file as requested. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean` (a separate thread with prior errors and a `sorry`), left untouched. All changes committed and pushed.

# Summary of changes for run 5b592783-26f6-48cc-a4d6-4456d221b350
Executed the next step of the `book.tex` formalization, staying on the main-conclusion thread as instructed (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana content fine).

**New work — Wave 123: `BookProof/ChapterElectroweakFieldStrength.lean`.** Formalized the self-contained algebraic content of the electroweak field-strength tensors from the book's Standard-Model section *"Majorana spinors in the Standard Model"* (chapter *"On the physical parity transformation and antiparticles"*, `book.tex` line ~7728), which defines them as **trace projections** of the covariant-derivative commutator onto the Pauli generators:
`W_{μν}^j = -(i/g)·tr([D_μ,D_ν] τ^j) = ∂_μ W_ν^j − ∂_ν W_μ^j − g ε^{jkl} W_μ^k W_ν^l` and `B_{μν} = -(i/g')·tr([D_μ,D_ν] σ_3) = ∂_μ B_ν − ∂_ν B_μ`.

Reusing the Pauli matrices already in `ChapterParitySU2`/`ChapterParity`, the file introduces the totally antisymmetric `su(2)` structure constants `eps` (ε_{jkl}, with `eps_cyclic`/`eps_swap`) and proves: `pauli_trace_orthonormal` (tr(σ_a σ_b)=2δ_{ab}), `pauli_triple_trace` (tr(σ_a σ_b σ_c)=2i ε_{abc}), `pauli_commutator` (the su(2) relations [σ_k,σ_l]=2i∑_m ε_{klm} σ_m) and `pauli_commutator_trace`. It models the connection `∑_j W^j(σ_j/2)` and the curvature `Fmat = i g(∑_j G_j σ_j/2)+(i g)²[A_μ,A_ν]` written from [D_μ,D_ν] (with the curl G_j = ∂_μ W_ν^j − ∂_ν W_μ^j as an abstract input), with projection `proj g F j = -(i/g)·tr(F σ^j)`. The supporting `linear_trace` and `connection_comm_trace` assemble into the headline **`electroweak_fieldStrength`** (the book's `W_{μν}^j` formula) and the companion **`abelian_fieldStrength`** (the quadratic term drops for a single abelian U(1) field, giving the book's `B_{μν}`).

The file is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified via `#print axioms` on the headlines), is registered in `BookProof.lean`, and `lake build BookProof` completes green (8180 jobs). Documentation was updated in `BookProof/STATUS.md` (new Wave 123 section) and `ARISTOTLE_SUMMARY.md` (new top section) as requested. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean` (a separate thread with prior errors and a `sorry`), left untouched. All changes committed and pushed.

# Summary of changes — Wave 123 (electroweak `SU(2)_L` field strength via the trace projection)
Executed the next step of the `book.tex` formalization, staying on the main-conclusion thread as instructed (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana content included).

**New work — Wave 123: `BookProof/ChapterElectroweakFieldStrength.lean`.** Formalized the self-contained algebraic content of the electroweak field-strength tensors from the book's Standard-Model section *"Majorana spinors in the Standard Model"* (chapter *"On the physical parity transformation and antiparticles"*, `book.tex` line ~7728). The book defines these tensors as **trace projections** of the covariant-derivative commutator onto the Pauli generators, `W_{μν}^j = -\frac{i}{g}\,\mathrm{tr}([D_μ,D_ν]\,τ^j) = ∂_μ W_ν^j - ∂_ν W_μ^j - g\,ε^{jkl} W_μ^k W_ν^l` and `B_{μν} = -\frac{i}{g'}\,\mathrm{tr}([D_μ,D_ν]\,σ_3) = ∂_μ B_ν - ∂_ν B_μ`. Reusing the Pauli matrices of `ChapterParitySU2`/`ChapterParity`, the file introduces the totally antisymmetric `su(2)` structure constants `eps` (`ε_{jkl}`; `eps_cyclic`, `eps_swap`) and proves the generator identities `pauli_trace_orthonormal` (`tr(σ_a σ_b)=2δ_{ab}`), `pauli_triple_trace` (`tr(σ_a σ_b σ_c)=2i ε_{abc}`), `pauli_commutator` (`[σ_k,σ_l]=2i∑_m ε_{klm} σ_m`), and `pauli_commutator_trace` (`tr([σ_k,σ_l]σ_j)=4i ε_{klj}`). It then models the `su(2)`-valued connection `connection W = ∑_j W^j (σ_j/2)`, the curvature `Fmat g G Wμ Wν = i g(∑_j G_j σ_j/2)+(i g)²[A_μ,A_ν]` written from `[D_μ,D_ν]` (with the curl `G_j = ∂_μ W_ν^j - ∂_ν W_μ^j` as an abstract input), and the trace projection `proj g F j = -\frac{i}{g}\,\mathrm{tr}(F σ^j)`. Supporting lemmas `linear_trace` (linear part ↦ `G_j`) and `connection_comm_trace` (quadratic part ↦ `i∑_{k,l} ε_{klj} W_μ^k W_ν^l`) assemble into the headline **`electroweak_fieldStrength`** (`proj g (Fmat …) j = G_j - g∑_{k,l} ε^{jkl} W_μ^k W_ν^l`, the book's `W_{μν}^j`), with companion **`abelian_fieldStrength`** showing the quadratic term drops for a single abelian `U(1)` field (the book's `B_{μν}`).

The file is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified with `#print axioms`), is registered in `BookProof.lean`, and `lake build BookProof` completes green (8180 jobs). The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean` (a separate thread with prior errors and a `sorry`), which was left untouched.

# Summary of changes for run 8278272b-7b83-4f05-8c77-daa7924d692e
Executed the next step of the `book.tex` formalization, staying on the main-conclusion thread as instructed (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana content included).

**New work — Wave 122: `BookProof/ChapterBosonicCCR.lean`.** Formalized the self-contained algebraic content of the **bosonic** paragraph of the book section *"Majorana spinors in canonical quantization and antiparticles"* (chapter *"On the physical parity transformation and antiparticles"*) — the companion of the fermionic Clifford/CAR construction already in `BookProof/ChapterMajoranaClifford.lean`. The book states that for bosons the commutation relation `[a(v),a(w)] = ⟪v, J w⟫ i` (a symplectic product) replaces the fermionic anticommutation, with the field operators `a(v)` again self-adjoint. Since the Weyl/CCR algebra has no finite-dimensional representation and Mathlib has no Weyl algebra, the two book relations are packaged (like the existing `GhostCAR` structure) as a hypothesis structure `BosonicCCR` on an abstract complex `*`-algebra with a real-linear field map `a : V →ₗ[ℝ] R`. Proved: `symplectic_antisymm`/`symplectic_self` (the symplectic form from a skew J is antisymmetric and alternating), `field_commute_self_scalar`, `commutator_antiSelfAdjoint`, `field_comp_selfAdjoint` (real representations preserve self-adjointness), `ccr_symplectic_invariant` (symplectic symmetries transport the CCR), the creation/annihilation split `ann`/`cre` with `star_ann`/`star_cre`/`ann_add_cre`, `commutator_field_Jfield`, and `commutator_cre_ann` (the number-operator CCR `[c(v),a(v)] = (2‖v‖²)·1`, the bosonic analogue of `[a,a†]=1`).

The file is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified with `#print axioms`), is registered in `BookProof.lean`, and `lake build BookProof` completes green. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean` (a separate thread with prior errors and a `sorry`), which was left untouched.

Documentation updated in `BookProof/STATUS.md` (Wave 122) and `ARISTOTLE_SUMMARY.md` (new top section). All changes committed and pushed.

# Summary of changes — Wave 122 (Bosonic canonical commutation relations: the CCR companion of the Majorana quantization)
Executed the next step of the `book.tex` formalization, staying on the main-conclusion thread as instructed (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana content fine).

**New work — Wave 122: `BookProof/ChapterBosonicCCR.lean`.** Formalized the self-contained algebraic content of the **bosonic** paragraph of the book section *"Majorana spinors in canonical quantization and antiparticles"* (chapter *"On the physical parity transformation and antiparticles"*, `book.tex` line ~7700) — the companion of the fermionic Clifford/CAR construction already in `ChapterMajoranaClifford.lean` (Wave 118). There the book states that for bosons a commutation relation `[a(v),a(w)] = ⟪v, J w⟫ i` replaces the fermionic anticommutation, a symplectic product replacing the inner product, with the field operators `a(v)` again self-adjoint ("a particle which is its own antiparticle"). Since the Weyl/CCR algebra has no finite-dimensional representation and Mathlib has no ready-made Weyl algebra, the two book relations are packaged (exactly as `ChapterBRSTNilpotent`'s `GhostCAR` does for the fermionic ghosts) as a hypothesis structure `BosonicCCR` on an abstract complex `*`-algebra `R`, with a real-linear field map `a : V →ₗ[ℝ] R`, `selfAdjoint : star (a v) = a v`, and `ccr : a v * a w − a w * a v = algebraMap ℂ R (i · ⟪v, J w⟫)`. Proved (sorry-free, axiom-free — only `propext`, `Classical.choice`, `Quot.sound`):
- `symplectic_antisymm` / `symplectic_self` — the symplectic form ω(v,w)=⟪v,Jw⟫ from a skew J is antisymmetric and alternating (ω(v,v)=0);
- `field_commute_self_scalar` — the CCR scalar vanishes for v=w (a field commutes with itself);
- `commutator_antiSelfAdjoint` — [a(v),a(w)] is anti-self-adjoint, the self-adjointness constraint on i·ω·1;
- `field_comp_selfAdjoint` — real representations preserve self-adjointness: a(Tv) is self-adjoint for any real-linear T;
- `ccr_symplectic_invariant` — a symplectic symmetry T (preserving ω) transports the CCR unchanged to a∘T;
- `ann`/`cre` with `star_ann`/`star_cre` — the creation/annihilation split a(v±iJv); the involution swaps annihilation and creation; `ann_add_cre` recovers a v + a v;
- `commutator_field_Jfield` — [a(v),a(Jv)] = −(i·‖v‖²)·1 (using J²=−1);
- `commutator_cre_ann` — the number-operator CCR [c(v),a(v)] = (2‖v‖²)·1, the bosonic analogue of [a,a†]=1.

Registered in `BookProof.lean`; `lake build BookProof` completes green (the only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched). Documentation updated in `BookProof/STATUS.md` (Wave 122). All changes committed and pushed.

# Summary of changes for run 4a6baaeb-2a73-48dc-8979-a1d852dc6bc3
Executed the next step of the `book.tex` formalization, staying on the main-conclusion thread as instructed (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana content fine).

**New work — Wave 121: `BookProof/ChapterFreeEMField.lean`.** Formalized the self-contained content of the book section *"Free electromagnetic field: an exact example"* (chapter "Timepiece and the Gribov ambiguity"), which specializes the preceding Yang-Mills machinery to the abelian (electromagnetic) case by "setting the structure constants f_{abc} to zero". Building on `BookProof/ChapterYangMillsFieldStrength.lean`, it defines the abelian field strength / single curl component `emFieldStrength δ A j k = δ_j (A_k) − δ_k (A_j)` and proves:
- `emFieldStrength_antisymm` — F_{jk} = −F_{kj};
- `emFieldStrength_gauge_invariant` — abelian gauge invariance ("no Gribov ambiguity"): invariance under A_j ↦ A_j + δ_j θ, the curl of a gradient vanishing by commutativity of the partial derivatives;
- `fieldStrengthMul_eq_emFieldStrength_of_commute` — the f = 0 reduction: when the connection components commute, the non-abelian field strength loses its quadratic [a_j,a_k] correction and becomes the linear abelian one (why "the Hamiltonian is quadratic in the fields");
- `Fbook_eq_emFieldStrength_of_commute` — the same reduction for the book's coupled field strength `Fbook`;
- `emFieldStrength_isSelfAdjoint` — the curl of self-adjoint operator fields is self-adjoint (the book's "local self-adjoint operator ∂×π, the curl of the Electric Field").

The new file is sorry-free and axiom-free (only `propext`, `Quot.sound`, verified with `#print axioms`), and is registered in `BookProof.lean`; `lake build BookProof` completes green. Documentation updated in `BookProof/STATUS.md` (Wave 121) and `ARISTOTLE_SUMMARY.md` (new top section). The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean` (a separate thread with prior errors and a `sorry`), which was left untouched. All changes are committed and pushed.

# Summary of changes — Wave 121 (Free electromagnetic field: abelian reduction of the field strength)
Executed the next step of the `book.tex` formalization, staying on the main-conclusion thread as instructed (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana content fine).

**New work — Wave 121: `BookProof/ChapterFreeEMField.lean`.** Formalized the self-contained content of the book section *"Free electromagnetic field: an exact example"* (chapter "Timepiece and the Gribov ambiguity", `book.tex` line ~7413), which specializes the preceding Yang-Mills machinery to the abelian (electromagnetic) case by "setting the structure constants `f_{abc}` to zero". Building on `ChapterYangMillsFieldStrength.lean`, the file defines the abelian field strength / single curl component `emFieldStrength δ A j k = δ_j (A_k) - δ_k (A_j)` and proves:
- `emFieldStrength_antisymm` — `F_{jk} = -F_{kj}`;
- `emFieldStrength_gauge_invariant` — abelian gauge invariance ("no Gribov ambiguity"): invariance under `A_j ↦ A_j + δ_j θ`, the curl of a gradient vanishing by commutativity of the partial derivatives;
- `fieldStrengthMul_eq_emFieldStrength_of_commute` — the `f = 0` reduction: when the connection components commute, the non-abelian `fieldStrengthMul` loses its quadratic `[a_j,a_k]` correction and becomes the linear abelian one (why "the Hamiltonian is quadratic in the fields");
- `Fbook_eq_emFieldStrength_of_commute` — the same reduction for the book's coupled field strength `Fbook`;
- `emFieldStrength_isSelfAdjoint` — the curl of self-adjoint operator fields is self-adjoint (the book's "local self-adjoint operator `∂×π`, the curl of the Electric Field").

The new file is `sorry`-free and `axiom`-free (only `propext`, `Quot.sound`, verified with `#print axioms` / `lean_verify`), registered in `BookProof.lean`. `lake build BookProof` completes green. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean` (separate thread with prior errors and a `sorry`), left untouched. Documented in `BookProof/STATUS.md` (Wave 121).

---

# Summary of changes for run 0a528776-bf67-4c98-84a4-b1e6974c5a42
Executed the next step of the `book.tex` formalization, staying on the main-conclusion thread as instructed (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform).

**New work — Wave 120: `BookProof/ChapterWeylHamiltonian.lean`.** Formalized the positive-definiteness of the Weyl-gauge Yang-Mills Hamiltonian, the fact the book invokes for its Millennium mass-gap discussion (chapter "Timepiece and the Gribov ambiguity", §"Renormalization, the mass gap and the Millennium prize": *"the Hamiltonian in the Weyl gauge is positive definite"*). On an arbitrary complex Hilbert space, with the electric-field operators `π` and magnetic-field operators `B` modelled as bounded self-adjoint operators, the file defines the Weyl-gauge Hamiltonian density `weylHamiltonian π B = ½•(∑ i, π i ∘L π i) + ½•(∑ a, B a ∘L B a)` and proves:
- `weylHamiltonian_isPositive` — it is a positive operator (the book's "positive definite");
- `weylHamiltonian_expectation_nonneg` — every expectation value `re ⟪H_W x, x⟫ ≥ 0` (operational bounded-below form, the bridge to the earlier `ChapterMassGap` result);
- `weylHamiltonian_isSelfAdjoint` — it is itself a genuine observable;
- supporting lemmas `selfAdjoint_sq_isPositive` and `smul_nonneg_isPositive`.

The new file is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, checked with `#print axioms`), registered in `BookProof.lean`. `lake build BookProof` completes green (8177 jobs).

**Documentation.** Recorded the wave in `BookProof/STATUS.md` and added a corresponding section to `ARISTOTLE_SUMMARY.md`.

The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean` (separate RCP/RandomMap thread with prior errors and a `sorry`), which was left untouched. All changes are committed and pushed.

# Summary of changes (Wave 120 — Weyl-gauge Hamiltonian positivity)
Continued the `book.tex` formalization on its main-conclusion thread (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana content fine), picking up right after the Wave 119 BRST-charge nilpotency work. Added one new self-contained file, `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified with `#print axioms`), registered in `BookProof.lean`; the `BookProof` library builds green (`lake build BookProof`).

**Wave 120 — `BookProof/ChapterWeylHamiltonian.lean`: positive-definiteness of the Weyl-gauge Yang-Mills Hamiltonian.** This is the fact the book invokes for the Millennium mass-gap discussion (`book.tex` chapter "Timepiece and the Gribov ambiguity", §"Renormalization, the mass gap and the Millennium prize", line ~7490: *"the Hamiltonian in the Weyl gauge is positive definite"*), and the bridge to the earlier `ChapterMassGap` result. On an arbitrary complex Hilbert space, modelling the electric-field operators `π : Fin n → H →L[ℂ] H` and magnetic-field operators `B : Fin m → H →L[ℂ] H` as bounded self-adjoint operators, it defines the Weyl-gauge Hamiltonian density `weylHamiltonian π B = ½•(∑ i, π i ∘L π i) + ½•(∑ a, B a ∘L B a)` and proves `weylHamiltonian_isPositive` (it is a positive operator — the book's "positive definite"), `weylHamiltonian_expectation_nonneg` (every expectation value `re ⟪H_W x, x⟫ ≥ 0`, the operational bounded-below form), and `weylHamiltonian_isSelfAdjoint` (it is itself a genuine observable). Supporting lemmas: `selfAdjoint_sq_isPositive` (square of a self-adjoint operator is positive) and `smul_nonneg_isPositive` (a nonnegative real multiple of a positive operator is positive).

Recorded as Wave 120 in `BookProof/STATUS.md`. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. All changes committed and pushed.

# Summary of changes for run 5e69f836-09dd-4dcd-8cdb-3f9be1c0b2ff
Continued the `book.tex` formalization on its main-conclusion thread (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana content fine), picking up right after the previous SU(3) Yang-Mills field-strength work. Added two new self-contained files, both `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified with `#print axioms`), each registered in `BookProof.lean`; the whole `BookProof` library builds green (`lake build BookProof`).

**Wave 119 — `BookProof/ChapterBRSTNilpotent.lean` (flagship result): nilpotency of the BRST charge, `Ω² = 0`.** This is the central algebraic fact behind the book's BRST / gauge-invariant-algebra programme (the physical algebra the book proposes as its definition of Quantum Yang-Mills). Isolating the cubic ghost term (the only part whose nilpotency needs the non-abelian structure), in any associative ℝ-algebra with ghost creation operators `χ` (the book's `ψ†`) and annihilation operators `β` (`ψ`) obeying the canonical anticommutation relations, and real structure constants antisymmetric in their first two indices and satisfying the Jacobi identity (both already proved for SU(N) generators in `ChapterYangMillsSU3.lean`), the cubic ghost charge `Q = ∑ f_{abe}·(χ_a χ_b β_e)` satisfies `brst_charge_nilpotent` (`Q·Q = 0`). Proved via supporting lemmas: `beta_move` (normal-ordering an annihilation operator), `chi_swap4`/`chi_cyc3` (fermionic reordering), `quartic_term_zero` (the quartic piece vanishes by fermionic antisymmetry), and `contracted_terms_zero` (the contracted pieces vanish by the Jacobi identity).

**Wave 118 — `BookProof/ChapterMajoranaClifford.lean`: the complex Clifford C\*-algebra of a real Hilbert space** (book §"Majorana spinors in canonical quantization and antiparticles"). Realizing the book's `C(V)` as Mathlib's `CliffordAlgebra` for the quadratic form induced by the inner product, with the canonical involution `reverse`, it proves the Clifford relation `a(v)² = ⟪v,v⟫·1` (`a_sq`), the canonical anticommutation relation `{a(v),a(w)} = 2⟪v,w⟫·1` (`car`), self-adjointness `reverse(a v) = a v` (`a_selfAdjoint`, the Majorana / "particle is its own antiparticle" property), the involution as an order-two anti-automorphism, that real symmetries `a(v) → a(Tv)` preserve self-adjointness (`a_map_selfAdjoint`, real representations), and the creation/annihilation split `a_anticomm_skew` for a skew-symmetric complex structure `J`.

Recorded both as Waves 118–119 in `BookProof/STATUS.md`. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. All changes committed and pushed.

# Summary of changes for run 18000494-39a6-4a09-ad4a-239387935cd1
Continued the `book.tex` formalization on its main-conclusion thread (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana fine), picking up right after the previous run's SU(3) Yang-Mills Bianchi/Jacobi identity.

Added a new file `BookProof/ChapterYangMillsFieldStrength.lean` formalizing the next self-contained algebraic content of the chapter *"Quantization due to time-evolution: Yang-Mills and Classical Statistical Field Theory"*, §*"Pure SU(3) Yang-Mills theory"*: the **non-abelian field strength / magnetic field formula** the book records right after the covariant derivative, `[D_j, D_k] = -i g T_a F_{j k a}` with `B_{i a} = ½ ε_{i j k}(∂_j A_{k a} - ∂_k A_{j a} - g f_{a b c} A_{j b} A_{k c})`.

Modeling the covariant derivative acting on the ring `R` of field values as `D_j x = δ_j x + a_j * x` (with `δ` a family of commuting Leibniz derivations = the partial derivatives `∂_j`, and `a_j` the connection = `-i g A_j`), the file proves:
- `nonabelian_fieldStrength`: the commutator of two covariant derivatives is multiplication by the field strength, `[D_j, D_k] x = F_{j k} * x` with `F_{j k} = δ_j a_k - δ_k a_j + (a_j a_k - a_k a_j)` — the second-order terms cancel by commutativity of the derivations and the mixed first-order terms cancel identically, leaving a pure zeroth-order operator (exactly the book's `[D_j,D_k] = -i g T_a F_{j k a}`);
- `fieldStrengthMul_antisymm` (`F_{j k} = -F_{k j}`);
- `commutator_eq_coupling`: the book specialization `[D_j, D_k] x = (-i g • F^{book}_{j k}) * x` for `a_j = -i g A_j` in a complex algebra, with `F^{book}_{j k} = (∂_j A_k - ∂_k A_j) - i g (A_j A_k - A_k A_j)` (whose non-abelian term `-i g [A_j, A_k]` expands via `[T_a,T_b] = i f_{a b c} T_c` into the book's `+ g f_{a b c} A_{j b} A_{k c}`);
- `Fbook_antisymm` (`F^{book}_{j k} = -F^{book}_{k j}`).

The file is registered in `BookProof.lean`, is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified), and `lake build BookProof` is green. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. Recorded the work as Wave 117 in `BookProof/STATUS.md` and updated `ARISTOTLE_SUMMARY.md`. All changes committed and pushed.

# Summary of latest run
Continued the `book.tex` formalization on its main-conclusion thread (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana fine), picking up right after the previous run's SU(3) Yang-Mills Bianchi/Jacobi identity.

New file `BookProof/ChapterYangMillsFieldStrength.lean` formalizes the next self-contained algebraic content of the chapter *"Quantization due to time-evolution: Yang-Mills and Classical Statistical Field Theory"*, §*"Pure SU(3) Yang-Mills theory"* (`book.tex` line ~7020): the **non-abelian field strength formula** the book records right after the covariant derivative, `[D_j, D_k] = -i g T_a F_{j k a}` with `B_{i a} = ½ ε_{i j k}(∂_j A_{k a} - ∂_k A_{j a} - g f_{a b c} A_{j b} A_{k c})`. Modeling the covariant derivative acting on the ring `R` of field values as `D_j x = δ_j x + a_j * x` (with `δ` a family of commuting Leibniz derivations = the partial derivatives `∂_j`, and `a_j` the connection `= -i g A_j`), it proves:
- `nonabelian_fieldStrength` — the commutator of two covariant derivatives is multiplication by the field strength, `[D_j, D_k] x = F_{j k} * x` with `F_{j k} = δ_j a_k - δ_k a_j + (a_j a_k - a_k a_j)` (second-order terms cancel by commutativity of the `δ`'s, mixed first-order terms cancel identically — a pure zeroth-order operator);
- `fieldStrengthMul_antisymm` (`F_{j k} = -F_{k j}`);
- `commutator_eq_coupling` — the book specialization `[D_j, D_k] x = (-i g • F^{book}_{j k}) * x` for `a_j = -i g A_j` in a complex algebra, with `F^{book}_{j k} = (∂_j A_k - ∂_k A_j) - i g (A_j A_k - A_k A_j)` (the non-abelian term `-i g [A_j, A_k]` expands via `[T_a, T_b] = i f_{a b c} T_c` into the book's `+ g f_{a b c} A_{j b} A_{k c}`);
- `Fbook_antisymm` (`F^{book}_{j k} = -F^{book}_{k j}`).

The file is registered in `BookProof.lean`, is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed), and `lake build BookProof` is green. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. Recorded the work as Wave 117 in `BookProof/STATUS.md`.

# Summary of changes for run c4c42f87-4887-452c-8786-c758e71afe43
Continued the `book.tex` formalization on its main-conclusion thread (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana fine), picking up right after the previous run's SU(3) Yang-Mills structure constants.

New file `BookProof/ChapterYangMillsBianchi.lean` formalizes the next self-contained algebraic content of the chapter *"Quantization due to time-evolution: Yang-Mills and Classical Statistical Field Theory"*, §*"Pure SU(3) Yang-Mills theory"* (`book.tex` line ~7010): the covariant derivative `D_j` and the **Jacobi (Bianchi) relation** the book states for it, `ε_{i j k} [D_i, [D_j, D_k]] = 0`. Working with the covariant derivatives as elements of an arbitrary associative (possibly non-commutative) ring under the commutator bracket `⁅a,b⁆ = a*b - b*a`, it proves:
- `fieldStrength_antisymm` (`F_{j k} = ⁅D_j,D_k⁆ = -F_{k j}`);
- `bianchi_cyclic` (cyclic Jacobi identity for the double commutators);
- `bianchi` (the book's `ε_{i j k} [D_i,[D_j,D_k]] = 0`);
- `bianchi_fieldStrength` (the same with the field strength, `ε_{i j k} [D_i, F_{j k}] = 0` — the homogeneous Yang-Mills equation / `∇·B = 0`).

The file is registered in `BookProof.lean`, is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed), and `lake build BookProof` is green. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. Recorded the work as Wave 116 in `BookProof/STATUS.md` and updated `ARISTOTLE_SUMMARY.md` as requested. All changes committed and pushed.

# Summary of changes (latest run)

Continued the `book.tex` formalization on its main-conclusion thread (chapters
other than Gravity, off the Bell/CHSH comparison results, no Hankel transform;
Majorana fine). Picking up right after the previous run's SU(3) Yang-Mills
structure constants, I stayed in the same chapter, *"Quantization due to
time-evolution: Yang-Mills and Classical Statistical Field Theory"*, §*"Pure
SU(3) Yang-Mills theory"* (`book.tex` line ~7010), and formalized the next
self-contained algebraic content: the covariant derivative `D_j` and the
**Jacobi (Bianchi) relation** the book states for it,
`ε_{i j k} [D_i, [D_j, D_k]] = 0`.

New file `BookProof/ChapterYangMillsBianchi.lean` works with the covariant
derivatives `D_i` as elements of an arbitrary associative (possibly
non-commutative) ring `R` under the ambient commutator bracket
`⁅a,b⁆ = a*b - b*a`. It defines the Levi-Civita symbol `eps` on `Fin 3` and the
field strength `fieldStrength D j k = ⁅D j, D k⁆` (the book's
`-i g T_a F_{j k a}`), and proves:
- `fieldStrength_antisymm`: `F_{j k} = -F_{k j}`;
- `bianchi_cyclic`: the cyclic Jacobi identity for the double commutators;
- `bianchi`: the book's `ε_{i j k} [D_i, [D_j, D_k]] = 0` (expanding the triple
  `Fin 3` sum, the 21 repeated-index terms vanish and the 6 permutation terms
  collapse to twice the Jacobi sum, hence `0`);
- `bianchi_fieldStrength`: the same written with the field strength,
  `ε_{i j k} [D_i, F_{j k}] = 0` (the homogeneous Yang-Mills equation / `∇·B = 0`
  the book records right after `B_{i a}`).

The file is registered in `BookProof.lean`, is `sorry`-free and `axiom`-free
(only `propext`, `Classical.choice`, `Quot.sound`, confirmed by axiom check), and
`lake build BookProof` is green. The only remaining repository build failure is
the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. I
recorded the work as Wave 116 in `BookProof/STATUS.md` and updated this file as
requested. All changes are committed and pushed.

# Summary of changes for run cb27581d-b011-48f2-9c0f-55d121415e11
Continued the `book.tex` formalization on its main-conclusion thread (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana fine). The previous work had just completed the Navier-Stokes chapter (through the ghost field / BRST charge), so I moved to the next main-thread field-theory chapter, *"Quantization due to time-evolution: Yang-Mills and Classical Statistical Field Theory"*, §*"Pure SU(3) Yang-Mills theory"* (`book.tex` line ~7001).

New file `BookProof/ChapterYangMillsSU3.lean` formalizes the self-contained algebraic content of the SU(N) generators and their structure constants. Working with an arbitrary finite family of complex matrices `T : Fin d → Matrix (Fin n) (Fin n) ℂ` satisfying the book's two defining relations — trace-orthonormality `tr(T_a T_b) = ½ δ_{ab}` and closure with real structure constants `[T_a, T_b] = i f_{abc} T_c` — I proved:
- `structureConstant_formula`: `f_{abd} = -2 i · tr([T_a, T_b] T_d)` (the two relations determine `f` uniquely);
- `structureConstant_antisymm_swap`: `f_{abc} = -f_{bac}`;
- `structureConstant_antisymm_rotate`: `f_{abc} = -f_{acb}` (via cyclicity of the trace);
- `structureConstant_totally_antisymmetric`: total antisymmetry;
- `structureConstant_jacobi`: the Jacobi identity `Σₑ (f_{abe} f_{ech} + f_{bce} f_{eah} + f_{cae} f_{ebh}) = 0`, obtained by projecting the matrix Jacobi identity onto the trace-orthonormal basis (the identity underlying BRST-charge nilpotency).

The file is registered in `BookProof.lean`, is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed by axiom check), and `lake build BookProof` is green with no linter warnings on the new file. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. I recorded the work as Wave 115 in `BookProof/STATUS.md` and updated `ARISTOTLE_SUMMARY.md` as requested. All changes are committed and pushed.

# Summary of changes (latest run)
Continued the `book.tex` formalization on its main-conclusion thread (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana fine), picking up after the previously-done Navier-Stokes chapter (through the ghost field / BRST charge). Moved to the next main-thread field-theory chapter, *"Quantization due to time-evolution: Yang-Mills and Classical Statistical Field Theory"*, §*"Pure SU(3) Yang-Mills theory"* (`book.tex` line ~7001), formalizing the self-contained algebraic content of the SU(N) generators and their structure constants.

Added one new file, `BookProof/ChapterYangMillsSU3.lean`, modelling an arbitrary finite family of complex matrices `T : Fin d → Matrix (Fin n) (Fin n) ℂ` satisfying the book's two defining relations — trace-orthonormality `tr(T_a T_b) = ½ δ_{ab}` (`TraceOrthonormal`) and closure with real structure constants `[T_a, T_b] = i f_{abc} T_c` (`ClosesWithStructureConstants`) — and proving:
- `structureConstant_formula`: the closed formula `f_{abd} = -2 i · tr([T_a, T_b] T_d)` recovering the structure constants from the trace;
- `structureConstant_antisymm_swap`: antisymmetry in the first two indices `f_{abc} = - f_{bac}`;
- `structureConstant_antisymm_rotate`: antisymmetry in the last two indices `f_{abc} = - f_{acb}` (via cyclicity of the trace);
- `structureConstant_totally_antisymmetric`: the total antisymmetry corollary;
- `structureConstant_jacobi`: the Jacobi identity for the structure constants, `Σₑ (f_{abe} f_{ech} + f_{bce} f_{eah} + f_{cae} f_{ebh}) = 0`, obtained by projecting the matrix Jacobi identity onto the trace-orthonormal basis (the identity underlying BRST nilpotency).

The file is registered in `BookProof.lean`, is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, verified via `lean_verify`/`#print axioms`), and `lake build BookProof` is green with no linter warnings for the new file. Recorded the work as Wave 115 in `BookProof/STATUS.md`. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. All changes are committed and pushed.

# Summary of changes for run 7acba01a-b0ee-4be1-9e6e-0fc7ed387886
Continued the `book.tex` formalization on its main-conclusion thread (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana fine), picking up after the previously-done §§"Local operators", "Quadratic Ordering", and "Mass gap" of the "Free field parametrization … Navier-Stokes equations" chapter.

Added one new file, `BookProof/ChapterGhostField.lean`, formalizing the self-contained algebraic content of the ghost-field / BRST construction in §"Free field parametrization in Navier-Stokes equations" (`book.tex` line ~4134), where the divergence constraint is imposed via a single fermionic ghost field ψ with BRST charge Ω = ∫ … [u_{j,j} ψ†]. It models the single fermionic mode as concrete 2×2 matrices on the ℤ₂ Fock factor ℂ² (matching the book's action ψ†{a}(j)=a(1)δ_{j0}, ψ{a}(j)=a(0)δ_{j1}) and proves:
- `psiDag_eq_conjTranspose` (ψ† = ψᴴ);
- `car`, the canonical anticommutation relation {ψ,ψ†} = ψψ† + ψ†ψ = 1;
- `psi_sq`, `psiDag_sq` (ψ² = 0, ψ†² = 0);
- the number operator N = ψ†ψ: `numberOp_eq`, `numberOp_idempotent` (N²=N), `numberOp_selfAdjoint` (N=Nᴴ), and `numberOp_add_hole` (ψ†ψ + ψψ† = 1) — so N is an orthogonal projection with occupation 0 or 1;
- `brst_charge_nilpotent` (in any ring, f²=0 and Commute b f ⇒ (b·f)²=0) and its ghost instance `brst_charge_nilpotent_ghost`, i.e. the BRST charge satisfies Ω²=0.

The file is registered in `BookProof.lean`, is `sorry`-free and `axiom`-free (only propext, Classical.choice, Quot.sound, verified via `#print axioms`), and `lake build BookProof` is green. Recorded the work as Wave 114 in `BookProof/STATUS.md` and prepended a run entry to `ARISTOTLE_SUMMARY.md`. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. All changes are committed and pushed.

# Summary of changes (latest run)
Continued the book formalization on its main-conclusion thread (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform; Majorana fine). Formalized the self-contained algebraic content of the ghost field / BRST construction in the §"Free field parametrization in Navier-Stokes equations" section (`book.tex` line ~4134), the section that follows the already-done §"Holomorphic fields"/§"Mass gap" material. One new file `BookProof/ChapterGhostField.lean` was added, `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`), registered in `BookProof.lean`; `lake build BookProof` is green.

New file `BookProof/ChapterGhostField.lean` — the single fermionic ghost mode on the `ℤ₂` Fock factor `ℂ²` as concrete `2×2` matrices (`psi = !![0,0;1,0]`, `psiDag = !![0,1;0,0]`, matching the book's action `ψ†{a}(j)=a(1)δ_{j0}`, `ψ{a}(j)=a(0)δ_{j1}`):
- `psiDag_eq_conjTranspose`: `ψ† = ψᴴ` (`ψ†` really is the adjoint);
- `car`: the canonical anticommutation relation `{ψ,ψ†} = ψψ† + ψ†ψ = 1`;
- `psi_sq`, `psiDag_sq`: `ψ² = 0`, `ψ†² = 0` (ghost nilpotency / Pauli exclusion);
- `numberOp = ψ†ψ` with `numberOp_eq` (`= !![1,0;0,0]`), `numberOp_idempotent` (`N²=N`), `numberOp_selfAdjoint` (`N=Nᴴ`) — `N` is an orthogonal projection, occupation `0` or `1` — and `numberOp_add_hole` (`ψ†ψ + ψψ† = 1`);
- `brst_charge_nilpotent`: in any ring, `f²=0` and `Commute b f` imply `(b·f)²=0`, with the ghost instance `brst_charge_nilpotent_ghost` (`(b·ψ†)²=0`), i.e. the BRST charge `Ω²=0`.

Bookkeeping: added a Wave 114 entry to `BookProof/STATUS.md` and prepended this run entry to `ARISTOTLE_SUMMARY.md`. All work is committed and pushed. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, which was left untouched.

# Summary of changes for run b2d387f3-ea0c-4762-b59f-54ce51281237
Continued the book formalization on its main-conclusion thread (chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform). Formalized the two self-contained sections of the "Free field parametrization in Classical Statistical Field Theory and Navier-Stokes equations" chapter that immediately precede the already-done §"Mass gap" (`book.tex` lines ~4011 and ~4031). Two new files were added, both `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`), registered in `BookProof.lean`; `lake build BookProof` is green.

New file `BookProof/ChapterLocalOperators.lean` — §"Local operators and the momentum constraint". For an operator-valued field `l : ℝ^d → E`:
- `localIntegral_translation_invariant`: the space integral `∫ l(x) dx` is translation invariant (`∫ l(x + y) dx = ∫ l(x) dx`), the admissible translation-invariant operator of the book;
- `not_translationInvariant_of_pointSupported`: a genuinely local (single-point-supported, nonzero) field is not translation invariant (dimension `d ≥ 1`) — the precise sense in which "in rigor we can't" define local operators under the momentum constraint.

New file `BookProof/ChapterQuadraticOrdering.lean` — §"Quadratic Ordering", the algebraic content of "the (symmetric) Weyl ordering conserves the exponential of operators, unlike normal-ordering": the central Baker–Campbell–Hausdorff identity in an arbitrary real Banach algebra. For a central commutator `C = A·B − B·A`:
- `exp_smul_mul_central`: the adjoint identity `exp(t•A)·B = (B + t•C)·exp(t•A)`;
- `exp_mul_exp_central` (headline): `exp A · exp B = exp(A+B) · exp(½•C)` — the normal-ordered product equals the symmetric-ordered exponential `exp(A+B)` times the central correction `exp(½•C)`;
- `exp_add_central`: the rearranged form `exp(A+B) = exp A · exp B · exp(−½•C)`;
- `symmetric_ordering_correction_of_sq_zero`: for a nilpotent commutator the correction is the affine factor `1 + ½•C`;
- supporting: `exp_of_sq_eq_zero` and the two ODE derivative lemmas `hasDerivAt_normalCurve`/`hasDerivAt_symCurve`, assembled via ODE uniqueness on `[0,1]`.

Bookkeeping: added a Wave 113 entry to `BookProof/STATUS.md` and prepended a run entry to `ARISTOTLE_SUMMARY.md`. All work is committed and pushed. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, which was left untouched.

# Summary of changes (latest run) — Navier-Stokes chapter §§"Local operators / momentum constraint" and "Quadratic Ordering"

Continued the book formalization on its main-conclusion thread (author
instruction: chapters other than Gravity, off the Bell/CHSH comparison results,
no Hankel transform, Majorana fine). Formalized the two self-contained sections
of the chapter "Free field parametrization in Classical Statistical Field Theory
and Navier-Stokes equations" that immediately precede the already-done §"Mass
gap" (`book.tex` lines ~4011 and ~4031). Two new files, both `sorry`-free and
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, checked with
`#print axioms`), registered in `BookProof.lean`.

**New file `BookProof/ChapterLocalOperators.lean`** — §"Local operators and the
momentum constraint". For an operator-valued local field `l : ℝ^d → E` (values in
a real Banach space `E`):
- `localIntegral_translation_invariant` — the space integral `∫ l(x) dx` **is**
  translation invariant (`∫ l(x + y) dx = ∫ l(x) dx`), the admissible
  translation-invariant operator `∫ d\vec{x}\ l(\vec{x})` of the book.
- `not_translationInvariant_of_pointSupported` — a genuinely local
  (single-point-supported, nonzero) field is **not** translation invariant
  (dimension `d ≥ 1`): the precise sense in which "in rigor we can't" define local
  operators under the momentum constraint.

**New file `BookProof/ChapterQuadraticOrdering.lean`** — §"Quadratic Ordering".
The algebraic heart of the book's claim that "the (symmetric) Weyl ordering of
operators conserves the exponential of operators, unlike normal-ordering": the
**central Baker–Campbell–Hausdorff identity** in an arbitrary real Banach algebra.
For a central commutator `C = A·B − B·A` (commuting with both `A` and `B`, the
canonical/Heisenberg situation):
- `exp_smul_mul_central` — the adjoint identity `exp(t•A)·B = (B + t•C)·exp(t•A)`.
- `exp_mul_exp_central` (headline) — `exp A · exp B = exp(A+B) · exp(½•C)`: the
  normal-ordered product equals the symmetric-ordered exponential `exp(A+B)` times
  the central correction factor `exp(½•C)` (symmetric ordering reproduces
  `exp(A+B)` on the nose; normal ordering carries the extra factor).
- `exp_add_central` — the rearranged form `exp(A+B) = exp A · exp B · exp(−½•C)`.
- `symmetric_ordering_correction_of_sq_zero` — for a square-zero/nilpotent
  commutator the correction is the affine factor `1 + ½•C`.
- Supporting: `exp_of_sq_eq_zero` (`exp x = 1 + x` when `x² = 0`) and the two ODE
  derivative lemmas `hasDerivAt_normalCurve` / `hasDerivAt_symCurve` (both curves
  `exp(t•A)exp(t•B)` and `exp(t•(A+B))exp((t²/2)•C)` solve the same linear ODE
  `y' = (A+B+t•C)·y`), assembled via `ODE_solution_unique_of_mem_Icc_right`.

**Verification.** `lake build BookProof` is green; both new files are `sorry`-free
and `axiom`-free. The only remaining repository build failure is the pre-existing,
out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

**Bookkeeping.** Added a Wave 113 entry to `BookProof/STATUS.md` and prepended
this run entry to `ARISTOTLE_SUMMARY.md`. All work is committed and pushed.

# Summary of changes for run 56dd851f-3a47-45c0-990b-53a5949a2cb5
Continued the book formalization on its main-conclusion thread (per your instruction: chapters other than Gravity, off the Bell/CHSH comparison results, no Hankel transform, Majorana fine).

**What I did.** Formalized the self-contained mathematical backbone of the §"Mass gap" section (`book.tex` line ~4061) of the chapter "Free field parametrization in Classical Statistical Field Theory and Navier-Stokes equations". The book claims to solve "the hardest part" of the Yang–Mills mass-gap problem within its own formalism: because the number operator commutes with the algebra of observables, it can be added to the Hamiltonian, "modifying the mass gap without observable consequences" — so a Hamiltonian with a null mass gap (the free electromagnetic field) can be given an arbitrary mass gap without any observable consequence.

**New file `BookProof/ChapterMassGap.lean`** (registered in `BookProof.lean`), sorry-free and axiom-free (only `propext`, `Classical.choice`, `Quot.sound`, checked with `#print axioms`):
- `exp_conj_eq_self` — in a complex Banach algebra of operators, conjugating an observable by `exp Y` is trivial when the observable commutes with `Y`.
- `heisenberg_number_shift_invariant` (headline, observable invariance) — if the Hamiltonian `H` and every observable `Obs` commute with the number operator `N`, then the Heisenberg-picture evolution of `Obs` under the shifted Hamiltonian `H + λN` is identical to its evolution under `H`, for every scalar `t` and shift `λ`. This is the precise sense in which the number-operator shift has no observable consequence.
- A diagonal spectral-shift model (`numberOp`, `shiftedSpectrum`, `excited`, `massGap`) with `shiftedSpectrum_vacuum` (vacuum energy unchanged), `shiftedSpectrum_excited` (each excited energy shifted by exactly `λ`), and the headline `massGap_shifted_gapless` — for the gapless free field the shifted mass gap equals `λ`, i.e. it can be set to any value.

**Verification.** `lake build BookProof` is green (8190 jobs); the new file has no `sorry`. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, which I left untouched.

**Bookkeeping.** Added a Wave 112 entry to `BookProof/STATUS.md` and, as you requested, prepended a new run entry to `ARISTOTLE_SUMMARY.md`. All work is committed and pushed.

# Summary of changes (latest run) — Mass gap section (`ChapterMassGap`)
Continued the book formalization on its main-conclusion thread (per your instruction: prioritize chapters other than Gravity and off the Bell/CHSH comparison results; no Hankel transform, Majorana fine).

**What I did.** Formalized the self-contained mathematical backbone of the §*"Mass gap"* section (`book.tex` line ~4061) of the chapter *"Free field parametrization in Classical Statistical Field Theory and Navier-Stokes equations"*. The book claims to "solve the hardest part" of the Yang–Mills mass-gap Millenium problem within its own formalism: *"the number operator commutes with the algebra of observables which implies that the number operator can be added to the Hamiltonian, modifying the mass gap without observable consequences."* So a bounded-from-below Hamiltonian with a **null** mass gap (the free electromagnetic field) can be turned into one with an **arbitrary** mass gap without any observable consequence.

**New file `BookProof/ChapterMassGap.lean`** (registered in `BookProof.lean`), `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`):
- `exp_conj_eq_self` — in a complex Banach algebra, conjugating an observable by `exp Y` is trivial when the observable commutes with `Y` (`exp Y · Obs · exp(-Y) = Obs`).
- `heisenberg_number_shift_invariant` (**headline, observable invariance**) — if the Hamiltonian `H` and every observable `Obs` commute with the number operator `N`, then the Heisenberg-picture time evolution of `Obs` under the number-shifted Hamiltonian `H + λN` is **identical** to its evolution under `H`, for every scalar `t` and shift `λ` (`exp(t(H+λN))·Obs·exp(-t(H+λN)) = exp(tH)·Obs·exp(-tH)`). This is the precise sense in which adding `λN` to the Hamiltonian has *no observable consequence*.
- `numberOp` / `shiftedSpectrum` / `excited` / `massGap` — the diagonal model (vacuum index `0`, number operator `1` on excited states) with `shiftedSpectrum_vacuum` (the vacuum energy is unchanged) and `shiftedSpectrum_excited` (every excited energy is shifted by exactly `λ`).
- `massGap_shifted_gapless` (**headline, arbitrary mass gap**) — for the gapless free field (`E ≡ 0`) the number-operator shift produces a mass gap equal to `λ`, i.e. the mass gap can be set to any value.

**Verification.** `lake build BookProof` is green (8190 jobs); the new file is `sorry`-free, and each named theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (checked with `#print axioms`). The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, which I left untouched. Recorded the corresponding wave entry in `BookProof/STATUS.md`.

---

# Summary of changes for run ac3988fa-4d97-4c98-84bd-3a2fe6987d05
Continued the book formalization on its main-conclusion thread (per your instruction: prioritize chapters other than Gravity and off the Bell/CHSH comparison results; no Hankel transform, Majorana fine).

**What I did.** Formalized the mathematical backbone of the subsection *"Any deterministic theory compatible with relativistic Quantum Mechanics necessarily respects relativistic causality"* of the chapter *"Reconstructing the classical trajectory of any isolated quantum system"* (`book.tex` line ~2915). The book's argument is: *"Since in relativistic Quantum Mechanics the probability that the system moves faster than light is null, then no system in the ensemble moves faster than light."* This built directly on the explicit deterministic decoder already established in `BookProof/ChapterInverseTransform.lean` (uniform seed `u ∈ [0,1)`, with the ensemble member of seed `u` yielding outcome `k` when `u ∈ seedSet p k`).

**New file `BookProof/ChapterCausality.lean`** (registered in `BookProof.lean`):
- `seedSet_biUnion_measure` — the Lebesgue measure of the ensemble members whose decoded outcome lies in a finite set `S` of faster-than-light outcomes is exactly `∑_{k∈S} p k` (the deterministic ensemble reproduces the quantum probability of any set of outcomes).
- `causality` (headline) — if Quantum Mechanics predicts a null faster-than-light probability (`∑_{k∈S} p k = 0`), then the set of ensemble members that move faster than light is a null set.
- `causality_ae` — the a.e. reformulation: for almost every seed, the corresponding deterministic member does not land in the faster-than-light set — the precise sense of "no system in the ensemble moves faster than light".

This completes the last formalizable subsection of that chapter that is off the Bell/EPR comparison thread (the remaining "Quantum Mechanics is EPR-complete" and "Do the Bell inequalities hold" subsections are prose / Bell-comparison material and out of scope per your instruction).

**Verification.** `lake build BookProof` is green (8167 jobs); the new file is `sorry`-free, and each named theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (checked with `#print axioms`). The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, which I left untouched.

**Bookkeeping.** Recorded a Wave 111 entry in `BookProof/STATUS.md`. Following the standing convention of prior runs, I did not directly edit `ARISTOTLE_SUMMARY.md`; this run summary documents the update. All changes are committed and pushed.

# Summary of changes for run 1e7adb5d-baaa-4d0a-b8a4-52ef0b47d4e9
Continued the book formalization on its main-conclusion thread, per your instructions: prioritized a core chapter over the Gravity line and the Bell/CHSH comparison results, and used no Hankel transform.

**What I did.** Formalized the headline result of §9 *"Deterministic transformations"* of the chapter *"Wave-function parametrization of a probability measure"* (`book.tex` line ~1958): the book's statement that *"an automorphism `U` is deterministic if and only if `P_A` and `U P_B U†` commute for all events `A, B`."* This is the commutation form of the same determinism criterion whose off-diagonal-Born core is in `ChapterReconstruct.lean` and whose density-matrix/trace form is in `ChapterTimeTranslation.lean`, so it slots directly onto the existing thread.

**New file `BookProof/ChapterDeterministic.lean`** (registered in `BookProof.lean`), building on the existing rank-one projection `proj a = |e_a⟩⟨e_a|`, transformed measurement operator `measOp U b = U P_b U†`, and `IsDeterministic` (each matrix column has at most one nonzero entry = permutation up to phases):
- Entry lemmas `proj_mul_measOp_apply`, `measOp_mul_proj_apply`.
- `commute_proj_measOp_iff_isDeterministicCol` — per-column criterion: for a fixed outcome `b`, `P_a` commutes with `U P_b U†` for all `a` iff column `b` of `U` is deterministic.
- `commute_proj_measOp_iff_isDeterministic` — single-outcome headline: `P_a` and `U P_b U†` commute for all `a, b` iff `U` is deterministic.
- Event projections `projSet A = ∑_{a∈A} P_a`, transformed event operator `measOpSet U B = U P_B U†`, `measOpSet_eq_sum`, and the literal book statement `commute_projSet_measOpSet_iff_isDeterministic` — `P_A` and `U P_B U†` commute for all events `A, B` iff `U` is deterministic.

**Verification.** `lake build BookProof` is green; the new file is `sorry`-free and each named theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (checked via `#print axioms`). The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, which I left untouched.

**Bookkeeping.** Recorded a Wave 110 entry in `BookProof/STATUS.md`; per the standing instruction I did not directly edit `ARISTOTLE_SUMMARY.md` (this run summary documents the update). All changes are committed and pushed.

# Summary of changes for run 8860944a-fecc-48d3-b121-fd23e0550c01
Continued the book formalization on its **main-conclusion thread**, staying off Bell/CHSH (a comparison only), off the Gravity line, and using no Hankel transform (Majorana allowed), as requested.

**What I did.** Formalized the next unformalized subsection on the same thread as the two most recent waves — *"Reconstruction of the trajectory"* (from the chapter *"Reconstructing the classical trajectory of any isolated quantum system"*, `book.tex` line ~3044). The book argues that although only the *final* time of a quantum trajectory is directly measurable, *post-selection* (probabilities conditional on the final state, under the same time-evolution) lets one predict/reconstruct the intermediate-time statistics.

**New file `BookProof/ChapterTrajectory.lean`** (registered in `BookProof.lean`) models the three-instant (initial → intermediate → final) collapsed Born process on a finite phase space `Fin n`:
- Definitions: `midProb` (intermediate Born law `‖(U Ψ)_a‖²`), `transProb` (post-collapse transition `‖V_{f a}‖²`), `jointProb`, `finalProb`, `condProb` (the Aharonov–Bergmann–Lebowitz / two-state post-selected law), and `coherentFinal` (`‖(V U Ψ)_f‖²`, coherent evolution with no intermediate measurement).
- Headlines: `finalProb_total` (the collapsed process is a genuine probability law, `∑_f finalProb = 1`); `jointProb_sum_final_eq_midProb` (reconstruction consistency — summing the post-selected joint law over final outcomes recovers the intermediate Born law); `condProb_sum` (the post-selected law is a probability distribution). Support lemmas `transProb_sum`, `midProb_sum` (unitaries preserve ℓ² mass) and nonnegativity of all laws.
- Double-slit capstone (reusing the existing `ChapterDoubleSlit` Hadamard): `dslit_finalProb`/`dslit_condProb` (collapsed and post-selected laws are uniform `1/2`), `dslit_coherentFinal` (coherent law is certain `(1,0)`), and `dslit_interference` (`1/2 ≠ 1`), making precise that the "self-interference mystery" is exactly the mismatch between the collapsed/post-selected picture and coherent evolution.

**Verification.** `lake build BookProof` is green (8165 jobs); the new file is `sorry`-free and every named theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (checked via `#print axioms`). The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

**Bookkeeping.** Added a Wave 109 entry to `BookProof/STATUS.md` and prepended a run summary to `ARISTOTLE_SUMMARY.md`. All changes are committed and pushed.

# Summary of changes for this run

Did the next formalization step on the book's **main-conclusion** thread, staying
off Bell/CHSH (a comparison only — the main results do not depend on it), off the
Gravity line, and using no Hankel transform (Majorana allowed), as requested.

**Target:** the `book.tex` subsection *"Reconstruction of the trajectory"*
(chapter *"Reconstructing the classical trajectory of any isolated quantum
system"*, line ~3044) — the next unformalized subsection on the same thread as
Waves 107–108. The book argues that although only the *final* time of a quantum
trajectory is directly measurable, *post-selection* ("using probabilities
conditional on the final state and the same quantum time-evolution") lets one
"predict the results of a measurement at another time between the initial and
final times", so the trajectory can be reconstructed at intermediate instants.

**New file `BookProof/ChapterTrajectory.lean`** (registered in `BookProof.lean`),
the three-instant (initial → intermediate → final) *collapsed* Born process on a
finite phase space `Fin n`:
- Definitions: `midProb U Ψ a = ‖(U Ψ)_a‖²` (intermediate Born law after the
  unitary `U`), `transProb V f a = ‖V_{f a}‖²` (post-collapse transition to the
  final outcome under the unitary `V`), `jointProb = midProb · transProb`,
  `finalProb = ∑ₐ jointProb` (final marginal), `condProb = jointProb / finalProb`
  (the Aharonov–Bergmann–Lebowitz / two-state *post-selected* law of the
  intermediate outcome), and `coherentFinal V U Ψ f = ‖(V U Ψ)_f‖²` (the coherent
  final law with **no** intermediate measurement).
- Support lemmas: nonnegativity of all four laws; `transProb_sum` (columns of a
  unitary have unit ℓ² norm) and `midProb_sum` (a unitary preserves the ℓ² mass
  of `Ψ`).
- Headlines: `finalProb_total` (the collapsed process is a genuine probability
  law — `∑_f finalProb = 1` for unitary `U,V` and unit `Ψ`),
  `jointProb_sum_final_eq_midProb` (**reconstruction consistency**: summing the
  post-selected joint law over all final outcomes recovers the intermediate Born
  law — the reconstructed statistics do not depend on the post-selection choice),
  and `condProb_sum` (the post-selected law is a probability distribution for any
  realizable final outcome).
- Double-slit capstone (reusing `ChapterDoubleSlit`'s Hadamard `H`, `Ψ = (1,0)`):
  `dslit_finalProb`/`dslit_condProb` (the collapsed and post-selected laws are
  uniform `1/2`), `dslit_coherentFinal` (the coherent law is certain `(1,0)`), and
  `dslit_interference` (`finalProb = 1/2 ≠ 1 = coherentFinal`) — the
  self-interference "mystery" is exactly the mismatch between the collapsed
  (post-selected/reconstructed) picture and coherent evolution.

**Verification:** `lake build BookProof` is green (8165 jobs); the new file is
`sorry`-free and, by `#print axioms`, every named theorem depends only on
`propext`, `Classical.choice`, `Quot.sound`. The only remaining repository build
failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, which was
left untouched.

**Bookkeeping:** added a Wave 109 entry to `BookProof/STATUS.md` and prepended
this summary to `ARISTOTLE_SUMMARY.md`. All changes are committed and pushed.

# Summary of changes for run 169956b7-1f9b-42fe-8fcc-6f474dd3e73b
Did the next formalization step on the book's main-conclusion thread, staying off Bell/CHSH (a comparison only), off the Gravity line, and using no Hankel transform (Majorana allowed), as requested.

Target: the `book.tex` subsection "Symmetries as irreversible processes" (chapter "Reconstructing the classical trajectory of any isolated quantum system", line ~2679) — the Shannon-entropy counterpart of that chapter's main result (time translation is a stochastic process iff it is deterministic). The book claims a non-deterministic symmetry, acting on a deterministic ensemble, increases the entropy after wave-function collapse (irreversible), while a deterministic symmetry preserves it (reversible).

New file `BookProof/ChapterIrreversible.lean` (registered in `BookProof.lean`):
- Definitions: `entropy p = ∑ a, negMulLog (p a)` (Shannon entropy of a finite probability vector), `IsPointMass` (deterministic ensemble / point mass), `bornDist v a = ‖v a‖²` (Born distribution after collapsing the column `v = U e_k`), `IsDeterministicColumn` (the symmetry sends a basis state to a basis state up to phase).
- Lemmas: `entropy_nonneg`, `entropy_pointMass_zero` (deterministic ensemble ⇒ entropy 0), `entropy_pos_of_not_pointMass` (non-deterministic ensemble ⇒ entropy > 0), `entropy_eq_zero_iff_pointMass`, `isPointMass_bornDist_iff`.
- Headlines: `entropy_bornDist_eq_zero_iff` (reversible case — for a unit column the collapsed ensemble has entropy 0 iff the column is deterministic) and `entropy_bornDist_pos_iff` (irreversible case — the collapsed ensemble has strictly positive entropy iff the column is non-deterministic, i.e. the symmetry strictly increases the entropy).

Verification: `lake build BookProof` is green; the new file is sorry-free and, by `#print axioms`, every named theorem depends only on `propext`, `Classical.choice`, `Quot.sound`. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, which was left untouched.

Bookkeeping: added a Wave 108 entry to `BookProof/STATUS.md` and prepended a summary section to `ARISTOTLE_SUMMARY.md`. All changes are committed and pushed.

# Summary of changes for this run

Did the next formalization step on the book's **main-conclusion** thread, staying
off Bell/CHSH (a comparison only — the main results do not depend on it), off the
Gravity line, and using no Hankel transform (Majorana allowed), as requested.
Target: the `book.tex` subsection *"Symmetries as irreversible processes"*
(chapter *"Reconstructing the classical trajectory of any isolated quantum
system"*, line ~2679), the entropy counterpart of that chapter's main result
(*time translation is a stochastic process if and only if it is deterministic*).

The book states: *"A non-deterministic symmetry transformation, when acting on a
deterministic ensemble increases the entropy of the ensemble after the
wave-function collapse and therefore must be an irreversible transformation"*,
while a deterministic symmetry preserves the entropy (reversible).

**New file `BookProof/ChapterIrreversible.lean`** (registered in `BookProof.lean`):
- `entropy p = ∑ a, Real.negMulLog (p a)` — Shannon entropy of a finite
  probability vector; `IsPointMass` — a deterministic ensemble (point mass);
  `bornDist v a = ‖v a‖²` — the Born distribution obtained by collapsing the
  wave-function column `v = U e_k`; `IsDeterministicColumn` — the symmetry sends a
  basis state to a basis state up to a phase.
- `entropy_nonneg`, `entropy_pointMass_zero` (deterministic ensemble ⇒ entropy 0),
  `entropy_pos_of_not_pointMass` (non-deterministic ensemble ⇒ entropy > 0),
  `entropy_eq_zero_iff_pointMass`, `isPointMass_bornDist_iff`.
- Headlines `entropy_bornDist_eq_zero_iff` (**reversible** — for a unit column the
  collapsed ensemble has entropy 0 iff the column is deterministic) and
  `entropy_bornDist_pos_iff` (**irreversible** — the collapsed ensemble has
  strictly positive entropy iff the column is non-deterministic, i.e. the symmetry
  strictly increases the entropy).

**Verification.** `lake build BookProof` is green; the new file is `sorry`-free and,
by `#print axioms`, every named theorem depends only on `propext`,
`Classical.choice`, `Quot.sound`. The only remaining repository build failure is
the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

**Bookkeeping.** Added a Wave 108 entry to `BookProof/STATUS.md` and prepended this
section to `ARISTOTLE_SUMMARY.md`. All changes are committed and pushed.

# Summary of changes for run 10375f16-20b1-483f-8bb1-23de1fd5d7b5
Did the next formalization step on the book's main-conclusion thread, staying off Bell/CHSH (a comparison only, per your note), off the Gravity line, and using no Hankel transform. Target: the `book.tex` section "Time translation is a stochastic process if and only if it is deterministic" (line ~2613), which the book itself calls "one of the main results of this paper".

Context: the linear-algebra core of that section (a symmetry acts well-definedly on probability distributions iff its off-diagonal Born sum vanishes, iff the symmetry is deterministic) was already formalized in `BookProof/ChapterReconstruct.lean`. What was missing was the book's literal density-matrix statement, which this run adds.

New file `BookProof/ChapterTimeTranslation.lean` (registered in `BookProof.lean`), building on `ChapterReconstruct`:
- Definitions: `rho Ψ = |Ψ⟩⟨Ψ|` (pure-state density matrix), `diagPart` (wave-function collapse = keep the diagonal), `proj a = |e_a⟩⟨e_a|` (rank-one outcome projection), `measOp U a = U P_a U†`.
- `measOp_apply`: `measOp U a k l = U k a · conj(U l a)`.
- `trace_rho_measOp` / `trace_diagPart_measOp`: identify the full Born probability `tr(ρ·U P_a U†)` and the collapsed one `tr(diag(ρ)·U P_a U†)` with the full and diagonal Born sums.
- `trace_diff`: their difference equals `ChapterReconstruct.offDiag`.
- Headlines `trace_eq_iff_isDeterministic` and `trace_eq_iff_isDeterministic_pure` (restricted to pure states `∑‖Ψ k‖²=1`): the collapsed and full Born probabilities agree for every outcome and state iff the symmetry `U` is deterministic — the density-matrix form of the book's main result.

Verification: `lake build BookProof` is green; the new file is sorry-free and every named theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (checked with `#print axioms`). The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

Bookkeeping: added a Wave 107 entry to `BookProof/STATUS.md` and prepended a summary section to `ARISTOTLE_SUMMARY.md`. All changes are committed and pushed.

# Summary of changes for this run

Did the next formalization step on the book's **main-conclusion** thread, staying
off Bell/CHSH (a comparison only — the main results do not depend on it), off the
Gravity line, and using no Hankel transform, as requested. Target: the `book.tex`
section *"Time translation is a stochastic process if and only if it is
deterministic"* (line ~2613), which the book itself calls *"one of the main
results of this paper"*.

**Context.** The linear-algebra core of that section — a Wigner symmetry `U` acts
well-definedly on probability distributions iff its off-diagonal Born sum vanishes,
iff `U` is *deterministic* (each column has at most one nonzero entry) — was
already formalized in `BookProof/ChapterReconstruct.lean`
(`offDiag_eq_zero_iff_isDeterministic`, `offDiag_unit_iff`). What was missing is
the book's **literal density-matrix statement**.

**New file `BookProof/ChapterTimeTranslation.lean`** (registered in
`BookProof.lean`), building on `ChapterReconstruct`:
- `rho Ψ = |Ψ⟩⟨Ψ|` (pure-state density matrix), `diagPart` (wave-function collapse
  = keep the diagonal), `proj a = |e_a⟩⟨e_a|` (rank-one outcome projection),
  `measOp U a = U P_a U†` (transformed measurement operator).
- `measOp_apply` — `measOp U a k l = U k a · conj(U l a)`.
- `trace_rho_measOp`, `trace_diagPart_measOp` — identify the *full* Born
  probability `tr(ρ·U P_a U†)` and the *collapsed* one `tr(diag(ρ)·U P_a U†)` with
  the full and diagonal Born sums.
- `trace_diff` — their difference is exactly `ChapterReconstruct.offDiag`.
- `trace_eq_iff_isDeterministic` (headline) — the collapsed and full Born
  probabilities agree for every outcome and every state iff `U` is deterministic.
- `trace_eq_iff_isDeterministic_pure` — the same restricted to pure states
  (`∑ ‖Ψ k‖² = 1`), matching the book's quantifier "for any pure density matrix".

**Verification.** `lake build BookProof` is green; the new file is `sorry`-free and,
by `#print axioms`, every named theorem depends only on `propext`,
`Classical.choice`, `Quot.sound`. The only remaining repository build failure is
the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

**Bookkeeping.** Added a Wave 107 entry to `BookProof/STATUS.md` and prepended this
section to `ARISTOTLE_SUMMARY.md`. All changes are committed and pushed.

# Summary of changes for run d2e5fe08-38d8-442d-b83f-1d050e3abffd
Did the next formalization step, moving off the Bell/CHSH thread of the previous waves (per your note that Bell/CHSH are only a comparison and the main conclusions do not depend on them), staying off the Gravity line, and using no Hankel transform. I targeted a main-conclusion subsection of the book's title chapter "Reconstructing the classical trajectory of any isolated quantum system", namely §"A deterministic theory compatible with relativistic Quantum Mechanics" (book.tex line ~2952), which constructively answers "Does a deterministic theory — consistent with the non-deterministic time evolution of Quantum Mechanics — exist?" with yes, via the inverse-transform sampling method.

New file BookProof/ChapterInverseTransform.lean (registered in BookProof.lean) formalizes the mathematical backbone of that construction. For a discrete probability distribution p on outcomes 0,…,n-1 (each p i ≥ 0, sum = 1), with CDF cdf p k = ∑_{i<k} p i and per-outcome seed intervals seedSet k = [cdf p k, cdf p (k+1)):
- seedSet_measure — the Lebesgue measure of seedSet k equals p k, so a uniformly drawn seed lands in seedSet k with probability exactly p k: the deterministic decoder reproduces the quantum distribution;
- seedSet_disjoint — the seed intervals are pairwise disjoint (each seed yields at most one outcome);
- seedSet_cover — the n seed intervals tile [0,1) exactly (each seed yields at least one outcome);
- seedSet_total_measure — the seed intervals carry total measure 1.
Together these show seed ↦ (the unique k<n with seed ∈ seedSet k) is a well-defined deterministic map [0,1) → {0,…,n-1} whose pushforward of the uniform seed distribution is precisely p — a deterministic theory experimentally indistinguishable from Quantum Mechanics, as the book claims. The surrounding physical/metaphysical discussion is left as prose.

Verification: the BookProof library builds cleanly; the new file is sorry-free and every named theorem depends only on the standard axioms (propext, Classical.choice, Quot.sound). The only pre-existing repository build failure remains the out-of-scope RiemannProof/RandomMap.lean, left untouched.

Bookkeeping: added a Wave 106 entry to BookProof/STATUS.md and prepended a summary section to ARISTOTLE_SUMMARY.md. All changes are committed and pushed.

# Summary of changes for this run

Did the next formalization step, moving **off** the Bell/CHSH thread of the
previous waves per the author's instruction (the Bell/CHSH results are cited in
the book only as a *comparison* — the main conclusions do not depend on them),
staying off the Gravity line, and using no Hankel transform. Targeted a
**main-conclusion** subsection of the book's title chapter *"Reconstructing the
classical trajectory of any isolated quantum system"*, namely §*"A deterministic
theory compatible with relativistic Quantum Mechanics"* (`book.tex` line ~2952),
which constructively answers *"Does a deterministic theory — consistent with the
non-deterministic time evolution of Quantum Mechanics — exist?"* with **yes** via
the **inverse-transform sampling** method.

**New file `BookProof/ChapterInverseTransform.lean`** (registered in
`BookProof.lean`) formalizes the mathematical backbone of that construction. For a
discrete probability distribution `p : ℕ → ℝ` on outcomes `0,…,n-1` (`p i ≥ 0`,
`∑_{i<n} p i = 1`), with cumulative distribution function `cdf p k = ∑_{i<k} p i`
and per-outcome "seed intervals" `seedSet k = [cdf p k, cdf p (k+1))`:

- `seedSet_measure` — `volume (seedSet k) = ENNReal.ofReal (p k)`: a uniformly
  drawn seed lands in `seedSet k` with probability exactly `p k`, so the
  deterministic decoder reproduces the quantum probability distribution.
- `seedSet_disjoint` — the seed intervals are pairwise disjoint (each seed yields
  at most one outcome).
- `seedSet_cover` — the `n` seed intervals tile `[0,1)` exactly (each seed yields
  at least one outcome), using `cdf p 0 = 0` and `cdf p n = 1`.
- `seedSet_total_measure` — the seed intervals carry total Lebesgue measure `1`.

Together these establish that `seed ↦ (the unique k<n with seed ∈ seedSet k)` is a
well-defined *deterministic* map `[0,1) → {0,…,n-1}` whose pushforward of the
uniform seed distribution is precisely the quantum distribution `p` — a
deterministic theory experimentally indistinguishable from Quantum Mechanics, as
the book claims. The surrounding physical/metaphysical discussion remains prose.

**Verification.** `lake build BookProof.ChapterInverseTransform` is green; the new
file is `sorry`-free and, by `#print axioms`, every named theorem depends only on
`propext`, `Classical.choice`, `Quot.sound`. The only pre-existing repository build
failure remains the out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

**Bookkeeping.** Added a Wave 106 entry to `BookProof/STATUS.md` and prepended
this summary to `ARISTOTLE_SUMMARY.md`. All changes are committed and pushed.

# Summary of changes for run 2c0954c6-74bc-4933-9828-29e68a1a235f
Did the next formalization step, continuing the Bell inequalities section of `book.tex` (chapter "Reconstructing the classical trajectory of any isolated quantum system") — off the Gravity line and with no Hankel transform, as requested.

**New file `BookProof/ChapterTsirelson.lean`** (registered in `BookProof.lean`), which proves that **Tsirelson's bound is tight**. The previous work (`BookProof/ChapterBell.lean`) had established the classical CHSH bound `≤ 2`, the concrete two-qubit quantum value `= 2√2`, and `2 < 2√2`. Mathlib already contains the abstract Tsirelson upper bound `A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁ ≤ √2³ • 1`, and its own documentation flags the tightness of this bound as future work; this run supplies that witness:

- `alA0, alA1, boB0, boB1` — the two-qubit CHSH tuple as elements of a single `*`-ring `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ`: Alice's `σ_z⊗1`, `σ_x⊗1`, Bob's `1⊗(σ_z±σ_x)/√2`.
- `chshTuple_isCHSHTuple` — this quadruple satisfies exactly the hypotheses of Mathlib's Tsirelson inequality (each observable is a self-adjoint involution; Alice's commute with Bob's).
- `chshOp_eq_tuple` — the Bell-chapter CHSH operator equals the tuple's CHSH combination.
- `tsirelson_value_eq` — `2√2 = √2³` (the quantum value equals the abstract bound constant).
- `chshOp_eigenvector` — the tightness witness: the CHSH operator has the Bell state as an eigenvector with eigenvalue `2√2`, refining the previous expectation-value computation.
- `tsirelson_bound_tight` — headline: the concrete tuple is a CHSH tuple whose operator attains the abstract bound `√2³ = 2√2` as an eigenvalue, so the inequality cannot be improved.

**Verification.** `lake build BookProof` is green; the new file is `sorry`-free and, by `#print axioms`, all named theorems depend only on `propext`, `Classical.choice`, `Quot.sound`. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

**Bookkeeping.** Added a Wave 105 entry to `BookProof/STATUS.md` and prepended a summary section to `ARISTOTLE_SUMMARY.md`. All changes are committed and pushed.

# Summary of changes for run tsirelson-tight-wave-105
Did the next formalization step (per the instruction: do the next steps, no Hankel transform, prioritize chapters other than Gravity), continuing the Bell chapter from the previous run, and updated `ARISTOTLE_SUMMARY.md` as requested.

**Target.** The `book.tex` section "Do the Bell inequalities hold?" (chapter "Reconstructing the classical trajectory of any isolated quantum system"). The previous run (Wave 104, `BookProof/ChapterBell.lean`) proved the classical CHSH bound `≤ 2`, the concrete two-qubit quantum CHSH expectation value `= 2√2`, and `2 < 2√2`. Mathlib itself contains the abstract **Tsirelson inequality** (`tsirelson_inequality`: for any CHSH tuple in an ordered `*`-algebra over `ℝ`, `A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁ ≤ √2^3 • 1`) whose docstring flags as *future work* that this upper bound is **tight**: there is a CHSH tuple of `4×4` complex matrices whose CHSH operator has `2√2` as an eigenvalue. This run supplies that witness, tied to the concrete `ChapterBell` model.

**Added** one new file, `BookProof/ChapterTsirelson.lean`, sorry-free and axiom-free (only `propext`, `Classical.choice`, `Quot.sound`, checked with `#print axioms`), registered in `BookProof.lean`:
- `alA0, alA1, boB0, boB1` — the two-qubit CHSH tuple as genuine elements of the *one* `*`-ring `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ`: Alice's `σ_z ⊗ 1`, `σ_x ⊗ 1`, Bob's `1 ⊗ (σ_z±σ_x)/√2`.
- `chshTuple_isCHSHTuple` — this quadruple is a Mathlib `IsCHSHTuple` (each observable a self-adjoint involution; Alice's commute with Bob's), i.e. it satisfies exactly the hypotheses of `tsirelson_inequality`.
- `chshOp_eq_tuple` — `ChapterBell.chshOp` equals the tuple's CHSH combination (via the mixed Kronecker product `(A⊗1)(1⊗B)=A⊗B`).
- `tsirelson_value_eq` — `2√2 = √2^3`, i.e. the Tsirelson value equals the abstract bound constant.
- `chshOp_eigenvector` — the tightness witness `chshOp *ᵥ |Φ⁺⟩ = 2√2 • |Φ⁺⟩`: the Bell state is an eigenvector of the CHSH operator with eigenvalue `2√2` (refining the previous run's expectation-value computation).
- `tsirelson_bound_tight` — headline bundling: the concrete tuple is a CHSH tuple whose operator has the abstract bound `√2^3 = 2√2` as an eigenvalue, so `tsirelson_inequality` cannot be improved.

**Verification.** `lake build BookProof` is green; `BookProof/ChapterTsirelson.lean` compiles with no `sorry`; all named theorems depend only on the standard axioms. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

**Bookkeeping.** Recorded a Wave 105 entry in `BookProof/STATUS.md` and prepended this section to `ARISTOTLE_SUMMARY.md`. All changes are committed and pushed.

# Summary of changes for run 2a6bec34-cbba-473e-a3c2-5ae8037a70be
Did the next formalization step, moving off the parity thread to a fresh, previously unmined chapter (per the instruction: no Hankel transform, and prioritizing chapters other than Gravity), and updated `ARISTOTLE_SUMMARY.md` as requested.

**New target.** The `book.tex` section "Do the Bell inequalities hold?" (in the chapter "Reconstructing the classical trajectory of any isolated quantum system"), which concedes the Bell inequalities are "mathematically valid inequalities [that] involve unrealistic assumptions." The two formalizable facts are the inequality itself and its quantum violation.

**Added** one new file, `BookProof/ChapterBell.lean`, sorry-free and axiom-free (only `propext`, `Classical.choice`, `Quot.sound`, checked with `#print axioms`), registered in `BookProof.lean`:
- Part A (classical / local hidden variables): `chsh_pointwise` — the pointwise bound `|a₀b₀ + a₀b₁ + a₁b₀ − a₁b₁| ≤ 2` for values in `[-1,1]`; and `chsh_local` — the measure-theoretic Bell/CHSH inequality: for any probability measure and `[-1,1]`-valued random variables, `|∫ (A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁) dμ| ≤ 2`.
- Part B (quantum violation): the concrete two-qubit model — Alice's `A₀ = σ_z`, `A₁ = σ_x`, Bob's `B₀ = (σ_z+σ_x)/√2`, `B₁ = (σ_z−σ_x)/√2`, the CHSH operator on `ℂ²⊗ℂ²` (Kronecker products), and the Bell state `|Φ⁺⟩ = (|00⟩+|11⟩)/√2` — with `chsh_quantum_value` proving `⟨Φ⁺|S|Φ⁺⟩ = 2√2` (the Tsirelson value) and `chsh_quantum_violates_local_bound` proving `2 < 2√2`, i.e. quantum mechanics exceeds the classical Bell bound.

**Verification.** `lake build BookProof` is green; `BookProof/ChapterBell.lean` compiles with no `sorry`; all four theorems depend only on the standard axioms. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

**Bookkeeping.** Recorded a Wave 104 entry in `BookProof/STATUS.md` and prepended a new summary section to `ARISTOTLE_SUMMARY.md`. All changes are committed and pushed.

# Summary of changes for run bell-chsh-wave-104
Continued the `book.tex` formalization by moving off the parity thread to a fresh, previously
unmined chapter (per the new instruction: *do the next steps; no Hankel transform (Majorana is
fine); prioritize chapters other than Gravity*). Target: the chapter *"Reconstructing the
classical trajectory of any isolated quantum system"*, §*"Do the Bell inequalities hold?"*
(`book.tex` line ~3175), which concedes the Bell inequalities are *"mathematically valid
inequalities [that] involve unrealistic assumptions"*.

**What I did.** Added one new file, **sorry-free** and **axiom-free** (only `propext`,
`Classical.choice`, `Quot.sound`, checked with `#print axioms`), registered in `BookProof.lean`:

`BookProof/ChapterBell.lean` — the two mathematically formalizable facts of the section:
- Part A (classical / local hidden-variable model): `chsh_pointwise` (the elementary pointwise
  bound `|a₀b₀ + a₀b₁ + a₁b₀ − a₁b₁| ≤ 2` for `a₀,a₁,b₀,b₁ ∈ [-1,1]`) and `chsh_local` (the
  measure-theoretic Bell/CHSH inequality: for any probability measure `μ` and `[-1,1]`-valued
  random variables, `|∫ (A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁) dμ| ≤ 2`).
- Part B (quantum violation): the concrete two-qubit model — Alice's `A₀ = σ_z`, `A₁ = σ_x`,
  Bob's `B₀ = (σ_z+σ_x)/√2`, `B₁ = (σ_z−σ_x)/√2`, the CHSH operator on `ℂ²⊗ℂ²` (Kronecker
  products), and the Bell state `|Φ⁺⟩ = (|00⟩+|11⟩)/√2` — with `chsh_quantum_value`
  (`⟨Φ⁺|S|Φ⁺⟩ = 2√2`, the Tsirelson value) and `chsh_quantum_violates_local_bound` (`2 < 2√2`),
  i.e. quantum mechanics exceeds the classical Bell bound.

**Verification.** `lake build BookProof` is green and `BookProof/ChapterBell.lean` compiles;
the file contains no `sorry` (the one grep match is the docstring note); all four headline
theorems were confirmed via `#print axioms` to depend only on `propext`, `Classical.choice`,
`Quot.sound`. The only remaining repository build failure is the pre-existing, out-of-scope
`RiemannProof/RandomMap.lean`, left untouched.

**Bookkeeping.** Recorded a Wave 104 entry in `BookProof/STATUS.md`, and — per the new
instruction — updated this `ARISTOTLE_SUMMARY.md`. All changes are committed and pushed.

---

# Summary of changes for run 50c0eef2-4d91-4fd9-af92-1ec2f0c25712
Continued the formalization of the book chapter *"On the physical parity transformation and antiparticles"* (off the gravity line, no Hankel transform, Majorana in scope), picking up after the previous parity/Majorana/CPT waves.

**What I did.** The chapter states that, promoting the CKM matrix to a background field, the electroweak Lagrangian is invariant under the background symmetry `SU(2)_L × (SU(3)_C × U(1)_Y) ⋊ Z₄`, where the `Z₄` factor is generated by the *single* generalized parity-reversal transformation acting simultaneously on all fields. Earlier waves proved each per-field internal parity is order four separately; no file yet assembled them into that one generator. This step does so.

Added one new file, **sorry-free** and **axiom-free** (only `propext`, `Classical.choice`, `Quot.sound`, checked with `#print axioms`), registered in `BookProof.lean`:

`BookProof/ChapterParityZ4.lean` — defines `combinedParity = (higgsParity, QLParity, mgamma 0, mgamma 0)` as one element of the product monoid `FieldOps` of field-space endomorphisms (Higgs doublet `iσ₂` on `ℂ²`, left-handed quark doublet `-(σ₂⊗iγ⁰)` on `ℂ²⊗ℂ⁴`, and the two right-handed quarks `iγ⁰` on `ℂ⁴`). Proven:
- `combinedParity_sq` (`P² = (-1,-1,-1,-1)` — every field squares to `-1`),
- `combinedParity_sq_ne_one` (`P² ≠ 1`, not an involution),
- `combinedParity_pow_four` (`P⁴ = 1`),
- `combinedParity_order_four` (the conjunction), and
- headline `combinedParity_orderOf` (`orderOf combinedParity = 4`) — the precise sense in which the single parity transformation generates a cyclic group `ℤ₄ = ℤ/4ℤ`.

It reuses the existing per-field facts `ChapterParity.higgsParity_sq`/`mgamma0_sq` and `ChapterParityQL.QLParity_sq`. The full background gauge group and its semidirect structure remain prose, matching the neighbouring parity files.

**Verification.** `lake build BookProof` is green; the file contains no `sorry` (the one grep match is the docstring note); the headline theorems were confirmed to depend only on the standard axioms. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

**Bookkeeping.** Recorded a Wave 103 entry in `BookProof/STATUS.md`. Per the standing instruction I did not edit `ARISTOTLE_SUMMARY.md` directly; this summary documents the update. All changes are committed and pushed.

# Summary of changes for run d261f5a8-0985-42db-a4da-2680e90ee558
Continued the formalization of the book chapter *"On the physical parity transformation and antiparticles"* — off the gravity line, no Hankel transform, Majorana in scope, as requested.

**What I did.** Where the previous waves had worked through the *"Majorana spinors in the Standard Model"* subsection, this step formalizes the earlier *"Majorana spinors in canonical quantization and antiparticles"* subsection (book §~7680): the book quantizes a real Hilbert/symplectic space by a skew-symmetric complex structure `J` (`J² = −1`) and splits the self-adjoint field `a(v) = a(v+iJv) + a(v−iJv)` into an annihilation part (`v+iJv`) and a creation part (`v−iJv = (v+iJv)*`).

Added one new file to the `BookProof` library, **sorry-free** and **axiom-free** (only `propext`, `Classical.choice`, `Quot.sound`, checked via `#print axioms`), and registered it in `BookProof.lean`:

`BookProof/ChapterParityMajoranaQuant.lean` — on the finite model `V = ℂᵐ`, a complex structure is a matrix `J` with `J·J = −1` and `Jᴴ = −J`. Writing `iJ = i·J`, `annihProj = ½(1+iJ)`, `creatProj = ½(1−iJ)`:
- `iJ_herm` (`(iJ)ᴴ = iJ`) and `iJ_sq` (`(iJ)² = 1`): `iJ` is a Hermitian involution with eigenvalues `±1`.
- `proj_add` (`annihProj + creatProj = 1`): the field split `a = a₋ + a₊`.
- `annihProj_idem` / `creatProj_idem` (idempotent), `annih_creat_zero` / `creat_annih_zero` (complementary, products `0`), `annihProj_herm` / `creatProj_herm` (Hermitian): the two are complementary orthogonal projections.
- `J_unitary` / `J_unitary'` (`Jᴴ·J = J·Jᴴ = 1`): a compatible complex structure is unitary (the metric/complex-structure/symplectic-form compatibility of the book's real Hilbert/symplectic space).
- `J_annih` (`J·annihProj = (−i)·annihProj`) and `J_creat` (`J·creatProj = i·creatProj`): the annihilation/creation combinations are the `∓i`-eigenprojections of `J`.
- `stdJ = !![0,1;−1,0]` with `stdJ_sq`, `stdJ_skew`: a concrete non-vacuous witness that the hypotheses are satisfiable.

The surrounding physics (the abstract Clifford/CAR C*-algebra, the bosonic symplectic CCR `[a(v),a(w)] = ⟨v,Jw⟩i`, the vacuum functional) is left as prose, matching the neighbouring parity files.

**Verification.** `lake build BookProof` is green; a grep confirms no `sorry` remains in the file (the single match is the docstring's "sorry-free" note); representative headline theorems (`J_annih`, `J_unitary`) were confirmed to depend only on the standard axioms. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

**Bookkeeping.** Recorded a Wave 102 entry in `BookProof/STATUS.md`. Per the standing instruction I did not edit `ARISTOTLE_SUMMARY.md` directly; this summary documents the update. All changes are committed and pushed to `origin/main`.

# Summary of changes for run 87138dec-d7bf-4c21-91ca-d0aaa931c960
Continued the formalization of the book chapter *"On the physical parity transformation and antiparticles"*, §"Majorana spinors in the Standard Model" — off the gravity line, no Hankel transform, Majorana in scope — picking up after the previous parity/Majorana/CPT waves (which had already exhausted the custodial commutant, hypercharge `U(1)_Y` phase, Higgs reality structure, `SU(2)_L` outer automorphism, `Q_L`/`u_R`/`d_R` parity order-four, and the Dirac-mass PT/CPT results).

Added one new file to the `BookProof` library, **sorry-free** and **axiom-free** (only `propext`, `Classical.choice`, `Quot.sound`, checked via `#print axioms`), registered in `BookProof.lean`:

`BookProof/ChapterParityChirality.lean` — the chapter's chirality/projection constraint on the left-handed quark doublet, `iγ⁵ Q_L = iσ₃ Q_L`, and the Yukawa-counting footnote's *"projector in Q_L"* (used to halve the 4 custodial matrices `{1, iσⱼ}` down to 2 independent products). On `ℂ²⊗ℂ⁴ ≅ ℂ⁸`, writing `isigma3 = (iσ₃)⊗1` and `igamma5 = 1⊗(iγ⁵)`:
- `isigma3_sq`, `igamma5_sq`: both square to `-1`.
- `isigma3_igamma5`, `igamma5_isigma3`: the two generators commute, their common product being the chirality operator `chi = (iσ₃)⊗(iγ⁵)`.
- `chi_sq` (`χ² = 1`, an involution with eigenvalues `±1`) and `chi_trace` (`tr χ = 0`, so the `±1` eigenspaces have equal dimension — the footnote's "divide by 2").
- `QLProj = ½(1 - χ)`, the chirality projector, with `QLProj_idem` (`P² = P`) and `QLProj_trace` (`tr P = 4`, half of the ambient dimension 8).
- Headline `chirality_iff`: the constraint `iσ₃ Q_L = iγ⁵ Q_L` is equivalent to `χ Q_L = -Q_L`; and `chirality_iff_proj`: equivalent to `Q_L` lying in the range of the projector, `P Q_L = Q_L`.
The surrounding physics (full Standard-Model Yukawa Lagrangian and the `SU(2)_L × (SU(3)_C × U(1)_Y) ⋊ ℤ₄` background symmetry) is left as prose, as in the neighbouring parity files.

Verification: `lake build BookProof` is green; a grep confirms no `sorry` remains in the file (the one match is the docstring's "sorry-free" note); the headline theorems were checked to depend only on the standard axioms. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

Recorded a Wave 101 entry in `BookProof/STATUS.md`. Per the standing instruction, I did not edit `ARISTOTLE_SUMMARY.md` directly; this summary documents the update. All changes are committed and pushed.

# Summary of changes for run c7bf342a-f65c-4d88-b05c-cd20a5d72369
Continued the formalization of the book chapter *"On the physical parity transformation and antiparticles"*, §"Majorana spinors in the Standard Model" (off the gravity line, no Hankel transform, Majorana in scope), picking up after the previous parity/CPT waves.

Added two new files to the `BookProof` library, both **sorry-free** and **axiom-free** (only `propext`, `Classical.choice`, `Quot.sound`, verified via `#print axioms`), each registered in `BookProof.lean`:

1. `BookProof/ChapterParityCustodial.lean` — the representation theory behind the chapter's footnote *"the basis of matrices commuting with the generators of SU(2)_L is {1, iσ_j}, for a total of 4 matrices."*
   - `commutant_pauli_scalar`: the Pauli matrices σ₁,σ₂,σ₃ act irreducibly on ℂ², so any matrix commuting with all three is a scalar `M = (M 0 0)•1` (Schur's lemma for the doublet).
   - `pauli_basis_indep`: {1, σ₁, σ₂, σ₃} are linearly independent over ℂ (a basis of the 2×2 complex matrices), so the custodial generators {1, iσ_j} are four linearly independent matrices.

2. `BookProof/ChapterParityHypercharge.lean` — the chapter's *"the generator of U(1)_Y is iγ⁵"* / *"the imaginary unit replaced by iγ⁵"*, in the concrete real Majorana model.
   - `mgamma5_real`: iγ⁵ = `mgamma5` is a genuine **real** matrix (`conj(iγ⁵) = iγ⁵`) which, together with (iγ⁵)² = −1, is a *real* complex structure.
   - `hyperPhase ϑ = cos ϑ·1 + sin ϑ·iγ⁵` (the closed form of e^{ϑ iγ⁵}) with `hyperPhase_zero`, `hyperPhase_add` (the abelian U(1)_Y group law), `hyperPhase_neg_mul` (invertibility) and `hyperPhase_comm` — establishing it as the one-parameter U(1)_Y group generated by iγ⁵.

Verification: `lake build BookProof` is green; a grep confirms no `sorry` remains in either file; the headline theorems were checked to depend only on the standard axioms. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

Recorded a Wave 100 entry in `BookProof/STATUS.md`. (I did not edit `ARISTOTLE_SUMMARY.md` directly per the standing instruction to leave that file unedited; this summary documents the update.) All changes are committed and pushed.

# Summary of changes for run f42d09ed-e032-41ce-81a3-c3057d6e5297
Executed the next steps of `FORMALIZATION_ROADMAP.md`, honoring the active constraints (chapter other than gravity; no Hankel transform; Majorana in scope). Continued the book chapter *"On the physical parity transformation and antiparticles"*, §"Majorana spinors in the Standard Model" (directly after the previous parity/CPT waves).

Two new files added to the `BookProof` library, both `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`), each registered in `BookProof.lean`:

1. `BookProof/ChapterParityHiggs.lean` — **the Higgs is a real representation.** The chapter's thesis that at the quantum level all fields are real representations is formalized for the electroweak Higgs doublet via its Majorana condition `iσ₂ φ = iτ₂ φ*`, realized on the bidoublet `ℂ²⊗ℂ²` by the antilinear operator `C(φ) = (τ₂⊗σ₂) φ*`. Introduces the reality operator `realityOp M v = M *ᵥ v*` with `realityOp_realityOp` (`C_M∘C_M = (M·M*) *ᵥ ·`), shows a single doublet is pseudoreal (`σ₂·σ₂* = -1`, `C₀² = -id`), proves the general lemma `pseudoreal_kron_pseudoreal_real` (a tensor product of two quaternionic structures is a real structure), and concludes the headline `higgs_real_structure` (`C∘C = id`): the Higgs bidoublet carries a genuine real structure even though neither `SU(2)` factor alone does.

2. `BookProof/ChapterParitySU2.lean` — **`SU(2)_L` has trivial outer automorphism.** Formalizes the chapter's remark that the outer automorphism group of `SU(2)_L` is trivial by showing complex conjugation is inner: the pseudoreality intertwiner `pauliV_pseudoreal` (`σ₂ σ_j σ₂ = -(σ_j)*`) gives `su2_conj_inner` (`conj(iσ_j) = σ₂ (iσ_j) σ₂`, with `σ₂²=1`), so the complex-conjugate representation is unitarily equivalent to the original — in contrast to `SU(3)`, whose conjugation negates `λ²,λ⁵,λ⁷` (the nontrivial `Z₂`, already in `ChapterParity.gellMann_conj`).

Verification: `lake build BookProof` is green (8154 jobs); the new headline theorems were checked via `#print axioms` to depend only on the standard axioms, and both files are `sorry`-free. Also updated `ARISTOTLE_SUMMARY.md` (as requested) and `BookProof/STATUS.md` with a Wave 99 entry. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. All changes are committed and pushed.

# Summary of latest run — Wave 99: the Higgs is a real representation, and `SU(2)_L` has trivial outer automorphism

Executed the next steps of `FORMALIZATION_ROADMAP.md`, honoring the active constraints
(prioritized a chapter other than gravity; no Hankel transform; Majorana in scope).
Continued the book chapter *"On the physical parity transformation and antiparticles"*,
§"Majorana spinors in the Standard Model", directly after Wave 97/98 (`ChapterParity`,
`ChapterParityQL`, `ChapterCPTPT`).

**Two new files, both `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`), registered in `BookProof.lean`:**

* **`BookProof/ChapterParityHiggs.lean` — the Higgs is a real representation.** The
  chapter's central thesis is that at the quantum level all fields are real
  representations. For the electroweak Higgs doublet this is the Majorana condition
  `iσ₂ φ = iτ₂ φ*`, realized on the bidoublet `ℂ²⊗ℂ²` by the antilinear operator
  `C(φ) = (τ₂⊗σ₂) φ*`. The file introduces the antilinear reality operator
  `realityOp M v = M *ᵥ v*` and proves `realityOp_realityOp`: `C_M∘C_M = (M·M*) *ᵥ ·`, so
  `C_M` is a *real structure* iff `M·M*=1` and a *quaternionic (pseudoreal) structure* iff
  `M·M*=-1`. A single `SU(2)` doublet is pseudoreal (`pauli2_pseudoreal` `σ₂·σ₂*=-1`,
  `higgsDoublet_pseudoreal` `C₀²=-id`), but the general lemma
  `pseudoreal_kron_pseudoreal_real` (`A·A*=-1` and `B·B*=-1` ⇒ `(A⊗B)·(A⊗B)*=1`) gives the
  headline `higgs_real_structure` `C∘C=id`: **a tensor product of two quaternionic
  structures is a real structure**, so the Higgs bidoublet carries a genuine real structure
  even though neither `SU(2)` factor alone does.
* **`BookProof/ChapterParitySU2.lean` — `SU(2)_L` has trivial outer automorphism.** The
  chapter states "the outer automorphism group of `SU(3)` or `U(1)_Y` is `Z₂`, while the
  outer automorphism group of `SU(2)_L` is the trivial group." For `SU(2)` the relevant
  automorphism (complex conjugation) is shown to be **inner**: `pauliV_pseudoreal`
  `σ₂ σ_j σ₂ = -(σ_j)*` yields `su2_conj_inner` `conj(iσ_j) = σ₂ (iσ_j) σ₂` (with `σ₂²=1`),
  so the complex-conjugate representation is unitarily equivalent to the original. This
  contrasts with `SU(3)`, whose conjugation negates `λ²,λ⁵,λ⁷` (`ChapterParity.gellMann_conj`,
  the nontrivial `Z₂`). The `SU(3)` outer-nontriviality and the full Standard-Model gauge
  structure remain prose.

Verification: `lake build BookProof` is green; the headline theorems carry only the
standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and both files are
`sorry`-free. Updated `ARISTOTLE_SUMMARY.md` (as requested) and `BookProof/STATUS.md` with
a Wave 99 entry. The only remaining repository build failure is the pre-existing,
out-of-scope `RiemannProof/RandomMap.lean`, left untouched. All changes are committed and
pushed.

---

# Summary of changes for run b5182d4b-9ccc-493a-a865-1b412e068859
Executed the next step of `FORMALIZATION_ROADMAP.md`, honoring the active constraints (prioritized a chapter other than gravity; no Hankel transform; Majorana in scope).

**New deliverable — one new file `BookProof/ChapterCPTPT.lean`** (registered in `BookProof.lean`), picking up directly after the previous Wave 96/97 and closing a gap those runs explicitly left as prose. The book's chapter *"Real representations, CPT theorem and the relativistic position operator"*, §"Spinor frame and CPT theorem" states that the most general Lorentz-covariant Dirac mass Hamiltonian `iH = ∂⃗·γ⃗γ⁰ + iγ⁰m₁ + γ⁰γ⁵m₂` "is invariant under a parity–time reversal transformation (PT) … this is essentially the CPT theorem." Wave 96 (`ChapterCPTParity`) had formalized only the parity classification (parity P alone flips the sign of the `γ⁰γ⁵ m₂` term) and deferred the full PT statement. This file discharges it in the concrete 4×4 Majorana model (`ChapterA3`), on top of `diracHamOp` from `ChapterCPTHamiltonian`:

- The PT map `ψ(t,x⃗) ↦ γ⁵ ψ*(-t,-x⃗)` is split into two ingredients.
- Time reversal = entrywise complex conjugation: since the building blocks `Kin j = γʲγ⁰`, `MassA = iγ⁰`, `MassB = γ⁰γ⁵` are real matrices, conjugation only flips the explicit `i`, i.e. flips the momentum — `conj_diracHamOp`: `conj(D(k,m₁,m₂)) = D(-k,m₁,m₂)`.
- γ⁵ dressing: `γ⁵` commutes with the kinetic blocks and anticommutes with both mass blocks (`Kin_dgamma5_comm`, `MassA_dgamma5_anticomm`, `MassB_dgamma5_anticomm`, from integer-model `decide` relations transported to ℂ) — `pt_diracHamOp`: `D(k)·γ⁵ = -(γ⁵·D(-k))`.
- Headline `cpt_diracHamOp`: `γ⁵ · conj(D(k,m₁,m₂)) = -(D(k,m₁,m₂) · γ⁵)`, a single-equation PT invariance holding for arbitrary `m₂`, even though parity `P` alone is broken by the `γ⁰γ⁵ m₂` term — the concrete content of "this is essentially the CPT theorem."

Verification: `lake build BookProof` is green; the headline theorems `cpt_diracHamOp` and `pt_diracHamOp` carry only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and the file has no `sorry`. Updated `ARISTOTLE_SUMMARY.md` (as requested) and `BookProof/STATUS.md` with a Wave 98 entry. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. All changes are committed and pushed.

# Summary of latest run — Wave 98: the Dirac mass Hamiltonian is PT (CPT) invariant (§"Spinor frame and CPT theorem")

Continued executing `FORMALIZATION_ROADMAP.md`, mining the next self-contained mathematical claim from `book.tex` and honoring the active constraints (prioritized a chapter other than gravity; no Hankel transform; Majorana in scope).

**New deliverable — Wave 98, one new file `BookProof/ChapterCPTPT.lean`** (registered in `BookProof.lean`), picking up directly after Wave 96/97 and closing the gap those runs explicitly left as prose. The book's chapter *"Real representations, CPT theorem and the relativistic position operator"*, §"Spinor frame and CPT theorem" (`book.tex` line ~6453) states that the most general Lorentz-covariant Dirac mass Hamiltonian `iH = ∂⃗·γ⃗γ⁰ + iγ⁰m₁ + γ⁰γ⁵m₂` "is also invariant under a parity–time reversal transformation (PT). This is essentially the CPT theorem." Wave 96 (`ChapterCPTParity`) formalized the *parity* classification (parity `P` alone flips the sign of the `γ⁰γ⁵ m₂` term — the parity-breaking term) but deferred the full PT statement to prose; this file discharges it in the concrete `4×4` Majorana model (`ChapterA3`, `M_μ = iγ^μ`) on top of `diracHamOp` from `ChapterCPTHamiltonian`.

- The PT transformation is the antiunitary map `ψ(t,x⃗) ↦ γ⁵ ψ*(-t,-x⃗)`, decomposed into two ingredients.
- **Time reversal (complex conjugation).** In the Majorana basis the three building blocks `Kin j = γʲγ⁰`, `MassA = iγ⁰`, `MassB = γ⁰γ⁵` are real matrices (`Kin_map_conj`/`MassA_map_conj`/`MassB_map_conj`), so entrywise conjugation of the Hamiltonian only flips the explicit `i` on the kinetic term: `conj_diracHamOp` — `conj(D(k,m₁,m₂)) = D(-k,m₁,m₂)`.
- **γ⁵ dressing.** The chirality matrix `γ⁵ = dgamma5` commutes with the kinetic blocks and anticommutes with both mass blocks (`Kin_dgamma5_comm`, `MassA_dgamma5_anticomm`, `MassB_dgamma5_anticomm`, established via integer-model `decide` relations `mgamma5Z_KinZ_comm`/`mgamma5Z_MassAZ_anticomm`/`mgamma5Z_MassBZ_anticomm` transported to ℂ), giving `pt_diracHamOp` — `D(k,m₁,m₂)·γ⁵ = -(γ⁵·D(-k,m₁,m₂))`.
- **Headline `cpt_diracHamOp`**: combining both, `γ⁵ · conj(D(k,m₁,m₂)) = -(D(k,m₁,m₂) · γ⁵)`, a single-equation form of PT invariance (no matrix inverse). Equivalently the antiunitary `ψ ↦ γ⁵ ψ*(-t,-x⃗)` sends solutions of `∂_t ψ = (iH)ψ` to solutions. Crucially this holds for **arbitrary** `m₂`, even though parity `P` alone is broken by the `γ⁰γ⁵ m₂` term — the concrete content of "this is essentially the CPT theorem."

Verification: `lake build BookProof` is green; `cpt_diracHamOp` and `pt_diracHamOp` carry only the standard axioms `propext`, `Classical.choice`, `Quot.sound` (confirmed with `lean_verify`), and the file has no `sorry`. Updated `ARISTOTLE_SUMMARY.md` (as requested) and `BookProof/STATUS.md` with a Wave 98 entry. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. All changes committed and pushed.

---

# Summary of changes for run 6f025e0a-8239-4f47-b8b6-932040af3296
Continued executing `FORMALIZATION_ROADMAP.md`, mining the next self-contained mathematical claim from `book.tex` and honoring the active constraints (prioritized a chapter other than gravity; no Hankel transform; Majorana in scope).

**New deliverable — Wave 97, one new file `BookProof/ChapterParityQL.lean`** (registered in `BookProof.lean`), picking up directly after the previous run's Wave 96 and moving into the following chapter *"On the physical parity transformation and antiparticles"* (§"Majorana spinors in the Standard Model"), extending the existing `BookProof/ChapterParity.lean`:

- Formalized that the internal (matrix) part of the chapter's generalized-parity (ℤ₄) transformation of the left-handed quark doublet `Q_L(t,x⃗) ↦ -σ₂ γ⁰ Q_L(t,-x⃗)` is **order exactly four**. Because `Q_L` carries both an `SU(2)_L` doublet index (acted on by `σ₂`) and a Majorana spinor index (acted on by the parity `iγ⁰` of the concrete Majorana model in `ChapterA3`), the operator is the Kronecker product `QLParity = -(σ₂ ⊗ iγ⁰)` on `ℂ² ⊗ ℂ⁴ ≅ ℂ⁸`.
- `QLParity_sq`: `(-σ₂ ⊗ iγ⁰)² = -1`, proved by reusing `ChapterParity.pauli2_sq` (`σ₂² = 1`) and `ChapterParity.mgamma0_sq` (`(iγ⁰)² = -1`) via `Matrix.mul_kronecker_mul`; `QLParity_pow_four`: `(…)⁴ = 1`; headline `QLParity_order_four`: not an involution, but its fourth power is `1`.
- The square being `-1` (not `+1`) is the invariant selecting the double cover `Pin(3,1)` over `Pin(1,3)`, matching the right-handed-quark result already in `ChapterParity` — the concrete content behind the chapter's conclusion that the cover "must be `Pin(3,1)`". The surrounding physical modelling (full Standard-Model Lagrangian, the background symmetry group) is left as prose.

Verification: `lake build BookProof` is green; the new theorems carry only the standard axioms `propext`, `Classical.choice`, `Quot.sound` (confirmed with `lean_verify`) and contain no `sorry`. Updated `ARISTOTLE_SUMMARY.md` (as requested) and `BookProof/STATUS.md` with a Wave 97 entry. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. All changes are committed and pushed.

# Summary of latest run — Wave 97: the Standard-Model left-handed quark-doublet parity is order four (§"Majorana spinors in the Standard Model")

Continued executing `FORMALIZATION_ROADMAP.md`, mining the next self-contained claim from `book.tex`, honoring the active constraints (prioritized a chapter other than gravity; no Hankel transform; Majorana in scope). Picked up directly after Wave 96's parity classification of the Dirac mass Hamiltonian, moving into the following chapter *"On the physical parity transformation and antiparticles"* (`book.tex` line ~7522), §"Majorana spinors in the Standard Model", extending the existing `BookProof/ChapterParity.lean`.

New work — one new file `BookProof/ChapterParityQL.lean`, registered in `BookProof.lean`, `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `lean_verify`):

- Formalized that the internal (matrix) part of the chapter's generalized-parity (`ℤ₄`) transformation of the **left-handed quark doublet** `Q_L(t,x⃗) ↦ -σ₂ γ⁰ Q_L(t,-x⃗)` is **order exactly four**. Since `Q_L` carries both an `SU(2)_L` doublet index (acted on by `σ₂`) and a Majorana spinor index (acted on by the parity `iγ⁰ = mgamma 0` of the concrete `ChapterA3` model), the operator is the Kronecker product `QLParity = -(σ₂ ⊗ iγ⁰)` on `ℂ² ⊗ ℂ⁴ ≅ ℂ⁸`.
- `QLParity_sq`: `(-σ₂ ⊗ iγ⁰)² = -1`, proved from the reused `ChapterParity.pauli2_sq` (`σ₂² = 1`) and `ChapterParity.mgamma0_sq` (`(iγ⁰)² = -1`) via `Matrix.mul_kronecker_mul`; `QLParity_pow_four`: `(…)⁴ = 1`; headline `QLParity_order_four`: the operator is not an involution but its fourth power is `1`.
- The value `-1` (rather than `+1`) of the square is the invariant selecting the double cover `Pin(3,1)` over `Pin(1,3)`, matching the right-handed-quark result `ChapterParity.fermionParity_order_four` — the concrete content behind the chapter's conclusion that the double cover "must be `Pin(3,1)`".

The surrounding physical modelling (the full Standard-Model Lagrangian, the `SU(2)_L × (SU(3)_C × U(1)_Y) ⋊ ℤ₄` background symmetry) is left as prose, consistent with prior waves.

Verification: `lake build BookProof` is green; the new theorems carry only the standard three axioms and contain no `sorry`. Updated `ARISTOTLE_SUMMARY.md` (as requested) and `BookProof/STATUS.md` with a Wave 97 entry. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. All changes committed and pushed.

# Summary of changes for run 5128ffea-80ec-4f8c-82e6-b98c87a3bb63
Continued the formalization of `book.tex`, chapter "Real representations, CPT theorem and the relativistic position operator", §"Spinor frame and CPT theorem" (book line ~6453), picking up directly after the previous run's Localization obstruction. Honored the active constraints: prioritized a chapter other than gravity, no Hankel transform, Majorana in scope.

New work — one new file `BookProof/ChapterCPTParity.lean`, registered in `BookProof.lean`, `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`):

- Formalized the **parity classification of the most general Lorentz-covariant Dirac mass Hamiltonian** `iH = ∂⃗·γ⃗γ⁰ + iγ⁰m₁ + γ⁰γ⁵m₂`, building on `ChapterCPTHamiltonian`'s `diracHamOp`. The parity (spatial-reflection) operation is the momentum flip `k⃗ ↦ -k⃗` together with conjugation of the spinor by the Majorana parity matrix `P = iγ⁰` (`P² = -1`, so `P⁻¹ = -P`; `parity_mul_neg_self`).
- Classified the three building blocks (integer model by `decide`, complex model by transport along the integer cast): the kinetic matrices `Kin j = γʲγ⁰` are parity-odd (`parity_Kin`/`parity_KinZ`); the `m₁` mass `iγ⁰` is parity-even (`parity_MassA`/`parity_MassAZ`); the `m₂` mass `γ⁰γ⁵` is parity-odd — the book's parity-breaking term (`parity_MassB`/`parity_MassBZ`).
- Headline `parity_diracHamOp`: `P · D(-k, m₁, m₂) · P⁻¹ = D(k, m₁, -m₂)` — under parity the Hamiltonian is mapped to the same one with `m₂ ↦ -m₂`. Corollary `parity_diracHamOp_invariant`: with `m₂ = 0` the Hamiltonian is exactly parity-invariant, so a nonzero `γ⁰γ⁵` mass is the sole source of parity (CP) violation — the concrete algebraic content of the section's CPT-theorem discussion.

The book's further claim that `iH` (including `m₂`) is invariant under the full parity–time-reversal PT transformation is an antiunitary statement about the field representation and is left as prose, consistent with prior waves.

Verification: `lake build BookProof` is green; the new theorems carry only the standard three axioms and contain no `sorry`. Updated `ARISTOTLE_SUMMARY.md` (as requested) and `BookProof/STATUS.md` with a new wave entry. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. All changes committed and pushed.

# Summary of latest run — Wave 96: parity classification of the Dirac mass Hamiltonian (§"Spinor frame and CPT theorem")

Continued the formalization of `book.tex`, chapter "Real representations, CPT theorem and the relativistic position operator", §"Spinor frame and CPT theorem" (book line ~6453), picking up directly after Wave 95's Localization obstruction. Honored the active constraints: prioritized a chapter other than gravity, no Hankel transform, Majorana in scope.

New work (Wave 96) — one new file `BookProof/ChapterCPTParity.lean`, registered in `BookProof.lean`, `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`):

- Formalized the **parity classification of the most general Lorentz-covariant Dirac mass Hamiltonian** `iH = ∂⃗·γ⃗γ⁰ + iγ⁰m₁ + γ⁰γ⁵m₂`, building on `ChapterCPTHamiltonian`'s `diracHamOp`. The parity (spatial-reflection) operation is the momentum flip `k⃗ ↦ -k⃗` together with conjugation of the spinor by the Majorana parity matrix `P = iγ⁰ = mgamma 0` (with `P² = -1`, so `P⁻¹ = -P`; `parity_mul_neg_self`).
- Classified the three building blocks (integer model by `decide`, complex model by transport along the integer cast): the kinetic matrices `Kin j = γʲγ⁰` are **parity-odd** (`parity_Kin` / `parity_KinZ`); the `m₁` mass `MassA = iγ⁰` is **parity-even** (`parity_MassA` / `parity_MassAZ`); the `m₂` mass `MassB = γ⁰γ⁵` is **parity-odd** — the book's **parity-breaking term** (`parity_MassB` / `parity_MassBZ`).
- Headline `parity_diracHamOp`: `P · D(-k, m₁, m₂) · P⁻¹ = D(k, m₁, -m₂)` — under parity the Hamiltonian is mapped to the same one with `m₂ ↦ -m₂`. Corollary `parity_diracHamOp_invariant`: with `m₂ = 0` the Hamiltonian is exactly parity-invariant, so a nonzero `γ⁰γ⁵` mass is the sole source of parity (CP) violation — the concrete algebraic content of the section's CPT-theorem discussion.

The book's further claim that `iH` (including `m₂`) is invariant under the full parity–time-reversal PT transformation ("this is essentially the CPT theorem") is an antiunitary statement about the field representation and remains prose; this file formalizes the decidable parity classification underlying it.

Verification: `lake build BookProof` is green and the new theorems' axiom sets are the standard three. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. Updated `ARISTOTLE_SUMMARY.md` and `BookProof/STATUS.md`. All changes committed and pushed.

---

# Summary of changes for run c384698b-adf1-494a-8d38-8713eacd7a99
Continued the formalization of `book.tex`, chapter "Real representations, CPT theorem and the relativistic position operator", §"Localization", picking up directly after the previous run's Proposition 79. Honored the active constraints: prioritized a chapter other than gravity, no Hankel transform, Majorana in scope.

New work (Wave 95) — one new file `BookProof/ChapterLocalization.lean`, registered in `BookProof.lean`, `sorry`-free and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`):

- Formalized the load-bearing algebraic core of **Proposition 88** and **Corollary 1**. Both proofs hinge on the concrete claim "γ⁰ does not commute with the matrices γ⃗γ⁰", which is why the iγ⁰-eigenspace projectors are not preserved by the system of imprimitivity. In the concrete real Majorana model (`ChapterA3`, `M_μ = iγ^μ`), the commutator is computed in closed form: for every spatial index `i ≠ 0`, `(iγ⁰)·((iγⁱ)(iγ⁰)) − ((iγⁱ)(iγ⁰))·(iγ⁰) = (iγⁱ) + (iγⁱ)` (`commZ_gamma0_spatial` over ℤ by `decide`; `comm_gamma0_spatial` over ℂ by transport along the integer cast), giving the non-commutation `gamma0_not_comm_spatialZ` / `gamma0_not_comm_spatial` (iγⁱ ≠ 0 since it is unitary).
- Added the complementary fact underlying Proposition 79's massive little group `G_l = SU(2)`: the spatial rotation generators `(iγⁱ)(iγʲ)` (both indices ≠ 0) do commute with iγ⁰ (`commZ_gamma0_rotation` / `comm_gamma0_rotation`).

The full analytic statements of Prop 88 / Corollary 1 (systems of imprimitivity, direct-sum decompositions of unitary Poincaré representations) are functional-analytic and remain prose; this file isolates their algebraic crux.

Verification: `lake build BookProof` is green and the new theorems' axiom sets are the standard three. The only remaining repository build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. Updated `ARISTOTLE_SUMMARY.md` (prepended a Wave 95 entry) and `BookProof/STATUS.md`. All changes committed and pushed.

# Summary of latest run — Wave 95: Localization obstruction (Proposition 88 / Corollary 1)

Continued the formalization of `book.tex`, chapter "Real representations, CPT theorem and the relativistic position operator", §"Localization", picking up directly after Wave 94's Proposition 79. Honored the active constraints (prioritized a chapter other than gravity; no Hankel transform; Majorana in scope). Added one new `BookProof` file, `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`); `lake build BookProof` is green. The only repository build failure remains the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

New work (Wave 95):

- `BookProof/ChapterLocalization.lean` — the **load-bearing algebraic core of Proposition 88 and Corollary 1** (§"Localization"). Both proofs hinge on the concrete fact that "`γ⁰` does not commute with the matrices `γ⃗γ⁰`", which makes the `iγ⁰`-eigenspace projectors *not* preserved by the system of imprimitivity. Working in the concrete real Majorana model of `ChapterA3` (`M_μ = iγ^μ`), the commutator is computed in closed form: for every spatial index `i ≠ 0`, `(iγ⁰)·((iγⁱ)(iγ⁰)) − ((iγⁱ)(iγ⁰))·(iγ⁰) = (iγⁱ) + (iγⁱ)` (`commZ_gamma0_spatial` over ℤ by `decide`; `comm_gamma0_spatial` over ℂ by transport along the integer cast). The corollaries `gamma0_not_comm_spatialZ` / `gamma0_not_comm_spatial` state the non-commutation directly (`iγⁱ ≠ 0` since it is unitary). As the complementary fact underlying Proposition 79's massive little group `G_l = SU(2)`, `commZ_gamma0_rotation` / `comm_gamma0_rotation` show the spatial *rotation* generators `(iγⁱ)(iγʲ)` (both indices `≠ 0`) **do** commute with `iγ⁰`. The full analytic statements of Prop 88 / Corollary 1 (systems of imprimitivity, direct-sum decompositions) remain prose; this isolates their algebraic crux. Registered in `BookProof.lean`.

Updated `ARISTOTLE_SUMMARY.md` (this entry) and `BookProof/STATUS.md`. All changes committed and pushed.

---

# Summary of changes for run 2d7987cd-8e6c-48d1-bdab-403a3ba0b43a
Continued the formalization of `book.tex`, chapter "Real representations, CPT theorem and the relativistic position operator", §"Real unitary representations of the Poincaré group", honoring the active constraints (prioritized a chapter other than gravity; no Hankel transform; Majorana in scope). Landed three new `BookProof` files (all registered in `BookProof.lean`), each `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`); `lake build BookProof` is green. The only repository build failure remains the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

New work (Wave 94):

- `BookProof/ChapterLittleGroup.lean` — **Definition 78** (little group `G_l = Subgroup.centralizer {q l₀}`, with `mem_littleGroup`) and the **Proposition 79** headline `prop79`: in any group with an injective momentum map `q`, intertwiners `α` (`α k · q l₀ · (α k)⁻¹ = q k`) and Lorentz action `Λ` (`S · q k · S⁻¹ = q (Λ S k)`), the set `H_k = {(α (Λ S k))⁻¹ · S · α k : S}` equals `G_l`. The concrete `SU(2)`/`SE(2)` instances are left as prose.
- `BookProof/ChapterIPin.lean` — **Definition 77**: the `IPin(3,1)` / Poincaré group `Pin(3,1) ⋉ ℝ⁴` as the semidirect product `Multiplicative V ⋊[φ] P`, reproducing the book's product formula `(A,a)(B,b) = (A B, a + Λ(A) b)` via `ipin_right`/`ipin_left`.
- `BookProof/ChapterSE2.lean` — **Proposition 79**, the `SE(2)` translation subgroup of the null little group, over the concrete real Majorana matrices of `ChapterA3`: `N(a,b) = 1 + iγ⁵(γ¹a+γ²b)(γ⁰+γ³)` forms an abelian group ≅ ℝ² (`Nmat_mul`, `Nmat_zero`, `Nmat_inv`, and the capstone monoid homomorphism `NmatHom`). The core reduces to the light-cone nilpotency `(γ⁰+γ³)² = 0` (`se2_P_sq`) and `X(a,b)·X(c,d) = 0` (`Xmat_mul_Xmat`), themselves the real casts of four decidable integer identities `se2_coef_*`. The `e^{iγ⁰γ³γ⁵θ}` rotation factor (matrix exponential) is left as prose.

Updated `ARISTOTLE_SUMMARY.md` (prepended a Wave 94 entry, as requested) and `BookProof/STATUS.md`. All changes committed and pushed.

# Summary of latest run — Wave 94: Poincaré-representation section (Def 77, Def 78, Prop 79)

Continued the self-contained formalization of the chapter "Real representations,
CPT theorem and the relativistic position operator", §"Real unitary representations
of the Poincaré group", honoring the active constraints (**prioritize a chapter
other than gravity**, **no Hankel transform**, Majorana in scope). Landed three new
files, all `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`), all registered in `BookProof.lean`; `lake build BookProof` is green
(the only repository build failure remains the pre-existing, out-of-scope
`RiemannProof/RandomMap.lean`, left untouched).

**`BookProof/ChapterLittleGroup.lean` — Definition 78 + Proposition 79.**
The little group `G_l` (Def 78) is formalized as `littleGroup q l₀ =
Subgroup.centralizer {q l₀}` with `mem_littleGroup` (membership ⇔ commuting with
`\cancel l`). The headline `prop79` proves, in an arbitrary group `G` with an
injective momentum map `q : K → G`, intertwiners `α` (`hα : α k * q l₀ * (α k)⁻¹ =
q k`) and a Lorentz action `Λ` (`hΛ : S * q k * S⁻¹ = q (Λ S k)`), that the set
`H_k = {(α (Λ S k))⁻¹ S (α k) : S ∈ G}` equals `G_l`. (Group-theoretic core;
the concrete `SU(2)`/`SE(2)` instances are prose.)

**`BookProof/ChapterIPin.lean` — Definition 77.** The `IPin(3,1)` / Poincaré group
`Pin(3,1) ⋉ ℝ⁴` is formalized as the Mathlib semidirect product
`Multiplicative V ⋊[φ] P` for an abstract group `P` acting on a translation module
`V` via `Λ : P →* AddAut V` (transported through `Multiplicative` with `phiHom`).
`ipin_right`/`ipin_left` reproduce the book's product formula
`(A,a)(B,b) = (A B, a + Λ(A) b)`.

**`BookProof/ChapterSE2.lean` — Proposition 79, `SE(2)` translation subgroup.**
Over the concrete real Majorana matrices of `BookProof.ChapterA3`, the null little
group's translation matrices `N(a,b) = 1 + iγ⁵(γ¹a + γ²b)(γ⁰+γ³)` form an abelian
group `≅ ℝ²`: `Nmat_mul` (`N(a,b)·N(c,d) = N(a+c,b+d)`), `Nmat_zero`, `Nmat_inv`,
and the capstone monoid homomorphism `NmatHom : Multiplicative (ℝ×ℝ) →* Matrix`.
The core reduces to the light-cone nilpotency `(γ⁰+γ³)² = 0` (`se2_P_sq`) and
`X(a,b)·X(c,d) = 0` (`Xmat_mul_Xmat`), themselves the real casts of four decidable
integer identities `se2_coef_*`. The `SE(2)` rotation factor `e^{iγ⁰γ³γ⁵θ}`
(matrix exponential) is left as prose.

All changes committed and pushed.

# Summary of changes for run 39f215b9-16ca-4136-87ee-6ea0d95d9923
Completed the next self-contained formalization step from `book.tex`, honoring the active constraints (prioritized a chapter other than gravity; no Hankel transform; Majorana in scope).

**New file `BookProof/ChapterMajoranaProp76.lean`** (registered in `BookProof.lean`), formalizing the chapter "Real representations, CPT theorem and the relativistic position operator", §"Fourier-Majorana Transform", **Proposition 76**: the energy transform `𝓔 = Θ ∘ 𝓕_P(−p⁰) ∘ Θ⁻¹` (the Pauli–Fourier transform in the time coordinate, conjugated by the real-linear identification `Θ`) is unitary "for the same conjugation reason" as Proposition 73, and the composite `𝓔 ∘ 𝓕_M` is the unitary energy–momentum transform.

The structural core is discharged with Note 4's unitarity predicate `IsNote4Unitary` (surjective + diagonal-inner preserving `⟪f x, f x⟫ = ⟪x, x⟫`, matching the Proposition 5 treatment):
- `note4_comp` — composition of Note-4 unitaries is a Note-4 unitary;
- `LinearIsometryEquiv.isNote4Unitary` — any linear isometry equivalence is a Note-4 unitary;
- `note4_conj` — conjugating a Note-4 unitary by a linear isometry equivalence is again one (needs no linearity of the conjugated map);
- `energyTransform` / `energyTransform_unitary` — headline: `𝓔` is unitary;
- `energyMomentum_unitary` — the composite `𝓔 ∘ 𝓕_M` is unitary;
- `fourierTransform_isNote4Unitary` / `energyTransform_fourier_unitary` — concrete instantiation on Mathlib's `MeasureTheory.Lp.fourierTransformₗᵢ` (Plancherel), exhibiting the actual L²-Fourier transform as a Note-4 unitary and building the concrete energy transform.

The `𝓔 ∘ 𝓗_M` "spherical" branch (Majorana–Hankel transform) was deliberately omitted per the no-Hankel constraint; the file stays off the gravity line. All new headlines are `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`), verified with `#print axioms` and a `grep` for `sorry`. The `BookProof` target builds green; the only build failure in the repository is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

Updated `ARISTOTLE_SUMMARY.md` and `BookProof/STATUS.md` with a new Wave 93 entry. All changes committed and pushed.

# Summary of changes (latest run) — Wave 93: Proposition 76 (energy transform)
Completed the next self-contained formalization step from `book.tex`, honoring the active constraints (**prioritize a chapter other than gravity**, **no Hankel transform**; Majorana is fine).

**New file `BookProof/ChapterMajoranaProp76.lean`** (registered in `BookProof.lean`), formalizing the chapter "Real representations, CPT theorem and the relativistic position operator", §"Fourier-Majorana Transform", **Proposition 76**: the **energy transform** `𝓔 = Θ_{L²} ∘ 𝓕_P(−p⁰) ∘ Θ_{L²}⁻¹` — the Pauli–Fourier transform `𝓕_P` in the *time* coordinate, conjugated by the real-linear identification `Θ` — is **unitary** "for the same conjugation reason" as Proposition 73, and the composite `𝓔 ∘ 𝓕_M` is the unitary **energy–momentum transform**.

The structural core is discharged with Note 4's unitarity predicate `IsNote4Unitary` (surjective + diagonal-inner preserving `⟪f x, f x⟫ = ⟪x, x⟫`, exactly as used for Proposition 5). Declarations (all sorry-free, axiom-free — only `propext`, `Classical.choice`, `Quot.sound`):
- `note4_comp` — a composition of Note-4 unitaries is a Note-4 unitary;
- `LinearIsometryEquiv.isNote4Unitary` — any linear isometry equivalence `≃ₗᵢ` is a Note-4 unitary;
- `note4_conj` — conjugating a Note-4 unitary by a linear isometry equivalence `Θ` is again one (needs *no* linearity of the conjugated map);
- `energyTransform` / `energyTransform_unitary` — the headline: `𝓔 = Θ ∘ V ∘ Θ⁻¹` is unitary;
- `energyMomentum_unitary` — the composite `𝓔 ∘ 𝓕_M` is unitary;
- `fourierTransform_isNote4Unitary` / `energyTransform_fourier_unitary` — concrete instantiation on Mathlib's `MeasureTheory.Lp.fourierTransformₗᵢ` (Plancherel `≃ₗᵢ[ℂ]`), exhibiting the actual `L²`-Fourier transform as a Note-4 unitary and building the concrete energy transform.

The `𝓔 ∘ 𝓗_M` "spherical" branch (Majorana–Hankel transform) is deliberately omitted (off the Hankel line); the whole file stays off the gravity line. Verified all new headlines with `#print axioms` (only `propext`, `Classical.choice`, `Quot.sound`) and confirmed no `sorry`. The `BookProof` target builds green; the only build failure in the repository is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. Updated `ARISTOTLE_SUMMARY.md` and `BookProof/STATUS.md` (new Wave 93 entry). All changes committed and pushed.

---

# Summary of changes for run b8fd750d-4d71-4c61-b6a3-b991a27ef5e0
Completed the next self-contained formalization step from `book.tex`, honoring the active constraints (prioritized a chapter other than gravity; no Hankel transform; Majorana in scope but not required here).

**New file `BookProof/ChapterA1Prop5.lean`** (registered in `BookProof.lean`), formalizing the chapter "Real representations, CPT theorem and the relativistic position operator", §"Systems on real and complex Hilbert spaces", **Proposition 5** (`book.tex` line ~4797): for complex Hilbert spaces `H₁, H₂` and their realifications `H₁ʳ, H₂ʳ`, an operator `U : H₁ → H₂` is (anti-)unitary — surjective and inner-preserving `⟪U x, U x⟫ = ⟪x, x⟫` in the sense of Note 4 — iff its realification `Uʳ = U` is (anti-)unitary between the realifications. The realification is modeled as the same carrier equipped with the real inner product `⟪·,·⟫_ℝ = re ⟪·,·⟫_ℂ` (Mathlib's `InnerProductSpace.rclikeToReal`, used as a local instance), so `Uʳ` is literally `U` and surjectivity is shared verbatim.

Declarations (all sorry-free, axiom-free — only `propext`, `Classical.choice`, `Quot.sound`):
- `inner_self_complex_iff_real` — the heart of the proposition, holding for an arbitrary function `T` (no linearity needed), so it covers both the unitary and anti-unitary cases uniformly;
- `prop5` — the headline bare-function form of Proposition 5;
- `prop5_linear` / `prop5_antilinear` — the ℂ-linear (unitary) and conjugate-linear (anti-unitary) specializations, recording that Note 4's "(anti-)" is handled uniformly.

Verified `prop5` and `prop5_antilinear` with the axiom checker (only `propext`, `Classical.choice`, `Quot.sound`) and confirmed no `sorry`. The `BookProof` target builds green; the only build failure in the repository is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, which was left untouched. Updated `ARISTOTLE_SUMMARY.md` (new Wave 92 entry, as requested) and `BookProof/STATUS.md`. All changes committed and pushed.

# Wave 92 — new file `BookProof/ChapterA1Prop5.lean`
Completed the next self-contained formalization step from `book.tex`, honoring the active constraints (**prioritize a chapter other than gravity**, **no Hankel transform**; Majorana is fine).

**New file `BookProof/ChapterA1Prop5.lean`** (registered in `BookProof.lean`), formalizing the chapter "Real representations, CPT theorem and the relativistic position operator", §"Systems on real and complex Hilbert spaces", **Proposition 5** (`book.tex` line ~4797): for complex Hilbert spaces `H₁, H₂` and their realifications `H₁ʳ, H₂ʳ`, an operator `U : H₁ → H₂` is (anti-)unitary — surjective and inner-preserving in the sense of **Note 4** — iff its realification `Uʳ = U` is (anti-)unitary between the realifications. The realification is modeled as the same carrier equipped with `⟪·,·⟫_ℝ = re ⟪·,·⟫_ℂ` (Mathlib's `InnerProductSpace.rclikeToReal`, a **local** instance), so `Uʳ` is literally `U` and surjectivity is shared verbatim.

Declarations (all `sorry`-free, `axiom`-free — only `propext`, `Classical.choice`, `Quot.sound`):
- `inner_self_complex_iff_real` — the heart of the proposition: for any function `T`, `∀x, ⟪Tx,Tx⟫_ℂ = ⟪x,x⟫_ℂ` iff `∀x, ⟪Tx,Tx⟫_ℝ = ⟪x,x⟫_ℝ` (forward by `real_inner_eq_re_inner`; backward upgrading real-part equality using `inner_self_im = 0`); needs no (anti-)linearity, so it covers both cases uniformly;
- `prop5` (headline) — the bare-function form of Proposition 5;
- `prop5_linear` / `prop5_antilinear` — the unitary (ℂ-linear `→ₗ[ℂ]`) and anti-unitary (conjugate-linear `→ₗ⋆[ℂ]`) specializations, recording that Note 4's "(anti-)" is handled uniformly.

This stays off the gravity line and off the Hankel line. Verified `prop5` and `prop5_antilinear` with the axiom checker (only `propext`, `Classical.choice`, `Quot.sound`). The `BookProof` target builds green (`✔ Built BookProof`); the only build failure in the repository is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, which was left untouched. Updated `ARISTOTLE_SUMMARY.md` (this Wave 92 entry, as requested) and `BookProof/STATUS.md`. All changes committed and pushed.

# Summary of changes for run 7f34a6fc-c334-4c0a-9c1f-14ce0ca6031b
Completed the next self-contained formalization step from `book.tex`, honoring the active constraints (prioritized a chapter other than gravity; no Hankel transform; Majorana matrices in scope).

**New file `BookProof/ChapterMajoranaProp74.lean`** (registered in `BookProof.lean`), formalizing the chapter "Real representations, CPT theorem and the relativistic position operator", §"Fourier-Majorana Transform", **Proposition 74**: the two intertwining identities of the inverse Majorana–Fourier transform `𝓕_M⁻¹ = (𝓕_P^Θ)⁻¹ ∘ S⁻¹`. The book reduces both to 2×2-block matrix identities over the concrete 4×4 Dirac matrices (reused from `ChapterMajoranaFourier`), on the (+p⃗, −p⃗) momentum splitting.

Declarations (all `sorry`-free, `axiom`-free — only `propext`, `Classical.choice`, `Quot.sound`):
- block operators `Qmat`, `Sinv`, `Rmat`, `Dmat` — `Q = [[iγ⁰m, i p⃗·γ⃗],[−i p⃗·γ⃗, iγ⁰m]]`, `S⁻¹ = [[c, sA],[−sA, c]]`, `R = diag(iγ⁰E, iγ⁰E)`, `Dⱼ = diag(iγ⁰pⱼ, −iγ⁰pⱼ)`;
- Clifford helper lemmas `ns_mul_A`, `g_mul_A`, `A_mul_g`;
- `prop74_intertwine` (abstract) — `Q·S⁻¹ = S⁻¹·R`, the Dirac/energy intertwining, for any `g, ns` with `g²=1`, `ns²=−1`, `g·ns=−ns·g` and reals with `c²+s²=1`, `m=(c²−s²)E`, `q=2csE`;
- `prop74_Rj_comm` (abstract) — `Dⱼ·S⁻¹ = S⁻¹·Dⱼ`;
- `majoranaFourier_prop74` and `majoranaFourier_prop74_Rj` (headlines) — the concrete Dirac-model instances, using the boost half-angle coefficients.

This stays off the gravity line and off the Hankel-transform line (Definitions 65–71 untouched). Verified both headline theorems with the axiom checker. The `BookProof` target builds green; the only build failure in the repository is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, which was left untouched. Updated `ARISTOTLE_SUMMARY.md` (Wave 91 entry, as requested) and `BookProof/STATUS.md`. All changes committed and pushed.

# Wave 91 — new file `BookProof/ChapterMajoranaProp74.lean`
Completed the next self-contained formalization step from `book.tex`, honoring the active constraints (**prioritize a chapter other than gravity**, **no Hankel transform**; Majorana matrices in scope).

**New file `BookProof/ChapterMajoranaProp74.lean`** (registered in `BookProof.lean`), formalizing the chapter "Real representations, CPT theorem and the relativistic position operator", §"Fourier-Majorana Transform", **Proposition 74** (`book.tex` line ~6003): the two intertwining identities of the inverse Majorana–Fourier transform `𝓕_M⁻¹ = (𝓕_P^Θ)⁻¹ ∘ S⁻¹`. The book reduces both to `2×2`-block matrix identities over the concrete `4×4` Dirac matrices (from `ChapterMajoranaFourier`), on the `(+p⃗, −p⃗)` momentum splitting:

- `Qmat`, `Sinv`, `Rmat`, `Dmat` — the blocks `Q = [[iγ⁰m, i p⃗·γ⃗],[−i p⃗·γ⃗, iγ⁰m]]`, `S⁻¹ = [[c, sA],[−sA, c]]`, `R = diag(iγ⁰E, iγ⁰E)`, `Dⱼ = diag(iγ⁰pⱼ, −iγ⁰pⱼ)` (with `A = (n̂·γ⃗)γ⁰`, `c = √((E+m)/2E)`, `s = √((E−m)/2E)`);
- `ns_mul_A`/`g_mul_A`/`A_mul_g` — the Clifford consequences `ns·A = −g`, `g·A = −ns`, `A·g = ns`;
- `prop74_intertwine` (abstract) — `Q·S⁻¹ = S⁻¹·R` for any `g, ns` with `g²=1`, `ns²=−1`, `g·ns=−ns·g` and reals with `c²+s²=1`, `m=(c²−s²)E`, `q=2csE` (the Dirac/energy intertwining);
- `prop74_Rj_comm` (abstract) — `Dⱼ·S⁻¹ = S⁻¹·Dⱼ` (the momentum-component block commutes with the boost mixing);
- `majoranaFourier_prop74` (headline) — the concrete Dirac-model instance of the first identity, using `Ep`/`boostC`/`boostS` and the boost half-angle identities `boost_sq_add`/`boost_sq_sub`/`boost_two_mul`;
- `majoranaFourier_prop74_Rj` (headline) — the concrete Dirac-model instance of the second identity.

All declarations are `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `lean_verify` on both headline theorems). The `BookProof` target builds green; the only build failure in the repository is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. Off the gravity line and off the Hankel-transform line (Definitions 65–71 untouched). Also updated `BookProof/STATUS.md`. All changes committed and pushed.

# Summary of changes for run 528b2477-f0be-422f-a2e3-642b33d3a7fa
Completed the next self-contained formalization step from `book.tex`, honoring the active constraints (prioritized a chapter other than gravity; no Hankel transform; Majorana matrices in scope).

**New file `BookProof/ChapterMajoranaProp61.lean`** (registered in `BookProof.lean`), formalizing the chapter "Real representations, CPT theorem and the relativistic position operator", §"Fourier-Majorana Transform", **Proposition 61**: the boost intertwiner `U' = (E + U H γ⁰ U†)/(√(E+m)√(2E))` is unitary, given a unitary `U` with `U H² = E² U` (Majorana/Dirac Hamiltonian `iH = γ⁰(∂⃗·γ⃗) + iγ⁰m`).

The physical operator identity is captured as pure ℝ-star-algebra content in a general star algebra, with the Majorana setup encoded as named hypotheses (Clifford anticommutator `H*g + g*H = (2m)•1`, intertwining `E² = U H² U†`, and the energy/normaliser commuting with `A = U H γ⁰ U†`). Declarations:
- `gsq_Hsq_comm` — `g*(H*H) = (H*H)*g` follows purely from the anticommutator;
- `Aop`, `Uprime` — the operators `A = U H γ⁰ U†` and `U' = N⁻¹(E+A)`;
- `prop61_star_mul_self` — `(U')† U' = 1`;
- `prop61_mul_star_self` — `U' (U')† = 1`;
- `prop61_isUnit` (headline) — `U'` is a unit with two-sided inverse `(U')†`.

All four results are `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`). The `BookProof` target (which imports the new file) builds green; the only build failure in the repository is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. This stays off the gravity line and off the Hankel-transform line (the Hankel-Majorana material of Definitions 65–66 is not touched).

Also updated `ARISTOTLE_SUMMARY.md` and `BookProof/STATUS.md` with a Wave 90 entry. All changes are committed and pushed.

# Wave 90 — new file `BookProof/ChapterMajoranaProp61.lean`
Did the next self-contained formalization step from `book.tex`, honoring the
active constraints (**prioritize a chapter other than gravity**, **no Hankel
transform**; Majorana matrices in scope).

**New file `BookProof/ChapterMajoranaProp61.lean`** (registered in
`BookProof.lean`), formalizing the chapter "Real representations, CPT theorem and
the relativistic position operator", §"Fourier-Majorana Transform",
**Proposition 61** (`book.tex` line ~5712): the boost intertwiner

  `U' = (E + U H γ⁰ U†) / (√(E+m) √(2E))`

is **unitary**, given a unitary `U` with `U H² = E² U`, where `iH = γ⁰(∂⃗·γ⃗) + iγ⁰m`
is the Majorana/Dirac Hamiltonian.

The physical operator identity is formalized as pure `ℝ`-star-algebra content in a
general `[Ring 𝒜] [StarRing 𝒜] [Algebra ℝ 𝒜] [StarModule ℝ 𝒜]`, capturing the
Majorana setup by named hypotheses (`U` unitary; `g = γ⁰` self-adjoint involution;
`H` self-adjoint with the Clifford anticommutator `H*g + g*H = (2m)•1`; `E`
self-adjoint with `E² = U H² U†`; `A := U H g U†` commuting with `E`; and a
self-adjoint invertible normaliser `N = √(2E(E+m))` with `N² = 2•E² + (2m)•E`
commuting with `E` and `A`). Declarations:
- `gsq_Hsq_comm` — `g*(H*H) = (H*H)*g` follows purely from the anticommutator;
- `Aop`, `Uprime` — the operators `A = U H γ⁰ U†` and `U' = N⁻¹(E+A)`;
- `prop61_star_mul_self` — `(U')† U' = 1`;
- `prop61_mul_star_self` — `U' (U')† = 1`;
- `prop61_isUnit` (headline) — `U'` is a unit with two-sided inverse `(U')†`
  (the algebraic form of "`U'` is unitary").

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed with `#print axioms` on all four results). Building the
`BookProof` target (which imports the new file) is green; the only build failure
in the repository is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`,
left untouched. This stays off the gravity line and off the Hankel-transform line
(the surrounding integral operators `𝓕_M` and the Hankel-Majorana material of
Definitions 65–66 are not touched). All changes are committed and pushed.

# Summary of changes for run 448b6255-9130-4ef8-b1c7-b0f308692ed6
Did the next self-contained formalization step from `book.tex`, honoring the active constraints (prioritized a chapter other than gravity; no Hankel transform; Majorana matrices in scope).

**New file `BookProof/ChapterLorentzRealRepDirect.lean`** (registered in `BookProof.lean`), continuing the recent waves on the chapter "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups", Lemma 52. The earlier files (`ChapterLorentzRealRep`, `ChapterLorentzRealRepSum`, `ChapterLorentzRealRepFull`) had built the four mutually Frobenius-orthogonal real representation spaces `WHalf` (4), `W10` (6), `WPs` (4), `WTwo` (2) inside the 16-dimensional real matrix algebra `Matrix (Fin 4) (Fin 4) ℝ`, but only certified their "internal direct sum" through a dimension count (`16 = 4 + 6 + 4 + 2`).

This wave upgrades that dimension count to the genuine structural theorem and adds the representation-theoretic corollary:
- `WFam = ![WHalf, W10, WPs, WTwo]`;
- `iSup_WFam_eq_top` — the fourfold supremum is all of the matrix algebra;
- `sum_finrank_WFam` — the summand dimensions add up to the ambient dimension;
- `WFam_isInternal : DirectSum.IsInternal WFam` (headline) — the canonical map `⨁ᵢ WFam i → Matrix (Fin 4) (Fin 4) ℝ` is an isomorphism (finite-dimensional bijectivity argument);
- `WFam_iSupIndep` — the four spaces are supremum-independent;
- `WFam_conj_invariant` — conjugation by every element of the discrete Pin subgroup Ω preserves each summand, so the 16-dimensional conjugation representation of Ω decomposes as the internal direct sum of the four subrepresentations.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed with the axiom checker on `WFam_isInternal` and `WFam_conj_invariant`). Building the `BookProof` target (which imports the new file) is green; the only build failure in the repository is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

Also updated `ARISTOTLE_SUMMARY.md` and `BookProof/STATUS.md` with a Wave 89 entry. All changes are committed and pushed.

# Wave 89 — new file `BookProof/ChapterLorentzRealRepDirect.lean`
Continued the `book.tex` formalization with the next self-contained step, honoring the active constraints (**prioritize a chapter other than gravity**, **no Hankel transform**; Majorana matrices in scope).

**New file `BookProof/ChapterLorentzRealRepDirect.lean`** (registered in `BookProof.lean`), building on Waves 86–88 (`ChapterLorentzRealRep`, `ChapterLorentzRealRepSum`, `ChapterLorentzRealRepFull`; Lemma 52 of the chapter "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups"). Those built the four mutually Frobenius-orthogonal real representation spaces `WHalf` (dim 4), `W10` (dim 6), `WPs` (dim 4), `WTwo` (dim 2) inside the 16-dimensional real matrix algebra `Matrix (Fin 4) (Fin 4) ℝ`, and certified the *internal direct sum* only through a dimension count (`16 = 4 + 6 + 4 + 2`, `finrank_full_eq_add`).

This wave upgrades that dimension count to the genuine structural statement, and records the representation-theoretic corollary:

- the family `WFam = ![WHalf, W10, WPs, WTwo]`;
- **spanning** `iSup_WFam_eq_top` (`⨆ i, WFam i = ⊤`, from `decomposition_top`);
- **dimension count** `sum_finrank_WFam` (`∑ i, finrank (WFam i) = finrank (Matrix (Fin 4) (Fin 4) ℝ)`);
- **headline** `WFam_isInternal : DirectSum.IsInternal WFam` — the canonical map `⨁ᵢ WFam i → Matrix (Fin 4) (Fin 4) ℝ` is an isomorphism (finite-dimensional bijectivity argument: surjective because its range is `⨆ i, WFam i = ⊤`, and its domain has dimension `∑ finrank (WFam i) = 16 = finrank` of the codomain, so a surjection between equidimensional finite spaces is bijective);
- **independence** `WFam_iSupIndep : iSupIndep WFam`;
- **conjugation representation** `WFam_conj_invariant` — for every `S ∈ Ω` and index `i`, conjugation by `S` maps `WFam i` into itself, so the 16-dimensional conjugation representation of the discrete Pin subgroup `Ω` decomposes as the internal direct sum of the four subrepresentations.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via the axiom checker on `WFam_isInternal` and `WFam_conj_invariant`). `lake build BookProof` is green (the only pre-existing build failure in the repository is the out-of-scope `RiemannProof/RandomMap.lean`, left untouched). Updated `BookProof/STATUS.md` and this file. All changes are committed and pushed.

# Summary of changes for run 903e5d12-fa81-4512-80f5-07cd6955396f
Continued the `book.tex` formalization with the next self-contained step, honoring the active constraints (prioritized a chapter other than gravity; no Hankel transform; Majorana matrices in scope).

**New file `BookProof/ChapterLorentzRealRepFull.lean`** (registered in `BookProof.lean`), building on the prior waves `ChapterLorentzRealRep` / `ChapterLorentzRealRepSum` (Lemma 52 of the chapter "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups"). Those established the three real representation spaces `WHalf` (dim 4), `W10` (dim 6), `WPs` (dim 4) and their mutually-orthogonal 14-dimensional internal direct sum.

This wave exhibits the remaining two-dimensional summand `WTwo = span{iγ⁰, γ⁰γ⁵}` (the "discrete" Majorana directions generating the covering group Ω) and thereby the complete orthogonal decomposition of the full 16-dimensional real matrix algebra `Matrix (Fin 4) (Fin 4) ℝ`:
- conjugation invariance `conj_inv_two` and the submodule form `WTwo_invariant`;
- Frobenius Gram `gram_two`/`gram_twoR` (= 4·I) and cross-orthogonality of `WTwo` with `WHalf`, `W10`, `WPs`; `finrank_WTwo = 2`;
- the concatenated 16-element basis `bFull`/`bFullR` with Gram 4·I, hence `bFullR_linearIndependent`, and `span_bFullR_eq` (span = `WHalf ⊔ W10 ⊔ WPs ⊔ WTwo`);
- the headline results `decomposition_top` (`WHalf ⊔ W10 ⊔ WPs ⊔ WTwo = ⊤`) and `finrank_full_eq_add` (`16 = 4 + 6 + 4 + 2`), certifying the complete internal direct sum.

Everything is sorry-free and axiom-free (only propext, Classical.choice, Quot.sound, confirmed via the axiom checker on `decomposition_top` and `finrank_full_eq_add`). `lake build BookProof.ChapterLorentzRealRepFull` is green with no warnings in the new file. The only pre-existing build failure in the repository is the out-of-scope `RiemannProof/RandomMap.lean`, left untouched.

Updated `BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md` with a Wave 88 entry. All changes are committed and pushed.

# Wave 88 — new file `BookProof/ChapterLorentzRealRepFull.lean`
Continued the `book.tex` formalization with the next self-contained step, honoring the active constraints (**prioritize a chapter other than gravity**, **no Hankel transform**; Majorana matrices in scope).

**New file `BookProof/ChapterLorentzRealRepFull.lean`** (registered in `BookProof.lean`) builds directly on Waves 86–87 (`ChapterLorentzRealRep`, `ChapterLorentzRealRepSum`). Those waves established the three real representation spaces `WHalf` (dim 4), `W10` (dim 6), `WPs` (dim 4) of **Lemma 52** of the chapter "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups", and showed they are mutually Frobenius-orthogonal (a 14-dimensional internal direct sum). This wave exhibits the **remaining two-dimensional summand** `WTwo = span{iγ⁰, γ⁰γ⁵}` (the two "discrete" Majorana directions generating the covering group `Ω`) and thereby the **complete orthogonal decomposition of the full 16-dimensional matrix algebra** `Matrix (Fin 4) (Fin 4) ℝ`.

Content (all sorry-free, axiom-free — only propext/Classical.choice/Quot.sound):
- `w2`/`SW2`, conjugation invariance `conj_inv_two` (over ℤ by `decide`) and the `Submodule` form `WTwo_invariant` (conjugation by every `S ∈ Ω` maps `WTwo` into itself).
- Frobenius Gram `gram_two`/`gram_twoR` (= 4·I) and cross-orthogonality `gram_two_halfR`/`gram_two_10R`/`gram_two_PsR` (WTwo ⟂ WHalf, W10, WPs); `w2R_linearIndependent`, `finrank_WTwo = 2`.
- Concatenated 16-element basis `bFull`/`bFullR` with Frobenius Gram `4·I` (`gram_fullR`), hence `bFullR_linearIndependent`; span identification `range_bFullR`/`span_bFullR_eq` (`span (range bFullR) = WHalf ⊔ W10 ⊔ WPs ⊔ WTwo`).
- `finrank_matrix` (`dim (M₄(ℝ)) = 16`), `finrank_full = 16`, the complete-decomposition headline `decomposition_top` (`WHalf ⊔ W10 ⊔ WPs ⊔ WTwo = ⊤`), and `finrank_full_eq_add` (`16 = dim WHalf + dim W10 + dim WPs + dim WTwo = 4 + 6 + 4 + 2`), certifying the complete internal direct sum.

`lake build BookProof.ChapterLorentzRealRepFull` is green with no warnings in the new file; axioms confirmed via `lean_verify` (`decomposition_top`, `finrank_full_eq_add`). The only pre-existing build failure in the repository is the out-of-scope `RiemannProof/RandomMap.lean`, left untouched. Updated `BookProof/STATUS.md` and this file with a Wave 88 entry. All changes committed and pushed.

# Summary of changes for run 3863b3bb-a7f5-4345-94cd-38291a9ee48b
Continued the `book.tex` formalization with the next self-contained step, honoring the active constraints (prioritized a chapter other than gravity; no Hankel transform; Majorana matrices in scope).

**New file `BookProof/ChapterLorentzRealRepSum.lean`** (registered in `BookProof.lean`) builds directly on Wave 86 (`ChapterLorentzRealRep`, the three explicit real representation spaces `WHalf`/`W10`/`WPs` of **Lemma 52** of the chapter "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups"). It discharges the *distinctness* half of the classification: the three real representation spaces are mutually orthogonal in the Frobenius inner product ⟨A,B⟩ = tr(AᵀB), hence their sum inside the 16-dimensional space of real 4×4 matrices is an internal direct sum of dimension 4 + 6 + 4 = 14.

Content (all sorry-free, axiom-free — only propext/Classical.choice/Quot.sound):
- Mutual orthogonality: `gram_half10`/`gram_halfPs`/`gram_10Ps` (over ℤ) with real casts `gram_half10R`/`gram_halfPsR`/`gram_10PsR` — every cross Frobenius pairing between two different bases vanishes.
- Concatenated 14-element basis `bAll`/`bAllR` whose Frobenius Gram matrix is 4·I (`gram_all`/`gram_allR`), giving `bAllR_linearIndependent`.
- Span identification `range_bAllR` and `span_bAllR_eq` (span of the concatenated basis equals `WHalf ⊔ W10 ⊔ WPs`).
- Dimensions `finrank_WHalf = 4`, `finrank_W10 = 6`, `finrank_WPs = 4`, `finrank_sup = 14`, and the headline `finrank_sup_eq_add`: dim(WHalf ⊔ W10 ⊔ WPs) = dim WHalf + dim W10 + dim WPs, certifying the internal direct sum.

`lake build BookProof` is green (8139 jobs) with no warnings in the new file; axioms confirmed via `lean_verify`. The only remaining build failure in the repository is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, which was left untouched. Updated `BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md` with a Wave 87 entry. All changes are committed and pushed.

# Wave 87 — new file `BookProof/ChapterLorentzRealRepSum.lean`
Continued the `book.tex` formalization with the next self-contained step, honoring the active constraints (**prioritize a chapter other than gravity**, **no Hankel transform**; Majorana matrices in scope).

Building directly on Wave 86 (`ChapterLorentzRealRep`, the three explicit real representation spaces `WHalf`/`W10`/`WPs` of **Lemma 52** of the chapter *"Real representations, CPT theorem and the relativistic position operator"*, §*"On the Lorentz, SL(2,C) and Pin(3,1) groups"*), this wave discharges the *distinctness* half of the classification: the three real representation spaces are **mutually orthogonal** in the Frobenius inner product `⟨A,B⟩ = tr(Aᵀ B)`, and hence their sum inside the 16-dimensional space of real `4×4` matrices is an **internal direct sum** of dimension `4 + 6 + 4 = 14`. New file `BookProof/ChapterLorentzRealRepSum.lean` (registered in `BookProof.lean`).

- **Mutual orthogonality** `gram_half10`/`gram_halfPs`/`gram_10Ps` (over `ℤ`, by `decide`) and their real casts `gram_half10R`/`gram_halfPsR`/`gram_10PsR` — every cross Frobenius pairing between two different bases vanishes.
- **Concatenated basis** `bAll : Fin 14 → …` (the 4+6+4 concatenation of `bHalf`/`b10`/`bPs`) and its real cast `bAllR`, with `gram_all`/`gram_allR` proving the full Frobenius Gram matrix is `4·I`; hence `bAllR_linearIndependent` — the 14 matrices are linearly independent over `ℝ`.
- **Span identification** `range_bAllR` (the range of `bAllR` is the union of the three ranges) and `span_bAllR_eq` (its span is exactly `WHalf ⊔ W10 ⊔ WPs`).
- **Dimensions** `finrank_WHalf = 4`, `finrank_W10 = 6`, `finrank_WPs = 4`, `finrank_sup = 14`, with the headline `finrank_sup_eq_add` : `dim (WHalf ⊔ W10 ⊔ WPs) = dim WHalf + dim W10 + dim WPs`, certifying the internal direct sum.

All `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `lean_verify`). `lake build BookProof` green (8139 jobs); the only remaining build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. Updated `BookProof/STATUS.md`. All changes committed and pushed.

# Summary of changes for run cf8fa29c-dcdc-4663-bcea-89b6e502c074
Continued the `book.tex` formalization with the next self-contained step, honoring the active constraints (prioritize a chapter other than gravity; no Hankel transform; Majorana matrices in scope).

**New file `BookProof/ChapterLorentzRealRep.lean`** (registered in `BookProof.lean`) discharges the concrete core of **Lemma 52** of the chapter *"Real representations, CPT theorem and the relativistic position operator"*, §*"Finite-dimensional representations of SL(2,C)"*. It formalizes the three explicit real irreducible representation spaces of the spin group (acting by conjugation `A ↦ S A S†`), verified over the discrete Pin group `Ω ≅ Q₈` established in the previous waves:
- the `(1/2,1/2)` vector rep `WHalf` = real span of `{1, γ⁰γ¹, γ⁰γ², γ⁰γ³}` (dimension 4);
- the `(1,0)` rep `W10` = real span of `{iγ¹, iγ², iγ³, γ¹γ⁵, γ²γ⁵, γ³γ⁵}` (dimension 6);
- the pseudo-`(1/2,1/2)` rep `WPs` = real span of `{iγ⁵, iγ⁵γᵏγ⁰}` (dimension 4).

For each space it proves: conjugation invariance (`conj_inv_half`/`conj_inv_10`/`conj_inv_ps` — for every `S ∈ Ω`, `S A S⁻¹` is ± a basis matrix, a signed permutation, decided over ℤ); dimension via linear independence over ℝ (general lemma `linIndep_of_gram`: a family with Frobenius Gram matrix `4·I` is linearly independent, applied through the cast Gram lemmas — headlines `bHalfR_linearIndependent`, `b10R_linearIndependent`, `bPsR_linearIndependent`); and `Submodule` invariance (`WHalf_invariant`/`W10_invariant`/`WPs_invariant`, with elementwise corollary `WHalf_invariant_apply`). All entrywise facts are closed over ℤ by `decide` and transported to ℝ.

The new file is `sorry`-free and uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), confirmed via `lean_verify`. `lake build BookProof` is green; the only remaining build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. Updated `BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md` with a Wave 86 entry. All changes are committed and pushed.

# Wave 86 — new file `BookProof/ChapterLorentzRealRep.lean`
Continued the ongoing `book.tex` formalization, honoring the two active constraints (**prioritize a chapter other than gravity**, **no Hankel transform**; Majorana matrices in scope).

Building directly on Waves 84–85 (`ChapterPinOmega` = the discrete Pin subgroup `Ω ≅ Q₈`; `ChapterPinDoubleCover` = the 2-to-1 cover `Λ : Ω → Δ`), this wave discharges the concrete self-contained core of **Lemma 52** of the chapter *"Real representations, CPT theorem and the relativistic position operator"*, §*"Finite-dimensional representations of SL(2,C)"* (`book.tex` line ~5560): the three explicit real irreducible representation spaces on which `Spin⁺(1,3)` acts by conjugation `M(S)(A) = S A S†`, checked over the discrete Pin group `Ω`.

New file `BookProof/ChapterLorentzRealRep.lean` (registered in `BookProof.lean`), all `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `lean_verify`); `lake build BookProof` green. The three example spaces are:
- the **`(1/2,1/2)` vector representation** `WHalf` = real span of `{1, γ⁰γ¹, γ⁰γ², γ⁰γ³}` (dimension `4`);
- the **`(1,0)` representation** `W10` = real span of `{iγ¹, iγ², iγ³, γ¹γ⁵, γ²γ⁵, γ³γ⁵}` (dimension `6`);
- the **pseudo-`(1/2,1/2)` representation** `WPs` = real span of `{iγ⁵, iγ⁵γ¹γ⁰, iγ⁵γ²γ⁰, iγ⁵γ³γ⁰}` (dimension `4`).

For each space we proved:
- **conjugation invariance** (`conj_inv_half`/`conj_inv_10`/`conj_inv_ps`) — for every `S ∈ Ω`, conjugation `S · A · S⁻¹` maps each basis matrix to `±` a basis matrix (a signed permutation), decidable over `ℤ`; plus `cinv`/`cinv_correct` for the in-`Ω` inverse;
- **dimension** — the bases are linearly independent over `ℝ`, via the general lemma `linIndep_of_gram` (a family whose Frobenius Gram matrix is `4·I` is linearly independent) applied to the cast Gram lemmas `gram_halfR`/`gram_10R`/`gram_psR` (`gram_half`/`gram_10`/`gram_ps` are the `by decide` integer originals); headlines `bHalfR_linearIndependent`, `b10R_linearIndependent`, `bPsR_linearIndependent`;
- **`Submodule` invariance** — `WHalf_invariant`/`W10_invariant`/`WPs_invariant`: the conjugation map `conjL (castR S) (castR S⁻¹)` carries each `ℝ`-span into itself for every `S ∈ Ω`, with elementwise corollary `WHalf_invariant_apply`.

All entrywise facts are closed over `ℤ` by `decide` and transported to `ℝ` through `castR = (Int.castRingHom ℝ).mapMatrix` (`castR_mul`/`castR_transpose`/`castR_trace`). Reuses only `ChapterA3` (Majorana model) and `ChapterPinOmega` (the group `Ω`). Off the gravity line and off the Hankel line, as requested. The only build failure remains the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, left untouched. Updated `BookProof/STATUS.md` and this file with the Wave 86 entry; changes committed and pushed.

# Summary of changes for run 8bc45469-6e2c-4e3a-a192-148863462ba8
Continued the ongoing `book.tex` formalization, honoring the two active constraints (**prioritize a non-gravity chapter**, **no Hankel transform**; Majorana matrices in scope).

**Wave 85 — new file `BookProof/ChapterPinDoubleCover.lean`** (registered in `BookProof.lean`). Building on the previous wave (`ChapterPinOmega`, which proved the discrete Pin(3,1) subgroup `Ω = {±1, ±iγ⁰, ±γ⁰γ⁵, ±iγ⁵} ≅ Q₈`), this discharges the remaining finite core of **Definition 49** of the chapter *"Real representations, CPT theorem and the relativistic position operator"*, §*"On the Lorentz, SL(2,C) and Pin(3,1) groups"*: the two-to-one **covering map** `Λ : Ω → Δ` onto the Klein-four discrete Lorentz subgroup `Δ = {1, η, -η, -1}` (`η = diag(1,-1,-1,-1)`). `Λ` is defined via the conjugation action on the Majorana basis (`S⁻¹(iγ^μ)S = Λ(S)^μ_ν iγ^ν`), which is decidable over the integer Majorana model of `ChapterA3`.

Contents (all proved):
- `LamZ` — the explicit induced Lorentz matrix (`±1 ↦ 1`, `±iγ⁰ ↦ η`, `±γ⁰γ⁵ ↦ -η`, `±iγ⁵ ↦ -1`), with `etaZ_eq_mink` tying `η` to the chapter's Minkowski metric;
- `LamZ_spec` — the defining conjugation relation validating the formula;
- `LamZ_mem_Delta`, `LamZ_surjective` (`Δ = Ω.image LamZ`), `LamZ_hom` (homomorphism), `LamZ_neg` and `LamZ_fiber_card` (every fibre has exactly 2 elements) — i.e. `Λ : Ω → Δ` is a surjective 2-to-1 homomorphism, the double cover of Def 49;
- `LamZ_spec_C` — the relation transported to the complex Majorana matrices.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`). The `BookProof` library builds successfully with the new file; the only build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, which was left untouched. Updated `BookProof/STATUS.md` and `ARISTOTLE_SUMMARY.md` with the Wave 85 entry. All changes committed and pushed.

# Wave 85 — new file `BookProof/ChapterPinDoubleCover.lean`
Continued the standing formalization directive (mine the next self-contained mathematical claim from `book.tex`), honoring the two current constraints: **prioritize a chapter other than gravity** and **no Hankel transform** (Majorana matrices are in scope).

Building directly on Wave 84 (`ChapterPinOmega`, which showed the discrete `Pin(3,1)` subgroup `Ω = {±1, ±iγ⁰, ±γ⁰γ⁵, ±iγ⁵} ≅ Q₈`), Wave 85 discharges the remaining finite core of the chapter *"Real representations, CPT theorem and the relativistic position operator"*, §*"On the Lorentz, SL(2,C) and Pin(3,1) groups"*, **Definition 49**: the two-to-one **covering map** `Λ : Ω → Δ` onto the Klein-four discrete Lorentz subgroup `Δ = {1, η, -η, -1}` (`η = diag(1,-1,-1,-1)`). `Λ` is defined by the conjugation action on the Majorana basis (`S⁻¹(iγ^μ)S = Λ(S)^μ_ν iγ^ν`), which — rewritten without inverses — is decidable over the integer Majorana model `mgammaZ` of `ChapterA3` (no gravity, no spherical-Bessel/Hankel numerics). New file `BookProof/ChapterPinDoubleCover.lean` (registered in `BookProof.lean`).

- `qi`/`qj`/`qk`, `etaZ` (with `etaZ_eq_mink` connecting `η` to `minkowskiZ`), the 8-element `Omega` and 4-element `Delta`;
- `LamZ` — the explicit induced Lorentz matrix (`±1 ↦ 1`, `±iγ⁰ ↦ η`, `±γ⁰γ⁵ ↦ -η`, `±iγ⁵ ↦ -1`);
- `LamZ_spec` — the defining conjugation relation validating the formula for `LamZ`;
- `LamZ_mem_Delta`, `LamZ_surjective` (`Δ = Ω.image LamZ`), `LamZ_hom` (homomorphism), `LamZ_neg` and `LamZ_fiber_card` (every fibre has exactly 2 elements) — i.e. `Λ : Ω → Δ` is a surjective 2-to-1 homomorphism, the double cover of Definition 49;
- `LamZ_spec_C` — the conjugation relation transported to the complex Majorana matrices `mgamma`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`). `lake build BookProof` is green with the new file; the only build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, which was left untouched. `BookProof/STATUS.md` gained a Wave 85 entry.

# Summary of changes for run 34ae8709-069e-4127-af16-bdee3b9ac0e3
Continued the standing formalization directive (mine the next self-contained mathematical claim from `book.tex`), honoring the two current constraints: **prioritize a chapter other than gravity** and **no Hankel transform** (Majorana matrices now in scope).

**Wave 84 — new file `BookProof/ChapterPinOmega.lean`** (registered in `BookProof.lean`). From the chapter "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups", **Definition 49**, it formalizes the algebraic core of the claim that the discrete `Pin(3,1)` subgroup `Ω = {±1, ±iγ⁰, ±γ⁰γ⁵, ±iγ⁵}` is a group of order 8 — namely that **Ω is the quaternion group Q₈**. It reuses only the concrete 4×4 real Majorana/Dirac matrix model of `BookProof/ChapterA3.lean` (no gravity, no spherical-Bessel/Hankel numerics):

- `qi = iγ⁰`, `qj = γ⁰γ⁵ = -(iγ⁰)(iγ⁵)`, `qk = iγ⁵`, the three imaginary units;
- the quaternion relations `qi² = qj² = qk² = -1`, `qi·qj = qk`, `qj·qk = qi`, `qk·qi = qj` (with the anti-commuted forms) and Hamilton's identity `qi·qj·qk = -1`; plus `noncomm` (Ω is nonabelian);
- the 8-element `Finset` `Omega` with `Omega_card = 8`, `one_mem_Omega`, `neg_one_mem_Omega`, `Omega_mul_closed` (closure) and `Omega_inv` (inverses) — i.e. Ω is a group of order 8 (≅ Q₈);
- the complex model `qiC`/`qjC`/`qkC`, the identification `qjC_eq_dirac` of `qj` with `γ⁰γ⁵` in the book's `γ^μ = -i(iγ^μ)` normalization, and all relations transported to ℂ.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via the axiom check). `lake build BookProof` is green with the new file; the only build failure is the pre-existing, out-of-scope `RiemannProof/RandomMap.lean`, which was left untouched.

Updated `BookProof/STATUS.md` (new Wave 84 entry) and `ARISTOTLE_SUMMARY.md` (prepended a Wave 84 summary). All changes are committed and pushed.

# Summary of latest run — Wave 84 (`BookProof/ChapterPinOmega.lean`)
Continued the standing formalization directive (mine the next self-contained
mathematical claim from `book.tex`), honoring the two current constraints:
**prioritize a chapter other than gravity** and **no Hankel transform**
(Majorana matrices are now explicitly in scope).

**Wave 84 — new file `BookProof/ChapterPinOmega.lean`** (registered in
`BookProof.lean`). From the chapter *"Real representations, CPT theorem and the
relativistic position operator"*, §*"On the Lorentz, SL(2,C) and Pin(3,1)
groups"*, **Definition 49** (`book.tex` line ~5510), it formalizes the algebraic
core of the claim that the discrete `Pin(3,1)` subgroup
`Ω = {±1, ±iγ⁰, ±γ⁰γ⁵, ±iγ⁵}` is a group of order 8 — namely that **`Ω` is the
quaternion group `Q₈`**.  It reuses only the concrete `4×4` real Majorana/Dirac
matrix model of `BookProof.ChapterA3` (no gravity, no spherical-Bessel/Hankel
numerics):

- `qi = iγ⁰`, `qj = γ⁰γ⁵ = -(iγ⁰)(iγ⁵)`, `qk = iγ⁵`, the three imaginary units;
- the quaternion relations `qi²=qj²=qk²=-1`, `qi·qj=qk`, `qj·qk=qi`, `qk·qi=qj`
  (with the anti-commuted forms) and Hamilton's `qi·qj·qk=-1`; `noncomm`;
- the 8-element `Finset` `Omega` with `Omega_card = 8`, `one_mem_Omega`,
  `neg_one_mem_Omega`, `Omega_mul_closed` (closure) and `Omega_inv` (inverses),
  i.e. `Ω` is a group of order 8 (≅ `Q₈`);
- the complex model `qiC`/`qjC`/`qkC`, the identification `qjC_eq_dirac` of `qj`
  with `γ⁰γ⁵` in the book's `γ^μ = -i(iγ^μ)` normalization, and all relations
  transported to `ℂ`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`, confirmed via `lean_verify`).  `lake build BookProof` is green with
the new file.  Updated `BookProof/STATUS.md` (new Wave 84 entry) and this file.
The pre-existing, out-of-scope `RiemannProof/RandomMap.lean` build failures were
left untouched.  All changes are committed and pushed.

# Summary of changes for run 69dda846-8743-477a-a4a4-ab667661865d
Continued the standing formalization directive — mining the next self-contained mathematical claim from `book.tex` — honoring both constraints: prioritize a chapter other than gravity, and stay off the Hankel–Majorana line.

**Wave 83 — new file `BookProof/ChapterPauliSU2.lean`** (registered in `BookProof.lean`). From the chapter "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups", Note 47 / Def 49, it formalizes the `SU(2) → SO(3)` restriction of the spinor map `Υ : SL(2,ℂ) → SO⁺(1,3)`, `Υᵘ_ν(T) σ^ν = T† σᵘ T`, building on the previous wave's `ChapterPauliLorentz` using only concrete 2×2 Pauli matrices (no gamma/Majorana matrices, no gravity, no spherical-Bessel numerics):

- `spinorAction T X = Tᴴ * X * T` — the spinor conjugation;
- `spinorAction_comp` — it is a right action (conjugating by `T₁*T₂` = conjugate by `T₁` then `T₂`);
- `spinorAction_neg` — two-to-one: `T` and `-T` induce the same conjugation (the `±1` kernel of the double cover);
- `spinorAction_isHermitian` — the conjugation preserves hermiticity;
- `spinorAction_trace_of_unitary` — for unitary `T` (`T†T = 1`) it preserves the trace;
- `su2_preserves_time` — hence a unitary `T` fixes the time component `x⁰` (`x⁰ = ½ tr X`);
- `su2_preserves_spatialNormSq` — headline: for `T ∈ SU(2)` (`T†T = 1`, `det T = 1`) the conjugation preserves the Euclidean spatial length `(x¹)² + (x²)² + (x³)²`, i.e. the induced map is a rotation in `SO(3)`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed by axiom check). `lake build BookProof` is green with the new file. Updated `BookProof/STATUS.md` (new Wave 83 entry) and prepended a Wave 83 summary to `ARISTOTLE_SUMMARY.md`. The pre-existing, out-of-scope `RiemannProof/RandomMap.lean` build failures were left untouched. All changes are committed and pushed.

# Summary of latest run — Wave 83 (`BookProof/ChapterPauliSU2.lean`)
Continued the standing formalization directive (mine the next self-contained mathematical claim from `book.tex`), honoring the two constraints: **prioritize a chapter other than gravity** and **stay off the Hankel–Majorana line**.

**Wave 83 — new file `BookProof/ChapterPauliSU2.lean`** (registered in `BookProof.lean`). From the chapter *"Real representations, CPT theorem and the relativistic position operator"*, §*"On the Lorentz, SL(2,C) and Pin(3,1) groups"*, **Note 47 / Def 49**, it formalizes the `SU(2) → SO(3)` restriction of the spinor map `Υ : SL(2,ℂ) → SO⁺(1,3)`, `Υᵘ_ν(T) σ^ν = T† σᵘ T`, building directly on Wave 82's `ChapterPauliLorentz` (concrete `2×2` Pauli matrices only — no gamma/Majorana matrices, no gravity, no spherical-Bessel numerics):

- `spinorAction T X = Tᴴ * X * T` — the spinor conjugation;
- `spinorAction_comp` — it is a right action (conjugation by `T₁*T₂` = conjugation by `T₁` then `T₂`);
- `spinorAction_neg` — **two-to-one**: `T` and `-T` induce the same conjugation (the `±1` kernel of the double cover);
- `spinorAction_isHermitian` — the conjugation preserves hermiticity;
- `spinorAction_trace_of_unitary` — for unitary `T` (`T†T = 1`) the conjugation preserves the trace;
- `su2_preserves_time` — hence a unitary `T` fixes the time component `x⁰` (`x⁰ = ½ tr X`);
- `su2_preserves_spatialNormSq` — **headline**: for `T ∈ SU(2)` (`T†T = 1`, `det T = 1`) the conjugation preserves the Euclidean spatial length `(x¹)² + (x²)² + (x³)²` (combining `su2_preserves_time` with `spinorMap_preserves_mink` from `ChapterPauliLorentz`), i.e. the induced map is a rotation in `SO(3)`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `lean_verify`). `lake build BookProof` is green with the new file. Updated `BookProof/STATUS.md` (new Wave 83 entry) and prepended this Wave 83 summary to `ARISTOTLE_SUMMARY.md`. The pre-existing, out-of-scope `RiemannProof/RandomMap.lean` build failures were left untouched. All changes committed and pushed.

# Summary of changes for run be477a1b-a778-4586-b8d4-219ea9aab92d
Continued the standing formalization directive (mine the next self-contained mathematical claim from `book.tex`), honoring the two constraints: **prioritize a chapter other than gravity** and **stay off the Hankel–Majorana line**.

**Wave 82 — new file `BookProof/ChapterPauliLorentz.lean`** (registered in `BookProof.lean`). From the chapter *"Real representations, CPT theorem and the relativistic position operator"*, §*"On the Lorentz, SL(2,C) and Pin(3,1) groups"*, **Definition 42** and **Note 47**. It formalizes the algebraic heart of the `SL(2,ℂ) → SO⁺(1,3)` double cover using only the concrete `2×2` complex Pauli matrices (no gamma/Majorana matrices, no gravity, no spherical-Bessel numerics):

- Definition 42: the Pauli matrices are hermitian (`σ1_herm`/`σ2_herm`/`σ3_herm`), unitary/involutive (`σ1_sq`/`σ2_sq`/`σ3_sq`), and pairwise anti-commuting (`σ1σ2_anti`/`σ2σ3_anti`/`σ1σ3_anti`);
- the 4-vector ↔ hermitian-matrix correspondence `hermMat` with `hermMat_eq_pauli` (Pauli expansion `X = xᵤσᵘ`) and `hermMat_isHermitian`;
- `det_hermMat` — the key identity `det(xᵤσᵘ) = (x⁰)²−(x¹)²−(x²)²−(x³)²`: the determinant of the hermitian matrix is the Minkowski norm;
- `vecOfMat`/`hermMat_vecOfMat`/`hermMat_injective` — the real-linear bijection between Minkowski 4-vectors and hermitian `2×2` matrices;
- `spinorMap_preserves_mink` — the headline: for `T` with `det T = 1` (i.e. `T ∈ SL(2,ℂ)`), the spinor conjugation `X ↦ T† X T` sends `xᵤσᵘ` to `yᵤσᵘ` with `mink y = mink x`, which is exactly why the induced map is a Lorentz transformation.

Everything is `sorry`-free and axiom-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via verification). `lake build BookProof` is green with the new file included. Updated `BookProof/STATUS.md` (new Wave 82 entry) and, as requested, prepended a Wave 82 summary to `ARISTOTLE_SUMMARY.md`. The pre-existing, out-of-scope `RiemannProof/RandomMap.lean` build failures were left untouched. All changes are committed and pushed.

# Summary of latest run — Wave 82 (`BookProof/ChapterPauliLorentz.lean`)
Executed the next step of the standing formalization directive — mining the next
self-contained mathematical claim from `book.tex` — honoring the current
instructions to **prioritize a chapter other than gravity** and to **stay off
the Hankel–Majorana line**.

**Wave 82 — new file `BookProof/ChapterPauliLorentz.lean`** (registered in
`BookProof.lean`). From the chapter *"Real representations, CPT theorem and the
relativistic position operator"*, §*"On the Lorentz, SL(2,C) and Pin(3,1)
groups"*, **Definition 42** and **Note 47** (`book.tex` line ~5344, ~5455). The
book states that the Pauli matrices `σᵏ` are `2×2` hermitian, unitary,
anti-commuting complex matrices, and that there is a two-to-one surjection
`Υ : SL(2,ℂ) → SO⁺(1,3)` defined by `Υᵘ_ν(T) σ^ν = T† σᵘ T`. This wave pins down
the algebraic heart of Note 47: the correspondence between real Minkowski
4-vectors and hermitian `2×2` complex matrices, and the fact that the spinor
conjugation `X ↦ T† X T` by `T ∈ SL(2,ℂ)` (`det T = 1`) **preserves the
Minkowski quadratic form** `⟨x⟩ = (x⁰)²−(x¹)²−(x²)²−(x³)²` — which is exactly
what makes `Υ(T)` a Lorentz transformation. It uses only the concrete Pauli
matrices (`2×2` complex); nothing touches the gravity or γ/Majorana lines.

Proved (all sorry-free and axiom-free — only `propext`/`Classical.choice`/`Quot.sound`,
confirmed via verification):
- Definition 42 — `σ1_herm`/`σ2_herm`/`σ3_herm` (hermitian),
  `σ1_sq`/`σ2_sq`/`σ3_sq` (`(σᵏ)²=1`, hence unitary),
  `σ1σ2_anti`/`σ2σ3_anti`/`σ1σ3_anti` (pairwise anti-commuting);
- `hermMat` / `hermMat_eq_pauli` / `hermMat_isHermitian` — the hermitian matrix
  `X = xᵤσᵘ` of a real 4-vector and its Pauli expansion;
- `det_hermMat` — **the key identity** `det(xᵤσᵘ) = (x⁰)²−(x¹)²−(x²)²−(x³)²`;
- `vecOfMat` / `hermMat_vecOfMat` — every hermitian `2×2` matrix is `xᵤσᵘ` for a
  unique real 4-vector;
- `spinorMap_preserves_mink` — **headline**: `det T = 1 ⇒` the 4-vector of
  `T† (xᵤσᵘ) T` has the same Minkowski norm as `x`.

`lake build BookProof` is green with the new file included and sorry-free.
Updated `BookProof/STATUS.md` (new Wave 82 entry) and, as requested, prepended
this Wave 82 summary to `ARISTOTLE_SUMMARY.md`. The pre-existing, out-of-scope
`RiemannProof/RandomMap.lean` build failures were left untouched. All changes
are committed and pushed.

# Summary of changes for run 602e3b8e-9dce-4492-afff-7ebe2928a577
Executed the next step of the standing formalization directive (mine the next self-contained mathematical claim from `book.tex`), honoring the two constraints in the request: **prioritize a chapter other than gravity** and **stay off the Hankel–Majorana line**.

**Wave 81 — new file `BookProof/ChapterDoubleSlit.lean`** (registered in `BookProof.lean`). From the chapter *"Reconstructing the classical trajectory of any isolated quantum system"*, §*"The Young's double slit experiment"*. The book models the two-angle electron by the normalized 2×2 Hadamard matrix `H = (1/√2)·[[1,1],[1,-1]]` with source state `Ψ = (1,0)`, and notes the "mystery" that a 50/50 intermediate probability becomes a 100/0 detector probability when the second slit is open. This wave pins that down as the purely algebraic fact that `H` is an involution (`H² = 1`): composing the two non-deterministic steps yields certainty. It reuses only the concrete Hadamard matrix (as in `BookProof/ChapterE.lean`); nothing touches the gravity or γ/Majorana lines.

Proved (all sorry-free and axiom-free — only `propext`/`Classical.choice`/`Quot.sound`, confirmed via verification):
- `H_unitary` — `Hᴴ H = 1` (unitary evolution);
- `H_involutive` — the crux, `H² = 1`;
- `Hpsi0` — `H·Ψ = (1/√2)(1,1)`, the uniform intermediate superposition;
- `slit_closed_born` — slit closed: final Born distribution `(1/2, 1/2)`;
- `slit_open_state` / `slit_open_born` — slit open: `H·(H·Ψ) = Ψ`, final Born distribution `(1, 0)`.

`lake build BookProof` is green (8155 jobs) with the new file included and sorry-free. Updated `BookProof/STATUS.md` (new Wave 81 entry) and, as requested, prepended a Wave 81 summary to `ARISTOTLE_SUMMARY.md`. The pre-existing, out-of-scope `RiemannProof/RandomMap.lean` build failures were left untouched. All changes are committed and pushed.

# Summary of latest run — Wave 81 (`BookProof/ChapterDoubleSlit.lean`)
Executed the next step of the standing formalization directive — mining the next self-contained mathematical claim from `book.tex` — honoring the current instructions to **prioritize a chapter other than gravity** and to **stay off the Hankel–Majorana line**.

**Wave 81 — new file `BookProof/ChapterDoubleSlit.lean`** (registered in `BookProof.lean`). From the chapter *"Reconstructing the classical trajectory of any isolated quantum system"*, §*"The Young's double slit experiment"* (`book.tex` line ~3082). The book models the two-angle electron by the normalized `2×2` Hadamard matrix `H = (1/√2)·[[1,1],[1,-1]]` with source state `Ψ = (1,0)`, and observes the "mystery" that a `50/50` intermediate probability becomes a `100/0` detector probability when the second slit is open. This wave pins that down as the purely algebraic fact that `H` is an **involution** (`H² = 1`). Uses only the concrete Hadamard matrix (as in `ChapterE.lean`); no gravity, no γ/Majorana content.

Proved (all sorry-free and axiom-free; only `propext`/`Classical.choice`/`Quot.sound`, confirmed via `lean_verify`):
- `H_unitary` — `Hᴴ H = 1` (the Hadamard evolution is unitary);
- `H_involutive` — **the crux**: `H² = 1`, so composing the two non-deterministic steps yields the identity;
- `Hpsi0` — `H·Ψ = (1/√2)(1,1)`, the uniform intermediate superposition;
- `slit_closed_born` — **slit closed**: the final Born distribution is uniform, `(1/2, 1/2)`;
- `slit_open_state` / `slit_open_born` — **slit open**: `H·(H·Ψ) = Ψ`, so the final Born distribution is certain, `(1, 0)` — the electron arrives only along angle 1.

`lake build BookProof` is green with the new file sorry-free and axiom-free. Updated `BookProof/STATUS.md` (new Wave 81 entry) and prepended this summary to `ARISTOTLE_SUMMARY.md`. The pre-existing, out-of-scope `RiemannProof/RandomMap.lean` build failures were left untouched. All changes are committed and pushed.

# Summary of changes for run 365ea778-165e-4948-84a5-416c92ca03ef
Executed the next step of the standing formalization directive — mining the next self-contained mathematical claim from `book.tex` — honoring the instructions to prioritize a chapter other than gravity and to stay off the Hankel–Majorana line.

**Wave 80 — new file `BookProof/ChapterLorentzDecomp.lean`** (registered in `BookProof.lean`). This continues Waves 78–79 (chapter "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups", Note 43) with the claim Wave 78 had left as prose: the discrete Klein-four subgroup `Δ = {1, η, -η, -1}` and the proper orthochronous normal subgroup `SO⁺(1,3)` assemble into the whole group as the semidirect product **`O(1,3) = Δ ⋉ SO⁺(1,3)`**. Equivalently, `Δ` is a complete, irredundant set of coset representatives for `SO⁺(1,3)`, so `O(1,3)/SO⁺(1,3) ≅ Δ` is the Klein four-group of the four connected components indexed by `(det λ, sign λ⁰₀) ∈ {±1} × {±1}`. It uses only the Minkowski metric `η` and the groups from `ChapterLorentzGroup` / `ChapterLorentzOrthochronous` — no gamma/Majorana matrices, nothing from the gravity line.

Proved (all sorry-free and axiom-free; only `propext`/`Classical.choice`/`Quot.sound`):
- `delta_mul_time` — for a diagonal discrete generator `δ ∈ Δ`, the time component of a product factors: `(δ * m)⁰₀ = δ⁰₀ · m⁰₀`;
- `lorentz_delta_decomp` — existence: every Lorentz `λ` factors as `λ = δ * s` with `δ ∈ Δ` and `s ∈ SO⁺(1,3)`, the discrete factor chosen by a 4-way case split on `(sign det λ, sign λ⁰₀)`;
- `lorentz_delta_decomp_unique` — uniqueness: the factors are determined by `λ`, since `δ ↦ (det δ, sign δ⁰₀)` is injective on `Δ` and every `s ∈ SO⁺(1,3)` has `det s = 1`, `s⁰₀ > 0`.

`lake build BookProof` is green with the new file sorry-free and axiom-free (verified via the build, a `sorry` grep, and axiom checks on both headline theorems). Updated `BookProof/STATUS.md` (new Wave 80 entry) and prepended a Wave 80 summary to `ARISTOTLE_SUMMARY.md`. The pre-existing, out-of-scope `RiemannProof/RandomMap.lean` build failures were left untouched. All changes are committed and pushed.

# Summary of latest run — Wave 80 (`BookProof/ChapterLorentzDecomp.lean`)
Executed the next step of the standing formalization directive — mining the next self-contained mathematical claim from `book.tex` — while honoring your instructions to **prioritize a chapter other than gravity** and to **stay off the Hankel–Majorana line**.

**Wave 80 — new file `BookProof/ChapterLorentzDecomp.lean`** (registered in `BookProof.lean`). This continues Waves 78–79 (chapter "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups", Note 43) with the claim Wave 78 had left as prose: the discrete Klein-four subgroup `Δ = {1, η, -η, -1}` and the proper orthochronous normal subgroup `SO⁺(1,3)` assemble into the whole group as the semidirect product **`O(1,3) = Δ ⋉ SO⁺(1,3)`** — i.e. `Δ` is a complete, irredundant set of coset representatives, so `O(1,3)/SO⁺(1,3) ≅ Δ` is the Klein four-group of the four connected components of `O(1,3)`, indexed by `(det λ, sign λ⁰₀) ∈ {±1} × {±1}`. As requested it uses only the Minkowski metric `η` and the groups from `ChapterLorentzGroup` / `ChapterLorentzOrthochronous` — no gamma / Majorana matrices, and nothing from the gravity line.

Proved (all sorry-free and axiom-free; only `propext` / `Classical.choice` / `Quot.sound`):
- `delta_mul_time` — for a diagonal discrete generator `δ ∈ Δ`, the time component of a product factors as `(δ * m)⁰₀ = δ⁰₀ · m⁰₀`;
- `lorentz_delta_decomp` — **existence**: every Lorentz `λ` factors as `λ = δ * s` with `δ ∈ Δ` and `s ∈ SO⁺(1,3)`, the discrete factor selected by a 4-way case split on `(sign det λ, sign λ⁰₀)`;
- `lorentz_delta_decomp_unique` — **uniqueness**: the two factors are determined by `λ`, since `δ ↦ (det δ, sign δ⁰₀)` is injective on `Δ` and every `s ∈ SO⁺(1,3)` has `det s = 1`, `s⁰₀ > 0`.

`lake build BookProof` is green with the new file sorry-free and axiom-free (verified via the build, a `sorry` grep, and `lean_verify`). Updated `BookProof/STATUS.md` (new Wave 80 entry) and prepended this Wave 80 summary to `ARISTOTLE_SUMMARY.md`. The pre-existing, out-of-scope `RiemannProof/RandomMap.lean` build failures were left untouched. All changes committed and pushed.

# Summary of changes for run a56b0e5c-d261-452f-81b3-773686648bd2
Executed the next step of the standing formalization directive — mining the next self-contained mathematical claim from `book.tex` — while honoring your instructions to prioritize a chapter other than gravity and to stay off the Hankel–Majorana line.

**Wave 79 — new file `BookProof/ChapterLorentzOrthochronous.lean`** (registered in `BookProof.lean`). This continues Wave 78 (Note 43) with the next self-contained claim of that same Note 43 (chapter "Real representations, CPT theorem and the relativistic position operator", §"On the Lorentz, SL(2,C) and Pin(3,1) groups"): the **proper orthochronous Lorentz group `SO⁺(1,3) = {λ ∈ O(1,3) : det λ = 1, λ⁰₀ > 0}` is a normal subgroup of `O(1,3)`**. As requested it uses only the Minkowski metric η and the group `O(1,3)` from `ChapterLorentzGroup` — no gamma/Majorana matrices, and nothing from the gravity line.

Proved (all sorry-free and axiom-free; only `propext`/`Classical.choice`/`Quot.sound`):
- `isLorentz_neg`, `lorentz_inv_eq` (`λ⁻¹ = η λᵀ η`), `isLorentz_mul_eta_transpose` (`λ η λᵀ = η`);
- `lorentz_time_col`/`lorentz_time_row` (the unit time-like column/row identities), `lorentz_time_sq_ge_one` (`(λ⁰₀)² ≥ 1`), `lorentz_time_ne_zero`, `lorentz_inv_time` (`(λ⁻¹)⁰₀ = λ⁰₀`);
- `product_time_component` and the crux `orthochronous_mul` (product of two orthochronous Lorentz matrices is orthochronous), via the reverse Cauchy–Schwarz inequality on time components;
- `IsProperOrthochronous`; `isPO_one`, `isPO_mul`, `isPO_inv` (subgroup); and the headline `isPO_conj` — `SO⁺(1,3)` is a normal subgroup of `O(1,3)`.

`lake build BookProof` is green with the new file sorry-free and axiom-free (verified via the build, a `sorry` grep, and `lean_verify`). Updated `BookProof/STATUS.md` (new Wave 79 entry) and prepended a Wave 79 summary to `ARISTOTLE_SUMMARY.md`. The pre-existing, out-of-scope `RiemannProof/RandomMap.lean` build failures were left untouched. All changes committed and pushed.

# Summary of latest run (Wave 79)
Executed the next step of the standing `FORMALIZATION_ROADMAP.md` directive — mining the next self-contained mathematical claim from `book.tex` — honoring your instructions to **prioritize a chapter other than gravity** and to **stay off the Hankel–Majorana line**.

**Wave 79 — new file `BookProof/ChapterLorentzOrthochronous.lean`** (registered in `BookProof.lean`). This continues Wave 78 (Note 43) with the next self-contained claim of the *same* **Note 43** (chapter *"Real representations, CPT theorem and the relativistic position operator"*, §*"On the Lorentz, SL(2,C) and Pin(3,1) groups"*, `book.tex` line ~5366): the **proper orthochronous Lorentz group** `SO⁺(1,3) = {λ ∈ O(1,3) : det λ = 1, λ⁰₀ > 0}` **is a normal subgroup of `O(1,3)`**. Like Wave 78 this uses *only* the Minkowski metric `η = diag(1,−1,−1,−1)` and the group `O(1,3)` from `ChapterLorentzGroup` — no gamma/Majorana matrices — so it stays off both the gravity and the Hankel–Majorana lines. Proved (all `sorry`-free and `axiom`-free; only `propext`/`Classical.choice`/`Quot.sound`, confirmed via `lean_verify`):
- `isLorentz_neg` (`O(1,3)` closed under negation), `lorentz_inv_eq` (`λ⁻¹ = η λᵀ η`), `isLorentz_mul_eta_transpose` (the dual relation `λ η λᵀ = η`);
- `lorentz_time_col` / `lorentz_time_row` — the unit time-like column/row identities `(λ⁰₀)² = 1 + Σᵢ(λⁱ₀)² = 1 + Σᵢ(λ⁰ᵢ)²`; `lorentz_time_sq_ge_one` (`(λ⁰₀)² ≥ 1`), `lorentz_time_ne_zero`, `lorentz_inv_time` (`(λ⁻¹)⁰₀ = λ⁰₀`);
- `product_time_component`, and the crux `orthochronous_mul` (`a⁰₀ > 0`, `b⁰₀ > 0 ⇒ (ab)⁰₀ > 0`) via the reverse Cauchy–Schwarz inequality on the time components;
- `IsProperOrthochronous` (the `SO⁺(1,3)` predicate); `isPO_one`, `isPO_mul`, `isPO_inv` (subgroup); and the **headline** `isPO_conj` — `SO⁺(1,3)` is a **normal** subgroup of `O(1,3)`, proved by a sign case split on `g⁰₀` using that `-g` is Lorentz with `(-g)⁻¹ = -g⁻¹`.

`lake build BookProof` is green (8153 jobs) with the new file `sorry`-free and `axiom`-free (verified the build and grepped for `sorry` rather than relying on status reports). Updated `BookProof/STATUS.md` (new Wave 79 entry) and prepended this summary to `ARISTOTLE_SUMMARY.md` as requested. The pre-existing, out-of-scope `RiemannProof/RandomMap.lean` build failures were not touched. All changes are committed and pushed.

# Summary of changes for run 720daf6d-6bd7-4b0d-a18b-d5edf0448096
Executed the next step of the standing `FORMALIZATION_ROADMAP.md` directive — mining the next self-contained mathematical claim from `book.tex` — while honoring your instructions to prioritize a chapter other than gravity and to stay off the Hankel–Majorana line.

**Wave 78 — new file `BookProof/ChapterLorentzGroup.lean`** (registered in `BookProof.lean`). From the chapter *"Real representations, CPT theorem and the relativistic position operator"*, §*"On the Lorentz, SL(2,C) and Pin(3,1) groups"*, **Note 43**: the Lorentz group `O(1,3) = {λ ∈ ℝ⁴ˣ⁴ : λᵀ η λ = η}` preserving the Minkowski metric `η = diag(1,−1,−1,−1)`, and the discrete Lorentz subgroup `Δ = {1, η, −η, −1}` of parity and time-reversal. This uses only the metric η — no gamma/Majorana matrices — so it stays off both the gravity and the Hankel–Majorana lines. Proved (all `sorry`-free and `axiom`-free; only `propext`/`Classical.choice`/`Quot.sound`, confirmed with `#print axioms`):
- `eta_transpose`, `eta_mul_self` (η² = 1), `eta_det` (det η = −1);
- `IsLorentz` (the predicate λᵀ η λ = η), with `isLorentz_one`, `isLorentz_mul`, `isLorentz_inv` — O(1,3) is a group;
- `lorentz_det_sq_one` ((det λ)² = 1) and `lorentz_det_ne_zero` — every Lorentz matrix is invertible with det = ±1;
- `isLorentz_eta`, `isLorentz_neg_eta`, `isLorentz_neg_one` — the three nontrivial discrete generators lie in O(1,3);
- `Delta`, `delta_subset_lorentz` (Δ ⊆ O(1,3)), `delta_mul_closed` (closed under multiplication), `delta_involutive` (every element squares to 1, so Δ is the abelian Klein four-group ≅ ℤ₂ × ℤ₂), and `delta_card_four` (|Δ| = 4).

The full semidirect-product decomposition O(1,3) = Δ ⋉ SO⁺(1,3) is left as prose; this wave lands the group structure and the Klein-four subgroup. `lake build BookProof` is green (8130 jobs) with the new file `sorry`-free and `axiom`-free (I verified the build and grepped for `sorry` rather than relying on status reports). Updated `BookProof/STATUS.md` (new Wave 78 entry) and prepended a Wave 78 summary to `ARISTOTLE_SUMMARY.md` as requested. The pre-existing, out-of-scope `RiemannProof/RandomMap.lean` build failures were not touched. All changes are committed and pushed.

# Summary of latest run (Wave 78)
Executed the next step of the standing `FORMALIZATION_ROADMAP.md` directive — mining the next self-contained mathematical claim from `book.tex` — while honoring your instructions to prioritize a chapter other than gravity and to stay off the Hankel–Majorana line.

**Wave 78 — new file `BookProof/ChapterLorentzGroup.lean`** (registered in `BookProof.lean`). From the chapter *"Real representations, CPT theorem and the relativistic position operator"*, §*"On the Lorentz, SL(2,C) and Pin(3,1) groups"*, **Note 43**: the Lorentz group `O(1,3) = {λ ∈ ℝ^{4×4} : λᵀ η λ = η}` is the set of real matrices preserving the Minkowski metric `η = diag(1,-1,-1,-1)`, and `Δ = {1, η, -η, -1}` is the discrete Lorentz subgroup of parity and time-reversal. This wave uses *only* the metric `η` — no gamma/Majorana matrices — so it stays clear of the Hankel–Majorana line and off the gravity line. Proved (all `sorry`-free and `axiom`-free, only `propext`/`Classical.choice`/`Quot.sound`):
- `eta_transpose`, `eta_mul_self` (`η² = 1`), `eta_det` (`det η = -1`) — basic metric properties;
- `IsLorentz` (the predicate `λᵀ η λ = η`), with `isLorentz_one`, `isLorentz_mul`, `isLorentz_inv` — `O(1,3)` is a **group**;
- `lorentz_det_sq_one` (`(det λ)² = 1`) and `lorentz_det_ne_zero` — every Lorentz matrix is invertible with `det = ±1`;
- `isLorentz_eta`, `isLorentz_neg_eta`, `isLorentz_neg_one` — the three nontrivial discrete generators lie in `O(1,3)`;
- `Delta`, `delta_subset_lorentz` (`Δ ⊆ O(1,3)`), `delta_mul_closed` (closed under multiplication), `delta_involutive` (every element squares to `1`, so `Δ` is the abelian **Klein four-group** `≅ ℤ₂ × ℤ₂`), and `delta_card_four` (`|Δ| = 4`).

The full semidirect-product decomposition `O(1,3) = Δ ⋉ SO⁺(1,3)` is left as prose; this wave lands the group structure and the Klein-four subgroup. `lake build BookProof` is green (8130 jobs) with the new file `sorry`-free and `axiom`-free. Updated `BookProof/STATUS.md` (new Wave 78 entry). The pre-existing, out-of-scope `RiemannProof/RandomMap.lean` build failures are unchanged (not touched). All changes committed and pushed.

# Summary of changes for run f43bbd88-84f3-4fcd-8900-5416e755aa54
Executed the next step of the standing `FORMALIZATION_ROADMAP.md` directive — mining the next self-contained mathematical claim from `book.tex` — while honoring your instructions to prioritize a chapter other than gravity and to stay off the Hankel–Majorana line.

**Wave 77 — new file `BookProof/ChapterSuperBracket.lean`** (registered in `BookProof.lean`). From the chapter *"Quantization due to time-evolution: Yang-Mills and Classical Statistical Field Theory"* / *"Timepiece and the Gribov ambiguity"*, §*"Pure Yang-Mills theory"*: the Yang–Mills Fock space is a tensor product of a symmetric (bosonic) and antisymmetric (fermionic) Fock space, giving a *"graded Lie superalgebra of creation and annihilation operators"* whose unified canonical (anti)commutation relation carries the sign `(-1)^{(α mod 2)(β mod 2)}`. I isolated this ℤ₂-graded (super) commutator, modelling the parity of a homogeneous operator by a `Bool` inside an arbitrary associative ring `R`, defining the Koszul sign `eps p q = (-1)^{p·q}` and the super-bracket `sbracket p q a b = a·b − ε(p,q)·(b·a)`, and proving:
- sign properties: `eps_comm` (symmetry), `eps_mul_self` (`ε² = 1`), `eps_false_left`/`eps_false_right` (trivial against even);
- `sbracket_even_even` — even/even gives the **commutator** (bosonic CCR side);
- `sbracket_odd_odd` — odd/odd gives the **anticommutator** (fermionic CAR side): the single formula unifying the two canonical relations of the book;
- `sbracket_even_left`/`sbracket_even_right`;
- `sbracket_graded_antisymm` — graded antisymmetry `⟦a,b⟧ = −ε(p,q)⟦b,a⟧`;
- `super_jacobi` (headline) — the graded Jacobi identity, making `(R, ⟦·,·⟧)` a **Lie superalgebra** (exactly the graded-Lie-superalgebra structure the book asserts);
- `commutator_jacobi` — the all-even specialization is the ordinary Jacobi identity.

All results are `sorry`-free and `axiom`-free (the headline `super_jacobi` uses only `propext`, `Quot.sound`, confirmed by verification); the file compiles with no errors or warnings and the `BookProof` target builds green. The Hankel–Majorana line and the gravity line were left untouched. The out-of-scope `RiemannProof/` directory retains its pre-existing build failures (in `RandomMap.lean`) and was not modified.

Updated `BookProof/STATUS.md` (new Wave 77 entry) and `ARISTOTLE_SUMMARY.md` (prepended a new-run summary), as requested. All changes are committed and pushed.

# Summary of latest run (Wave 77)
Continued the `FORMALIZATION_ROADMAP.md` standing directive (mine the next self-contained mathematical claim from `book.tex`), and — per your instruction — prioritizing a chapter other than gravity and staying off the Hankel–Majorana line.

**Wave 77 — new file `BookProof/ChapterSuperBracket.lean`.** From the chapter *"Quantization due to time-evolution: Yang-Mills and Classical Statistical Field Theory"* / *"Timepiece and the Gribov ambiguity"*, §*"Pure Yang-Mills theory"*: the Yang–Mills Fock space is a tensor product of a symmetric (bosonic) and antisymmetric (fermionic) Fock space, giving a *"graded Lie superalgebra of creation and annihilation operators"* whose unified canonical (anti)commutation relation carries the sign `(-1)^{(α mod 2)(β mod 2)}`. The file isolates this ℤ₂-graded (super) commutator, modelling the parity of a homogeneous operator by a `Bool` (`false` = even/bosonic, `true` = odd/fermionic) inside an arbitrary associative ring `R`. It defines the Koszul sign `eps p q = (-1)^{p·q}` and the super-bracket `sbracket p q a b = a·b − ε(p,q)·(b·a)`, and proves:
- `eps_comm`, `eps_mul_self`, `eps_false_left`/`eps_false_right` — the sign is symmetric, squares to `1`, and is trivial against an even element;
- `sbracket_even_even` — even/even gives the **commutator** `a·b − b·a` (bosonic CCR side);
- `sbracket_odd_odd` — odd/odd gives the **anticommutator** `a·b + b·a` (fermionic CAR side): the single formula unifying the two canonical relations of the book;
- `sbracket_even_left`/`sbracket_even_right` — against an even element the bracket is always the commutator;
- `sbracket_graded_antisymm` — **graded antisymmetry** `⟦a,b⟧ = −ε(p,q)⟦b,a⟧`;
- `super_jacobi` (headline) — the graded Jacobi identity `ε(p,r)⟦a,⟦b,c⟧⟧ + ε(q,p)⟦b,⟦c,a⟧⟧ + ε(r,q)⟦c,⟦a,b⟧⟧ = 0`, which makes `(R, ⟦·,·⟧)` a **Lie superalgebra** — exactly the graded-Lie-superalgebra structure the book asserts;
- `commutator_jacobi` — the all-even specialization is the ordinary Jacobi identity of the commutator.

The file is registered in `BookProof.lean`; all results are sorry-free and axiom-free (`super_jacobi` uses only `propext`, `Quot.sound`, confirmed via verification); the `BookProof` target builds green with no warnings in the new file. Updated `BookProof/STATUS.md` (new Wave 77 entry) and this file. The out-of-scope `RiemannProof/` directory retains its pre-existing build failures (in `RandomMap.lean`) and was left untouched. All changes are committed and pushed.

# Summary of changes for run 4fc9902f-089c-4841-b68b-ccad74d611ef
Continued the `FORMALIZATION_ROADMAP.md` standing directive (mine the next self-contained mathematical claim from `book.tex`), this time — per your instruction — prioritizing a chapter other than gravity and staying off the Hankel–Majorana line.

**Wave 76 — new file `BookProof/ChapterLorentzTranslation.lean`.** From the chapter *"Quantization due to time-evolution: Yang-Mills and Classical Statistical Field Theory"*, §*"Lorentz covariance"*: in a basis where the 3-momentum operator is diagonal, the space-time translations of a free system of invariant mass `M` act by the phase `T(x)Ψ(γv) = e^{iMτ(γv,x)}Ψ(γv)` with proper time `τ = γ x₀ − (γv)·x` and Lorentz factor `γ = √(1+(γv)²)`. Modelling the spatial momentum `γv` by `w : Fin 3 → ℝ`, the file defines `gamma`, `properTime`, `transPhase` and proves:
- `gamma_sq` / `mass_shell` — the four-velocity `(γ, γv)` lies on the unit mass shell `γ² − (γv)² = 1`;
- `gamma_zero` — rest-frame value `γ = 1`;
- `properTime_add`, `properTime_zero` — `τ` is additive in the translation `x` (a homomorphism `(ℝ⁴,+) → (ℝ,+)`);
- `properTime_rest` — in the rest frame `τ = x₀`;
- `transPhase_add` (headline) `T(x+y) = T(x)·T(y)` and `transPhase_zero` `T(0)=1` — a one-dimensional representation of the translation group;
- `transPhase_norm` — each `T(x)` is unitary (`‖·‖ = 1`, real `M`);
- `transPhase_rest` — rest-frame reduction `T(x) = e^{iMx₀}`, the non-relativistic time-evolution phase.

The file is registered in `BookProof.lean`; all results are sorry-free and axiom-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via verification); the `BookProof` target builds green. Updated `BookProof/STATUS.md` (new Wave 76 entry) and `ARISTOTLE_SUMMARY.md` (prepended a new-run summary). The out-of-scope `RiemannProof/` directory retains its pre-existing build failures (in `RandomMap.lean`) and was left untouched. All changes are committed and pushed.

# Summary of latest run (Wave 76)
Continued the `FORMALIZATION_ROADMAP.md` standing directive (mine the next
self-contained mathematical claim from `book.tex`). Per the author's latest
instruction this wave **prioritizes a chapter other than gravity** and stays off
the Hankel–Majorana line: it steps onto the *"Quantization due to time-evolution:
Yang-Mills and Classical Statistical Field Theory"* chapter, §*"Lorentz
covariance"* (book line ~6506).

**Wave 76 — new file `BookProof/ChapterLorentzTranslation.lean`: the space-time
translation representation in the momentum-diagonal basis.** In a basis where the
3-momentum operator is diagonal, the book writes the space-time translations of a
free system of invariant mass `M` as `T(x) Ψ(γv) = e^{i M τ(γv, x)} Ψ(γv)` with
proper time `τ(γv, x) = γ x₀ − (γv)·x` and Lorentz factor `γ = √(1 + (γv)²)`, and
remarks that this has "the same structure as the non-relativistic time-evolution,
with `M` as the Hamiltonian and `τ` as (proper) time". Modelling the spatial
momentum `γv` by `w : Fin 3 → ℝ`, the file defines `gamma`, `properTime`,
`transPhase` and proves:
- `gamma_sq` / `mass_shell` — the four-velocity `(γ, γv)` lies on the unit mass
  shell `γ² − (γv)² = 1`;
- `gamma_zero` — rest-frame value `γ = 1`;
- `properTime_add`, `properTime_zero` — `τ` is additive in the translation `x`
  (a homomorphism `(ℝ⁴,+) → (ℝ,+)`);
- `properTime_rest` — in the rest frame `τ = x₀`;
- `transPhase_add` (headline) `T(x + y) = T(x)·T(y)` and `transPhase_zero`
  `T(0) = 1` — a one-dimensional representation of the translation group;
- `transPhase_norm` — each `T(x)` is unitary (`‖·‖ = 1`, real `M`);
- `transPhase_rest` — rest-frame reduction `T(x) = e^{i M x₀}`.

The file is registered in `BookProof.lean`; all results are `sorry`-free and
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via
`lean_verify`); the `BookProof` target builds green. Updated
`BookProof/STATUS.md` (new Wave 76 entry) and this `ARISTOTLE_SUMMARY.md`. The
out-of-scope `RiemannProof/` directory retains its pre-existing build failures
(in `RandomMap.lean`) and was left untouched. All changes are committed and
pushed.

# Summary of changes for run 79470082-ac2a-4555-a2ac-2c414394f377
Continued the `FORMALIZATION_ROADMAP.md` standing directive — mining the next self-contained mathematical claim from `book.tex` — staying off the Hankel–Majorana line as requested, and extending the "Diffeomorphisms and gravity", §"Classical Hamiltonian" projector/metric line (prior waves: spatial projector χ, induced spatial metric h, temporal projector Π, raised metric h♯, 3+1 split, generalized-inverse pair).

**Wave 75 — new file `BookProof/ChapterGravityIrrep.lean`: the irreducible SO(3) decomposition of the spatial torsion tensor.** The book decomposes the spatial torsion tensor `T_{ab}` (living on the 3-dimensional spatial hyperplane `v^⊥`) into its three irreducible pieces. Modelling the spatial slice as Euclidean `Fin 3` (η = δ, so `tr δ = 3`, which is exactly why the book's `2/3` factor makes the traceless part traceless), the file defines the antisymmetric part `A_{ab} = T_{ab} − T_{ba}`, the symmetric traceless part `S_{ab} = T_{ab} + T_{ba} − (2/3)δ_{ab}(tr T)`, and the Frobenius inner product, and proves:
- `antisymPart_antisymm` (Aᵀ = −A);
- `symTracelessPart_symm` (Sᵀ = S);
- `trace_symTracelessPart` (tr S = 0);
- headline `irrep_reconstruction` (M = ½S + ½A + ⅓(tr M)·I);
- mutual orthogonality: `frob_symTraceless_antisym`, `frob_symTraceless_trace`, `frob_antisym_trace`.

The file is registered in `BookProof.lean`; all results are sorry-free and axiom-free (only propext, Classical.choice, Quot.sound, confirmed via `#print axioms`), and the `BookProof` target builds green. Updated `BookProof/STATUS.md` (new Wave 75 entry) and `ARISTOTLE_SUMMARY.md` (prepended a latest-run summary, as requested). The out-of-scope `RiemannProof/` directory retains its pre-existing build failures (in `RandomMap.lean`) and was left untouched. All changes are committed and pushed.

# Summary of latest run (Wave 75)
Continued the `FORMALIZATION_ROADMAP.md` standing directive (mine the next
self-contained mathematical claim from `book.tex`), staying off the
Hankel–Majorana line as requested, extending the "Diffeomorphisms and gravity",
§"Classical Hamiltonian" projector/metric line (prior waves: spatial projector χ
(W69), induced spatial metric h (W70), temporal projector Π (W71), raised metric
h♯ (W72), 3+1 split (W73), generalized-inverse pair (W74)) with one new file.

**Wave 75 — `BookProof/ChapterGravityIrrep.lean` (irreducible SO(3) decomposition
of a spatial tensor).** In the Einstein–Cartan / teleparallel Hamiltonian
formalism the author decomposes the *spatial* torsion tensor `T_{ab}` (both
indices projected by χ, so it lives on the 3-dimensional spatial hyperplane
`v^⊥`) into its three SO(3)-irreducible pieces. Modelling the spatial slice as
Euclidean `Fin 3` (η = δ, so `tr δ = 3`, exactly why the book's `2/3` factor
makes `S` traceless), the file defines the antisymmetric part
`A_{ab} = T_{ab} − T_{ba}`, the symmetric traceless part
`S_{ab} = T_{ab} + T_{ba} − (2/3)δ_{ab}(tr T)`, and the Frobenius inner product
`⟨X,Y⟩ = ∑_{i,j} X_{ij}Y_{ij}`, and proves: `antisymPart_antisymm` (Aᵀ = −A);
`symTracelessPart_symm` (Sᵀ = S); `trace_symTracelessPart` (tr S = 0);
headline `irrep_reconstruction` (M = ½S + ½A + ⅓(tr M)·I); and the three mutual
orthogonality relations `frob_symTraceless_antisym`, `frob_symTraceless_trace`,
`frob_antisym_trace` (the decomposition is orthogonal).

The file is registered in `BookProof.lean`; all results are sorry-free and
axiom-free (only propext, Classical.choice, Quot.sound, confirmed via
`#print axioms`); the `BookProof` target builds green. Updated
`BookProof/STATUS.md` (new Wave 75 entry) and this `ARISTOTLE_SUMMARY.md`. The
out-of-scope `RiemannProof/` directory retains its pre-existing build failures
(in `RandomMap.lean`) and was left untouched. All changes are committed and
pushed.

# Summary of changes for run 83759078-c295-4d6f-95e1-81ce7a111306
Continued the `FORMALIZATION_ROADMAP.md` standing directive (mine the next self-contained mathematical claim from `book.tex`), staying off the Hankel–Majorana line as requested, extending the "Diffeomorphisms and gravity", §"Classical Hamiltonian" projector/metric line (prior waves: spatial projector χ, induced spatial metric h, temporal projector Π, raised metric h♯) with two new files.

**Wave 73 — `BookProof/ChapterGravitySplit.lean` (orthogonal 3+1 spacetime split).** Relative to the unit timelike vector v (minkSq v = −1, mostly-plus η = diag(−1,1,1,1)), every vector x splits uniquely into a spatial part χx ∈ v^⊥ and a temporal part Πx (a multiple of v), the two Minkowski-orthogonal. Proves: the Minkowski bilinear form `minkForm` with `minkForm_comm`/`minkForm_self`; `spatialPart_add_timePart` (completeness χx + Πx = x); `timePart_eq_smul` (Πx = −⟨x,v⟩_η · v); `spatialPart_orthogonal` (⟨χx, v⟩_η = 0); headline `parts_orthogonal` (⟨χx, Πx⟩_η = 0); and `split_unique` (uniqueness of the split).

**Wave 74 — `BookProof/ChapterGravityGenInverse.lean` (h and h♯ are a generalized-inverse pair).** Although both are degenerate along v, the pair (h, h♯) satisfies the Moore–Penrose-type absorption identities on v^⊥. Proves: `spatialMetric_mul_spatialProj` (h·χ = h); `spatialProj_mul_invSpatialMetric` (χ·h♯ = h♯); headline `spatialMetric_genInverse` (h·h♯·h = h); headline `invSpatialMetric_genInverse` (h♯·h·h♯ = h♯).

Both files are registered in `BookProof.lean`; all results are sorry-free and axiom-free (only propext, Classical.choice, Quot.sound, confirmed via `#print axioms`); the `BookProof` target builds green (8126 jobs). Updated `BookProof/STATUS.md` (new Wave 73 and Wave 74 entries) and `ARISTOTLE_SUMMARY.md`. The out-of-scope `RiemannProof/` directory retains its pre-existing build failures (in `RandomMap.lean`) and was left untouched. All changes are committed and pushed.

# Summary of latest run (Waves 73–74)
Continued executing `FORMALIZATION_ROADMAP.md` under its standing directive (mine the next self-contained mathematical claim from `book.tex`), staying off the Hankel–Majorana line as requested, extending the gravity projector/metric line (Waves 69–72) with two new files.

**Wave 74 — `BookProof/ChapterGravityGenInverse.lean`.** From *"Diffeomorphisms and gravity"*, §*"Classical Hamiltonian"*: the induced spatial metric `h` (Wave 70) and its raised counterpart `h♯` (Wave 72) form a **generalized (Moore–Penrose-type) inverse pair** on the spatial hyperplane `v^⊥`, even though both are degenerate along the time direction `v` (`minkSq v = -1`). Reusing `spatialProj_idempotent`, `spatialMetric_eq_metric_mul_proj`, `invSpatialMetric_mulVec_lower_self`, `invSpatialMetric_symm` and the headline `invSpatialMetric_mul_spatialMetric` (`h♯·h = χ`), it proves:
- `spatialMetric_mul_spatialProj` — `h · χ = h`;
- `spatialProj_mul_invSpatialMetric` — `χ · h♯ = h♯`;
- `spatialMetric_genInverse` — headline `h · h♯ · h = h`;
- `invSpatialMetric_genInverse` — headline `h♯ · h · h♯ = h♯`.

Both new files are registered in `BookProof.lean`, all results are `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`), and the `BookProof` target builds green. `BookProof/STATUS.md` gained Wave 73 and Wave 74 entries. The out-of-scope `RiemannProof/` directory retains its pre-existing build failures (in `RandomMap.lean`) and was left untouched. All changes are committed and pushed.

## Wave 73 — `BookProof/ChapterGravitySplit.lean`
Continued executing `FORMALIZATION_ROADMAP.md` under its standing directive (mine the next self-contained mathematical claim from `book.tex`), staying off the Hankel–Majorana line as requested, building on the gravity projector/metric line (Waves 69–72).

**New deliverable — `BookProof/ChapterGravitySplit.lean` (Wave 73).** From the book chapter *"Diffeomorphisms and gravity"*, §*"Classical Hamiltonian"*: the orthogonal `3+1` spacetime split implemented by the spatial projector `χ` (Wave 69) and temporal projector `Π` (Wave 71). Relative to the globally defined unit timelike vector `v` (`minkSq v = -1`, mostly-plus `η = diag(-1,1,1,1)`), every contravariant vector `x` splits uniquely into a spatial part `χx ∈ v^⊥` and a temporal part `Πx` (a multiple of `v`), the two being Minkowski-orthogonal. Reusing `spatialProj`, `timeProj`, `metric`, `lower`, `minkSq` and the projector lemmas `spatialProj_mulVec_self`, `spatialProj_mulVec_of_orthogonal`, `spatialProj_add_timeProj`, the file proves:
- `minkForm` (the Minkowski bilinear form `⟨x,y⟩_η`), `minkForm_comm` (symmetry), `minkForm_self` (`= minkSq`);
- `spatialPart_add_timePart` — completeness `χx + Πx = x`;
- `timePart_eq_smul` — `Πx = -⟨x,v⟩_η · v`, so the temporal part is a multiple of `v`;
- `spatialPart_orthogonal` — `⟨χx, v⟩_η = 0`, the spatial part lies in `v^⊥`;
- `parts_orthogonal` — headline `⟨χx, Πx⟩_η = 0`, spatial and temporal parts are Minkowski-orthogonal;
- `split_unique` — uniqueness of the split: if `x = s + c • v` with `s ⊥ v` then `s = χx` and `c • v = Πx`.

All results are `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`). The file is registered in `BookProof.lean`; the `BookProof` target builds green (verified with the module explicitly built). I updated `BookProof/STATUS.md` (new Wave 73 entry) and this file. The out-of-scope `RiemannProof/` directory retains its pre-existing build failures (in `RandomMap.lean`) and was left untouched. All changes are committed and pushed.

# Summary of changes for run 557fbb40-594e-4831-a729-f3fdd9aaa7ca
Continued the `FORMALIZATION_ROADMAP.md` standing directive (mine the next self-contained mathematical claim from `book.tex`), staying off the Hankel–Majorana line as requested.

**New deliverable — `BookProof/ChapterGravityInvMetric.lean` (Wave 72).** From the book chapter *"Diffeomorphisms and gravity"*, §*"Classical Hamiltonian"*: raising both indices of the induced spatial metric `h_{ab} = η_{ab} + v_a v_b` (from the prior wave) with the mostly-plus Minkowski metric `η = diag(−1,1,1,1)` gives the inverse (raised) spatial metric `h^{ab} = η^{ab} + v^a v^b`, relative to the globally defined unit timelike vector `v` (`minkSq v = −1`). Reusing `metric`, `lower`, `minkSq`, `spatialProj` from `ChapterGravityProjector` and `spatialMetric` from `ChapterGravityMetric`, the file proves:
- `metric_mul_metric` — the Minkowski metric is an involution `η · η = 1` (η is its own inverse);
- `invSpatialMetric_symm` — `h♯` is symmetric;
- `invSpatialMetric_mulVec_lower_self` — `h^{ab} v_b = 0` (the inverse metric degenerates along the time covector);
- `invSpatialMetric_mul_spatialMetric` — headline `h♯ · h = χ`: the raised and lowered spatial metrics compose to the spatial projector χ (identity on `v^⊥`), the defining relation of an inverse-metric pair on the degenerate hyperplane.

All four results are `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`). The file is registered in `BookProof.lean`; the `BookProof` target builds green (verified with the module explicitly built). I updated `BookProof/STATUS.md` (new Wave 72 entry) and added a new run section to `ARISTOTLE_SUMMARY.md` as requested.

The out-of-scope `RiemannProof/` directory retains its pre-existing build failures (in `RandomMap.lean`) and was left untouched. All changes are committed and pushed.

# Summary of latest run (Wave 72)
Continued executing `FORMALIZATION_ROADMAP.md` under its standing directive (mine the next self-contained mathematical claim from `book.tex`), staying off the Hankel–Majorana line as requested, and building directly on the previous runs' gravity projector/metric line.

**New deliverable — `BookProof/ChapterGravityInvMetric.lean` (Wave 72).** From the book chapter *"Diffeomorphisms and gravity"*, §*"Classical Hamiltonian"*: raising both indices of Wave 70's induced spatial metric `h_{ab} = η_{ab} + v_a v_b` with the mostly-plus Minkowski metric `η = diag(−1,1,1,1)` gives the **inverse (raised) spatial metric** `h^{ab} = η^{ab} + v^a v^b`, the metric induced on the cotangent spatial hyperplane relative to the globally defined unit timelike vector `v` (`minkSq v = −1`). Reusing `metric`, `lower`, `minkSq`, `spatialProj` from `ChapterGravityProjector` and `spatialMetric` from `ChapterGravityMetric`, the file proves and I verified:
- `metric_mul_metric` — the Minkowski metric is an involution `η · η = 1` (so `η` is its own inverse, `η^{ab} η_{bc} = δ^a{}_c`);
- `invSpatialMetric_symm` — `h^♯` is symmetric (`(h♯)ᵀ = h♯`);
- `invSpatialMetric_mulVec_lower_self` — `h^{ab} v_b = 0` (the inverse metric degenerates along the time covector, complementary to `h_{ab} v^b = 0`);
- `invSpatialMetric_mul_spatialMetric` — **headline** `h^♯ · h = χ`: the raised and lowered spatial metrics compose to the spatial projector `χ` (identity on `v^⊥`), the defining relation of an inverse-metric pair on the degenerate hyperplane.

All four results are `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`). The file is registered in `BookProof.lean`; the `BookProof` target builds green. `BookProof/STATUS.md` records this as Wave 72, and this run section was added to `ARISTOTLE_SUMMARY.md` as requested. The out-of-scope `RiemannProof/` directory retains its pre-existing build failures (in `RandomMap.lean`) and was left untouched. All changes are committed and pushed.

# Summary of changes for run 2619d86c-4e5c-49d0-ae0d-56591133bdb0
Continued executing `FORMALIZATION_ROADMAP.md` under its standing directive (mine the next self-contained mathematical claim from `book.tex`), staying off the Hankel–Majorana line as requested.

**New deliverable — `BookProof/ChapterGravityTimeProj.lean` (Wave 71).** From the book chapter *"Diffeomorphisms and gravity"*, §*"Classical Hamiltonian"*: the spatial projector `χ_a{}^b = δ_a{}^b + v_a v^b` (established in a prior wave) onto the spatial hyperplane `v^⊥` has a complement `Π = δ − χ = −v⊗v♭`, the temporal projector onto the 1-dimensional time direction spanned by the globally defined unit timelike vector `v` (`minkSq v = -1`). Reusing `metric`, `lower`, `minkSq`, `spatialProj` from the existing `ChapterGravityProjector`, the file proves and I verified:
- `spatialProj_add_timeProj` — completeness `χ + Π = δ`;
- `timeProj_idempotent` — `Π² = Π` (a genuine projector);
- `trace_timeProj` — `tr Π = 1` (rank 1, complementary to `tr χ = 3`);
- `timeProj_mulVec_self` — `Π v = v` (`v` spans the image of `Π`);
- `spatialProj_mul_timeProj` / `timeProj_mul_spatialProj` — `χ·Π = 0` and `Π·χ = 0` (orthogonal projectors).

All six results are `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`). The file is registered in `BookProof.lean`; the `BookProof` target builds green. `BookProof/STATUS.md` records this as Wave 71, and `ARISTOTLE_SUMMARY.md` was updated with a new run section as requested.

The out-of-scope `RiemannProof/` directory retains its pre-existing build failures (in `RandomMap.lean`) and was left untouched. All changes are committed and pushed.

# Summary of latest run (Wave 71)
Continued executing `FORMALIZATION_ROADMAP.md` under its standing directive (mine the next self-contained mathematical claim from `book.tex`), staying off the Hankel–Majorana line as requested, and building directly on the previous runs' gravity projector.

**New deliverable — `BookProof/ChapterGravityTimeProj.lean` (Wave 71).** From the book chapter *"Diffeomorphisms and gravity"*, §*"Classical Hamiltonian"*: the mixed spatial projector `χ_a{}^b = δ_a{}^b + v_a v^b` (Wave 69) onto the spatial hyperplane `v^⊥` has a complement `Π = δ − χ = −v⊗v♭`, the **temporal projector** onto the `1`-dimensional time direction spanned by the globally defined unit timelike vector `v` (`minkSq v = -1`). Reusing `metric`, `lower`, `minkSq`, `spatialProj` from the existing `ChapterGravityProjector`, the file proves:
- `spatialProj_add_timeProj` — completeness `χ + Π = δ` (the identity split);
- `timeProj_idempotent` — `Π² = Π` (a genuine projector);
- `trace_timeProj` — `tr Π = 1` (rank `1`, complementary to `tr χ = 3`);
- `timeProj_mulVec_self` — `Π v = v` (`v` spans the image of `Π`);
- `spatialProj_mul_timeProj` / `timeProj_mul_spatialProj` — `χ·Π = 0` and `Π·χ = 0` (the two projectors are orthogonal).

All six results are `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`). The file is registered in `BookProof.lean`; `lake build BookProof` is green. `BookProof/STATUS.md` records this as Wave 71.

The out-of-scope `RiemannProof/` directory retains its pre-existing build failures (in `RandomMap.lean`) and was left untouched. All changes are committed and pushed.

# Summary of changes for run 1930b2f9-ea85-4b8e-84ad-82ad8abb633e
Continued executing `FORMALIZATION_ROADMAP.md` under its standing directive (mine the next self-contained mathematical claim from `book.tex`), staying off the Hankel–Majorana line as requested, and building directly on the previous run's gravity projector.

**New deliverable — `BookProof/ChapterGravityMetric.lean` (Wave 70).** From the book chapter *"Diffeomorphisms and gravity"*, §*"Classical Hamiltonian"*: lowering the free index of the mixed projector `χ_a{}^b = δ_a{}^b + v_a v^b` with the mostly-plus Minkowski metric `η = diag(−1,1,1,1)` yields the associated `(0,2)` induced spatial metric `h_{ab} = η_{ab} + v_a v_b`, the (degenerate) Riemannian metric on the spatial hyperplane orthogonal to the globally defined unit timelike vector `v` (`minkSq v = -1`). Reusing `metric`, `lower`, `minkSq`, `spatialProj` from the existing `ChapterGravityProjector`, the file proves:
- `spatialMetric_symm` — `h` is symmetric;
- `spatialMetric_eq_metric_mul_proj` — the tensor identity `h = η · χ`;
- `spatialMetric_mulVec_self` — `h v = 0` (the kernel is the time direction);
- `reverse_cauchy_schwarz` — the reverse Cauchy–Schwarz inequality for the timelike vector `v`, `⟨x,v⟩_η² ≥ −⟨x,x⟩_η`, proved via an explicit sum-of-squares certificate;
- `spatialMetric_quadForm_nonneg` (headline) — `0 ≤ xᵀ h x` for all `x`;
- `spatialMetric_posSemidef` — the packaged `Matrix.PosSemidef` statement (positive definite on the spatial hyperplane).

All six results are `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`). The file is registered in `BookProof.lean`; `lake build BookProof` is green (8122 jobs). `BookProof/STATUS.md` records this as Wave 70, and `ARISTOTLE_SUMMARY.md` was updated with a new run section per your request.

The out-of-scope `RiemannProof/` directory retains its pre-existing build failures (in `RandomMap.lean`) and was left untouched. All changes are committed and pushed.

# Summary of latest run
Continued executing `FORMALIZATION_ROADMAP.md` under its standing directive (mine the next self-contained mathematical claim from `book.tex`), and per your instruction stayed off the Hankel–Majorana line. I added one new fully-proved deliverable group (`sorry`-free and `axiom`-free — only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`), building directly on the previous run's gravity projector.

**New file `BookProof/ChapterGravityMetric.lean` (Wave 70)** — Book chapter *"Diffeomorphisms and gravity"*, §*"Classical Hamiltonian"* (line ~8091). Lowering the free index of the Wave-69 mixed projector `χ_a{}^b = δ_a{}^b + v_a v^b` with the mostly-plus Minkowski metric `η = diag(−1,1,1,1)` gives the associated `(0,2)` **induced spatial metric** `h_{ab} = η_{ab} + v_a v_b`, the (degenerate) Riemannian metric on the spatial hyperplane `v^⊥` orthogonal to the globally defined unit timelike vector `v` (`minkSq v = -1`). The file reuses `metric`, `lower`, `minkSq`, `spatialProj` from `ChapterGravityProjector` and proves:
- `spatialMetric_symm` — `h` is symmetric (`hᵀ = h`);
- `spatialMetric_eq_metric_mul_proj` — the tensor identity `h = η · χ`;
- `spatialMetric_mulVec_self` — `h v = 0` (the kernel is the time direction);
- `reverse_cauchy_schwarz` — the reverse Cauchy–Schwarz inequality for the timelike `v`: `⟨x,v⟩_η² ≥ −⟨x,x⟩_η` (via an explicit sum-of-squares certificate);
- `spatialMetric_quadForm_nonneg` — **headline**: `0 ≤ xᵀ h x` for all `x`;
- `spatialMetric_posSemidef` — the packaged `Matrix.PosSemidef` (positive definite on `v^⊥`).

The file is registered in `BookProof.lean` and recorded as Wave 70 in `BookProof/STATUS.md`. `lake build BookProof` is green (8122 jobs). The out-of-scope `RiemannProof/` directory retains its pre-existing build failures (in `RandomMap.lean`) and was left untouched. All changes are committed and pushed.

# Summary of changes for run c478357a-4ad7-4b44-88f2-f1f6d4dc0472
Continued executing `FORMALIZATION_ROADMAP.md` by following its standing directive to mine the next self-contained mathematical claims from `book.tex`. I added two new deliverable groups, both fully proved (`sorry`-free and `axiom`-free — only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`).

1. `BookProof/ChapterSphericalBessel2.lean` (§A.5 "Hankel–Majorana Transform") extends the base `ChapterSphericalBessel` module (which had `j₀, j₁, j₂`) one order further to the spherical Bessel function `j₃`: the closed form `sj3`, the derivative of `j₂` (`deriv_sj2`), that the Rayleigh formula reproduces `j₃` (`sbessel_three_eq`), the three-term recurrence `j₁ + j₃ = (5/r)·j₂` (`sbessel_recurrence_123`), the differentiation law `d/dr j₂ = j₁ − (3/r)·j₂` (`deriv_recurrence_sj2`), and the `l = 3` ODE `r² j'' + 2 r j' + (r² − 12) j = 0` (`sj3_satisfies_ode`).

2. Per your instruction to leave the Hankel–Majorana line, I moved to a different chapter. `BookProof/ChapterGravityProjector.lean` formalizes the spatial projector `χ = δ + v⊗v` from the "Diffeomorphisms and gravity" chapter (§"Classical Hamiltonian"), relative to a unit timelike vector `v` (`v·v = −1`) in the Minkowski metric `diag(−1,1,1,1)`. Modelling the mixed tensor as a 4×4 real matrix, it proves χ annihilates `v` (`spatialProj_mulVec_self`), is idempotent `χ² = χ` (`spatialProj_idempotent`), has trace 3 (`trace_spatialProj`, a rank-3 projector), and acts as the identity on `v^⊥` (`spatialProj_mulVec_of_orthogonal`) — i.e. it is the orthogonal projection onto the spatial hyperplane.

Both files are registered in `BookProof.lean` and recorded as Waves 68–69 in `BookProof/STATUS.md`; `ARISTOTLE_SUMMARY.md` was updated with a new run section. `lake build BookProof` is green (8121 jobs). The out-of-scope `RiemannProof/` directory still has its pre-existing build failures (in `RandomMap.lean`) and was left untouched. All changes are committed and pushed.

# Summary of latest run
Continued executing `FORMALIZATION_ROADMAP.md` by following its standing directive to mine the next self-contained mathematical claims from `book.tex`, and added two new deliverable groups (both `sorry`-free and `axiom`-free, only `propext`/`Classical.choice`/`Quot.sound`).

**New file `BookProof/ChapterSphericalBessel2.lean`** (Wave 68) extends the base `BookProof/ChapterSphericalBessel.lean` module — which established the spherical Bessel functions of the first kind `j₀, j₁, j₂` via the Rayleigh formula and the `l = 0` ODE — one order further to `j₃` (§A.5 *"Hankel–Majorana Transform"*). It proves the closed form `sj3`, the first derivative of `j₂` (`deriv_sj2`), that the Rayleigh formula reproduces `j₃` (`sbessel_three_eq`), the three-term recurrence `j₁ + j₃ = (5/r)·j₂` (`sbessel_recurrence_123`), the differentiation law `d/dr j₂ = j₁ − (3/r)·j₂` (`deriv_recurrence_sj2`), and that `j₃` solves the `l = 3` spherical Bessel ODE `r² j'' + 2 r j' + (r² − 12) j = 0` (`sj3_satisfies_ode`).

**New file `BookProof/ChapterGravityProjector.lean`** (Wave 69) formalizes the spatial projector `χ_a{}^b = δ_a{}^b + v_a v^b` from the chapter *"Diffeomorphisms and gravity"*, §*"Classical Hamiltonian"* (`book.tex` line ~8091), defined relative to a unit timelike vector `v` (`v·v = −1`) in the mostly-plus Minkowski metric `η = diag(−1,1,1,1)`. Modelling the `(1,1)` tensor as an explicit `4×4` real matrix, it proves that `χ` annihilates `v` (`spatialProj_mulVec_self`), is idempotent `χ² = χ` (`spatialProj_idempotent`), has trace `3` (`trace_spatialProj`, a rank-`3` projector = the spatial slice), and acts as the identity on `v^⊥` (`spatialProj_mulVec_of_orthogonal`) — i.e. it is the orthogonal projection onto the spatial hyperplane.

Both files are registered in `BookProof.lean` and recorded as Waves 68–69 in `BookProof/STATUS.md`. `lake build BookProof` is green (8121 jobs). As before, the out-of-scope `RiemannProof/` directory still fails to build (pre-existing `RandomMap.lean` errors/sorries) and was left untouched. All changes are committed and pushed.

# Summary of changes for run 5a3a2b26-2b25-4a6b-9bab-7e1a2283ba6f
Continued executing `FORMALIZATION_ROADMAP.md`. Its numbered queue and bonus chapters were already complete, so — following the roadmap's standing directive to mine the next self-contained mathematical claim from `book.tex` — I added one new deliverable group and verified everything builds cleanly.

**New file `BookProof/ChapterNoUniformCountable.lean`** formalizes the foundational assertion opening §10 of the wave-function-parametrization chapter ("There is no uniform countable measure. Thus, the rationals are not enough for Probability Theory."). This is distinct from the infinite-dimensional Lebesgue result already in `BookProof/ChapterNoLebesgue.lean`. Two theorems, both proved:
- `no_uniform_countable_measure` — on a countably infinite measurable space with measurable singletons, no probability measure assigns a common mass `c` to every singleton (total mass would be `∑' _, c`, which is `0` when `c = 0` and `⊤` when `c ≠ 0`, never `1`).
- `no_uniform_measure_nat` — the concrete `ℕ` instance ("the rationals are not enough").

The file is registered in `BookProof.lean` and recorded as Wave 67 in `BookProof/STATUS.md`. It is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`), and `lake build BookProof` is green (8119 jobs). `ARISTOTLE_SUMMARY.md` was updated with a new run section as requested.

Scope note (unchanged): the full-project build still fails only inside `RiemannProof/` (pre-existing `RandomMap.lean` elaboration errors and other sorries), which the roadmap explicitly marks out of scope; those were left untouched. All in-scope `BookProof` work builds green and is axiom-clean. All changes are committed and pushed.

# Summary of changes for run da12e45d-52ae-4342-8473-a5e3f3254ab0
Continued executing `FORMALIZATION_ROADMAP.md`. The numbered queue (N1–N14) and prior bonus chapters were already complete, so following the roadmap's standing directive I mined the next self-contained mathematical claim from `book.tex` and added one new deliverable group.

**New file `BookProof/ChapterE4.lean` — "Euler's formula for a generic phase-space"** (from the chapter *"Wave-function collapse versus Euler's formula"*, `book.tex` §"Euler's formula for a generic phase-space"). This extends the finite 4-state density matrix of `ChapterE3` to a countable orthonormal basis via the recursion `vₙ = cos(θₙ)·lₙ + sin(θₙ)·vₙ₊₁`, bridging `ChapterE2` (stick-breaking Born probabilities) and `ChapterE3` (finite density matrix). Modeled with index space `ℕ`, standard basis `eₖ = Pi.single k 1`, and a finite-support recursion `wave θ s d`; outer products written entrywise. Deliverables (all proved):
- `density_recursion` — headline: the entrywise density-matrix recursion `vₛ vₛ† = cₛ² eₛ eₛ† + sₛ² vₛ₊₁ vₛ₊₁† + cₛ sₛ (eₛ vₛ₊₁† + vₛ₊₁ eₛ†)`;
- `wave_eq_zero_of_lt` — the tail is supported on indices `≥ s` (orthogonality);
- `wave_self_succ` — leading component is `cos θₛ`;
- `cross_diag_zero` — the Euler cross term has vanishing diagonal;
- `diag_collapse` — "taking the real part" gives the classical stick-breaking recursion `(vₛ)ᵢ² = cₛ²(eₛ)ᵢ² + sₛ²(vₛ₊₁)ᵢ²`;
- `cond_prob_sum` — `cₛ² + sₛ² = 1`;
- `wave_prob_sum` — total probability is conserved: `∑ i ∈ Icc s (s+d), (vₛ)ᵢ² = 1`.

The file is registered in `BookProof.lean`, is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`), and `lake build BookProof` is green (8118 jobs). `BookProof/STATUS.md` records this as Wave 66, and `ARISTOTLE_SUMMARY.md` was updated with a new run section. All changes are committed and pushed.

Scope note: the full-project build still fails only inside `RiemannProof/` (pre-existing elaboration errors and sorries), which the roadmap explicitly marks out of scope; those were left untouched. All in-scope `BookProof` work builds green and is axiom-clean.

# Summary of changes — Euler's formula for a *generic* phase-space (`ChapterE4`)

Continued executing `FORMALIZATION_ROADMAP.md`. Its numbered queue (N1–N14) and
the bonus chapters were already complete and verified, so — following the
roadmap's standing directive to mine the next self-contained mathematical claim
from `book.tex` — this pass added one new deliverable group.

**New file `BookProof/ChapterE4.lean` — "Euler's formula for a generic
phase-space"** (from the chapter *"Wave-function collapse versus Euler's
formula"*, `book.tex` §"Euler's formula for a generic phase-space", line ~3565).
The book extends the finite 4-state density matrix of `ChapterE3` to a
**countable** orthonormal basis `{lₙ}` by the recursion
`vₙ = cos(θₙ)·lₙ + sin(θₙ)·vₙ₊₁`, and asserts that collapse of the wave-function
for a generic phase-space is a *recursion of collapses of 2-dimensional real
wave-functions*. This bridges the two prior chapters — `ChapterE2` (stick-breaking
Born *probabilities*) and `ChapterE3` (finite density matrix). Model: countable
index space `ℕ`, orthonormal basis the standard basis `eₖ = Pi.single k 1`, and a
finite-support recursion `wave θ s d`; outer products `v v†` written entrywise as
`v i * v j`. Deliverables:
- `density_recursion` — headline: the entrywise density-matrix recursion
  `vₛ vₛ† = cₛ² eₛ eₛ† + sₛ² vₛ₊₁ vₛ₊₁† + cₛ sₛ (eₛ vₛ₊₁† + vₛ₊₁ eₛ†)` (pure algebra);
- `wave_eq_zero_of_lt` — the tail `vₛ` is supported on indices `≥ s` (orthogonality);
- `wave_self_succ` — the leading component is `cos θₛ`;
- `cross_diag_zero` — the Euler cross term `eₛ vₛ₊₁†` has a vanishing diagonal;
- `diag_collapse` — "taking the real part": the diagonal obeys the classical
  stick-breaking recursion `(vₛ)ᵢ² = cₛ² (eₛ)ᵢ² + sₛ² (vₛ₊₁)ᵢ²`;
- `cond_prob_sum` — `cₛ² + sₛ² = 1`, the book's
  `P(s | s or above) + P(s+1 or above | s or above) = 1`;
- `wave_prob_sum` — total probability is conserved:
  `∑ i ∈ Icc s (s+d), (vₛ)ᵢ² = 1` (the trace of the density matrix is `1`).

The file is registered in `BookProof.lean`, is `sorry`-free and `axiom`-free
(only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`),
and `lake build BookProof` is green (8118 jobs). `BookProof/STATUS.md` records
this as Wave 66. All changes are committed and pushed.

Scope note: the full-project build still fails only inside `RiemannProof/`
(pre-existing elaboration errors and sorries), which the roadmap explicitly marks
out of scope; those were left untouched. All in-scope `BookProof` work builds
green and is axiom-clean.

# Summary of changes for run 9b8b98e2-4abc-48f0-8149-e647a2850f3a
Continued executing `FORMALIZATION_ROADMAP.md`. The numbered queue (N1–N14) and prior bonus chapters were already complete, so — following the roadmap's standing directive to mine the next self-contained mathematical claim from `book.tex` — this pass added one new deliverable group.

**New file `BookProof/ChapterE3.lean` — "Euler's formula for the density matrix"** (from the chapter *"Wave-function collapse versus Euler's formula"*, `book.tex` §"Euler's formula for a phase-space with 4 states"). The book writes each wave-function collapse step of a real normalized wave-function `φ = cos θ·l + sin θ·w` as an "Euler's formula for the density matrices": the rank-1 projector `φφ†` decomposes with a `cos(2θ) + J sin(2θ)` structure, `J := l w† − w l†` acting as the imaginary unit on `span{l,w}`. Earlier chapters covered only the 2-state clock (`ChapterE`) and the stick-breaking Born probabilities (`ChapterE2`); this density-matrix identity was not yet formalized. Deliverables (column vectors `l w : Fin n → ℝ`, outer products via `Matrix.vecMulVec`):
- `euler_density_matrix` — headline: `φφ† = ½(l l†+w w†) + ½cos(2θ)(l l†−w w†) + ½sin(2θ)(l w†+w l†)`, a double-angle identity needing no orthonormality;
- `eulerJ_antisymm` — `J` is antisymmetric (`Jᵀ = −J`);
- `eulerJ_sq` — under orthonormality `J² = −(l l†+w w†)`, so `J` behaves like `i`;
- `euler_density_diag_real` — "taking the real part": the l-diagonal entry is `cos²θ = ½+½cos(2θ)`, the book's conditional probability;
- `euler_density_isIdempotent` — under orthonormality `φφ†` is a genuine rank-1 projector (pure-state density matrix).

The file is registered in `BookProof.lean`, is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`), and `lake build BookProof` is green (8117 jobs). `BookProof/STATUS.md` records this as Wave 65 and `ARISTOTLE_SUMMARY.md` was updated with a new run section. All changes are committed and pushed.

Scope note: the full-project build still fails only inside `RiemannProof/` (pre-existing elaboration errors and sorries), which the roadmap explicitly marks out of scope; those were left untouched. All in-scope `BookProof` work builds green and is axiom-clean.

# Summary of changes — Euler's formula for the density matrix (`ChapterE3`)
Continued executing `FORMALIZATION_ROADMAP.md`. Its numbered queue (N1–N14) and the bonus chapters were already complete and verified, so — following the roadmap's standing directive to mine the next self-contained mathematical claim from `book.tex` — this pass landed one new deliverable group.

**New chapter `BookProof/ChapterE3.lean` — "Euler's formula for the density matrix."** The chapter *"Wave-function collapse versus Euler's formula"* (`book.tex` §"Euler's formula for a phase-space with 4 states", line ~3478) writes each wave-function collapse step of a real normalized wave-function `φ = cos θ · l + sin θ · w` as an *"Euler's formula for the corresponding density matrices"*: the rank-1 projector `φφ†` decomposes with a `cos(2θ) + J sin(2θ)` structure, with `J := l w† − w l†` acting as the imaginary unit on `span{l, w}`, and "collapse = taking the real part" being the `cos(2θ)` diagonal part. Earlier chapters covered only the 2-state clock (`ChapterE`) and the stick-breaking Born *probabilities* (`ChapterE2`); the density-matrix identity itself was not yet formalized. Modeling column vectors as `l w : Fin n → ℝ` with outer products via `Matrix.vecMulVec`:

- `euler_density_matrix` — headline: `φφ† = ½(l l† + w w†) + ½ cos(2θ)(l l† − w w†) + ½ sin(2θ)(l w† + w l†)`, a purely algebraic double-angle identity requiring no orthonormality.
- `eulerJ_antisymm` — the imaginary unit `J = l w† − w l†` is antisymmetric (`Jᵀ = −J`).
- `eulerJ_sq` — under orthonormality `J² = −(l l† + w w†)`, so `J` squares to minus the identity of the subspace: it genuinely behaves like `i`.
- `euler_density_diag_real` — "taking the real part": the `l`-diagonal entry of `φφ†` is `cos²θ = ½ + ½ cos(2θ)`, the book's conditional probability.
- `euler_density_isIdempotent` — under orthonormality `φφ†` is a genuine rank-1 projector (`φφ† · φφ† = φφ†`), the density matrix of a pure state.

The file is registered in `BookProof.lean`. It is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`), and `lake build BookProof` is green (8117 jobs). `BookProof/STATUS.md` records this as Wave 65. All changes are committed and pushed.

Scope note: the full-project build still fails only inside `RiemannProof/` (pre-existing elaboration errors and `sorry`s), which the roadmap explicitly marks out of scope; those are untouched. All in-scope `BookProof` work builds green and is axiom-clean.

# Summary of changes for run e5591ee6-8bbb-4c21-8f6b-e94a201d62c2
Continued executing `FORMALIZATION_ROADMAP.md`. Its numbered queue (N1–N14) and the earlier bonus chapters were already complete and verified, so — following the roadmap's standing directive to mine the next self-contained mathematical claim from `book.tex` — this pass landed one new deliverable group.

**New chapter `BookProof/ChapterNoLebesgue.lean` — "there is no infinite-dimensional Lebesgue measure."** The Yang–Mills chapter (book line ~6660) and the gauge chapters (line 2128) repeatedly invoke, as a load-bearing premise for the free-field / gauge-variant probability-measure framework, the classical fact that a translation-invariant "Lebesgue-like" measure on an infinite-dimensional space cannot exist. This is now formalized and proved for a real normed space `E`:

- `measure_ball_eq_measure_ball_zero` — a translation-invariant measure gives every ball the mass of the concentric origin ball.
- `measure_ball_zero_eq_zero` — core estimate: if `E` is infinite-dimensional and the measure is translation-invariant and finite on bounded sets, every origin ball has measure 0 (proved by rescaling a bounded 1-separated sequence to obtain infinitely many disjoint balls inside one bounded set).
- `eq_zero_of_isAddLeftInvariant_of_finite_on_bounded` — headline: the only translation-invariant Borel measure finite on bounded sets is the zero measure.
- `not_exists_nonzero_isAddLeftInvariant_finite_on_bounded` — existence restatement.
- `not_finite_on_bounded_of_isAddLeftInvariant_of_pos_ball` — contrapositive: a translation-invariant measure positive on some ball cannot be finite on all bounded sets.

The file is registered in `BookProof.lean`. It is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`, confirmed via `#print axioms`), and `lake build BookProof` is green. `BookProof/STATUS.md` records this as Wave 64, and `ARISTOTLE_SUMMARY.md` was updated with a new run section as requested. All changes are committed and pushed.

Scope note: the full-project build still fails only inside `RiemannProof/` (pre-existing elaboration errors and `sorry`s), which the roadmap explicitly marks out of scope; those are untouched. All in-scope `BookProof` work builds green and is axiom-clean.

# Summary of changes for run 622a092a-24b8-4eba-903a-f5974b99b950
Executed and verified `FORMALIZATION_ROADMAP.md`.

The roadmap's entire work-package queue (N1–N14) was already completed by prior waves; my task this pass was to execute the remaining HYGIENE step of the roadmap and independently verify the in-scope deliverables rather than trust the status notes. Verification results:

- `lake build BookProof` is green (8115 jobs, warnings only) — the roadmap's stated definition of done.
- The `BookProof` library is fully `sorry`-free and `admit`-free (grep over all `BookProof/*.lean` returns 0 code-level occurrences).
- `#print axioms` spot-checks on the roadmap's named headline theorems all report only the allowed axioms `propext`, `Classical.choice`, `Quot.sound`:
  - `ChapterF4.misraGries_bound`, `ChapterF4.countsketch_unbiased`
  - `ChapterH4.sirk_error_bound`, `ChapterH2.sirk_error_bound_of_crouzeix`
  - `ChapterHolomorphic.cauchyRiemann_iff_analyticOn`
  - `ChapterB4.no_pure_state_satisfies_both`
  - `ChapterMajoranaFourier.majoranaFourier_boostBlock_unitary`
- The git working tree is clean; all work is already committed, so there was nothing new to commit or push.

Scope note: the full-project `lake build` fails only inside `RiemannProof/` (specifically `RiemannProof/RandomMap.lean` has elaboration errors and other files contain `sorry`s). These belong to the ODE / P≠NP / Riemann-Hypothesis route, which `FORMALIZATION_ROADMAP.md` explicitly marks "Excluded by author" / out of scope, so they are not roadmap deliverables. All in-scope roadmap work (the `BookProof` library) is complete, builds green, and is axiom-clean. No new package has been promoted below the roadmap's queue, so there is no further in-scope work to perform.

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

# Summary of changes for the latest run — "Do the next steps"

Continued executing `FORMALIZATION_ROADMAP.md`. With the roadmap's numbered
queue (N1–N14) and the earlier bonus chapters all complete and verified, this
pass followed the roadmap's standing directive to *mine the next self-contained
mathematical claim from `book.tex`* and formalize it, landing one new deliverable
group.

**New chapter: `BookProof/ChapterNoLebesgue.lean` — there is no infinite-dimensional Lebesgue measure.**
The Yang–Mills chapter (`book.tex` line ~6660) and the gauge chapters
(line 2128) repeatedly invoke, as a load-bearing premise for the free-field /
gauge-*variant* probability-measure framework, the classical fact that a
translation-invariant "Lebesgue-like" measure on an infinite-dimensional space
cannot exist ("… it is proved that in rigor such infinite-dimensional Lebesgue
measure cannot exist"). This is now formalized and proved for a real normed
space `E`:

- `measure_ball_eq_measure_ball_zero` — a translation-invariant
  (`IsAddLeftInvariant`) measure assigns every ball the mass of the concentric
  origin ball.
- `measure_ball_zero_eq_zero` — core estimate: if `E` is infinite-dimensional and
  `μ` is translation-invariant and finite on bounded sets, every origin ball has
  measure `0` (via a rescaled bounded `1`-separated sequence, Mathlib's
  `exists_seq_norm_le_one_le_norm_sub`, giving infinitely many disjoint balls in
  one bounded set).
- `eq_zero_of_isAddLeftInvariant_of_finite_on_bounded` — headline: on an
  infinite-dimensional real normed space the only translation-invariant Borel
  measure finite on bounded sets is the zero measure.
- `not_exists_nonzero_isAddLeftInvariant_finite_on_bounded` — existence
  restatement.
- `not_finite_on_bounded_of_isAddLeftInvariant_of_pos_ball` — contrapositive used
  in the book: a translation-invariant measure positive on some ball cannot be
  finite on all bounded sets.

The file is registered in `BookProof.lean`, is `sorry`-free and `axiom`-free
(only `propext`, `Classical.choice`, `Quot.sound`, confirmed by
`#print axioms`), and `lake build BookProof` is green. `BookProof/STATUS.md`
records this as Wave 64.

Scope note (unchanged): the full-project build still fails only inside
`RiemannProof/` (`RandomMap.lean` elaboration errors and other `sorry`s), which
`FORMALIZATION_ROADMAP.md` explicitly marks out of scope ("Excluded by author");
those are not roadmap deliverables. All in-scope `BookProof` work builds green
and is axiom-clean.

# Summary of changes — There is no uniform countable measure (`ChapterNoUniformCountable`)

Continued executing `FORMALIZATION_ROADMAP.md`. Its numbered queue (N1–N14) and
the bonus chapters were already complete and verified, so — following the
roadmap's standing directive to mine the next self-contained mathematical claim
from `book.tex` — I added one new deliverable group.

**New file `BookProof/ChapterNoUniformCountable.lean`** — from §10 of the
Wave-function-parametrization chapter, *"Ensemble forecasting allows the
approximation of a non-linear infinite-dimensional model …"* (`book.tex`
line ~2005), whose opening assertion is:

> "There is no uniform countable measure. Thus, the rationals are not enough for
> Probability Theory. A standard probability space (which has countable and
> continuous measures) seems irreducible."

This measure-theoretic fact is distinct from the *infinite-dimensional Lebesgue*
non-existence result already formalized in `ChapterNoLebesgue`, and had not been
formalized. Deliverables (both proved):

- `no_uniform_countable_measure` — the headline: on a countably infinite
  measurable space with measurable singletons there is no probability measure
  assigning a common mass `c` to every singleton. Proof: total mass equals the
  sum of the singleton masses (`Measure.tsum_indicator_apply_singleton`), i.e.
  `∑' _, c`, which is `0` when `c = 0` and `⊤` when `c ≠ 0`
  (`ENNReal.tsum_const_eq_top_of_ne_zero`) — never `1`.
- `no_uniform_measure_nat` — the book's concrete `ℕ` instance ("the rationals
  are not enough"): no probability measure on `ℕ` is uniform on singletons.

The file is registered in `BookProof.lean`, is `sorry`-free and `axiom`-free
(only `propext`, `Classical.choice`, `Quot.sound`, confirmed via
`#print axioms`), and `lake build BookProof` is green (8119 jobs).
`BookProof/STATUS.md` records this as Wave 67.

Scope note (unchanged): the full-project build still fails only inside
`RiemannProof/` (`RandomMap.lean` elaboration errors and other `sorry`s), which
`FORMALIZATION_ROADMAP.md` explicitly marks out of scope; those were left
untouched. All in-scope `BookProof` work builds green and is axiom-clean.
