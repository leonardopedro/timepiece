# Executing `cftproof.md`: Euclidean 4D CFT → 3D CFT

This note records what was built for `timepiece/cftproof.md`, module by module, with the
distinction that matters for the MM0 pipeline: **what is a theorem**, and **what is boundary**.

No declaration in the nine new modules contains `sorry`; every statement is proved, and every
statement that could not be proved is *stated as a hypothesis* with the reason recorded in the
module docstring, not silently assumed.

## Modules

| Plan phase | Module | Contents |
|---|---|---|
| 1.1 | `BookProof/EuclideanFock4D/CoreBasis.lean` | `euclideanHermiteBasis4D` (= corpus `hermiteMvBasis` at `d = 4`), orthonormality, totality, the `ℕ`-enumerated `euclideanHermiteNet4D`, the colour basis |
| 1.2 | `BookProof/EuclideanFock4D/MehlerMeasure.lean` | `mehlerMeasure4D := gaussianE 4`, `mehler4D_O4_invariant`, `sphereUniform4D` and its `O(4)` invariance |
| 2.1 | `BookProof/BalabanRG/MultiscaleSpace.lean` | `Sector k`, `FTotal = ⊕_k ℱ_k` as an `ℓ²` sum, `rgOnTotal`, `rgOnTotal_norm_le`, `psiSeq` |
| 2.2 | `BookProof/BalabanRG/BlockOperator.lean` | `blockConst`, `blockAveragingOp`, **`blockAveragingOp_norm_le` (`‖Q_k‖ ≤ 1`)**, idempotence, image in the coarse subspace |
| 2.3 | `BookProof/BalabanRG/Convergence.lean` | `summable_of_increment_bound`, `psiSeq_has_limit`, `psiSeq_cauchy`, `balaban_rg_convergence` |
| 3.1 | `BookProof/ReflectionPositivity/Involution.lean` | `timeReflection` on `ℝ⁴` (`θ² = 1`, coordinate formula), **`timeReflection_measure_invariant`**, the lattice cell involution `flipCell`, `fieldReflection` on configurations |
| 3.2 | `BookProof/ReflectionPositivity/HalfSpaceAlgebra.lean` | `PositiveTimeAlgebra`, `CylindricalObservables`, `positiveTimeAlgebra_cylindrical`, `thetaObs` and **`thetaObs_dependsOn_negTime` (`θ : 𝔄₊ → 𝔄₋`)** |
| 3.3 | `BookProof/ReflectionPositivity/Proof.lean` | `osForm`, `IsReflectionPositive`, **`reflection_positivity_continuum`**, `psiSeq_component_tendsto` |
| 4.1 | `BookProof/OSReconstruction/PhysicalSpace.lean` | bilinearity, symmetry, positivity, `osForm_expand`, **Cauchy–Schwarz**, `Radical`, `osForm_well_defined`, `osNorm_triangle` |
| 4.2 | `BookProof/OSReconstruction/Hamiltonian.lean` | `TimeTranslation`, semigroup law, **`osNorm_evolution_antitone`**, `radical_invariant`, `timeEvolution_well_defined` |

## The five statements that carry the mathematics

1. **`blockAveragingOp_norm_le`** — the block-averaging projections are contractions.  Proved as
   a property of the orthogonal projection onto block-constant fields
   (`Submodule.norm_starProjection_apply_le`).
2. **`rgOnTotal_norm_le` / `norm_rgOnTotal_le`** — the total-space RG step is a contraction,
   `‖Q‖ ≤ 1`, via the `ℓ²` norm computation with the pointwise bound `‖Q_k x‖ ≤ ‖x‖`.
3. **`balaban_rg_convergence`** — a geometric bound on the increments of `Ψ_N` makes the sequence
   converge in the complete space `F_total`, with the limit exhibited as
   `Ψ₀ + Σ (Ψ_{n+1} − Ψ_n)`.
4. **`reflection_positivity_continuum`** — reflection positivity passes to the continuum limit
   along pointwise convergence, and `psiSeq_component_tendsto` supplies that convergence from the
   Phase 2 limit.  This is the plan's "the limit is reflection positive".
5. **`osForm_cauchy_schwarz` + `Radical` + `osForm_well_defined`** — the OS form of a reflection
   positive functional is an inner product modulo its radical; Cauchy–Schwarz is derived from
   positivity by minimising `t ↦ ⟨F + tG, F + tG⟩`.

## Boundary (recorded, never assumed)

* **Fock space, colour factor, `S^∞`.**  Mathlib has no symmetric Fock space and no Hilbert tensor
  product; `ℱ_k` is therefore modelled by its one-particle content, and the `su(N)` factor appears
  only as `CoreBasis.colourBasis`.  The `S^∞` projective limit is not built.
* **Scale measures `dγ_k`.**  Only `dγ₀ = mehlerMeasure4D` exists; the pushforward under `Q_k` is
  not constructed.  `θ`'s commutation with `Q_k` is likewise not claimed (see `Involution.lean`).
* **Lattice reflection positivity.**  `ω_N(θF F) ≥ 0` for the Wilson measure is a theorem of the
  literature, not a Lean bookkeeping fact; it enters only as the hypothesis `IsReflectionPositive`
  of `reflection_positivity_continuum`.
* **Hilbert-space assembly.**  The fields of `PreInnerProductSpace.Core` are proved
  (`osForm_symm'`, `osForm_self_nonneg`, `osForm_add_left`, `osForm_smul_left`) together with the
  descent `osForm_well_defined`, so `InnerProductSpace.ofCore` + `UniformSpace.Completion` finish
  the construction; that assembly, and the functoriality of the construction, are not done here.
* **Spectral theorem / `emergent_hamiltonian_selfAdjoint` / `nonnegative`.**  Requires a strongly
  continuous semigroup on the completed space and the spectral theorem for unbounded self-adjoint
  operators — neither exists in Mathlib.  What is proved is the semigroup law, contractivity in
  the OS norm, and the descent to `𝔄/𝔑`.
* **Phase 5 (beta function, Legendre transform) and Phase 6 (3D CFT).**  Out of scope of this
  execution: they depend on the OS Hilbert space and on estimates about the effective action that
  are not formalized anywhere.

## Reproducing

```bash
cd timepiece
lake build BookProof.EuclideanFock4D.CoreBasis \
           BookProof.EuclideanFock4D.MehlerMeasure \
           BookProof.BalabanRG.MultiscaleSpace \
           BookProof.BalabanRG.BlockOperator \
           BookProof.BalabanRG.Convergence \
           BookProof.ReflectionPositivity.Involution \
           BookProof.ReflectionPositivity.HalfSpaceAlgebra \
           BookProof.ReflectionPositivity.Proof \
           BookProof.OSReconstruction.PhysicalSpace \
           BookProof.OSReconstruction.Hamiltonian
```

The dependencies of the new modules that live outside Mathlib are the corpus chapters
`BookProof.Toolbox.ChapterHermiteProductBasis` (the `L²(ℝᵈ)` Hermite basis) and
`BookProof.Toolbox.PhysHSGaussian` (the Gaussian and sphere measures), both pre-existing and
already imported by `BookProof.lean`.
