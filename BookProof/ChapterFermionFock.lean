import BookProof.ChapterFermionFock.Part1
import BookProof.ChapterFermionFock.Part2
import BookProof.ChapterFermionFock.Part3

/-!
# Chapter FermionFock — the fermionic (CAR) Fock space and its second quantization

`CONSOLIDATED_PLAN.md` §10.6.2 item 3 asks for the missing **fermionic half** of
the quantum-gravity second quantization: the project builds the bosonic Fock
space `Γˢ` over a one-particle core (`ChapterFockSecondQuantization`, occupation
numbers `Conf = ℕ →₀ ℕ`), but the antisymmetric factor `Γᵃ` — the ghost/fermion
sector, whose canonical **anticommutation** relations `ChapterBRSTNilpotent`
carries as the abstract hypothesis `GhostCAR` — is not constructed anywhere.

This chapter constructs it, in exactly the style of the bosonic one.

## Deliverables

* `FConf`, `FermiAlg`, `FermiFock` — a fermionic configuration is the **finite
  set of occupied modes**, the algebraic Fock space is `FConf →₀ ℂ`, and the
  Fock space is `ℓ²(FConf)`.
* `fsign` — the Jordan–Wigner sign `(−1)^{#\{i ∈ S : i < j\}}`, and the sign
  calculus it obeys (`fsign_mul_self`, `fsign_erase`, `fsign_insert_self`,
  `fsign_insert_of_ne`).
* `creF`, `annF` — creation and annihilation, with their coordinate formulas
  `creF_apply`, `annF_apply`.
* **The canonical anticommutation relations**, all four of them:
  `car_annF_creF_self` (`{c_j, c_j†} = 1`), `car_creF_creF` (`{c_j†, c_k†} = 0`,
  including `creF_creF_self`: `(c_j†)² = 0`, the Pauli principle),
  `car_annF_annF` (`{c_j, c_k} = 0`) and `car_annF_creF_of_ne`
  (`{c_j, c_k†} = 0` for `j ≠ k`).
* `inner_creF_left` — creation and annihilation are formal adjoints of each
  other on the finite-occupation domain.
* `dGammaF`, `dGammaOpF` — the fermionic second quantization
  `dΓᵃ(A) = Σ_{j,k} ⟪e_j, A e_k⟫ c_j† c_k`, its symmetry
  (`dGammaOpF_symmetricOn`) and positivity (`dGammaOpF_quadForm_nonneg`) for a
  Hermitian, positive semidefinite one-particle matrix.
* `dGammaF_friedrichs_extension`, `secondQuantizationF_friedrichs` — the
  fermionic second quantization of any symmetric positive one-particle operator
  has a positive self-adjoint (Friedrichs) extension …
* `dGammaF_hashimoto_selects`, `secondQuantizationF_hashimoto_selects` — … and
  the Hashimoto/SIRK shift-invert limit selects exactly that extension, with the
  Galerkin truncations converging strongly and in the resolvent sense.
* `parityF` — the fermion-number parity `(−1)^{N_f}`, the `ℤ₂` grading
  operator: an involution (`parityF_involutive`) that anticommutes with both
  creation and annihilation (`parityF_creF`, `parityF_annF`).
* `ghostCAR_creF_annF` — **the abstract ghost relations are realized**: the
  operators built here satisfy `BookProof.BRSTNilpotent.GhostCAR`, so the BRST
  chapter's hypotheses are not vacuous — and `brst_charge_nilpotent_fermiFock`
  is the resulting concrete nilpotency `Q² = 0`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/
