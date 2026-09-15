import Mathlib
import BookProof.ChapterFockSecondQuantization
import BookProof.ChapterNavierStokesFockEsa
import BookProof.ChapterStoneBridge
import BookProof.ChapterQuantumGravityFock.Part1

/-!
# The graded (bosonic ⊗ fermionic) Fock space of quantum gravity — Part E

`PLAN_LEAN_SPECIALIST_QG_FLOW.md` Part E (`CONSOLIDATED_PLAN.md` §10.6.2 item 3) asks for
the second quantization of the gauge-fixed gravity Hamiltonian on the book's graded Fock
space

`Γˢ(L²(ℝ⁸⁴ × ℤ₂¹⁹)) ⊗ Γᵃ(L²(ℝ⁸⁴ × ℤ₂¹⁹))`,

the tensor product of a symmetric (bosonic) and an antisymmetric (fermionic, ghost) Fock
space, together with the `ℤ₂`-graded superalgebra of its creation and annihilation
operators.  The bosonic half is a direct reuse of
`BookProof/ChapterFockSecondQuantization.lean` (the Yang–Mills Part F.11 module); the new
content of this module is the **fermionic (CAR) half and the `ℤ₂` grading**.

## What is proved here

* **The fermionic configurations and the Jordan–Wigner sign.**  A fermionic configuration
  is a finite set of occupied modes (`FermConf = Finset ℕ`; the Pauli principle is built
  into the *set*, not imposed), and `jwSign j α = (−1)^{#\{i ∈ α : i < j\}}` is the sign
  that orders the mode `j` against the already occupied lower modes.
* **The ladder operators** `fermAnn j`, `fermCre j` on the algebraic fermionic Fock space
  `FermAlg = FermConf →₀ ℂ`, with their coordinate formulas `fermAnn_apply`,
  `fermCre_apply`, and the **canonical anticommutation relations** (E.3)
  * `car_fermAnn_fermCre` — `{ψ_j, ψ_j†} = 1`;
  * `car_fermAnn_fermCre_of_ne` — `{ψ_j, ψ_k†} = 0` for `j ≠ k`;
  * `car_fermAnn_fermAnn`, `car_fermCre_fermCre` — `{ψ_j, ψ_k} = {ψ_j†, ψ_k†} = 0`;
  * `fermAnn_comp_self`, `fermCre_comp_self` — hence `ψ_j² = (ψ_j†)² = 0`, the Pauli
    exclusion principle in operator form.
  `inner_fermCre_left` checks on the Hilbert space `ℓ²(FermConf)` that `ψ_j†` really is the
  adjoint of `ψ_j`, so the CAR are relations between an operator and its adjoint.
* **The `ℤ₂` grading** (E.4).  `fermGrade` is the parity operator `Γ = (−1)^F`, with
  `fermGrade_involutive`; the ladder operators are **odd** (`fermGrade_fermAnn`,
  `fermGrade_fermCre`), and `superBracket` is the graded bracket
  `[x, y} = xy − (−1)^{|x||y|} yx`, for which `superBracket_fermAnn_fermCre` restates the
  CAR and `superBracket_bosOp_ghostOp` says bosonic and ghost operators supercommute.
* **The graded state space** `QGGraded = FockAlg ⊗ FermAlg` with `bosOp` and `ghostOp`, the
  commutation `bosOp_ghostOp_comm`, the canonical relations `qgCCR` (bosonic) and
  `qgGhostCar` (fermionic) transported to it, and `qgGrade`, the total parity, for which
  `bosOp_even` and `ghostOp_odd` fix the degrees.
* **The graded Fock space and its Hamiltonian** (E.5, E.5b, E.6).  `GradedIdx =
  Conf × FermConf` indexes the joint occupation states; `qgGradedSymbol ω g` is the total
  energy `∑ₖ nₖ ωₖ + ∑_{a ∈ α} gₐ` of a boson configuration together with a ghost
  configuration, `qgGradedHam` the corresponding operator on the finite-occupation domain,
  and
  * **`qgGradedFock_esa`** — it is essentially self-adjoint there, with **no** boundedness
    or positivity assumption on either the boson or the ghost energies (the QG operator is
    indefinite, so this matters), and
  * **`qgGradedFock_stone_flow`** — hence it generates the unitary group `e^{−itH}` on the
    graded Fock space.
  `qgGradedFock_not_bounded` records that this is not a boundedness phenomenon.
  `qgDGamma_esa` and `qgTwoLevel_esa` register the general (bosonic) second-quantization
  and Fock-of-Fock theorems the plan asks to reuse, and `qgFock_hashimoto_selects`
  instantiates the shift-invert selection theorem on the Gauss–polynomial core of
  `L²(ℝ⁸⁴)`.

## Honest boundary

The Hamiltonian second-quantized here is the **particle-number preserving** one: a real
one-particle symbol for the bosons and a real ghost energy, with no sector-changing
interaction and no BRST charge (that is `ChapterQuantumGravityBrstCharge`, whose ghost CAR
on `Λ(ℂ¹⁹)` is the finite-mode counterpart of the fermionic half built here).  The
continuum one-particle essential self-adjointness of the full gauge-fixed operator on
`L²(ℝ⁸⁴ × ℤ₂¹⁹)` is *not* claimed; it is the hypothesis that the Fock-level theorems
consume.  No mass gap and no global existence is claimed.
-/

namespace BookProof.QuantumGravityFock

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section
/-! ## The fermionic Fock space `ℓ²(FermConf)` and the adjoint pairing -/

/-- The fermionic Fock space `ℓ²` over the fermionic configurations. -/
abbrev FermFock := lp (fun _ : FermConf => ℂ) 2

/-- A finitely supported fermionic state as an element of `ℓ²(FermConf)`. -/
def fermToLp (u : FermAlg) : FermFock :=
  ⟨fun α => u α, memLpTwo_of_finite_support u.finite_support⟩

@[simp] theorem fermToLp_apply (u : FermAlg) (α : FermConf) :
    ((fermToLp u : FermFock) : FermConf → ℂ) α = u α := rfl

theorem fermToLp_mem (u : FermAlg) : fermToLp u ∈ lpFiniteModes FermConf := u.finite_support

@[simp] theorem fermToLp_zero : fermToLp (0 : FermAlg) = 0 := by
  refine lp.ext (funext fun α => ?_)
  simp [fermToLp]

theorem fermToLp_add (x y : FermAlg) : fermToLp (x + y) = fermToLp x + fermToLp y := by
  refine lp.ext (funext fun α => ?_)
  simp [fermToLp]

theorem inner_fermToLp_of_subset {u : FermAlg} {s : Finset FermConf} (hs : u.support ⊆ s)
    (v : FermAlg) :
    (inner ℂ (fermToLp u) (fermToLp v) : ℂ) = ∑ α ∈ s, (starRingEnd ℂ) (u α) * v α := by
  rw [lp.inner_eq_tsum]
  have hcoord : ∀ α : FermConf,
      (inner ℂ (((fermToLp u : FermFock) : FermConf → ℂ) α)
        (((fermToLp v : FermFock) : FermConf → ℂ) α) : ℂ)
        = (starRingEnd ℂ) (u α) * v α := by
    intro α
    simp [RCLike.inner_apply, mul_comm]
  rw [tsum_congr hcoord]
  refine tsum_eq_sum fun α hα => ?_
  have hu : u α = 0 := by
    by_contra hc
    exact hα (hs (Finsupp.mem_support_iff.mpr hc))
  rw [hu, map_zero, zero_mul]

theorem inner_fermToLp_single (p q : FermConf) (a b : ℂ) :
    (inner ℂ (fermToLp (Finsupp.single p a)) (fermToLp (Finsupp.single q b)) : ℂ)
      = if q = p then (starRingEnd ℂ) a * b else 0 := by
  classical
  rw [inner_fermToLp_of_subset (s := {p}) Finsupp.support_single_subset, Finset.sum_singleton,
    Finsupp.single_eq_same, Finsupp.single_apply]
  by_cases h : q = p
  · simp [h]
  · simp [h]

/-- **The creation operator is the adjoint of the annihilation operator**:
`⟪ψ_j† u, v⟫ = ⟪u, ψ_j v⟫`. -/
theorem inner_fermCre_left (j : ℕ) (u v : FermAlg) :
    (inner ℂ (fermToLp (fermCre j u)) (fermToLp v) : ℂ)
      = inner ℂ (fermToLp u) (fermToLp (fermAnn j v)) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => rw [map_zero, fermToLp_zero, inner_zero_left, inner_zero_left]
  | add f g hf hg =>
      rw [map_add, fermToLp_add, fermToLp_add, inner_add_left, inner_add_left, hf, hg]
  | single β c =>
    induction v using Finsupp.induction_linear with
    | zero => rw [map_zero, fermToLp_zero, inner_zero_right, inner_zero_right]
    | add f g hf hg =>
        rw [map_add, fermToLp_add, fermToLp_add, inner_add_right, inner_add_right, hf, hg]
    | single α d =>
      by_cases hjb : j ∈ β
      · have h0 : fermCre j (Finsupp.single β c) = 0 := by simp [hjb]
        rw [h0, fermToLp_zero, inner_zero_left,
          inner_fermToLp_of_subset (s := {β}) Finsupp.support_single_subset,
          Finset.sum_singleton, fermAnn_apply, if_pos hjb, mul_zero]
      · have h1 : fermCre j (Finsupp.single β c)
            = Finsupp.single (insert j β) (c * jwSign j β) := by
          simp [hjb, Finsupp.smul_single]
        rw [h1, inner_fermToLp_single,
          inner_fermToLp_of_subset (s := {β}) Finsupp.support_single_subset,
          Finset.sum_singleton, Finsupp.single_eq_same, fermAnn_apply, if_neg hjb,
          Finsupp.single_apply]
        by_cases hα : α = insert j β
        · subst hα
          simp [map_mul, conj_jwSign]
          ring
        · simp [hα]

/-! ## E.4 — the `ℤ₂` grading and the superbracket -/

/-- **The total fermionic parity operator** `Γ = (−1)^F` on the fermionic Fock space. -/
def fermGrade : FermAlg →ₗ[ℂ] FermAlg :=
  Finsupp.lsum ℂ fun β => LinearMap.toSpanSingleton ℂ FermAlg
    (Finsupp.single β ((-1 : ℂ) ^ β.card))

@[simp] theorem fermGrade_single (β : FermConf) (c : ℂ) :
    fermGrade (Finsupp.single β c) = Finsupp.single β (((-1 : ℂ) ^ β.card) * c) := by
  simp [fermGrade, LinearMap.toSpanSingleton, Finsupp.smul_single, mul_comm]

theorem fermGrade_apply (u : FermAlg) (α : FermConf) :
    fermGrade u α = ((-1 : ℂ) ^ α.card) * u α := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg]; ring
  | single β c =>
    rw [fermGrade_single]
    by_cases h : α = β
    · subst h; simp
    · simp [h]

/-- The parity operator is an involution. -/
theorem fermGrade_involutive (u : FermAlg) : fermGrade (fermGrade u) = u := by
  refine Finsupp.ext fun α => ?_
  rw [fermGrade_apply, fermGrade_apply, ← mul_assoc, ← pow_add]
  rcases Nat.even_or_odd α.card with he | ho
  · rw [Even.neg_one_pow (he.add he), one_mul]
  · rw [Even.neg_one_pow (ho.add_odd ho), one_mul]

/-- **The annihilation operator is odd**: `Γ ψ_j = − ψ_j Γ`. -/
theorem fermGrade_fermAnn (j : ℕ) (u : FermAlg) :
    fermGrade (fermAnn j u) = - fermAnn j (fermGrade u) := by
  refine Finsupp.ext fun α => ?_
  rw [fermGrade_apply, fermAnn_apply, Finsupp.neg_apply, fermAnn_apply]
  by_cases hj : j ∈ α
  · simp [hj]
  · rw [if_neg hj, if_neg hj, fermGrade_apply, Finset.card_insert_of_notMem hj, pow_succ]
    ring

/-- **The creation operator is odd**: `Γ ψ_j† = − ψ_j† Γ`. -/
theorem fermGrade_fermCre (j : ℕ) (u : FermAlg) :
    fermGrade (fermCre j u) = - fermCre j (fermGrade u) := by
  refine Finsupp.ext fun α => ?_
  rw [fermGrade_apply, fermCre_apply, Finsupp.neg_apply, fermCre_apply]
  by_cases hj : j ∈ α
  · rw [if_pos hj, if_pos hj, fermGrade_apply, Finset.card_erase_of_mem hj]
    have hc : 1 ≤ α.card := Finset.card_pos.mpr ⟨j, hj⟩
    have hpow : ((-1 : ℂ)) ^ α.card = -((-1 : ℂ) ^ (α.card - 1)) := by
      conv_lhs => rw [show α.card = (α.card - 1) + 1 from by omega]
      rw [pow_succ]
      ring
    rw [hpow]
    ring
  · simp [hj]

/-- The sign `(−1)^{pq}` of the superalgebra: `−1` exactly when both degrees are odd. -/
def sgnDeg (p q : ZMod 2) : ℂ := if p = 1 ∧ q = 1 then -1 else 1

/-- **The graded (super) bracket** `[x, y} = xy − (−1)^{|x||y|} yx` of two operators of
degrees `p` and `q`. -/
def superBracket {V : Type*} [AddCommGroup V] [Module ℂ V] (p q : ZMod 2)
    (A B : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  A ∘ₗ B - sgnDeg p q • (B ∘ₗ A)

theorem superBracket_apply {V : Type*} [AddCommGroup V] [Module ℂ V] (p q : ZMod 2)
    (A B : V →ₗ[ℂ] V) (x : V) :
    superBracket p q A B x = A (B x) - sgnDeg p q • B (A x) := rfl

/-- For two odd operators the superbracket is the **anticommutator**. -/
theorem superBracket_odd_odd {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : V →ₗ[ℂ] V) (x : V) : superBracket 1 1 A B x = A (B x) + B (A x) := by
  rw [superBracket_apply, sgnDeg, if_pos ⟨rfl, rfl⟩]
  simp

/-- For an even and an odd operator the superbracket is the **commutator**. -/
theorem superBracket_even_odd {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : V →ₗ[ℂ] V) (x : V) : superBracket 0 1 A B x = A (B x) - B (A x) := by
  rw [superBracket_apply, sgnDeg, if_neg (by decide)]
  simp

/-- **E.4/E.3 — the CAR as a superbracket**: `[ψ_j, ψ_j†} = 1`. -/
theorem superBracket_fermAnn_fermCre (j : ℕ) :
    superBracket 1 1 (fermAnn j) (fermCre j) = LinearMap.id := by
  refine LinearMap.ext fun u => ?_
  rw [superBracket_odd_odd, car_fermAnn_fermCre]
  rfl

/-- `[ψ_j, ψ_k†} = 0` for `j ≠ k`. -/
theorem superBracket_fermAnn_fermCre_of_ne {j k : ℕ} (h : j ≠ k) :
    superBracket 1 1 (fermAnn j) (fermCre k) = 0 := by
  refine LinearMap.ext fun u => ?_
  rw [superBracket_odd_odd, car_fermAnn_fermCre_of_ne h]
  rfl

/-- `[ψ_j, ψ_k} = 0`. -/
theorem superBracket_fermAnn_fermAnn (j k : ℕ) :
    superBracket 1 1 (fermAnn j) (fermAnn k) = 0 := by
  refine LinearMap.ext fun u => ?_
  rw [superBracket_odd_odd, car_fermAnn_fermAnn]
  rfl

/-- `[ψ_j†, ψ_k†} = 0`. -/
theorem superBracket_fermCre_fermCre (j k : ℕ) :
    superBracket 1 1 (fermCre j) (fermCre k) = 0 := by
  refine LinearMap.ext fun u => ?_
  rw [superBracket_odd_odd, car_fermCre_fermCre]
  rfl

end

end BookProof.QuantumGravityFock
