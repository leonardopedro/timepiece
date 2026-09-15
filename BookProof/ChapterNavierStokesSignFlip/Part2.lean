import Mathlib
import BookProof.ChapterNavierStokesAffineBlockEsa
import BookProof.ChapterNavierStokesSignFlip.Part1

/-!
# The sign-flip unitary: removing the `c ≥ 0` hypothesis

`BookProof.ChapterNavierStokesAffineFiberEsa` proves that the affine
Navier–Stokes fiber Hamiltonian `H = ½(π V + V π)` with `V(u) = κ u + c` is
essentially self-adjoint on the finite-mode core of `ℓ²(ℕ)`, but only for
`c ≥ 0`: the `±1`-hopping amplitude `(c/√2)√(n+1)` of a `ShiftData` is required
to be non-negative.  The recorded remedy was the **sign-flip unitary**
`(U x)_n = (−1)ⁿ x_n`, which reverses the sign of a `±1`-hopping and preserves a
`±2`-hopping.  This module formalizes it and removes the hypothesis.

## What is proved

* `deficiencyTrivialAt_of_intertwine`, `essentiallySelfAdjointOn_of_intertwine` —
  essential self-adjointness is a unitary invariant: if a unitary `U` of the
  ambient Hilbert space preserves the core and intertwines two operators on it,
  `U ∘ T = T' ∘ U`, then `T` is essentially self-adjoint iff `T'` is;
* `flipU` — the sign-flip unitary `(U x)_β = (−1)^{p β} x_β` attached to a parity
  function `p : ι → ℕ`, a `LinearIsometryEquiv` of `ℓ²(ι)` preserving the
  finite-mode core and every maximal domain;
* `hFun_flip`, `shiftH_flip` — the conjugation rule: a shift Hamiltonian whose
  shift changes the parity by `k` is conjugated by `U` into `(−1)^k` times
  itself;
* `saffH` — the affine fiber Hamiltonian for an **arbitrary real** constant `c`
  (the `±1`-hopping amplitude is the signed `(c/√2)√(n+1)`);
* `saffH_conj_flip` — the unitary equivalence `U (affH κ |c|) U = saffH κ c` for
  `c < 0`;
* `saffH_essentiallySelfAdjointOn_core` — **the headline for one fiber**: for
  every `κ ≥ 0` and **every** `c ∈ ℝ`, the affine fiber Hamiltonian is
  essentially self-adjoint on the finite-mode core;
* `saffBlockH_essentiallySelfAdjointOn_core` — the same over the strain-rate
  spectrum: on `ℓ²(ℕ × J)`, for arbitrary families `κ ≥ 0` and `c : J → ℝ` of
  **arbitrary sign**.

## Honest boundary

`κ ≥ 0` is still assumed (the sign-flip unitary preserves the `±2`-hopping, so
it cannot remove that one; it is removed instead in
`BookProof.ChapterNavierStokesSignedShift`).  As in the modules quoted above,
everything is stated on the abstract sequence space with the operator given by
its matrix in the Hermite basis, and nothing here claims global regularity for
the classical Navier–Stokes equation.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace SignFlip

open LpNat FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber
/-! ## The signed `±1`-hopping is genuinely present -/

/-- The coordinate of `H eₙ` at Hermite level `n + 1` is the **signed**
`±1`-hopping amplitude `(c/√2)√(n+1)`. -/
theorem saffH_coord_succ {κ : ℝ} (hκ : 0 ≤ κ) (c : ℝ) (n : ℕ) :
    ((saffH hκ c (basisState κ |c| n) : L2I ℕ) : ℕ → ℂ) (n + 1)
      = Complex.I * ((shear c n : ℝ) : ℂ) := by
  have hX := basisState_coe κ |c| n
  have hfst : (affData hκ (abs_nonneg c)).fst.hFun
      ((basisState κ |c| n : L2I ℕ) : ℕ → ℂ) (n + 1) = 0 := by
    refine hFun_eq_zero _ (fun α hα => ?_) ?_
    · simp only [affData_shift₁] at hα
      rw [hX]
      have : α ≠ n := by omega
      simp [this]
    · simp only [PairShift.fst_shift, affData_shift₁, hX]
      norm_num
      omega
  have hsnd : (affData hκ (abs_nonneg c)).snd.hFun
      ((basisState κ |c| n : L2I ℕ) : ℕ → ℂ) (n + 1)
      = Complex.I * ((shear |c| n : ℝ) : ℂ) := by
    have h := hFun_shift_of_single (affData hκ (abs_nonneg c)).snd
      (X := ((basisState κ |c| n : L2I ℕ) : ℕ → ℂ)) (o := n)
      (by simp [hX]) (by simp [hX]; omega)
    simpa using h
  rw [saffH_coe, hfst, hsnd, zero_add, ← mul_assoc, mul_comm (esgn c) Complex.I, mul_assoc,
    esgn_mul_shear]

/-- The coordinate of `H eₙ` at Hermite level `n + 2` is the `±2`-hopping
amplitude `(κ/2)√((n+1)(n+2))` of the linear part, unchanged. -/
theorem saffH_coord_succ_succ {κ : ℝ} (hκ : 0 ≤ κ) (c : ℝ) (n : ℕ) :
    ((saffH hκ c (basisState κ |c| n) : L2I ℕ) : ℕ → ℂ) (n + 2)
      = Complex.I * ((amp κ n : ℝ) : ℂ) := by
  have hX := basisState_coe κ |c| n
  have hsnd : (affData hκ (abs_nonneg c)).snd.hFun
      ((basisState κ |c| n : L2I ℕ) : ℕ → ℂ) (n + 2) = 0 := by
    refine hFun_eq_zero _ (fun α hα => ?_) ?_
    · simp only [affData_shift₂] at hα
      rw [hX]
      have : α ≠ n := by omega
      simp [this]
    · simp only [PairShift.snd_shift, affData_shift₂, hX]
      norm_num
      omega
  have hfst : (affData hκ (abs_nonneg c)).fst.hFun
      ((basisState κ |c| n : L2I ℕ) : ℕ → ℂ) (n + 2)
      = Complex.I * ((amp κ n : ℝ) : ℂ) := by
    have h := hFun_shift_of_single (affData hκ (abs_nonneg c)).fst
      (X := ((basisState κ |c| n : L2I ℕ) : ℕ → ℂ)) (o := n)
      (by simp [hX]) (by simp [hX]; omega)
    simpa using h
  rw [saffH_coe, hfst, hsnd, mul_zero, add_zero]

/-- With a non-zero constant part — **of either sign** — the affine fiber
Hamiltonian does not vanish on the ground state. -/
theorem saffH_ne_zero_of_shear {κ : ℝ} (hκ : 0 ≤ κ) {c : ℝ} (hc : c ≠ 0) :
    saffH hκ c (basisState κ |c| 0) ≠ 0 := by
  intro h0
  have hcoord := saffH_coord_succ hκ c 0
  rw [h0] at hcoord
  simp only [lp.coeFn_zero, Pi.zero_apply] at hcoord
  have hshear : shear c 0 ≠ 0 := by
    have h2 : (0 : ℝ) < Real.sqrt 2 := by rw [Real.sqrt_pos]; norm_num
    have h1 : (0 : ℝ) < Real.sqrt (((0 : ℕ) : ℝ) + 1) := by rw [Real.sqrt_pos]; norm_num
    simp only [shear, ne_eq, mul_eq_zero, div_eq_zero_iff, not_or]
    exact ⟨⟨hc, ne_of_gt h2⟩, ne_of_gt h1⟩
  have hz : ((shear c 0 : ℝ) : ℂ) = 0 := by
    have h := hcoord.symm
    field_simp at h
    simpa using h
  exact hshear (by exact_mod_cast hz)

/-! ## The block assembly with constants of arbitrary sign -/

section Block

open BilinearEsa

variable {J : Type*}

/-- The coordinates of the Navier–Stokes generator whose block `j` carries the
affine field `V(u) = κ_j u + c_j` with `c_j` of **arbitrary sign**. -/
noncomputable def sblockFun (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (X : ℕ × J → ℂ) : ℕ × J → ℂ :=
  fun q => (affData (hκ q.2) (abs_nonneg (c q.2))).fst.hFun (fun n => X (n, q.2)) q.1
    + esgn (c q.2)
      * (affData (hκ q.2) (abs_nonneg (c q.2))).snd.hFun (fun n => X (n, q.2)) q.1

theorem support_sblockFun (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (X : ℕ × J → ℂ) :
    Function.support (sblockFun κ c hκ X)
      ⊆ (((fun q : ℕ × J => (q.1 + 2, q.2)) '' Function.support X)
          ∪ ((fun q : ℕ × J => (q.1 + 2, q.2)) ⁻¹' Function.support X))
        ∪ (((fun q : ℕ × J => (q.1 + 1, q.2)) '' Function.support X)
          ∪ ((fun q : ℕ × J => (q.1 + 1, q.2)) ⁻¹' Function.support X)) := by
  rintro ⟨m, j⟩ hq
  simp only [Function.mem_support, sblockFun] at hq
  by_cases h1 : (affData (hκ j) (abs_nonneg (c j))).fst.hFun (fun n => X (n, j)) m = 0
  · have h2 : (affData (hκ j) (abs_nonneg (c j))).snd.hFun (fun n => X (n, j)) m ≠ 0 := by
      intro h
      exact hq (by rw [h1, h]; ring)
    have hmem := support_hFun (affData (hκ j) (abs_nonneg (c j))).snd (fun n => X (n, j)) h2
    rcases hmem with ⟨a, ha, hae⟩ | hpre
    · refine Or.inr (Or.inl ⟨(a, j), ha, ?_⟩)
      simp only [Prod.mk.injEq]
      exact ⟨hae, trivial⟩
    · exact Or.inr (Or.inr hpre)
  · have hmem := support_hFun (affData (hκ j) (abs_nonneg (c j))).fst (fun n => X (n, j)) h1
    rcases hmem with ⟨a, ha, hae⟩ | hpre
    · refine Or.inl (Or.inl ⟨(a, j), ha, ?_⟩)
      simp only [Prod.mk.injEq]
      exact ⟨hae, trivial⟩
    · exact Or.inl (Or.inr hpre)

theorem sblockFun_finite_support (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (x : lpFiniteModes (ℕ × J)) :
    (Function.support (sblockFun κ c hκ (((x : L2I (ℕ × J))) : ℕ × J → ℂ))).Finite := by
  have hx := mem_lpFiniteModes.mp x.2
  refine Set.Finite.subset
    (((hx.image _).union (Set.Finite.preimage (AffineBlock.shiftProd_injective 2).injOn hx)).union
      ((hx.image _).union (Set.Finite.preimage (AffineBlock.shiftProd_injective 1).injOn hx)))
    (support_sblockFun κ c hκ _)

/-- **The Navier–Stokes generator with affine fiber fields of arbitrary sign**,
on the finite-mode core of `ℓ²(ℕ × J)`. -/
noncomputable def sblockH (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) :
    lpFiniteModes (ℕ × J) →ₗ[ℂ] L2I (ℕ × J) where
  toFun x := ⟨sblockFun κ c hκ (((x : L2I (ℕ × J))) : ℕ × J → ℂ),
    memLpTwo_of_finite_support (sblockFun_finite_support κ c hκ x)⟩
  map_add' x y := by
    refine lp.ext (funext fun q => ?_)
    simp only [Submodule.coe_add, lp.coeFn_add, Pi.add_apply, sblockFun]
    rw [hFun_add, hFun_add]
    ring
  map_smul' a x := by
    refine lp.ext (funext fun q => ?_)
    simp only [Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      sblockFun]
    rw [hFun_smul, hFun_smul]
    ring

@[simp] theorem sblockH_coe (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (x : lpFiniteModes (ℕ × J))
    (q : ℕ × J) :
    ((sblockH κ c hκ x : L2I (ℕ × J)) : ℕ × J → ℂ) q
      = sblockFun κ c hκ (((x : L2I (ℕ × J))) : ℕ × J → ℂ) q := rfl

/-- The generator preserves the blocks, acting on the block `j` by the signed
affine fiber Hamiltonian. -/
theorem sblockFun_embFun (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (j : J) (a : ℕ → ℂ) :
    sblockFun κ c hκ (embFun j a)
      = embFun j (fun n => (affData (hκ j) (abs_nonneg (c j))).fst.hFun a n
          + esgn (c j) * (affData (hκ j) (abs_nonneg (c j))).snd.hFun a n) := by
  funext q
  obtain ⟨m, j'⟩ := q
  by_cases hj : j' = j
  · subst hj
    simp only [sblockFun, embFun_self]
  · simp only [sblockFun, hFun_zero, mul_zero, add_zero, embFun_of_ne _ _ hj]

/-- The block of the image is the signed affine fiber Hamiltonian applied to the
block. -/
theorem blockVec_sblockH (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (v : lpFiniteModes (ℕ × J)) (j : J) :
    blockVec ((sblockH κ c hκ v : L2I (ℕ × J))) j
      = saffH (hκ j) (c j)
          ⟨blockVec ((v : L2I (ℕ × J))) j, AffineBlock.blockVec_mem_maxDom' _ v j⟩ := by
  refine lp.ext (funext fun n => ?_)
  rw [show ((saffH (hκ j) (c j)
      ⟨blockVec ((v : L2I (ℕ × J))) j, AffineBlock.blockVec_mem_maxDom' _ v j⟩ :
        L2I ℕ) : ℕ → ℂ) n = _ from saffH_coe (hκ j) (c j) _ n]
  rfl

/-- **The generator is symmetric** on the finite-mode core. -/
theorem sblockH_symmetricOn (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) :
    SymmetricOn (lpFiniteModes (ℕ × J)) (sblockH κ c hκ) := by
  intro x y
  have h1 := hasSum_inner_blocks ((sblockH κ c hκ x : L2I (ℕ × J))) ((y : L2I (ℕ × J)))
  have h2 := hasSum_inner_blocks ((x : L2I (ℕ × J))) ((sblockH κ c hκ y : L2I (ℕ × J)))
  have heq : ∀ j : J,
      (inner ℂ (blockVec ((sblockH κ c hκ x : L2I (ℕ × J))) j)
          (blockVec ((y : L2I (ℕ × J))) j) : ℂ)
        = inner ℂ (blockVec ((x : L2I (ℕ × J))) j)
            (blockVec ((sblockH κ c hκ y : L2I (ℕ × J))) j) := by
    intro j
    rw [blockVec_sblockH κ c hκ x j, blockVec_sblockH κ c hκ y j]
    exact saffH_symmetricOn (hκ j) (c j) ⟨_, AffineBlock.blockVec_mem_maxDom' _ x j⟩
      ⟨_, AffineBlock.blockVec_mem_maxDom' _ y j⟩
  simp only [heq] at h1
  exact h1.unique h2

/-- **Block reduction of the deficiency problem** for the signed generator. -/
theorem deficiencyTrivialAt_sblockH (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (z : ℂ)
    (hblk : ∀ j, DeficiencyTrivialAt (lpFiniteModes ℕ)
      ((saffH (hκ j) (c j)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol (affMu (κ j) |c j|))))) z) :
    DeficiencyTrivialAt (lpFiniteModes (ℕ × J)) (sblockH κ c hκ) z := by
  intro w hw
  have hb : ∀ j, blockVec w j = 0 := by
    intro j
    refine hblk j (blockVec w j) ?_
    intro u
    have hv := hw (blockEmb j u)
    have hHcoe : ∀ q : ℕ × J,
        ((sblockH κ c hκ (blockEmb j u) : L2I (ℕ × J)) : ℕ × J → ℂ) q
          = embFun j (((((saffH (hκ j) (c j))
              (Submodule.inclusion
                (finiteModes_le_maxDom (oscSymbol (affMu (κ j) |c j|))) u) :
                L2I ℕ)) : ℕ → ℂ)) q := by
      intro q
      have hb0 : ((sblockH κ c hκ (blockEmb j u) : L2I (ℕ × J)) : ℕ × J → ℂ)
          = sblockFun κ c hκ (embFun j (((u : L2I ℕ)) : ℕ → ℂ)) := rfl
      rw [hb0, sblockFun_embFun]
      congr 1
    have h1 := inner_of_block_supported j
      ((sblockH κ c hκ (blockEmb j u) : L2I (ℕ × J)))
      (((saffH (hκ j) (c j))
        (Submodule.inclusion
          (finiteModes_le_maxDom (oscSymbol (affMu (κ j) |c j|))) u) : L2I ℕ)) hHcoe w
    have h2 := inner_of_block_supported j
      (((blockEmb j u : lpFiniteModes (ℕ × J)) : L2I (ℕ × J))) ((u : L2I ℕ))
      (fun _ => rfl) w
    rw [h1, h2] at hv
    exact hv
  refine lp.ext (funext fun q => ?_)
  obtain ⟨n, j⟩ := q
  have hz := congrArg (fun v : L2I ℕ => ((v : ℕ → ℂ)) n) (hb j)
  simpa using hz

/-- **The headline over the strain-rate spectrum.**  The Navier–Stokes generator
whose fiber fields are the affine `V(u) = κ_j u + c_j` is essentially
self-adjoint on the finite-mode core of `ℓ²(ℕ × J)` for arbitrary families
`κ ≥ 0` and `c : J → ℝ` **of arbitrary sign**. -/
theorem sblockH_essentiallySelfAdjointOn_core (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) :
    EssentiallySelfAdjointOn (lpFiniteModes (ℕ × J)) (sblockH κ c hκ) :=
  ⟨deficiencyTrivialAt_sblockH κ c hκ Complex.I
      fun j => (saffH_essentiallySelfAdjointOn_core (hκ j) (c j)).1,
   deficiencyTrivialAt_sblockH κ c hκ (-Complex.I)
      fun j => (saffH_essentiallySelfAdjointOn_core (hκ j) (c j)).2⟩

/-- The finite-mode core is dense, so the generator is densely defined. -/
theorem sblockH_domain_dense :
    Dense ((lpFiniteModes (ℕ × J) : Submodule ℂ (L2I (ℕ × J))) : Set (L2I (ℕ × J))) :=
  lpFiniteModes_dense

end Block

end SignFlip

end BookProof.NavierStokesFlow
