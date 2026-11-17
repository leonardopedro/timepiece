import Mathlib
import BookProof.ChapterBRSTNilpotent
import BookProof.Qym.ChapterYangMillsSU3
import BookProof.Sm.ChapterSmCarAlgebra

/-!
# The ghost / BRST sector of the Standard-Model gauge algebra

This module closes the third honest boundary of the Standard-Model wave of
`CONSOLIDATED_PLAN.md` §D6b-SM: *“the ghost/BRST sector is not built”*.  The Grassmann
coordinates `ζ_F` of §D6b-SM.1 carry, besides the matter fermions, **one ghost per gauge
generator**; the Standard-Model gauge algebra `su(3) ⊕ su(2) ⊕ u(1)` has `8 + 3 + 1 = 12`
generators, so the ghost sector is a twelve-mode CAR algebra, and the BRST charge is

```
Ω = Σ_a c^a G_a − ½ Σ_{a,b,c} f_{abc} c^a c^b b_c .
```

## What is proved

* **The structure constants of the Standard-Model gauge algebra.**  `sumStruct` is the
  direct sum of two structure-constant families, `sumStruct_antisymm` and
  `sumStruct_jacobi` show that antisymmetry and the Jacobi identity are inherited;
  `su2Struct` is the concrete `su(2)` Levi-Civita family (antisymmetry and Jacobi by finite
  check), `u1Struct` the abelian one, and `smStruct f₃` assembles them with an `su(3)`
  family `f₃` into the twelve-generator family, with **`smStruct_antisymm`** and
  **`smStruct_jacobi`**: the Standard-Model gauge algebra has totally antisymmetric
  structure constants obeying Jacobi, which is exactly what BRST needs.
* **The ghost sector on the CAR algebra.**  The ghosts are the last twelve modes of the
  fermionic Fock space of `BookProof.ChapterSmCarAlgebra`; `smGhostCAR` is their canonical
  anticommutation relations, `ghostNumber` the ghost-number operator with
  `ghostNumber_occ` (its spectrum is the ghost occupation number) and the commutators
  `ghostNumber_comm_ghostCre`, `ghostNumber_comm_ghostAnn`.
* **The cubic ghost charge is nilpotent** — `smGhostCharge_nilpotent`, through the project's
  `BookProof.BRSTNilpotent.brst_charge_nilpotent` with the Standard-Model structure
  constants.
* **The full BRST charge is nilpotent** — `brstCharge_nilpotent`, an algebraic theorem in
  any ring carrying ghosts with the CAR and constraint operators `G_a` that commute with
  the ghosts and close with the structure constants: `Ω² = 0`.
* **Second quantization is a Lie-algebra homomorphism** — `fermiBilin_lie`,
  `creat_annih_commutator`: `[dΓ(A), dΓ(B)] = dΓ([A,B])`, so the Gauss-law generators
  `G_a = −i dΓ(T_a)` of the matter sector close with the *real* structure constants
  (`matterGen_lie`), and they commute with the ghosts (`matterGen_comm_ghostCre`,
  `matterGen_comm_ghostAnn`) because they are even.
* **The Standard-Model BRST charge** `smBrstCharge` on the joint matter ⊗ ghost Fock space,
  with **`smBrstCharge_nilpotent`**: `Ω² = 0`, which is what makes the BRST cohomology —
  the physical sector — well defined.

## Honest boundary

The mode set here is finite: one plane-wave matter multiplet and the twelve ghosts, i.e. the
gauge algebra of the collective-coordinate presentation of §D6b-SM.1.  The charge used in
this module is the abstract one, with the constraints `G_a` given as data.  The BRST charge
**as `book.tex` itself defines it** — the density
`Ω = π^μ_a ∂_μψ†_a − π^μ_a f_{abc}A_{μb}ψ†_c − (i/2) f_{abc}ψ†_aψ†_bψ_c` with the book's
canonical relations, the Gauss law *derived* from them, and the gauge-fixing fermion
`Ψ = i ψ_a A_{0a}` — is built in `BookProof.ChapterBookBrstYangMills`,
`BookProof.ChapterBookBrstGaugeFixing` and `BookProof.ChapterBookBrstInstances`, the last of
which instantiates it with the Standard-Model structure constants `smStruct f₃`.  The
`su(3)` structure constants enter as a family satisfying antisymmetry and Jacobi (which
`BookProof.ChapterYangMillsSU3` derives for trace-orthonormal generators); the book's
formalism uses no Faddeev–Popov determinant and none is constructed, and no statement about
the *size* of the BRST cohomology is made.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmBrstGhost

open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

/-! ## 1. The structure constants of `su(3) ⊕ su(2) ⊕ u(1)` -/

/-- The direct sum of two families of structure constants: a bracket never leaves its
summand. -/
def sumStruct {ι κ : Type*} (f1 : ι → ι → ι → ℝ) (f2 : κ → κ → κ → ℝ) :
    (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ
  | Sum.inl a, Sum.inl b, Sum.inl c => f1 a b c
  | Sum.inr a, Sum.inr b, Sum.inr c => f2 a b c
  | _, _, _ => 0

theorem sumStruct_antisymm {ι κ : Type*} {f1 : ι → ι → ι → ℝ}
    {f2 : κ → κ → κ → ℝ} (h1 : ∀ a b c, f1 a b c = -f1 b a c)
    (h2 : ∀ a b c, f2 a b c = -f2 b a c) (a b c : ι ⊕ κ) :
    sumStruct f1 f2 a b c = -sumStruct f1 f2 b a c := by
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
    simp only [sumStruct, neg_zero] <;> first | rfl | exact h1 a b c | exact h2 a b c

theorem sumStruct_jacobi {ι κ : Type*} [Fintype ι] [Fintype κ] {f1 : ι → ι → ι → ℝ}
    {f2 : κ → κ → κ → ℝ}
    (h1 : ∀ a b c h : ι, ∑ e, (f1 a b e * f1 e c h + f1 b c e * f1 e a h
      + f1 c a e * f1 e b h) = 0)
    (h2 : ∀ a b c h : κ, ∑ e, (f2 a b e * f2 e c h + f2 b c e * f2 e a h
      + f2 c a e * f2 e b h) = 0)
    (a b c h : ι ⊕ κ) :
    ∑ e, (sumStruct f1 f2 a b e * sumStruct f1 f2 e c h
      + sumStruct f1 f2 b c e * sumStruct f1 f2 e a h
      + sumStruct f1 f2 c a e * sumStruct f1 f2 e b h) = 0 := by
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> rcases h with h | h <;>
    simp only [Fintype.sum_sum_type, sumStruct, mul_zero, zero_mul, add_zero, zero_add,
      Finset.sum_const_zero] <;>
    first | rfl | exact h1 a b c h | exact h2 a b c h

/-- The Levi-Civita symbol on three indices, as an integer. -/
def epsZ (a b c : Fin 3) : ℤ :=
  if a = b ∨ b = c ∨ a = c then 0
  else if (a, b) = ((0 : Fin 3), (1 : Fin 3)) ∨ (a, b) = ((1 : Fin 3), (2 : Fin 3))
        ∨ (a, b) = ((2 : Fin 3), (0 : Fin 3)) then 1 else -1

/-- **The `su(2)` structure constants** `ε_{jkl}`. -/
def su2Struct (a b c : Fin 3) : ℝ := (epsZ a b c : ℝ)

/-- **The `u(1)` structure constants**: an abelian factor has none. -/
def u1Struct (_ _ _ : Fin 1) : ℝ := 0

theorem epsZ_antisymm : ∀ a b c : Fin 3, epsZ a b c = -epsZ b a c := by decide

theorem epsZ_jacobi : ∀ a b c h : Fin 3,
    ∑ e, (epsZ a b e * epsZ e c h + epsZ b c e * epsZ e a h + epsZ c a e * epsZ e b h) = 0 := by
  decide

theorem su2Struct_antisymm (a b c : Fin 3) : su2Struct a b c = -su2Struct b a c := by
  rw [su2Struct, su2Struct, epsZ_antisymm a b c]
  push_cast
  ring

theorem su2Struct_jacobi (a b c h : Fin 3) :
    ∑ e, (su2Struct a b e * su2Struct e c h + su2Struct b c e * su2Struct e a h
      + su2Struct c a e * su2Struct e b h) = 0 := by
  have hz := epsZ_jacobi a b c h
  have : ((∑ e, (epsZ a b e * epsZ e c h + epsZ b c e * epsZ e a h
      + epsZ c a e * epsZ e b h) : ℤ) : ℝ) = 0 := by rw [hz]; norm_num
  rw [← this]
  push_cast [su2Struct]
  ring

theorem u1Struct_antisymm (a b c : Fin 1) : u1Struct a b c = -u1Struct b a c := by
  simp [u1Struct]

theorem u1Struct_jacobi (a b c h : Fin 1) :
    ∑ e, (u1Struct a b e * u1Struct e c h + u1Struct b c e * u1Struct e a h
      + u1Struct c a e * u1Struct e b h) = 0 := by
  simp [u1Struct]

/-- The twelve generator labels of the Standard-Model gauge algebra, split into the eight
gluon, three weak and one hypercharge directions. -/
def smIdxEquiv : Fin 12 ≃ (Fin 8 ⊕ (Fin 3 ⊕ Fin 1)) :=
  (finCongr (by norm_num : (12 : ℕ) = 8 + (3 + 1))).trans
    (finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl (Fin 8)) finSumFinEquiv.symm))

/-- **The structure constants of the Standard-Model gauge algebra** `su(3) ⊕ su(2) ⊕ u(1)`,
given those of `su(3)`. -/
def smStruct (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ) (a b c : Fin 12) : ℝ :=
  sumStruct f3 (sumStruct su2Struct u1Struct) (smIdxEquiv a) (smIdxEquiv b) (smIdxEquiv c)

theorem smStruct_antisymm {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}
    (h3 : ∀ a b c, f3 a b c = -f3 b a c) (a b c : Fin 12) :
    smStruct f3 a b c = -smStruct f3 b a c := by
  exact sumStruct_antisymm h3
    (sumStruct_antisymm su2Struct_antisymm u1Struct_antisymm) _ _ _

theorem smStruct_jacobi {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}
    (h3 : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0) (a b c h : Fin 12) :
    ∑ e, (smStruct f3 a b e * smStruct f3 e c h + smStruct f3 b c e * smStruct f3 e a h
      + smStruct f3 c a e * smStruct f3 e b h) = 0 := by
  have hsum := sumStruct_jacobi (f1 := f3) (f2 := sumStruct su2Struct u1Struct) h3
    (sumStruct_jacobi su2Struct_jacobi u1Struct_jacobi)
    (smIdxEquiv a) (smIdxEquiv b) (smIdxEquiv c) (smIdxEquiv h)
  rw [← Equiv.sum_comp smIdxEquiv] at hsum
  simpa [smStruct] using hsum

/-! ## 2. The ghost sector inside the CAR algebra -/

variable {m : ℕ}

/-- The mode carrying the `a`-th ghost: the ghosts are the last twelve modes of the
fermionic Fock space, the matter modes being the first `m`. -/
def ghostMode (m : ℕ) (a : Fin 12) : Fin (m + 12) := Fin.natAdd m a

/-- The **ghost creation** operator `c^a`. -/
def ghostCre (m : ℕ) (a : Fin 12) : Module.End ℂ (FermiFock (m + 12)) :=
  creat (ghostMode m a)

/-- The **ghost annihilation** (antighost) operator `b_a`. -/
def ghostAnn (m : ℕ) (a : Fin 12) : Module.End ℂ (FermiFock (m + 12)) :=
  annih (ghostMode m a)

/-- **The ghosts obey the canonical anticommutation relations.** -/
theorem ghostMode_injective (m : ℕ) : Function.Injective (ghostMode m) := by
  intro a b hab
  have h : m + (a : ℕ) = m + (b : ℕ) := by
    simpa [ghostMode, Fin.ext_iff] using hab
  exact Fin.ext (by omega)

theorem smGhostCAR (m : ℕ) : GhostCAR (ghostCre m) (ghostAnn m) := by
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_⟩
  · exact car_creat_creat (ghostMode m a) (ghostMode m b)
  · exact car_annih_annih (ghostMode m a) (ghostMode m b)
  · by_cases h : a = b
    · subst h
      rw [if_pos rfl]
      exact car_annih_creat_self (ghostMode m a)
    · rw [if_neg h]
      exact car_annih_creat_of_ne (fun hh => h (ghostMode_injective m hh))

/-- **The ghost-number operator** `Σ_a c^a b_a`. -/
def ghostNumber (m : ℕ) : Module.End ℂ (FermiFock (m + 12)) :=
  ∑ a : Fin 12, ghostCre m a * ghostAnn m a

/-- The mixed canonical anticommutation relation in ring form. -/
theorem annih_mul_creat {N : ℕ} (p q : Fin N) :
    (annih p : Module.End ℂ (FermiFock N)) * creat q
      = (if p = q then 1 else 0) - creat q * annih p := by
  by_cases h : p = q
  · subst h
    rw [if_pos rfl]
    exact eq_sub_of_add_eq (car_annih_creat_self p)
  · rw [if_neg h]
    exact eq_sub_of_add_eq (car_annih_creat_of_ne h)

/-- Creation operators anticommute, in ring form. -/
theorem creat_mul_creat {N : ℕ} (p q : Fin N) :
    (creat p : Module.End ℂ (FermiFock N)) * creat q = -(creat q * creat p) :=
  eq_neg_of_add_eq_zero_left (car_creat_creat p q)

/-- Annihilation operators anticommute, in ring form. -/
theorem annih_mul_annih {N : ℕ} (p q : Fin N) :
    (annih p : Module.End ℂ (FermiFock N)) * annih q = -(annih q * annih p) :=
  eq_neg_of_add_eq_zero_left (car_annih_annih p q)

/-- The occupation-number operator of a mode on an occupation state. -/
theorem occupation_occ {N : ℕ} (i : Fin N) (S : Finset (Fin N)) :
    creat i (annih i (occ S)) = if i ∈ S then occ S else 0 := by
  ext T
  rw [occupation_apply]
  by_cases h : i ∈ S <;> by_cases hT : T = S <;>
    simp [h, hT, occ, EuclideanSpace.single_apply]

/-- **Annihilating the mode a state occupies leaves the vacuum.**  The `S = ∅` branch of
`annih_apply` is the only one that can match a one-mode state. -/
theorem annih_occ_self {N : ℕ} (j : Fin N) :
    annih j (occ ({j} : Finset (Fin N))) = occ (∅ : Finset (Fin N)) := by
  ext S
  rw [annih_apply]
  by_cases h : j ∈ S
  · rw [if_pos h]
    by_cases hS : S = ∅
    · subst hS; simp at h
    · simp [occ, EuclideanSpace.single_apply, hS]
  · rw [if_neg h]
    by_cases hS : S = ∅
    · subst hS; simp [occ, EuclideanSpace.single_apply, jwSign]
    · have hne : insert j S ≠ ({j} : Finset (Fin N)) := by
        intro hh
        refine hS (Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_)
        have hmem : x ∈ ({j} : Finset (Fin N)) := by
          rw [← hh]
          exact Finset.mem_insert_of_mem hx
        rw [Finset.mem_singleton] at hmem
        exact h (hmem ▸ hx)
      simp [occ, EuclideanSpace.single_apply, hne, hS]

/-- **Creating on the vacuum fills the mode.** -/
theorem creat_occ_empty {N : ℕ} (i : Fin N) :
    creat i (occ (∅ : Finset (Fin N))) = occ ({i} : Finset (Fin N)) := by
  ext S
  rw [creat_apply]
  by_cases h : i ∈ S
  · rw [if_pos h]
    by_cases hS : S.erase i = ∅
    · have hsingle : S = {i} := by
        rw [← Finset.insert_erase h, hS, Finset.insert_empty]
      subst hsingle
      simp [occ, EuclideanSpace.single_apply, jwSign]
    · have hne : S ≠ ({i} : Finset (Fin N)) := by
        intro hh
        exact hS (by rw [hh]; simp)
      simp [occ, EuclideanSpace.single_apply, hS, hne]
  · rw [if_neg h]
    have hne : S ≠ ({i} : Finset (Fin N)) := by
      intro hh
      exact h (by rw [hh]; simp)
    simp [occ, EuclideanSpace.single_apply, hne]

/-- **The ghost number of an occupation state** is the number of occupied ghost modes. -/
theorem ghostNumber_occ (m : ℕ) (S : Finset (Fin (m + 12))) :
    ghostNumber m (occ S)
      = (Finset.univ.filter (fun a : Fin 12 => ghostMode m a ∈ S)).card • occ S := by
  classical
  rw [ghostNumber, LinearMap.sum_apply]
  have hterm : ∀ a : Fin 12, (ghostCre m a * ghostAnn m a) (occ S)
      = if ghostMode m a ∈ S then occ S else 0 := fun a => occupation_occ (ghostMode m a) S
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hterm a]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero]

/-- Creation operators square to zero (the Pauli principle). -/
theorem creat_sq {N : ℕ} (i : Fin N) :
    (creat i : Module.End ℂ (FermiFock N)) * creat i = 0 := by
  have h2 : (2 : ℂ) • ((creat i : Module.End ℂ (FermiFock N)) * creat i) = 0 := by
    rw [two_smul]; exact car_creat_creat i i
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · exact h3

/-- Annihilation operators square to zero. -/
theorem annih_sq {N : ℕ} (i : Fin N) :
    (annih i : Module.End ℂ (FermiFock N)) * annih i = 0 := by
  have h2 : (2 : ℂ) • ((annih i : Module.End ℂ (FermiFock N)) * annih i) = 0 := by
    rw [two_smul]; exact car_annih_annih i i
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · exact h3

/-- A ghost creation operator raises the ghost number by one. -/
theorem ghostNumber_comm_ghostCre (m : ℕ) (a : Fin 12) :
    ghostNumber m * ghostCre m a - ghostCre m a * ghostNumber m = ghostCre m a := by
  rw [ghostNumber, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single a]
  · have hAC : (ghostAnn m a : Module.End ℂ (FermiFock (m + 12))) * ghostCre m a
        = 1 - ghostCre m a * ghostAnn m a := by
      rw [ghostAnn, ghostCre, annih_mul_creat, if_pos rfl]
    calc (ghostCre m a * ghostAnn m a : Module.End ℂ (FermiFock (m + 12))) * ghostCre m a
          - ghostCre m a * (ghostCre m a * ghostAnn m a)
        = ghostCre m a * ((ghostAnn m a : Module.End ℂ (FermiFock (m + 12))) * ghostCre m a)
            - (ghostCre m a * ghostCre m a) * ghostAnn m a := by noncomm_ring
      _ = ghostCre m a * (1 - ghostCre m a * ghostAnn m a)
            - (ghostCre m a * ghostCre m a) * ghostAnn m a := by rw [hAC]
      _ = ghostCre m a := by
            have hsq : (ghostCre m a : Module.End ℂ (FermiFock (m + 12))) * ghostCre m a = 0 := by
              rw [ghostCre]; exact creat_sq _
            calc (ghostCre m a : Module.End ℂ (FermiFock (m + 12)))
                    * (1 - ghostCre m a * ghostAnn m a)
                  - (ghostCre m a * ghostCre m a) * ghostAnn m a
                = ghostCre m a - (ghostCre m a * ghostCre m a) * ghostAnn m a
                  - (ghostCre m a * ghostCre m a) * ghostAnn m a := by noncomm_ring
              _ = ghostCre m a := by rw [hsq]; noncomm_ring
  · intro b _ hb
    have hne : ghostMode m b ≠ ghostMode m a := fun hh => hb (ghostMode_injective m hh)
    have hAC : (ghostAnn m b : Module.End ℂ (FermiFock (m + 12))) * ghostCre m a
        = -(ghostCre m a * ghostAnn m b) := by
      rw [ghostAnn, ghostCre, annih_mul_creat, if_neg hne, zero_sub]
    have hCC : (ghostCre m b : Module.End ℂ (FermiFock (m + 12))) * ghostCre m a
        = -(ghostCre m a * ghostCre m b) := by
      rw [ghostCre, ghostCre, creat_mul_creat]
    calc (ghostCre m b * ghostAnn m b : Module.End ℂ (FermiFock (m + 12))) * ghostCre m a
          - ghostCre m a * (ghostCre m b * ghostAnn m b)
        = ghostCre m b * ((ghostAnn m b : Module.End ℂ (FermiFock (m + 12))) * ghostCre m a)
            - ghostCre m a * (ghostCre m b * ghostAnn m b) := by noncomm_ring
      _ = ghostCre m b * -(ghostCre m a * ghostAnn m b)
            - ghostCre m a * (ghostCre m b * ghostAnn m b) := by rw [hAC]
      _ = -((ghostCre m b * ghostCre m a : Module.End ℂ (FermiFock (m + 12))) * ghostAnn m b)
            - ghostCre m a * (ghostCre m b * ghostAnn m b) := by noncomm_ring
      _ = -((-(ghostCre m a * ghostCre m b) : Module.End ℂ (FermiFock (m + 12)))
              * ghostAnn m b)
            - ghostCre m a * (ghostCre m b * ghostAnn m b) := by rw [hCC]
      _ = 0 := by noncomm_ring
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- A ghost annihilation operator lowers the ghost number by one. -/
theorem ghostNumber_comm_ghostAnn (m : ℕ) (a : Fin 12) :
    ghostNumber m * ghostAnn m a - ghostAnn m a * ghostNumber m = -ghostAnn m a := by
  rw [ghostNumber, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single a]
  · have hAC : (ghostAnn m a : Module.End ℂ (FermiFock (m + 12))) * ghostCre m a
        = 1 - ghostCre m a * ghostAnn m a := by
      rw [ghostAnn, ghostCre, annih_mul_creat, if_pos rfl]
    calc (ghostCre m a * ghostAnn m a : Module.End ℂ (FermiFock (m + 12))) * ghostAnn m a
          - ghostAnn m a * (ghostCre m a * ghostAnn m a)
        = ghostCre m a * ((ghostAnn m a : Module.End ℂ (FermiFock (m + 12))) * ghostAnn m a)
            - ((ghostAnn m a : Module.End ℂ (FermiFock (m + 12))) * ghostCre m a)
              * ghostAnn m a := by noncomm_ring
      _ = ghostCre m a * ((ghostAnn m a : Module.End ℂ (FermiFock (m + 12))) * ghostAnn m a)
            - (1 - ghostCre m a * ghostAnn m a) * ghostAnn m a := by rw [hAC]
      _ = -ghostAnn m a := by
            have hsqA : (ghostAnn m a : Module.End ℂ (FermiFock (m + 12))) * ghostAnn m a = 0 := by
              rw [ghostAnn]; exact annih_sq _
            calc (ghostCre m a : Module.End ℂ (FermiFock (m + 12)))
                    * (ghostAnn m a * ghostAnn m a)
                  - (1 - ghostCre m a * ghostAnn m a) * ghostAnn m a
                = ghostCre m a * (ghostAnn m a * ghostAnn m a) - ghostAnn m a
                  + ghostCre m a * (ghostAnn m a * ghostAnn m a) := by noncomm_ring
              _ = -ghostAnn m a := by rw [hsqA]; noncomm_ring
  · intro b _ hb
    have hne : ghostMode m b ≠ ghostMode m a := fun hh => hb (ghostMode_injective m hh)
    have hAC : (ghostAnn m a : Module.End ℂ (FermiFock (m + 12))) * ghostCre m b
        = -(ghostCre m b * ghostAnn m a) := by
      rw [ghostAnn, ghostCre, annih_mul_creat, if_neg (fun hh => hne hh.symm), zero_sub]
    have hAA : (ghostAnn m b : Module.End ℂ (FermiFock (m + 12))) * ghostAnn m a
        = -(ghostAnn m a * ghostAnn m b) := by
      rw [ghostAnn, ghostAnn, annih_mul_annih]
    calc (ghostCre m b * ghostAnn m b : Module.End ℂ (FermiFock (m + 12))) * ghostAnn m a
          - ghostAnn m a * (ghostCre m b * ghostAnn m b)
        = ghostCre m b * ((ghostAnn m b : Module.End ℂ (FermiFock (m + 12))) * ghostAnn m a)
            - ((ghostAnn m a : Module.End ℂ (FermiFock (m + 12))) * ghostCre m b)
              * ghostAnn m b := by noncomm_ring
      _ = ghostCre m b * -((ghostAnn m a : Module.End ℂ (FermiFock (m + 12))) * ghostAnn m b)
            - (-(ghostCre m b * ghostAnn m a) : Module.End ℂ (FermiFock (m + 12)))
              * ghostAnn m b := by rw [hAA, hAC]
      _ = 0 := by noncomm_ring
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- **The cubic ghost part of the Standard-Model BRST charge.** -/
def smGhostCharge (m : ℕ) (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    Module.End ℂ (FermiFock (m + 12)) :=
  Q (smStruct f3) (ghostCre m) (ghostAnn m)

/-- **The cubic ghost charge of the Standard Model is nilpotent.** -/
theorem smGhostCharge_nilpotent (m : ℕ) {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}
    (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0) :
    smGhostCharge m f3 * smGhostCharge m f3 = 0 :=
  brst_charge_nilpotent (smStruct f3) (ghostCre m) (ghostAnn m) (smGhostCAR m)
    (smStruct_antisymm h3anti) (smStruct_jacobi h3jac)


/-! ### Grading: the cubic term raises the ghost number by one -/

/-- **The ghost-number operator and a cubic ghost monomial do not commute.**  The two creation
factors each raise the ghost number by one and the annihilation factor lowers it by one, so
`N · c†_a c†_b b_e = c†_a c†_b b_e · N + c†_a c†_b b_e`: the monomial has ghost degree one. -/
theorem ghostNumber_mul_cubic_monomial (m : ℕ) (a b e : Fin 12) :
    ghostNumber m * (ghostCre m a * ghostCre m b * ghostAnn m e)
      = (ghostCre m a * ghostCre m b * ghostAnn m e) * ghostNumber m
        + (ghostCre m a * ghostCre m b * ghostAnn m e) := by
  have hC : ∀ a : Fin 12,
      ghostNumber m * ghostCre m a = ghostCre m a * ghostNumber m + ghostCre m a := by
    intro a
    have h := ghostNumber_comm_ghostCre m a
    rw [sub_eq_iff_eq_add] at h
    simpa [add_comm] using h
  have hA : ∀ e : Fin 12,
      ghostNumber m * ghostAnn m e = ghostAnn m e * ghostNumber m - ghostAnn m e := by
    intro e
    have h := ghostNumber_comm_ghostAnn m e
    rw [sub_eq_iff_eq_add] at h
    simpa [sub_eq_add_neg, add_comm] using h
  calc ghostNumber m * (ghostCre m a * ghostCre m b * ghostAnn m e)
      = (ghostNumber m * ghostCre m a) * (ghostCre m b * ghostAnn m e) := by noncomm_ring
    _ = (ghostCre m a * ghostNumber m + ghostCre m a)
          * (ghostCre m b * ghostAnn m e) := by rw [hC a]
    _ = ghostCre m a * (ghostNumber m * ghostCre m b) * ghostAnn m e
          + ghostCre m a * ghostCre m b * ghostAnn m e := by noncomm_ring
    _ = ghostCre m a * (ghostCre m b * ghostNumber m + ghostCre m b) * ghostAnn m e
          + ghostCre m a * ghostCre m b * ghostAnn m e := by rw [hC b]
    _ = ghostCre m a * ghostCre m b * (ghostNumber m * ghostAnn m e)
          + (2 : Module.End ℂ (FermiFock (m + 12)))
            * (ghostCre m a * ghostCre m b * ghostAnn m e) := by noncomm_ring
    _ = ghostCre m a * ghostCre m b * (ghostAnn m e * ghostNumber m - ghostAnn m e)
          + (2 : Module.End ℂ (FermiFock (m + 12)))
            * (ghostCre m a * ghostCre m b * ghostAnn m e) := by rw [hA e]
    _ = (ghostCre m a * ghostCre m b * ghostAnn m e) * ghostNumber m
          + ghostCre m a * ghostCre m b * ghostAnn m e := by noncomm_ring

set_option maxHeartbeats 800000 in
-- the twelvefold `Fin 8`-sum over `Module.End ℂ (FermiFock _)` exceeds the instance budget
set_option synthInstance.maxHeartbeats 800000 in
/-- **The cubic ghost charge raises the ghost number by exactly one**: `[N, Ω₃] = Ω₃`.  Hence
`Ω₃` maps the ghost-number-`g` subspace into the ghost-number-`g+1` subspace. -/
theorem ghostNumber_comm_smGhostCharge (m : ℕ) (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    ghostNumber m * smGhostCharge m f3 - smGhostCharge m f3 * ghostNumber m
      = smGhostCharge m f3 := by
  unfold smGhostCharge BookProof.BRSTNilpotent.Q
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, ghostNumber_mul_cubic_monomial,
    add_sub_cancel_left]

set_option maxHeartbeats 800000 in
-- the same `End`-of-`FermiFock` instance cost, now routed through the commutator
set_option synthInstance.maxHeartbeats 800000 in
/-- **The cubic term shifts ghost number by one on eigenvectors.**  If `ψ` has ghost number
`g`, then `Ω₃ ψ` has ghost number `g + 1`; in particular `Ω₃` is injective on a ghost-number
subspace only if the image misses it, which is why the cohomology is graded. -/
theorem ghostNumber_smGhostCharge_eigen (m : ℕ) (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (ψ : FermiFock (m + 12)) (g : ℂ) (hψ : ghostNumber m ψ = g • ψ) :
    ghostNumber m (smGhostCharge m f3 ψ) = (g + 1) • (smGhostCharge m f3 ψ) := by
  have h2 : ghostNumber m (smGhostCharge m f3 ψ) - smGhostCharge m f3 (ghostNumber m ψ)
      = smGhostCharge m f3 ψ := by
    have h := congrArg (fun A : Module.End ℂ (FermiFock (m + 12)) => A ψ)
      (ghostNumber_comm_smGhostCharge m f3)
    simpa using h
  calc ghostNumber m (smGhostCharge m f3 ψ)
      = (ghostNumber m (smGhostCharge m f3 ψ)
          - smGhostCharge m f3 (ghostNumber m ψ))
          + smGhostCharge m f3 (ghostNumber m ψ) := (sub_add_cancel _ _).symm
    _ = smGhostCharge m f3 ψ + smGhostCharge m f3 (g • ψ) := by rw [h2, hψ]
    _ = smGhostCharge m f3 ψ + g • smGhostCharge m f3 ψ := by rw [map_smul]
    _ = (1 + g) • (smGhostCharge m f3 ψ) := by rw [add_smul, one_smul]
    _ = (g + 1) • (smGhostCharge m f3 ψ) := by rw [add_comm 1 g]

/-! ## 3. The full BRST charge, in the abstract -/

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}

/-- Rotating the innermost index of a threefold sum to the front. -/
theorem sum_rotate3 {M : Type*} [AddCommMonoid M] {n : ℕ} (F : Fin n → Fin n → Fin n → M) :
    ∑ d : Fin n, ∑ g : Fin n, ∑ a : Fin n, F a d g
      = ∑ a : Fin n, ∑ d : Fin n, ∑ g : Fin n, F a d g := by
  calc ∑ d : Fin n, ∑ g : Fin n, ∑ a : Fin n, F a d g
      = ∑ d : Fin n, ∑ a : Fin n, ∑ g : Fin n, F a d g :=
        Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ a : Fin n, ∑ d : Fin n, ∑ g : Fin n, F a d g := Finset.sum_comm

/-- Rotating the innermost index of a fourfold sum to the front. -/
theorem sum_rotate4 {M : Type*} [AddCommMonoid M] {n : ℕ} (F : Fin n → Fin n → Fin n → Fin n → M) :
    ∑ d : Fin n, ∑ g : Fin n, ∑ h : Fin n, ∑ a : Fin n, F a d g h
      = ∑ a : Fin n, ∑ d : Fin n, ∑ g : Fin n, ∑ h : Fin n, F a d g h := by
  calc ∑ d : Fin n, ∑ g : Fin n, ∑ h : Fin n, ∑ a : Fin n, F a d g h
      = ∑ d : Fin n, ∑ g : Fin n, ∑ a : Fin n, ∑ h : Fin n, F a d g h :=
        Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun g _ => Finset.sum_comm
    _ = ∑ d : Fin n, ∑ a : Fin n, ∑ g : Fin n, ∑ h : Fin n, F a d g h :=
        Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ a : Fin n, ∑ d : Fin n, ∑ g : Fin n, ∑ h : Fin n, F a d g h := Finset.sum_comm

/-- **The BRST charge** `Ω = Σ_a c^a G_a − ½ f_{abc} c^a c^b b_c` of a family of first-class
constraints `G_a`. -/
def brstCharge (f : Fin n → Fin n → Fin n → ℝ) (χ β : Fin n → R) (G : Fin n → R) : R :=
  (∑ a, χ a * G a) - (1 / 2 : ℝ) • Q f χ β

/-- **Nilpotency of the full BRST charge.**  If the ghosts obey the CAR, the constraints
commute with the ghosts and close with real structure constants that are antisymmetric and
satisfy the Jacobi identity, then `Ω² = 0` — the fact that makes the BRST cohomology, hence
the physical (gauge-invariant) sector, well defined. -/
theorem brstCharge_nilpotent (f : Fin n → Fin n → Fin n → ℝ) (χ β G : Fin n → R)
    (hCAR : GhostCAR χ β)
    (hGχ : ∀ a b, G a * χ b = χ b * G a) (hGβ : ∀ a b, G a * β b = β b * G a)
    (hclose : ∀ a b, G a * G b - G b * G a = ∑ c, f a b c • G c)
    (hf12 : ∀ a b c, f a b c = -f b a c)
    (hjac : ∀ a b c h : Fin n,
      ∑ e, (f a b e * f e c h + f b c e * f e a h + f c a e * f e b h) = 0) :
    brstCharge f χ β G * brstCharge f χ β G = 0 := by
  classical
  -- the two halves of the charge
  set X : R := ∑ a, χ a * G a with hXdef
  -- moving a ghost creation operator through a cubic ghost monomial
  have hmove : ∀ a d g h : Fin n,
      χ a * (χ d * χ g * β h) + (χ d * χ g * β h) * χ a
        = (if h = a then (1 : R) else 0) * (χ d * χ g) := by
    intro a d g h
    have hb : β h * χ a = (if h = a then (1 : R) else 0) - χ a * β h :=
      eq_sub_of_add_eq (hCAR.betachi h a)
    have hda : χ d * χ a = -(χ a * χ d) := eq_neg_of_add_eq_zero_left (hCAR.chichi d a)
    have hga : χ g * χ a = -(χ a * χ g) := eq_neg_of_add_eq_zero_left (hCAR.chichi g a)
    have h3 : χ d * χ g * χ a = χ a * (χ d * χ g) := by
      calc χ d * χ g * χ a = χ d * (χ g * χ a) := by noncomm_ring
        _ = χ d * -(χ a * χ g) := by rw [hga]
        _ = -((χ d * χ a) * χ g) := by noncomm_ring
        _ = -((-(χ a * χ d)) * χ g) := by rw [hda]
        _ = χ a * (χ d * χ g) := by noncomm_ring
    have key : (χ d * χ g * β h) * χ a
        = (if h = a then (1 : R) else 0) * (χ d * χ g) - χ a * (χ d * χ g * β h) := by
      have h1 : (χ d * χ g * β h) * χ a = χ d * χ g * (β h * χ a) := by noncomm_ring
      rw [h1, hb]
      have h2 : χ d * χ g * ((if h = a then (1 : R) else 0) - χ a * β h)
          = (if h = a then (1 : R) else 0) * (χ d * χ g) - (χ d * χ g * χ a) * β h := by
        by_cases hh : h = a
        · simp only [hh, if_pos]; noncomm_ring
        · simp only [if_neg hh]; noncomm_ring
      rw [h2, h3]
      noncomm_ring
    rw [key]
    abel
  -- the square of the linear part
  have hXXexp : X * X = ∑ a, ∑ b, (χ a * χ b) * (G a * G b) := by
    rw [hXdef, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show (χ a * G a) * (χ b * G b) = χ a * (G a * χ b) * G b by noncomm_ring, hGχ a b]
    noncomm_ring
  have hswap : (∑ a, ∑ b, (χ a * χ b) * (G b * G a))
      = -∑ a, ∑ b, (χ a * χ b) * (G a * G b) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show χ b * χ a = -(χ a * χ b) from eq_neg_of_add_eq_zero_left (hCAR.chichi b a)]
    noncomm_ring
  have hXX2 : (2 : ℝ) • (X * X) = ∑ a, ∑ b, ∑ c, f a b c • (χ a * χ b * G c) := by
    rw [two_smul, hXXexp]
    nth_rewrite 2 [show (∑ a, ∑ b, (χ a * χ b) * (G a * G b))
        = -∑ a, ∑ b, (χ a * χ b) * (G b * G a) from by rw [hswap, neg_neg]]
    rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_sub, hclose a b, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [mul_smul_comm]
  -- the cross term
  have hXQ : X * Q f χ β + Q f χ β * X = ∑ a, ∑ b, ∑ c, f a b c • (χ a * χ b * G c) := by
    have hX1 : X * Q f χ β
        = ∑ a, ∑ d, ∑ g, ∑ h, f d g h • ((χ a * G a) * (χ d * χ g * β h)) := by
      rw [hXdef, Q, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun h _ => by rw [mul_smul_comm]
    have hQ1 : Q f χ β * X
        = ∑ a, ∑ d, ∑ g, ∑ h, f d g h • ((χ d * χ g * β h) * (χ a * G a)) := by
      rw [← sum_rotate4 (fun a d g h => f d g h • ((χ d * χ g * β h) * (χ a * G a)))]
      rw [hXdef, Q, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [smul_mul_assoc, Finset.mul_sum, Finset.smul_sum]
    rw [hX1, hQ1, ← Finset.sum_add_distrib]
    have hcollapse : ∀ a : Fin n,
        ((∑ d, ∑ g, ∑ h, f d g h • ((χ a * G a) * (χ d * χ g * β h)))
          + ∑ d, ∑ g, ∑ h, f d g h • ((χ d * χ g * β h) * (χ a * G a)))
        = ∑ d, ∑ g, f d g a • (χ d * χ g * G a) := by
      intro a
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      refine Finset.sum_congr rfl fun g _ => ?_
      have hterm : ∀ h : Fin n,
          f d g h • ((χ a * G a) * (χ d * χ g * β h))
            + f d g h • ((χ d * χ g * β h) * (χ a * G a))
          = f d g h • ((if h = a then (1 : R) else 0) * (χ d * χ g * G a)) := by
        intro h
        rw [← smul_add]
        congr 1
        have hc1 : (χ a * G a) * (χ d * χ g * β h) = (χ a * (χ d * χ g * β h)) * G a := by
          have hg1 : G a * (χ d * χ g * β h) = (χ d * χ g * β h) * G a := by
            rw [show G a * (χ d * χ g * β h) = ((G a * χ d) * χ g) * β h by noncomm_ring,
              hGχ a d,
              show ((χ d * G a) * χ g) * β h = (χ d * (G a * χ g)) * β h by noncomm_ring,
              hGχ a g,
              show (χ d * (χ g * G a)) * β h = (χ d * χ g) * (G a * β h) by noncomm_ring,
              hGβ a h]
            noncomm_ring
          calc (χ a * G a) * (χ d * χ g * β h)
              = χ a * (G a * (χ d * χ g * β h)) := by noncomm_ring
            _ = χ a * ((χ d * χ g * β h) * G a) := by rw [hg1]
            _ = (χ a * (χ d * χ g * β h)) * G a := by noncomm_ring
        have hc2 : (χ d * χ g * β h) * (χ a * G a)
            = ((χ d * χ g * β h) * χ a) * G a := by noncomm_ring
        rw [hc1, hc2, ← add_mul, hmove a d g h]
        noncomm_ring
      rw [Finset.sum_congr rfl fun h (_ : h ∈ Finset.univ) => hterm h]
      rw [Finset.sum_eq_single a]
      · rw [if_pos rfl, one_mul]
      · intro h _ hh
        rw [if_neg hh, zero_mul, smul_zero]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
    rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hcollapse a]
    rw [← sum_rotate3 (fun a d g => f d g a • (χ d * χ g * G a))]
  -- nilpotency of the cubic ghost term
  have hQnil : Q f χ β * Q f χ β = 0 := brst_charge_nilpotent f χ β hCAR hf12 hjac
  -- assemble
  have h2 : (2 : ℝ) • (brstCharge f χ β G * brstCharge f χ β G) = 0 := by
    have hexp : brstCharge f χ β G * brstCharge f χ β G
        = X * X - (1 / 2 : ℝ) • (X * Q f χ β + Q f χ β * X)
          + (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (Q f χ β * Q f χ β)) := by
      rw [brstCharge, ← hXdef]
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub]
      abel
    have htwo : ((2 : ℝ) * (1 / 2 : ℝ)) = 1 := by norm_num
    rw [hexp, hQnil, smul_zero, smul_zero, add_zero, smul_sub, smul_smul, htwo, one_smul,
      hXX2, hXQ, sub_self]
  have hne : (2 : ℝ) ≠ 0 := two_ne_zero
  rcases smul_eq_zero.mp h2 with h | h
  · exact absurd h hne
  · exact h

/-! ## 4. The Gauss-law constraints: second quantization as a Lie homomorphism -/

variable {N : ℕ}

/-- The commutator of two occupation bilinears, from the canonical anticommutation
relations. -/
theorem creat_annih_commutator (i j k l : Fin N) :
    (creat i * annih j : Module.End ℂ (FermiFock N)) * (creat k * annih l)
        - (creat k * annih l) * (creat i * annih j)
      = (if j = k then (creat i * annih l : Module.End ℂ (FermiFock N)) else 0)
        - (if l = i then (creat k * annih j : Module.End ℂ (FermiFock N)) else 0) := by
  have e1 : (creat i * annih j : Module.End ℂ (FermiFock N)) * (creat k * annih l)
      = (if j = k then (creat i * annih l : Module.End ℂ (FermiFock N)) else 0)
        - creat i * creat k * (annih j * annih l) := by
    have h0 : (creat i * annih j : Module.End ℂ (FermiFock N)) * (creat k * annih l)
        = creat i * ((annih j : Module.End ℂ (FermiFock N)) * creat k) * annih l := by
      noncomm_ring
    rw [h0, annih_mul_creat j k]
    by_cases h : j = k
    · rw [if_pos h, if_pos h]; noncomm_ring
    · rw [if_neg h, if_neg h]; noncomm_ring
  have e2 : (creat k * annih l : Module.End ℂ (FermiFock N)) * (creat i * annih j)
      = (if l = i then (creat k * annih j : Module.End ℂ (FermiFock N)) else 0)
        - creat k * creat i * (annih l * annih j) := by
    have h0 : (creat k * annih l : Module.End ℂ (FermiFock N)) * (creat i * annih j)
        = creat k * ((annih l : Module.End ℂ (FermiFock N)) * creat i) * annih j := by
      noncomm_ring
    rw [h0, annih_mul_creat l i]
    by_cases h : l = i
    · rw [if_pos h, if_pos h]; noncomm_ring
    · rw [if_neg h, if_neg h]; noncomm_ring
  have e3 : (creat k * creat i : Module.End ℂ (FermiFock N)) * (annih l * annih j)
      = creat i * creat k * (annih j * annih l) := by
    rw [creat_mul_creat k i, annih_mul_annih l j]
    noncomm_ring
  rw [e1, e2, e3]
  abel

/-- The second quantization written with the ring multiplication of `Module.End`. -/
theorem fermiBilin_eq4 (M : Matrix (Fin N) (Fin N) ℂ) :
    (fermiBilin M : Module.End ℂ (FermiFock N))
      = ∑ i : Fin N, ∑ j : Fin N, M i j • (creat i * annih j) := rfl

theorem fermiBilin_sub (M P : Matrix (Fin N) (Fin N) ℂ) :
    (fermiBilin (M - P) : Module.End ℂ (FermiFock N)) = fermiBilin M - fermiBilin P := by
  rw [fermiBilin_eq4, fermiBilin_eq4, fermiBilin_eq4, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [Matrix.sub_apply, sub_smul]

theorem fermiBilin_mul4 (M P : Matrix (Fin N) (Fin N) ℂ) :
    (fermiBilin M : Module.End ℂ (FermiFock N)) * fermiBilin P
      = ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
          (M i j * P k l) • ((creat i * annih j) * (creat k * annih l)) := by
  rw [fermiBilin_eq4, fermiBilin_eq4, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

/-- Swapping the two index pairs of a fourfold sum. -/
theorem sum4_swap (F : Fin N → Fin N → Fin N → Fin N → Module.End ℂ (FermiFock N)) :
    ∑ k : Fin N, ∑ l : Fin N, ∑ i : Fin N, ∑ j : Fin N, F i j k l
      = ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, F i j k l := by
  calc ∑ k : Fin N, ∑ l : Fin N, ∑ i : Fin N, ∑ j : Fin N, F i j k l
      = ∑ q : Fin N × Fin N, ∑ p : Fin N × Fin N, F p.1 p.2 q.1 q.2 := by
        simp [Fintype.sum_prod_type]
    _ = ∑ p : Fin N × Fin N, ∑ q : Fin N × Fin N, F p.1 p.2 q.1 q.2 := Finset.sum_comm
    _ = ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, F i j k l := by
        simp [Fintype.sum_prod_type]

/-- The first delta contraction of the commutator sum. -/
theorem sum_delta_left (M P : Matrix (Fin N) (Fin N) ℂ) :
    ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        (M i j * P k l) • (if j = k then (creat i * annih l : Module.End ℂ (FermiFock N)) else 0)
      = fermiBilin (M * P) := by
  have step1 : ∀ i j : Fin N,
      (∑ k : Fin N, ∑ l : Fin N,
        (M i j * P k l) • (if j = k then (creat i * annih l : Module.End ℂ (FermiFock N)) else 0))
        = ∑ l : Fin N, (M i j * P j l) • (creat i * annih l : Module.End ℂ (FermiFock N)) := by
    intro i j
    rw [Finset.sum_eq_single j]
    · exact Finset.sum_congr rfl fun l _ => by rw [if_pos rfl]
    · intro k _ hk
      exact Finset.sum_eq_zero fun l _ => by rw [if_neg (Ne.symm hk), smul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  calc ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        (M i j * P k l) • (if j = k then (creat i * annih l : Module.End ℂ (FermiFock N)) else 0)
      = ∑ i : Fin N, ∑ j : Fin N, ∑ l : Fin N,
          (M i j * P j l) • (creat i * annih l : Module.End ℂ (FermiFock N)) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => step1 i j
    _ = ∑ i : Fin N, ∑ l : Fin N, ∑ j : Fin N,
          (M i j * P j l) • (creat i * annih l : Module.End ℂ (FermiFock N)) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i : Fin N, ∑ l : Fin N,
          ((M * P) i l) • (creat i * annih l : Module.End ℂ (FermiFock N)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
        rw [← Finset.sum_smul, Matrix.mul_apply]
    _ = fermiBilin (M * P) := (fermiBilin_eq4 (M * P)).symm

/-- The second delta contraction of the commutator sum. -/
theorem sum_delta_right (M P : Matrix (Fin N) (Fin N) ℂ) :
    ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        (M i j * P k l) • (if l = i then (creat k * annih j : Module.End ℂ (FermiFock N)) else 0)
      = fermiBilin (P * M) := by
  have step1 : ∀ i j k : Fin N,
      (∑ l : Fin N,
        (M i j * P k l) • (if l = i then (creat k * annih j : Module.End ℂ (FermiFock N)) else 0))
        = (M i j * P k i) • (creat k * annih j : Module.End ℂ (FermiFock N)) := by
    intro i j k
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]
    · intro l _ hl
      rw [if_neg hl, smul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  calc ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        (M i j * P k l) • (if l = i then (creat k * annih j : Module.End ℂ (FermiFock N)) else 0)
      = ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
          (M i j * P k i) • (creat k * annih j : Module.End ℂ (FermiFock N)) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => step1 i j k
    _ = ∑ i : Fin N, ∑ k : Fin N, ∑ j : Fin N,
          (M i j * P k i) • (creat k * annih j : Module.End ℂ (FermiFock N)) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k : Fin N, ∑ i : Fin N, ∑ j : Fin N,
          (M i j * P k i) • (creat k * annih j : Module.End ℂ (FermiFock N)) := Finset.sum_comm
    _ = ∑ k : Fin N, ∑ j : Fin N, ∑ i : Fin N,
          (M i j * P k i) • (creat k * annih j : Module.End ℂ (FermiFock N)) := by
        exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k : Fin N, ∑ j : Fin N,
          ((P * M) k j) • (creat k * annih j : Module.End ℂ (FermiFock N)) := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_smul, Matrix.mul_apply]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = fermiBilin (P * M) := (fermiBilin_eq4 (P * M)).symm

/-- **Second quantization is a Lie-algebra homomorphism**: `[dΓ(A), dΓ(B)] = dΓ([A,B])`. -/
theorem fermiBilin_lie (A B : Matrix (Fin N) (Fin N) ℂ) :
    (fermiBilin A : Module.End ℂ (FermiFock N)) * fermiBilin B
        - fermiBilin B * fermiBilin A
      = fermiBilin (A * B - B * A) := by
  have h2 : (fermiBilin B : Module.End ℂ (FermiFock N)) * fermiBilin A
      = ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
          (A i j * B k l) • ((creat k * annih l) * (creat i * annih j)) := by
    rw [fermiBilin_mul4 B A,
      ← sum4_swap (fun i j k l =>
        (A i j * B k l) • ((creat k * annih l : Module.End ℂ (FermiFock N))
          * (creat i * annih j)))]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  rw [fermiBilin_mul4 A B, h2]
  have hcomb : ∀ X Y : Fin N → Fin N → Fin N → Fin N → Module.End ℂ (FermiFock N),
      (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, X i j k l)
        - (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, Y i j k l)
      = ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, (X i j k l - Y i j k l) := by
    intro X Y
    simp only [← Finset.sum_sub_distrib]
  rw [hcomb]
  have hterm : ∀ i j k l : Fin N,
      ((A i j * B k l) • ((creat i * annih j : Module.End ℂ (FermiFock N)) * (creat k * annih l))
        - (A i j * B k l) • ((creat k * annih l : Module.End ℂ (FermiFock N))
            * (creat i * annih j)))
      = (A i j * B k l) • (if j = k then (creat i * annih l : Module.End ℂ (FermiFock N)) else 0)
        - (A i j * B k l)
            • (if l = i then (creat k * annih j : Module.End ℂ (FermiFock N)) else 0) := by
    intro i j k l
    rw [← smul_sub, ← smul_sub, creat_annih_commutator i j k l]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => Finset.sum_congr rfl
    fun j (_ : j ∈ Finset.univ) => Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
      Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hterm i j k l]
  rw [← hcomb, sum_delta_left A B, sum_delta_right A B, ← fermiBilin_sub]

/-- A second-quantized operator whose `k`-th column vanishes commutes with the creation
operator of the mode `k`: bilinears are even. -/
theorem fermiBilin_comm_creat {A : Matrix (Fin N) (Fin N) ℂ} {k : Fin N}
    (hcol : ∀ i, A i k = 0) :
    (fermiBilin A : Module.End ℂ (FermiFock N)) * creat k
      = creat k * fermiBilin A := by
  rw [fermiBilin_eq4, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j = k
  · subst h
    rw [hcol i, zero_smul, zero_mul, mul_zero]
  · rw [smul_mul_assoc, mul_smul_comm]
    congr 1
    have h1 : (annih j : Module.End ℂ (FermiFock N)) * creat k = -(creat k * annih j) := by
      rw [annih_mul_creat j k, if_neg h, zero_sub]
    calc (creat i * annih j : Module.End ℂ (FermiFock N)) * creat k
        = creat i * ((annih j : Module.End ℂ (FermiFock N)) * creat k) := by noncomm_ring
      _ = creat i * -(creat k * annih j) := by rw [h1]
      _ = -((creat i : Module.End ℂ (FermiFock N)) * creat k) * annih j := by noncomm_ring
      _ = -(-((creat k : Module.End ℂ (FermiFock N)) * creat i)) * annih j := by
            rw [creat_mul_creat i k]
      _ = creat k * (creat i * annih j) := by noncomm_ring

/-- A second-quantized operator whose `k`-th row vanishes commutes with the annihilation
operator of the mode `k`. -/
theorem fermiBilin_comm_annih {A : Matrix (Fin N) (Fin N) ℂ} {k : Fin N}
    (hrow : ∀ j, A k j = 0) :
    (fermiBilin A : Module.End ℂ (FermiFock N)) * annih k
      = annih k * fermiBilin A := by
  rw [fermiBilin_eq4, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i = k
  · subst h
    rw [hrow j, zero_smul, zero_mul, mul_zero]
  · rw [smul_mul_assoc, mul_smul_comm]
    congr 1
    have h1 : (annih k : Module.End ℂ (FermiFock N)) * creat i = -(creat i * annih k) := by
      rw [annih_mul_creat k i, if_neg (fun hh => h hh.symm), zero_sub]
    calc (creat i * annih j : Module.End ℂ (FermiFock N)) * annih k
        = creat i * ((annih j : Module.End ℂ (FermiFock N)) * annih k) := by noncomm_ring
      _ = creat i * -((annih k : Module.End ℂ (FermiFock N)) * annih j) := by
            rw [annih_mul_annih j k]
      _ = -((creat i : Module.End ℂ (FermiFock N)) * annih k) * annih j := by noncomm_ring
      _ = ((annih k : Module.End ℂ (FermiFock N)) * creat i) * annih j := by rw [← h1]
      _ = annih k * (creat i * annih j) := by noncomm_ring

/-- Second quantization is linear in the one-particle matrix. -/
theorem fermiBilin_smul (c : ℂ) (M : Matrix (Fin N) (Fin N) ℂ) :
    (fermiBilin (c • M) : Module.End ℂ (FermiFock N)) = c • fermiBilin M := by
  rw [fermiBilin_eq4, fermiBilin_eq4, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [Matrix.smul_apply, smul_eq_mul, mul_smul]

/-- Second quantization is additive in the one-particle matrix. -/
theorem fermiBilin_add' (M P : Matrix (Fin N) (Fin N) ℂ) :
    (fermiBilin (M + P) : Module.End ℂ (FermiFock N)) = fermiBilin M + fermiBilin P := by
  rw [fermiBilin_eq4, fermiBilin_eq4, fermiBilin_eq4, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [Matrix.add_apply, add_smul]

/-- Second quantization commutes with finite sums of one-particle matrices. -/
theorem fermiBilin_sum {ι : Type*} (s : Finset ι) (M : ι → Matrix (Fin N) (Fin N) ℂ) :
    (fermiBilin (∑ t ∈ s, M t) : Module.End ℂ (FermiFock N))
      = ∑ t ∈ s, fermiBilin (M t) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, fermiBilin_eq4]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      exact fermiBilin_add' (M a) (∑ t ∈ s, M t)

/-! ## 5. The Standard-Model BRST charge -/

/-- The matter block of a one-particle operator, embedded in the joint matter ⊗ ghost mode
set: the operator acts on the first `m` modes and annihilates the ghosts. -/
def embedMatter (m : ℕ) (M : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin (m + 12)) (Fin (m + 12)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M 0 0 0)

/-- **The Gauss-law generator** of the `a`-th gauge direction: the second quantization
`−i dΓ(T_a)` of the one-particle generator on the matter modes. -/
def matterGen (m : ℕ) (T : Fin 12 → Matrix (Fin m) (Fin m) ℂ) (a : Fin 12) :
    Module.End ℂ (FermiFock (m + 12)) :=
  (-Complex.I) • fermiBilin (embedMatter m (T a))

/-- The embedded matter block has no entry in a ghost column. -/
theorem embedMatter_col_ghost (m : ℕ) (M : Matrix (Fin m) (Fin m) ℂ) (b : Fin 12)
    (i : Fin (m + 12)) : embedMatter m M i (ghostMode m b) = 0 := by
  rcases h : finSumFinEquiv.symm i with u | u <;>
    simp [embedMatter, ghostMode, Matrix.reindex_apply, Matrix.submatrix_apply, h]

/-- The embedded matter block has no entry in a ghost row. -/
theorem embedMatter_row_ghost (m : ℕ) (M : Matrix (Fin m) (Fin m) ℂ) (b : Fin 12)
    (j : Fin (m + 12)) : embedMatter m M (ghostMode m b) j = 0 := by
  rcases h : finSumFinEquiv.symm j with u | u <;>
    simp [embedMatter, ghostMode, Matrix.reindex_apply, Matrix.submatrix_apply, h]

/-- Embedding the matter block is multiplicative. -/
theorem embedMatter_mul (m : ℕ) (M P : Matrix (Fin m) (Fin m) ℂ) :
    embedMatter m M * embedMatter m P = embedMatter m (M * P) := by
  simp only [embedMatter, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv (Matrix.fromBlocks M 0 0 0) (Matrix.fromBlocks P 0 0 0)
    finSumFinEquiv.symm finSumFinEquiv.symm finSumFinEquiv.symm]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  simp

/-- Embedding the matter block is compatible with subtraction. -/
theorem embedMatter_sub (m : ℕ) (M P : Matrix (Fin m) (Fin m) ℂ) :
    embedMatter m (M - P) = embedMatter m M - embedMatter m P := by
  ext i j
  simp only [embedMatter, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply]
  rcases finSumFinEquiv.symm i with u | u <;> rcases finSumFinEquiv.symm j with v | v <;> simp

/-- Embedding the matter block is compatible with scalar multiplication. -/
theorem embedMatter_smul (m : ℕ) (c : ℂ) (M : Matrix (Fin m) (Fin m) ℂ) :
    embedMatter m (c • M) = c • embedMatter m M := by
  ext i j
  simp only [embedMatter, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply,
    smul_eq_mul]
  rcases finSumFinEquiv.symm i with u | u <;> rcases finSumFinEquiv.symm j with v | v <;> simp

/-- Embedding the matter block is compatible with finite sums. -/
theorem embedMatter_sum {m : ℕ} {ι : Type*} (s : Finset ι) (M : ι → Matrix (Fin m) (Fin m) ℂ) :
    embedMatter m (∑ t ∈ s, M t) = ∑ t ∈ s, embedMatter m (M t) := by
  classical
  induction s using Finset.induction with
  | empty =>
      ext i j
      simp [embedMatter, Matrix.reindex_apply, Matrix.submatrix_apply]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      ext i j
      simp only [embedMatter, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply]
      rcases finSumFinEquiv.symm i with u | u <;> rcases finSumFinEquiv.symm j with v | v <;> simp

/-- **The Gauss-law generators close with the real structure constants.** -/
theorem matterGen_lie {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ}
    {f : Fin 12 → Fin 12 → Fin 12 → ℝ} (hT : ClosesWithStructureConstants T f) (a b : Fin 12) :
    matterGen m T a * matterGen m T b - matterGen m T b * matterGen m T a
      = ∑ c, f a b c • matterGen m T c := by
  have hstep : matterGen m T a * matterGen m T b - matterGen m T b * matterGen m T a
      = ((-Complex.I) * (-Complex.I)) •
          (fermiBilin (embedMatter m (T a * T b - T b * T a))
            : Module.End ℂ (FermiFock (m + 12))) := by
    rw [matterGen, matterGen, smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub,
      fermiBilin_lie, embedMatter_mul, embedMatter_mul, ← embedMatter_sub]
  rw [hstep, hT a b, embedMatter_smul, fermiBilin_smul, embedMatter_sum, fermiBilin_sum,
    smul_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [embedMatter_smul, fermiBilin_smul, matterGen, smul_smul, ← Complex.coe_smul, smul_smul]
  congr 1
  have hII : (-Complex.I) * (-Complex.I) = -1 := by rw [neg_mul_neg, Complex.I_mul_I]
  rw [hII]
  ring

/-- The Gauss-law generators commute with the ghost creation operators. -/
theorem matterGen_comm_ghostCre (m : ℕ) (T : Fin 12 → Matrix (Fin m) (Fin m) ℂ) (a b : Fin 12) :
    matterGen m T a * ghostCre m b = ghostCre m b * matterGen m T a := by
  rw [matterGen, ghostCre, smul_mul_assoc, mul_smul_comm,
    fermiBilin_comm_creat (fun i => embedMatter_col_ghost m (T a) b i)]

/-- The Gauss-law generators commute with the ghost annihilation operators. -/
theorem matterGen_comm_ghostAnn (m : ℕ) (T : Fin 12 → Matrix (Fin m) (Fin m) ℂ) (a b : Fin 12) :
    matterGen m T a * ghostAnn m b = ghostAnn m b * matterGen m T a := by
  rw [matterGen, ghostAnn, smul_mul_assoc, mul_smul_comm,
    fermiBilin_comm_annih (fun j => embedMatter_row_ghost m (T a) b j)]

/-- **The Standard-Model BRST charge** on the joint matter ⊗ ghost Fock space. -/
def smBrstCharge (m : ℕ) (T : Fin 12 → Matrix (Fin m) (Fin m) ℂ)
    (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ) : Module.End ℂ (FermiFock (m + 12)) :=
  brstCharge (smStruct f3) (ghostCre m) (ghostAnn m) (matterGen m T)

/-- **The Standard-Model BRST charge is nilpotent**: `Ω² = 0`.  The gauge algebra
`su(3) ⊕ su(2) ⊕ u(1)`, its Gauss-law generators on the matter CAR algebra and the twelve
ghosts assemble into a nilpotent charge, so the BRST cohomology — the physical sector of the
gauge-fixed Standard-Model Hamiltonian — is well defined. -/
theorem smBrstCharge_nilpotent {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ}
    {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ} (hT : ClosesWithStructureConstants T (smStruct f3))
    (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0) :
    smBrstCharge m T f3 * smBrstCharge m T f3 = 0 :=
  brstCharge_nilpotent (smStruct f3) (ghostCre m) (ghostAnn m) (matterGen m T) (smGhostCAR m)
    (matterGen_comm_ghostCre m T) (matterGen_comm_ghostAnn m T)
    (fun a b => matterGen_lie hT a b) (smStruct_antisymm h3anti) (smStruct_jacobi h3jac)

/-! ## 6. The ghost-parity operator

`ghostNumber` is diagonal in the occupation basis with integer eigenvalue the number of occupied
ghost modes.  Its parity — `U = (-1)^{N_ghost}` — is the fundamental symmetry of the indefinite Fock
space: an involution, an isometry of the ambient inner product, and self-adjoint, so that
`kform U x y = ⟪x, U y⟫` is a Krein form.  The charge is *odd* for it
(`smGhostParity_mul_smBrstCharge`, `U Ω = -Ω U`): the Gauss term carries one ghost field and the
cubic term three.  That is what lets the sector split of `ChapterSmBrstQuotient` §3 be applied to
the SM charge, and it is the operator against which the no-ghost sign on `range smPhysProj` is
computed (`ChapterSmQuartet` §12).

The parity is written in the occupation basis rather than as the product `∏_a (1 - 2 c^a b_a)` so
that its metric properties (involution, isometry, self-adjointness) are one computation each; the
product form is the same operator, but nothing below needs that identification.
-/

/-- The eigenvalue of the ghost parity on the occupation state `S`: `(-1)` to the number of
occupied ghost modes. -/
noncomputable def ghostParitySign (m : ℕ) (S : Finset (Fin (m + 12))) : ℂ :=
  (-1 : ℂ) ^ (S.filter (fun i => ∃ a : Fin 12, ghostMode m a = i)).card

theorem ghostParitySign_sq (m : ℕ) (S : Finset (Fin (m + 12))) :
    ghostParitySign m S * ghostParitySign m S = 1 := by
  rw [ghostParitySign, ← pow_add, ← two_mul, pow_mul]
  norm_num

@[simp] theorem conj_ghostParitySign (m : ℕ) (S : Finset (Fin (m + 12))) :
    (starRingEnd ℂ) (ghostParitySign m S) = ghostParitySign m S := by
  simp [ghostParitySign]

@[simp] theorem norm_ghostParitySign (m : ℕ) (S : Finset (Fin (m + 12))) :
    ‖ghostParitySign m S‖ = 1 := by
  simp [ghostParitySign]

/-- Occupying a ghost mode flips the parity. -/
theorem ghostParitySign_insert_ghost (m : ℕ) (a : Fin 12) {S : Finset (Fin (m + 12))}
    (h : ghostMode m a ∉ S) :
    ghostParitySign m (insert (ghostMode m a) S) = -ghostParitySign m S := by
  rw [ghostParitySign, ghostParitySign, Finset.filter_insert, if_pos ⟨a, rfl⟩,
    Finset.card_insert_of_notMem (fun hmem => h (Finset.mem_filter.mp hmem).1), pow_succ]
  ring

/-- Occupying a matter mode leaves the parity alone. -/
theorem ghostParitySign_insert_matter (m : ℕ) {i : Fin (m + 12)}
    (h : ∀ a : Fin 12, ghostMode m a ≠ i) (S : Finset (Fin (m + 12))) :
    ghostParitySign m (insert i S) = ghostParitySign m S := by
  rw [ghostParitySign, ghostParitySign, Finset.filter_insert, if_neg (fun hx => hx.elim h)]

/-- The same flip, in the direction needed when erasing an occupied ghost. -/
theorem ghostParitySign_erase_ghost (m : ℕ) (a : Fin 12) {S : Finset (Fin (m + 12))}
    (h : ghostMode m a ∈ S) :
    ghostParitySign m S = -ghostParitySign m (S.erase (ghostMode m a)) := by
  nth_rewrite 1 [← Finset.insert_erase h]
  exact ghostParitySign_insert_ghost m a (Finset.notMem_erase _ _)

/-- The same, for a matter mode. -/
theorem ghostParitySign_erase_matter (m : ℕ) {i : Fin (m + 12)}
    (h : ∀ a : Fin 12, ghostMode m a ≠ i) {S : Finset (Fin (m + 12))} (hi : i ∈ S) :
    ghostParitySign m S = ghostParitySign m (S.erase i) := by
  nth_rewrite 1 [← Finset.insert_erase hi]
  exact ghostParitySign_insert_matter m h _

/-- **The ghost parity** `U = (-1)^{N_ghost}`, diagonal in the occupation basis. -/
noncomputable def smGhostParity (m : ℕ) : Module.End ℂ (FermiFock (m + 12)) where
  toFun ψ := WithLp.toLp 2 (fun S => ghostParitySign m S * ψ S)
  map_add' x y := by
    ext S
    simp [mul_add]
  map_smul' c x := by
    ext S
    simp [mul_left_comm]

@[simp] theorem smGhostParity_apply (m : ℕ) (ψ : FermiFock (m + 12))
    (S : Finset (Fin (m + 12))) :
    smGhostParity m ψ S = ghostParitySign m S * ψ S := rfl

/-- The ghost parity is an involution. -/
theorem smGhostParity_involutive (m : ℕ) (ψ : FermiFock (m + 12)) :
    smGhostParity m (smGhostParity m ψ) = ψ := by
  ext S
  rw [smGhostParity_apply, smGhostParity_apply, ← mul_assoc, ghostParitySign_sq, one_mul]

/-- The ghost parity composed with itself is the identity, in `End` form. -/
theorem smGhostParity_comp (m : ℕ) :
    smGhostParity m ∘ₗ smGhostParity m = LinearMap.id :=
  LinearMap.ext (smGhostParity_involutive m)

/-- The ghost parity is an isometry of the ambient inner product. -/
theorem smGhostParity_isometry (m : ℕ) (ψ : FermiFock (m + 12)) :
    ‖smGhostParity m ψ‖ = ‖ψ‖ := by
  have h : ‖smGhostParity m ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [normSq_eq_sum, normSq_eq_sum]
    exact Finset.sum_congr rfl fun S _ => by
      rw [smGhostParity_apply, norm_mul, norm_ghostParitySign, one_mul]
  nlinarith [norm_nonneg (smGhostParity m ψ), norm_nonneg ψ]

/-- The ghost parity is self-adjoint for the ambient inner product, which is what makes
`kform U` a symmetric form. -/
theorem smGhostParity_selfAdjoint (m : ℕ) (x y : FermiFock (m + 12)) :
    inner ℂ (smGhostParity m x) y = inner ℂ x (smGhostParity m y) := by
  rw [inner_eq_sum, inner_eq_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [smGhostParity_apply, smGhostParity_apply, map_mul, conj_ghostParitySign]
  ring

/-- **A ghost creation operator anticommutes with the parity**: it flips the number of occupied
ghost modes. -/
theorem smGhostParity_add_ghostCre (m : ℕ) (a : Fin 12) :
    smGhostParity m * ghostCre m a + ghostCre m a * smGhostParity m = 0 := by
  refine LinearMap.ext fun ψ => ?_
  ext S
  by_cases h : ghostMode m a ∈ S
  · simp only [Module.End.mul_apply, smGhostParity_apply, ghostCre, creat_apply,
      Module.End.mul_apply, LinearMap.add_apply, PiLp.add_apply, PiLp.zero_apply,
      LinearMap.zero_apply, if_pos h]
    rw [ghostParitySign_erase_ghost m a h]
    ring
  · simp only [Module.End.mul_apply, smGhostParity_apply, ghostCre, creat_apply,
      Module.End.mul_apply, LinearMap.add_apply, PiLp.add_apply, PiLp.zero_apply,
      LinearMap.zero_apply, if_neg h, mul_zero, add_zero]

theorem smGhostParity_mul_ghostCre (m : ℕ) (a : Fin 12) :
    smGhostParity m * ghostCre m a = -(ghostCre m a * smGhostParity m) :=
  eq_neg_of_add_eq_zero_left (smGhostParity_add_ghostCre m a)

/-- A ghost annihilation operator anticommutes with the parity. -/
theorem smGhostParity_add_ghostAnn (m : ℕ) (a : Fin 12) :
    smGhostParity m * ghostAnn m a + ghostAnn m a * smGhostParity m = 0 := by
  refine LinearMap.ext fun ψ => ?_
  ext S
  by_cases h : ghostMode m a ∈ S
  · simp only [Module.End.mul_apply, smGhostParity_apply, ghostAnn, annih_apply,
      Module.End.mul_apply, LinearMap.add_apply, PiLp.add_apply, PiLp.zero_apply,
      LinearMap.zero_apply, if_pos h, mul_zero, add_zero]
  · simp only [Module.End.mul_apply, smGhostParity_apply, ghostAnn, annih_apply,
      Module.End.mul_apply, LinearMap.add_apply, PiLp.add_apply, PiLp.zero_apply,
      LinearMap.zero_apply, if_neg h]
    rw [ghostParitySign_insert_ghost m a h]
    ring

theorem smGhostParity_mul_ghostAnn (m : ℕ) (a : Fin 12) :
    smGhostParity m * ghostAnn m a = -(ghostAnn m a * smGhostParity m) :=
  eq_neg_of_add_eq_zero_left (smGhostParity_add_ghostAnn m a)

/-- A matter creation operator commutes with the parity: it does not change the number of
occupied ghost modes. -/
theorem smGhostParity_mul_creat_matter (m : ℕ) {i : Fin (m + 12)}
    (h : ∀ a : Fin 12, ghostMode m a ≠ i) :
    smGhostParity m * creat i = creat i * smGhostParity m := by
  refine LinearMap.ext fun ψ => ?_
  ext S
  by_cases hi : i ∈ S
  · simp only [Module.End.mul_apply, smGhostParity_apply, creat_apply, if_pos hi]
    rw [ghostParitySign_erase_matter m h hi]
    ring
  · simp only [Module.End.mul_apply, smGhostParity_apply, creat_apply, if_neg hi, mul_zero]

/-- A matter annihilation operator commutes with the parity. -/
theorem smGhostParity_mul_annih_matter (m : ℕ) {i : Fin (m + 12)}
    (h : ∀ a : Fin 12, ghostMode m a ≠ i) :
    smGhostParity m * annih i = annih i * smGhostParity m := by
  refine LinearMap.ext fun ψ => ?_
  ext S
  by_cases hi : i ∈ S
  · simp only [Module.End.mul_apply, smGhostParity_apply, annih_apply, if_pos hi, mul_zero]
  · simp only [Module.End.mul_apply, smGhostParity_apply, annih_apply, if_neg hi]
    rw [ghostParitySign_insert_matter m h S]
    ring

/-- **The parity commutes with second quantization of a matter-only matrix**: every mode it touches
is a matter mode. -/
theorem smGhostParity_comm_fermiBilin_matter (m : ℕ) (M : Matrix (Fin m) (Fin m) ℂ) :
    smGhostParity m * fermiBilin (embedMatter m M)
      = fermiBilin (embedMatter m M) * smGhostParity m := by
  rw [fermiBilin_eq4, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hi : ∃ a : Fin 12, ghostMode m a = i
  · obtain ⟨a, rfl⟩ := hi
    rw [embedMatter_row_ghost]
    simp
  by_cases hj : ∃ a : Fin 12, ghostMode m a = j
  · obtain ⟨a, rfl⟩ := hj
    rw [embedMatter_col_ghost]
    simp
  push_neg at hi hj
  rw [mul_smul_comm]
  conv_rhs => rw [smul_mul_assoc]
  congr 1
  calc smGhostParity m * (creat i * annih j)
      = (smGhostParity m * creat i) * annih j := by rw [mul_assoc]
    _ = (creat i * smGhostParity m) * annih j := by
          rw [smGhostParity_mul_creat_matter m hi]
    _ = creat i * (smGhostParity m * annih j) := by rw [mul_assoc]
    _ = creat i * (annih j * smGhostParity m) := by
          rw [smGhostParity_mul_annih_matter m hj]
    _ = (creat i * annih j) * smGhostParity m := by rw [mul_assoc]

/-- The parity commutes with the Gauss generators. -/
theorem smGhostParity_comm_matterGen (m : ℕ) (T : Fin 12 → Matrix (Fin m) (Fin m) ℂ)
    (a : Fin 12) : smGhostParity m * matterGen m T a = matterGen m T a * smGhostParity m := by
  rw [matterGen, mul_smul_comm, smul_mul_assoc, smGhostParity_comm_fermiBilin_matter]

/-- **A Gauss term is parity-odd**: one ghost field. -/
theorem smGhostParity_mul_gauss (m : ℕ) (T : Fin 12 → Matrix (Fin m) (Fin m) ℂ)
    (a : Fin 12) :
    smGhostParity m * (ghostCre m a * matterGen m T a)
      = -(ghostCre m a * matterGen m T a * smGhostParity m) := by
  calc smGhostParity m * (ghostCre m a * matterGen m T a)
      = (smGhostParity m * ghostCre m a) * matterGen m T a := by rw [mul_assoc]
    _ = (-(ghostCre m a * smGhostParity m)) * matterGen m T a := by
          rw [smGhostParity_mul_ghostCre]
    _ = -(ghostCre m a * (smGhostParity m * matterGen m T a)) := by noncomm_ring
    _ = -(ghostCre m a * (matterGen m T a * smGhostParity m)) := by
          rw [smGhostParity_comm_matterGen]
    _ = -(ghostCre m a * matterGen m T a * smGhostParity m) := by noncomm_ring

/-- **odd · odd is even** for the parity. -/
theorem smGhostParity_mul_mul_odd_odd {A B : Module.End ℂ (FermiFock (m + 12))}
    (hA : smGhostParity m * A = -(A * smGhostParity m))
    (hB : smGhostParity m * B = -(B * smGhostParity m)) :
    smGhostParity m * (A * B) = A * B * smGhostParity m := by
  rw [← mul_assoc, hA, neg_mul, mul_assoc, hB, mul_neg, neg_neg, mul_assoc]

/-- **odd · even is odd** for the parity. -/
theorem smGhostParity_mul_mul_odd_even {A B : Module.End ℂ (FermiFock (m + 12))}
    (hA : smGhostParity m * A = -(A * smGhostParity m))
    (hB : smGhostParity m * B = B * smGhostParity m) :
    smGhostParity m * (A * B) = -(A * B * smGhostParity m) := by
  rw [← mul_assoc, hA, neg_mul, mul_assoc, hB, mul_assoc]

/-- **even · odd is odd** for the parity. -/
theorem smGhostParity_mul_mul_even_odd {A B : Module.End ℂ (FermiFock (m + 12))}
    (hA : smGhostParity m * A = A * smGhostParity m)
    (hB : smGhostParity m * B = -(B * smGhostParity m)) :
    smGhostParity m * (A * B) = -(A * B * smGhostParity m) := by
  rw [← mul_assoc, hA, mul_assoc, hB, mul_neg, mul_assoc]

/-- **A cubic ghost term is parity-odd**: three ghost fields. -/
theorem smGhostParity_mul_cubic (m : ℕ) (a b e : Fin 12) :
    smGhostParity m * (ghostCre m a * ghostCre m b * ghostAnn m e)
      = -(ghostCre m a * ghostCre m b * ghostAnn m e * smGhostParity m) :=
  smGhostParity_mul_mul_even_odd
    (smGhostParity_mul_mul_odd_odd (smGhostParity_mul_ghostCre m a)
      (smGhostParity_mul_ghostCre m b))
    (smGhostParity_mul_ghostAnn m e)

/-! ### Oddness is closed under sums and scalar multiples -/

/-- A sum of parity-odd operators is parity-odd. -/
theorem smGhostParity_mul_sum {ι : Type*} (s : Finset ι)
    (A : ι → Module.End ℂ (FermiFock (m + 12)))
    (h : ∀ i ∈ s, smGhostParity m * A i = -(A i * smGhostParity m)) :
    smGhostParity m * (∑ i ∈ s, A i) = -((∑ i ∈ s, A i) * smGhostParity m) := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i hi => h i hi

/-- A complex multiple of a parity-odd operator is parity-odd. -/
theorem smGhostParity_mul_smul {c : ℂ} {A : Module.End ℂ (FermiFock (m + 12))}
    (h : smGhostParity m * A = -(A * smGhostParity m)) :
    smGhostParity m * (c • A) = -(c • A * smGhostParity m) := by
  rw [mul_smul_comm, smul_mul_assoc, h, smul_neg]

-- the `Algebra ℝ (Module.End ℂ (FermiFock _))` instance is over the typeclass budget here
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- A real multiple of a parity-odd operator is parity-odd. -/
theorem smGhostParity_mul_real_smul {c : ℝ} {A : Module.End ℂ (FermiFock (m + 12))}
    (h : smGhostParity m * A = -(A * smGhostParity m)) :
    smGhostParity m * (c • A) = -(c • A * smGhostParity m) := by
  rw [mul_smul_comm, h, smul_neg, smul_mul_assoc]

/-! ### The charge is parity-odd -/

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The Standard-Model charge anticommutes with the ghost parity**: `U Ω = -Ω U`.  Every term of
the charge carries an odd number of ghost fields — one in `c^a G^a`, three in the cubic term — so
the charge exchanges the two parity sectors, which is the grading the sector split consumes. -/
theorem smGhostParity_mul_smBrstCharge (m : ℕ) (T : Fin 12 → Matrix (Fin m) (Fin m) ℂ)
    (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    smGhostParity m * smBrstCharge m T f3 = -(smBrstCharge m T f3 * smGhostParity m) := by
  have hA : smGhostParity m * (∑ a : Fin 12, ghostCre m a * matterGen m T a)
      = -((∑ a : Fin 12, ghostCre m a * matterGen m T a) * smGhostParity m) :=
    smGhostParity_mul_sum (m := m) Finset.univ
      (fun a : Fin 12 => ghostCre m a * matterGen m T a) fun a _ =>
        smGhostParity_mul_gauss m T a
  have hB : smGhostParity m
      * (∑ a : Fin 12, ∑ b : Fin 12, ∑ e : Fin 12,
          smStruct f3 a b e • (ghostCre m a * ghostCre m b * ghostAnn m e))
      = -((∑ a : Fin 12, ∑ b : Fin 12, ∑ e : Fin 12,
          smStruct f3 a b e • (ghostCre m a * ghostCre m b * ghostAnn m e)) * smGhostParity m) :=
    by
    refine smGhostParity_mul_sum (m := m) Finset.univ
      (fun a : Fin 12 => ∑ b : Fin 12, ∑ e : Fin 12,
        smStruct f3 a b e • (ghostCre m a * ghostCre m b * ghostAnn m e)) fun a _ => ?_
    refine smGhostParity_mul_sum (m := m) Finset.univ
      (fun b : Fin 12 => ∑ e : Fin 12,
        smStruct f3 a b e • (ghostCre m a * ghostCre m b * ghostAnn m e)) fun b _ => ?_
    exact smGhostParity_mul_sum (m := m) Finset.univ
      (fun e : Fin 12 => smStruct f3 a b e • (ghostCre m a * ghostCre m b * ghostAnn m e))
      fun e _ => smGhostParity_mul_real_smul (m := m) (smGhostParity_mul_cubic m a b e)
  unfold smBrstCharge brstCharge Q
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, hA, hB]
  simp only [smul_neg]
  abel

end

end BookProof.SmBrstGhost

namespace BookProof.SmBrstGhost

open BookProof.SmCar BookProof.BRSTNilpotent

/-! ## 2b. The cubic term on a pure-weak pair of ghosts

The cubic term `Omega_3 = -1/2 f_{abe} c^a c^b b^e` raises the ghost number by one, so it maps
ghost number two to ghost number three.  The exact computation in
`scripts/sm-cubic-kernel-basis.py` shows that the kernel there is eleven-dimensional; the
theorems below supply the part of that statement that is provable without knowing the gluon
structure constants: every state whose two ghosts are *both weak* is killed.  The reason is
block-diagonality of the Standard-Model structure constants (a nonzero `smStruct` confines all
three indices to one simple summand) together with the pigeonhole count in the weak block: after
the annihilation removes one of the two ghost modes there are only two weak labels left, so the
two creation indices repeat one of them and `epsZ` vanishes. -/

theorem annih_occ_of_notMem {N : ℕ} {i : Fin N} {S : Finset (Fin N)} (h : i ∉ S) :
    annih i (occ S) = 0 := by
  ext T
  rw [annih_apply]
  by_cases hT : i ∈ T
  · simp [hT]
  · have hne : insert i T ≠ S := fun hh => h (hh ▸ Finset.mem_insert_self i T)
    simp [hT, occ, EuclideanSpace.single_apply, hne]

theorem creat_occ_of_mem {N : ℕ} {i : Fin N} {S : Finset (Fin N)} (h : i ∈ S) :
    creat i (occ S) = 0 := by
  ext T
  rw [creat_apply]
  by_cases hT : i ∈ T
  · have hne : T.erase i ≠ S := fun hh => Finset.notMem_erase i T (hh ▸ h)
    simp [hT, occ, EuclideanSpace.single_apply, hne]
  · simp [hT]

/-- Creating on a mode that the remaining state occupies kills the state: the Pauli principle
applied to the outer creation operator. -/
theorem creat_creat_occ_of_mem {N : ℕ} {i j : Fin N} {S : Finset (Fin N)} (h : i ∈ S) :
    creat i (creat j (occ S)) = 0 := by
  ext T
  rw [creat_apply]
  by_cases hT : i ∈ T
  · rw [if_pos hT, creat_apply]
    by_cases hJ : j ∈ T.erase i
    · have hne : (T.erase i).erase j ≠ S := by
        intro hh
        have hmem : i ∈ (T.erase i).erase j := hh ▸ h
        exact Finset.notMem_erase i T (Finset.mem_of_mem_erase hmem)
      simp [hJ, occ, EuclideanSpace.single_apply, hne]
    · simp [hJ]
  · simp [hT]

theorem annih_occ_of_mem {N : ℕ} {i : Fin N} {S : Finset (Fin N)} (h : i ∈ S) :
    annih i (occ S) = jwSign i (S.erase i) • occ (S.erase i) := by
  ext T
  rw [annih_apply, smul_apply_fock]
  by_cases hT : i ∈ T
  · have hne : T ≠ S.erase i := fun hh => Finset.notMem_erase i S (hh ▸ hT)
    simp [hT, occ, EuclideanSpace.single_apply, hne]
  · by_cases hE : T = S.erase i
    · subst hE
      rw [Finset.insert_erase h]
      simp [occ, EuclideanSpace.single_apply]
    · have hne : insert i T ≠ S := by
        intro hh
        exact hE (by rw [← hh, Finset.erase_insert hT])
      simp [hT, occ, EuclideanSpace.single_apply, hE, hne]

/-- The three weak generator labels. -/
def wGhost (k : Fin 3) : Fin 12 := smIdxEquiv.symm (Sum.inr (Sum.inl k))

theorem wGhost_spec (k : Fin 3) : smIdxEquiv (wGhost k) = Sum.inr (Sum.inl k) :=
  Equiv.apply_symm_apply smIdxEquiv (Sum.inr (Sum.inl k))

theorem wGhost_injective : Function.Injective wGhost := by
  intro k l h
  have h' := smIdxEquiv.symm.injective h
  simpa using h'

/-! ## The structure constants of the weak block -/

theorem su2Struct_self_right (a b : Fin 3) : su2Struct a b a = 0 := by
  rw [su2Struct]
  exact_mod_cast (by decide +revert : epsZ a b a = 0)

theorem su2Struct_self_left (a b : Fin 3) : su2Struct a a b = 0 := by
  rw [su2Struct]
  exact_mod_cast (by decide +revert : epsZ a a b = 0)

/-- With the annihilation at the first weak label, only the two remaining labels are available. -/
theorem epsZ_zero_of_pair_left : ∀ ka kb k l : Fin 3, k ≠ l → ka ≠ l → kb ≠ l → ka ≠ kb →
    epsZ ka kb k = 0 := by decide

theorem su2Struct_zero_of_pair_left {ka kb k l : Fin 3} (hkl : k ≠ l) (h1 : ka ≠ l)
    (h2 : kb ≠ l) (h3 : ka ≠ kb) : su2Struct ka kb k = 0 := by
  rw [su2Struct]
  exact_mod_cast epsZ_zero_of_pair_left ka kb k l hkl h1 h2 h3

/-- With the annihilation at the second weak label, only the two remaining labels are available. -/
theorem epsZ_zero_of_pair_right : ∀ ka kb k l : Fin 3, k ≠ l → ka ≠ k → kb ≠ k → ka ≠ kb →
    epsZ ka kb l = 0 := by decide

theorem su2Struct_zero_of_pair_right {ka kb k l : Fin 3} (hkl : k ≠ l) (h1 : ka ≠ k)
    (h2 : kb ≠ k) (h3 : ka ≠ kb) : su2Struct ka kb l = 0 := by
  rw [su2Struct]
  exact_mod_cast epsZ_zero_of_pair_right ka kb k l hkl h1 h2 h3

/-- A `smStruct` with a weak third index kills a first index outside the weak block. -/
theorem smStruct_eq_zero_of_not_weak_left {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ} {a b e : Fin 12}
    {ke : Fin 3} (he : smIdxEquiv e = Sum.inr (Sum.inl ke))
    (ha : ∀ ka, smIdxEquiv a ≠ Sum.inr (Sum.inl ka)) : smStruct f3 a b e = 0 := by
  rcases hb : smIdxEquiv b with gb | (kb | ub) <;> rcases hx : smIdxEquiv a with ga | (ka | ua)
  · simp only [smStruct, sumStruct, he, hb, hx]
  · exact absurd hx (ha ka)
  · simp only [smStruct, sumStruct, he, hb, hx]
  · simp only [smStruct, sumStruct, he, hb, hx]
  · exact absurd hx (ha ka)
  · simp only [smStruct, sumStruct, he, hb, hx]
  · simp only [smStruct, sumStruct, he, hb, hx]
  · exact absurd hx (ha ka)
  · simp only [smStruct, sumStruct, he, hb, hx]

/-- A `smStruct` with a weak third index kills a second index outside the weak block. -/
theorem smStruct_eq_zero_of_not_weak_right {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ} {a b e : Fin 12}
    {ke : Fin 3} (he : smIdxEquiv e = Sum.inr (Sum.inl ke))
    (hb : ∀ kb, smIdxEquiv b ≠ Sum.inr (Sum.inl kb)) : smStruct f3 a b e = 0 := by
  rcases hx : smIdxEquiv a with ga | (ka | ua) <;> rcases hy : smIdxEquiv b with gb | (kb | ub)
  · simp only [smStruct, sumStruct, he, hx, hy]
  · exact absurd hy (hb kb)
  · simp only [smStruct, sumStruct, he, hx, hy]
  · simp only [smStruct, sumStruct, he, hx, hy]
  · exact absurd hy (hb kb)
  · simp only [smStruct, sumStruct, he, hx, hy]
  · simp only [smStruct, sumStruct, he, hx, hy]
  · exact absurd hy (hb kb)
  · simp only [smStruct, sumStruct, he, hx, hy]

/-! ## The cubic charge on a pure-weak pair of ghosts -/

/-- **The cubic ghost term kills every pure-weak ghost pair.**  A cubic monomial applies two
creation and one annihilation operator, so `Omega_3` moves ghost number two to ghost number
three.  On a state whose two ghosts are both weak the only surviving structure constants are
those of the weak block, and there the third index is forced to repeat one of the two already
used: at ghost number two the weak sector has only two labels left over, so `epsZ` vanishes. -/
theorem smGhostCharge_occ_weakPair (m : ℕ) (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ)
    {k l : Fin 3} (hkl : k ≠ l) :
    smGhostCharge m f3
      (occ ({ghostMode m (wGhost k), ghostMode m (wGhost l)} : Finset (Fin (m + 12)))) = 0 := by
  classical
  have hklm : ghostMode m (wGhost k) ≠ ghostMode m (wGhost l) := fun h =>
    hkl (wGhost_injective (ghostMode_injective m h))
  have hSk : ({ghostMode m (wGhost k), ghostMode m (wGhost l)} : Finset (Fin (m + 12))).erase
      (ghostMode m (wGhost k)) = {ghostMode m (wGhost l)} :=
    Finset.erase_insert (by simpa using hklm)
  have hSl : ({ghostMode m (wGhost k), ghostMode m (wGhost l)} : Finset (Fin (m + 12))).erase
      (ghostMode m (wGhost l)) = {ghostMode m (wGhost k)} := by
    rw [Finset.pair_comm]
    exact Finset.erase_insert (by simpa using hklm.symm)
  rw [smGhostCharge, Q]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun e _ => ?_
  have kill : ∀ (p q x : Fin 12), x ≠ wGhost k → x ≠ wGhost l →
      ((ghostCre m p * ghostCre m q * ghostAnn m x)
        (occ ({ghostMode m (wGhost k), ghostMode m (wGhost l)} :
          Finset (Fin (m + 12))))) = 0 := by
    intro p q x hx hx'
    have hmem : ghostMode m x ∉ ({ghostMode m (wGhost k), ghostMode m (wGhost l)} :
        Finset (Fin (m + 12))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact hx (ghostMode_injective m h)
      · exact hx' (ghostMode_injective m h)
    rw [Module.End.mul_apply, Module.End.mul_apply, ghostAnn, annih_occ_of_notMem hmem]
    simp
  by_cases hwe : ∃ ke : Fin 3, smIdxEquiv e = Sum.inr (Sum.inl ke)
  · obtain ⟨ke, he⟩ := hwe
    by_cases hwa : ∃ ka : Fin 3, smIdxEquiv a = Sum.inr (Sum.inl ka)
    · obtain ⟨ka, ha⟩ := hwa
      by_cases hwb : ∃ kb : Fin 3, smIdxEquiv b = Sum.inr (Sum.inl kb)
      · obtain ⟨kb, hb⟩ := hwb
        have ha' : a = wGhost ka := ((Equiv.symm_apply_eq smIdxEquiv).mpr ha.symm).symm
        have hb' : b = wGhost kb := ((Equiv.symm_apply_eq smIdxEquiv).mpr hb.symm).symm
        have he' : e = wGhost ke := ((Equiv.symm_apply_eq smIdxEquiv).mpr he.symm).symm
        have hsub : smStruct f3 a b e = su2Struct ka kb ke := by
          simp only [smStruct, sumStruct, ha, hb, he]
        rw [hsub, ha', hb', he']
        by_cases hk : ke = k
        · rw [hk]
          by_cases h1 : ka = l
          · rw [h1]
            have hz : ((ghostCre m (wGhost l) * ghostCre m (wGhost kb) *
                ghostAnn m (wGhost k))
                (occ ({ghostMode m (wGhost k), ghostMode m (wGhost l)} :
                  Finset (Fin (m + 12))))) = 0 := by
              rw [Module.End.mul_apply, Module.End.mul_apply, ghostAnn,
                annih_occ_of_mem (by simp [Finset.mem_insert]), hSk, map_smul, map_smul,
                ghostCre, ghostCre,
                creat_creat_occ_of_mem (by simp)]
              simp
            rw [hz, smul_zero]
          · by_cases h2 : kb = l
            · rw [h2]
              have hz : ((ghostCre m (wGhost ka) * ghostCre m (wGhost l) *
                  ghostAnn m (wGhost k))
                  (occ ({ghostMode m (wGhost k), ghostMode m (wGhost l)} :
                    Finset (Fin (m + 12))))) = 0 := by
                rw [Module.End.mul_apply, Module.End.mul_apply, ghostAnn,
                  annih_occ_of_mem (by simp [Finset.mem_insert]), hSk, map_smul, map_smul,
                  ghostCre, ghostCre, creat_occ_of_mem (by simp)]
                simp
              rw [hz, smul_zero]
            · by_cases h3 : ka = kb
              · rw [h3]
                have hz : ((ghostCre m (wGhost kb) * ghostCre m (wGhost kb) *
                    ghostAnn m (wGhost k))
                    (occ ({ghostMode m (wGhost k), ghostMode m (wGhost l)} :
                      Finset (Fin (m + 12))))) = 0 := by
                  have hsq : (ghostCre m (wGhost kb) * ghostCre m (wGhost kb) :
                      Module.End ℂ (FermiFock (m + 12))) = 0 := by
                    rw [ghostCre]
                    exact creat_sq _
                  rw [Module.End.mul_apply, hsq]
                  simp
                rw [hz, smul_zero]
              · rw [su2Struct_zero_of_pair_left hkl h1 h2 h3, zero_smul]
        · by_cases hl : ke = l
          · rw [hl]
            by_cases h1 : ka = k
            · rw [h1]
              have hz : ((ghostCre m (wGhost k) * ghostCre m (wGhost kb) *
                  ghostAnn m (wGhost l))
                  (occ ({ghostMode m (wGhost k), ghostMode m (wGhost l)} :
                    Finset (Fin (m + 12))))) = 0 := by
                rw [Module.End.mul_apply, Module.End.mul_apply, ghostAnn,
                  annih_occ_of_mem (by simp [Finset.mem_insert]), hSl, map_smul, map_smul,
                  ghostCre, ghostCre,
                  creat_creat_occ_of_mem (by simp)]
                simp
              rw [hz, smul_zero]
            · by_cases h2 : kb = k
              · rw [h2]
                have hz : ((ghostCre m (wGhost ka) * ghostCre m (wGhost k) *
                    ghostAnn m (wGhost l))
                    (occ ({ghostMode m (wGhost k), ghostMode m (wGhost l)} :
                      Finset (Fin (m + 12))))) = 0 := by
                  rw [Module.End.mul_apply, Module.End.mul_apply, ghostAnn,
                    annih_occ_of_mem (by simp [Finset.mem_insert]), hSl, map_smul, map_smul,
                    ghostCre, ghostCre, creat_occ_of_mem (by simp)]
                  simp
                rw [hz, smul_zero]
              · by_cases h3 : ka = kb
                · rw [h3]
                  have hz : ((ghostCre m (wGhost kb) * ghostCre m (wGhost kb) *
                      ghostAnn m (wGhost l))
                      (occ ({ghostMode m (wGhost k), ghostMode m (wGhost l)} :
                        Finset (Fin (m + 12))))) = 0 := by
                    have hsq : (ghostCre m (wGhost kb) * ghostCre m (wGhost kb) :
                        Module.End ℂ (FermiFock (m + 12))) = 0 := by
                      rw [ghostCre]
                      exact creat_sq _
                    rw [Module.End.mul_apply, hsq]
                    simp
                  rw [hz, smul_zero]
                · rw [su2Struct_zero_of_pair_right hkl h1 h2 h3, zero_smul]
          · have hz : ((ghostCre m (wGhost ka) * ghostCre m (wGhost kb) *
                ghostAnn m (wGhost ke))
                (occ ({ghostMode m (wGhost k), ghostMode m (wGhost l)} :
                  Finset (Fin (m + 12))))) = 0 :=
              kill (wGhost ka) (wGhost kb) (wGhost ke) (fun h => hk (wGhost_injective h))
                (fun h => hl (wGhost_injective h))
            rw [hz, smul_zero]
      · push_neg at hwb
        rw [smStruct_eq_zero_of_not_weak_right he hwb, zero_smul]
    · push_neg at hwa
      rw [smStruct_eq_zero_of_not_weak_left he hwa, zero_smul]
  · push_neg at hwe
    have hx : e ≠ wGhost k := fun h => hwe k (by rw [h, wGhost_spec])
    have hx' : e ≠ wGhost l := fun h => hwe l (by rw [h, wGhost_spec])
    rw [kill a b e hx hx']
    simp

/-- A pure-weak pair state. -/
noncomputable def weakPair (m : ℕ) (k l : Fin 3) : FermiFock (m + 12) :=
  occ ({ghostMode m (wGhost k), ghostMode m (wGhost l)} : Finset (Fin (m + 12)))

theorem weakPair_occ_apply (m : ℕ) (k l : Fin 3) :
    weakPair m k l ({ghostMode m (wGhost k), ghostMode m (wGhost l)} :
      Finset (Fin (m + 12))) = 1 := by
  simp [weakPair, occ, EuclideanSpace.single_apply]

/-- The occupation state of a pure-weak pair of ghosts. -/
noncomputable abbrev weakOcc (m : ℕ) (k l : Fin 3) : FermiFock (m + 12) :=
  occ ({ghostMode m (wGhost k), ghostMode m (wGhost l)} : Finset (Fin (m + 12)))

theorem weakOcc_inner (m : ℕ) (k l k' l' : Fin 3) :
    inner ℂ (weakOcc m k l) (weakOcc m k' l')
      = if ({ghostMode m (wGhost k), ghostMode m (wGhost l)} : Finset (Fin (m + 12)))
          = {ghostMode m (wGhost k'), ghostMode m (wGhost l')} then 1 else 0 := by
  simp [weakOcc, occ, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

theorem weakOcc_norm (m : ℕ) (k l : Fin 3) : ‖weakOcc m k l‖ = 1 := by
  simp [weakOcc, occ]

theorem gm_ne {m : ℕ} {a b : Fin 3} (h : a ≠ b) :
    ghostMode m (wGhost a) ≠ ghostMode m (wGhost b) :=
  fun hh => h (wGhost_injective (ghostMode_injective m hh))

set_option maxHeartbeats 800000 in
-- The three-element matrix literal of occupation states, with the inner-product normalisation facts
-- for each of them, exceeds the default heartbeat budget.
/-- **The three pure-weak pair states are orthonormal.** -/
theorem weakOcc_orthonormal (m : ℕ) :
    Orthonormal ℂ ![weakOcc m 0 1, weakOcc m 0 2, weakOcc m 1 2] := by
  rw [orthonormal_iff_ite]
  have h01 : ({ghostMode m (wGhost 0), ghostMode m (wGhost 1)} : Finset (Fin (m + 12)))
      ≠ {ghostMode m (wGhost 0), ghostMode m (wGhost 2)} := by
    intro h
    have hm : ghostMode m (wGhost 1) ∈ ({ghostMode m (wGhost 0),
        ghostMode m (wGhost 2)} : Finset (Fin (m + 12))) := by rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exact (gm_ne (by decide : (1 : Fin 3) ≠ 0)) hm
    · exact (gm_ne (by decide : (1 : Fin 3) ≠ 2)) hm
  have h02 : ({ghostMode m (wGhost 0), ghostMode m (wGhost 1)} : Finset (Fin (m + 12)))
      ≠ {ghostMode m (wGhost 1), ghostMode m (wGhost 2)} := by
    intro h
    have hm : ghostMode m (wGhost 0) ∈ ({ghostMode m (wGhost 1),
        ghostMode m (wGhost 2)} : Finset (Fin (m + 12))) := by rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exact (gm_ne (by decide : (0 : Fin 3) ≠ 1)) hm
    · exact (gm_ne (by decide : (0 : Fin 3) ≠ 2)) hm
  have h12 : ({ghostMode m (wGhost 0), ghostMode m (wGhost 2)} : Finset (Fin (m + 12)))
      ≠ {ghostMode m (wGhost 1), ghostMode m (wGhost 2)} := by
    intro h
    have hm : ghostMode m (wGhost 0) ∈ ({ghostMode m (wGhost 1),
        ghostMode m (wGhost 2)} : Finset (Fin (m + 12))) := by rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exact (gm_ne (by decide : (0 : Fin 3) ≠ 1)) hm
    · exact (gm_ne (by decide : (0 : Fin 3) ≠ 2)) hm
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [weakOcc_inner, weakOcc_norm, h01, h02, h12, Ne.symm h01, Ne.symm h02,
      Ne.symm h12]

/-- **Three independent kernel vectors force a three-dimensional kernel.** -/
theorem finrank_ker_ge_three {m : ℕ} {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}
    {u v w : FermiFock (m + 12)}
    (hu : u ∈ LinearMap.ker (smGhostCharge m f3 : Module.End ℂ (FermiFock (m + 12))))
    (hv : v ∈ LinearMap.ker (smGhostCharge m f3 : Module.End ℂ (FermiFock (m + 12))))
    (hw : w ∈ LinearMap.ker (smGhostCharge m f3 : Module.End ℂ (FermiFock (m + 12))))
    (hli : LinearIndependent ℂ ![u, v, w]) :
    3 ≤ Module.finrank ℂ
      (LinearMap.ker (smGhostCharge m f3 : Module.End ℂ (FermiFock (m + 12)))) := by
  classical
  have hmem : ∀ i : Fin 3, ![u, v, w] i ∈
      LinearMap.ker (smGhostCharge m f3 : Module.End ℂ (FermiFock (m + 12))) := by
    intro i
    fin_cases i
    · exact hu
    · exact hv
    · exact hw
  have hspan : Submodule.span ℂ (Set.range ![u, v, w])
      ≤ LinearMap.ker (smGhostCharge m f3 : Module.End ℂ (FermiFock (m + 12))) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  have hdim : Module.finrank ℂ (Submodule.span ℂ (Set.range ![u, v, w])) = 3 := by
    rw [finrank_span_eq_card hli]
    simp
  calc (3 : ℕ) = Module.finrank ℂ (Submodule.span ℂ (Set.range ![u, v, w])) := hdim.symm
    _ ≤ Module.finrank ℂ
        (LinearMap.ker (smGhostCharge m f3 : Module.End ℂ (FermiFock (m + 12)))) :=
        Submodule.finrank_mono hspan

set_option maxHeartbeats 800000 in
-- The final instantiation unfolds the three occupation states into the matrix literal.
/-- **The cubic term's kernel at ghost number two is at least three-dimensional.** -/
theorem finrank_ker_smGhostCharge_ge_three (m : ℕ) (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    3 ≤ Module.finrank ℂ
      (LinearMap.ker (smGhostCharge m f3 : Module.End ℂ (FermiFock (m + 12)))) := by
  have h01 := smGhostCharge_occ_weakPair m f3 (k := (0 : Fin 3)) (l := 1) (by decide)
  have h02 := smGhostCharge_occ_weakPair m f3 (k := (0 : Fin 3)) (l := 2) (by decide)
  have h12 := smGhostCharge_occ_weakPair m f3 (k := (1 : Fin 3)) (l := 2) (by decide)
  have hli : LinearIndependent ℂ ![weakOcc m 0 1, weakOcc m 0 2, weakOcc m 1 2] :=
    (weakOcc_orthonormal m).linearIndependent
  exact finrank_ker_ge_three (f3 := f3) (LinearMap.mem_ker.mpr h01)
    (LinearMap.mem_ker.mpr h02) (LinearMap.mem_ker.mpr h12) hli


/-! ### Why the bound is about ghost degree two: the matter-only sector

The lower bound above is degree-free.  An *upper* bound of eleven is not: the kernel of the cubic
ghost charge on the whole Fock space grows with the number of matter modes, because a cubic
monomial never contains a matter mode, so it annihilates every state built from matter modes alone.

The general form of the annihilation lemma is `smGhostCharge_occ_of_ghostFree` in
`ChapterSmQuartet`, which imports this chapter; the free-standing `smGhostCharge_occ_matterOnly`
below is stated in terms of the numeric cutoff so that it can be used without that import.
-/
/-- A ghost mode is never among the first `m` modes. -/
theorem val_ghostMode (m : ℕ) (a : Fin 12) : ((ghostMode m a : Fin (m + 12)) : ℕ) = m + a := by
  simp [ghostMode]

/-- **A state with no ghost mode occupied is annihilated by the cubic ghost charge**, for every
choice of structure constants: the annihilation factor sees no occupied ghost mode. -/
theorem smGhostCharge_occ_matterOnly {m : ℕ} (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ)
    {T : Finset (Fin (m + 12))} (hT : ∀ i ∈ T, (i : ℕ) < m) :
    smGhostCharge m f3 (occ T) = 0 := by
  unfold smGhostCharge Q
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun e _ => ?_
  have hnotmem : ghostMode m e ∉ T := by
    intro h
    have h1 := hT _ h
    rw [val_ghostMode] at h1
    omega
  rw [ghostAnn, annih_occ_of_notMem hnotmem]
  simp

/-- The canonical embedding of the `m` matter modes into the `m + 12` modes. -/
abbrev matterEmb (m : ℕ) : Fin m ↪ Fin (m + 12) :=
  ⟨Fin.castAdd 12, fun _ _ h => by simpa using h⟩

theorem matterEmb_mem (m : ℕ) {i : Fin m} : ((matterEmb m i : Fin (m + 12)) : ℕ) = i := by
  simp [matterEmb]

/-- **The matter-only occupation states are orthonormal.** -/
theorem matterOcc_orthonormal (m : ℕ) :
    Orthonormal ℂ (fun T : Finset (Fin m) => occ (T.map (matterEmb m))) := by
  rw [orthonormal_iff_ite]
  intro T T'
  by_cases h : T = T'
  · subst h
    rw [if_pos rfl]
    simp [occ]
  · have hne : T.map (matterEmb m) ≠ T'.map (matterEmb m) :=
      fun hh => h (Finset.map_injective _ hh)
    simp [occ, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, h, hne]

/-- **A cardinality lower bound for the kernel from an orthonormal family of kernel vectors.** -/
theorem finrank_ker_ge_card {m : ℕ} {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ} {ι : Type*}
    [Fintype ι] (v : ι → FermiFock (m + 12)) (horth : Orthonormal ℂ v)
    (hk : ∀ i, v i ∈ LinearMap.ker (smGhostCharge m f3 : Module.End ℂ (FermiFock (m + 12)))) :
    Fintype.card ι ≤ Module.finrank ℂ
      (LinearMap.ker (smGhostCharge m f3 : Module.End ℂ (FermiFock (m + 12)))) := by
  have hspan : Submodule.span ℂ (Set.range v) ≤
      LinearMap.ker (smGhostCharge m f3 : Module.End ℂ (FermiFock (m + 12))) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hk i
  rw [← finrank_span_eq_card horth.linearIndependent]
  exact Submodule.finrank_mono hspan

set_option maxHeartbeats 800000 in
-- Elaborating the family over `Finset (Fin m)` against the `FermiFock (m + 12)` finrank exceeds the
-- default heartbeat budget.
/-- **The kernel of the cubic ghost charge is at least `2^m`-dimensional**: every matter-only
occupation state is annihilated, for every choice of structure constants. -/
theorem finrank_ker_smGhostCharge_ge_two_pow (m : ℕ) (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    2 ^ m ≤ Module.finrank ℂ
      (LinearMap.ker (smGhostCharge m f3 : Module.End ℂ (FermiFock (m + 12)))) := by
  have hcard : Fintype.card (Finset (Fin m)) = 2 ^ m := by
    rw [Fintype.card_finset, Fintype.card_fin]
  rw [← hcard]
  refine finrank_ker_ge_card (fun T : Finset (Fin m) => occ (T.map (matterEmb m)))
    (matterOcc_orthonormal m) fun T => ?_
  rw [LinearMap.mem_ker]
  unfold smGhostCharge Q
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun e _ => ?_
  have hnotmem : ghostMode m e ∉ T.map (matterEmb m) := by
    rw [Finset.mem_map]
    rintro ⟨j, _, hj⟩
    have h1 : ((ghostMode m e : Fin (m + 12)) : ℕ) = m + e := val_ghostMode m e
    have h2 : ((matterEmb m j : Fin (m + 12)) : ℕ) = j := matterEmb_mem m
    rw [← hj] at h1
    omega
  rw [ghostAnn, annih_occ_of_notMem hnotmem]
  simp

/-- **No unconditional upper bound of eleven**: with four matter modes the kernel is at least
sixteen-dimensional, whatever the structure constants. -/
theorem not_finrank_ker_le_eleven :
    ¬ ∀ (m : ℕ) (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ),
      Module.finrank ℂ (LinearMap.ker (smGhostCharge m f3 :
        Module.End ℂ (FermiFock (m + 12)))) ≤ 11 := by
  intro h
  have h4 := h 4 (fun _ _ _ => (0 : ℝ))
  have hge := finrank_ker_smGhostCharge_ge_two_pow 4 (fun _ _ _ => (0 : ℝ))
  norm_num at hge
  omega

end BookProof.SmBrstGhost
