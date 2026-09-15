import Mathlib
import BookProof.ChapterNavierStokesAffineFiberEsa
import BookProof.ChapterNavierStokesSignedShift.Part1

/-!
# Hopping Hamiltonians with **signed**, non-monotone amplitudes

`BookProof.ChapterNavierStokesShiftHamiltonian` proves the two Faris–Lavine
inequalities for a hopping (shift) Hamiltonian whose amplitude `w` is
*non-negative* and *non-decreasing along the shift*.  Both restrictions are
artefacts of the bookkeeping — they are used only to produce a majorant for the
two terms of `(H x)_β = i(w(s⁻¹β) x_{s⁻¹β} − w(β) x_{sβ})` — and both are
obstacles for the coupled Navier–Stokes symbol:

* a negative amplitude occurs whenever a strain rate or a fiber constant is
  negative, and
* a non-monotone amplitude occurs for the *number-conserving* hoppings
  `a_i† a_k` produced by the antisymmetric (vorticity) part of the velocity
  gradient, whose amplitude `√((β_i+1) β_k)` increases in one coordinate and
  decreases in the other.

This module removes both.  The observation is that the estimates never need the
amplitude itself: they need a **majorant** which is non-negative, monotone along
the shift and dominated by the comparison symbol.  The canonical such majorant
is `¼ σ + K`, which is monotone as soon as the symbol increases along the shift.

## The data

A `SignedHop ι σ` consists of an injective shift `s`, an **arbitrary real**
amplitude `w` with `|w| ≤ ¼ σ + K`, and a constant, non-negative symbol
increment `σ (s β) = σ β + Δ`.  Its `maj` is the majorant `ShiftData` with the
same shift and symbol and amplitude `¼ σ + K`, so all the transport lemmas of
`ShiftData` are available.

## What is proved

* `SignedHop.hopH` — the signed hopping Hamiltonian on the maximal domain of
  the comparison symbol, and `SignedHop.hopH_symmetricOn`;
* `SignedHop.hopH_relative_bound` — `‖Hx‖² ≤ ½‖Nx‖² + 8K²‖x‖²`;
* `SignedHop.hopH_commForm_bound` — `|⟪x, i[H, N]x⟫| ≤ 2Δ(¼+K) ⟪x, Nx⟫`;
* `SignedHop.hopH_essentiallySelfAdjointOn_core` — essential self-adjointness on
  the finite-mode core;
* `listH` and `listH_essentiallySelfAdjointOn_core` — **the instrument**: a
  finite family of signed hops sharing one comparison symbol sums to an operator
  that is again essentially self-adjoint on the finite-mode core;
* `gaffH` and `gaffH_essentiallySelfAdjointOn_core` — the affine fiber
  Hamiltonian `½(π V + V π)` for `V(u) = κ u + c` with **no sign hypothesis at
  all** on `κ` and `c`.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace SignedShift

open LpNat FarisLavine IkebeKato ShiftHamiltonian AffineFiber

variable {ι : Type*}
/-! ## Finite families of hops sharing one comparison symbol -/

variable {sym : ι → ℝ}

/-- **The Hamiltonian of a finite family of signed hops** sharing one comparison
symbol: the sum of the individual hopping Hamiltonians, on the maximal domain of
the symbol. -/
noncomputable def listH (L : List (SignedHop ι sym)) : maxDom sym →ₗ[ℂ] L2I ι :=
  (L.map SignedHop.hopH).sum

@[simp] theorem listH_nil : listH ([] : List (SignedHop ι sym)) = 0 := rfl

@[simp] theorem listH_cons (S : SignedHop ι sym) (L : List (SignedHop ι sym)) :
    listH (S :: L) = SignedHop.hopH S + listH L := rfl

/-- The sum of the family is symmetric on the maximal domain. -/
theorem listH_symmetricOn (L : List (SignedHop ι sym)) : SymmetricOn (maxDom sym) (listH L) := by
  induction L with
  | nil =>
      intro x y
      simp [listH]
  | cons S L ih =>
      intro x y
      have h₁ := SignedHop.hopH_symmetricOn S x y
      have h₂ := ih x y
      change (inner ℂ (listH (S :: L) x : L2I ι) (y : L2I ι) : ℂ)
        = inner ℂ (x : L2I ι) (listH (S :: L) y : L2I ι)
      simp only [listH_cons, LinearMap.add_apply, inner_add_left, inner_add_right]
      linear_combination h₁ + h₂

/-- The relative bound for the sum, with explicit (existential) constants. -/
theorem listH_relative_bound (L : List (SignedHop ι sym)) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ x : maxDom sym,
      ‖(listH L x : L2I ι)‖ ^ 2
        ≤ a * ‖(diagMax sym x : L2I ι)‖ ^ 2 + b * ‖(x : L2I ι)‖ ^ 2 := by
  induction L with
  | nil =>
      refine ⟨0, 0, le_rfl, le_rfl, fun x => ?_⟩
      simp [listH]
  | cons S L ih =>
      obtain ⟨a, b, ha, hb, hbound⟩ := ih
      refine ⟨2 * (1 / 2) + 2 * a, 2 * (8 * S.K ^ 2) + 2 * b, by linarith,
        by nlinarith [sq_nonneg S.K], fun x => ?_⟩
      have h₁ := SignedHop.hopH_relative_bound S x
      have h₂ := hbound x
      have htri : ‖(listH (S :: L) x : L2I ι)‖
          ≤ ‖(SignedHop.hopH S x : L2I ι)‖ + ‖(listH L x : L2I ι)‖ := by
        simp only [listH_cons, LinearMap.add_apply]
        exact norm_add_le _ _
      have hsq : ‖(listH (S :: L) x : L2I ι)‖ ^ 2
          ≤ 2 * ‖(SignedHop.hopH S x : L2I ι)‖ ^ 2 + 2 * ‖(listH L x : L2I ι)‖ ^ 2 := by
        nlinarith [norm_nonneg (listH (S :: L) x : L2I ι),
          norm_nonneg (SignedHop.hopH S x : L2I ι), norm_nonneg (listH L x : L2I ι),
          sq_nonneg (‖(SignedHop.hopH S x : L2I ι)‖ - ‖(listH L x : L2I ι)‖)]
      nlinarith [h₁, h₂, hsq]

/-- The commutator bound for the sum, with an explicit (existential) constant. -/
theorem listH_commForm_bound (L : List (SignedHop ι sym)) (hsym : ∀ β, 1 ≤ sym β) :
    ∃ cst : ℝ, 0 ≤ cst ∧ ∀ x : maxDom sym,
      |commForm (listH L) (diagMax sym) x| ≤ cst * quadForm (diagMax sym) x := by
  induction L with
  | nil =>
      refine ⟨0, le_rfl, fun x => ?_⟩
      have : commForm (listH ([] : List (SignedHop ι sym))) (diagMax sym) x = 0 := by
        simp [commForm, listH]
      rw [this]
      simp
  | cons S L ih =>
      obtain ⟨cst, hcst, hbound⟩ := ih
      refine ⟨2 * S.step * (1 / 4 + S.K) + cst, by nlinarith [S.step_nonneg, S.K_nonneg],
        fun x => ?_⟩
      have h₁ := SignedHop.hopH_commForm_bound S x
      have h₂ := hbound x
      have hadd : commForm (listH (S :: L)) (diagMax sym) x
          = commForm (SignedHop.hopH S) (diagMax sym) x + commForm (listH L) (diagMax sym) x := by
        simpa only [listH_cons] using commForm_add (SignedHop.hopH S) (listH L) (diagMax sym) x
      have hqf : 0 ≤ quadForm (diagMax sym) x :=
        diagMax_quadForm_nonneg _ (fun β => le_trans zero_le_one (hsym β)) x
      rw [hadd]
      refine le_trans (abs_add_le _ _) ?_
      nlinarith [h₁, h₂]

/-- **The instrument.**  A finite family of signed hopping terms sharing one
comparison symbol sums to an operator that is essentially self-adjoint on the
finite-mode core.  No positivity and no monotonicity of the amplitudes is
required. -/
theorem listH_essentiallySelfAdjointOn_core (L : List (SignedHop ι sym)) (hsym : ∀ β, 1 ≤ sym β) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((listH L).comp (Submodule.inclusion (finiteModes_le_maxDom sym))) := by
  obtain ⟨a, b, _, _, hrel⟩ := listH_relative_bound L
  obtain ⟨cst, hcst, hcomm⟩ := listH_commForm_bound L hsym
  exact essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds sym
    (fun β => le_trans zero_le_one (hsym β)) (listH L) a b cst
    (listH_symmetricOn L) hcst hrel hcomm

/-! ## Matrix entries on a basis vector -/

/-- The coordinates of a signed hop applied to the basis vector at `o`: the
amplitude `w(o)` at the coordinate `s o`, and `−w(γ)` at the coordinate `γ` with
`s γ = o`, times `i`. -/
theorem SignedHop.hFun_single [DecidableEq ι] {sym : ι → ℝ} (S : SignedHop ι sym)
    {X : ι → ℂ} {o : ι} (hX : ∀ α, X α = if α = o then 1 else 0) (γ : ι) :
    S.hFun X γ = Complex.I * ((if γ = S.shift o then (S.amp o : ℂ) else 0)
      - (if S.shift γ = o then (S.amp γ : ℂ) else 0)) := by
  have h2 : (S.amp γ : ℂ) * X (S.shift γ)
      = if S.shift γ = o then (S.amp γ : ℂ) else 0 := by
    rw [hX]
    split <;> simp
  have h1 : S.maj.hop (fun α => (S.amp α : ℂ) * X α) γ
      = if γ = S.shift o then (S.amp o : ℂ) else 0 := by
    by_cases hb : ∃ α, S.shift α = γ
    · obtain ⟨α, rfl⟩ := hb
      have hiff : S.shift α = S.shift o ↔ α = o :=
        ⟨fun h => S.shift_injective h, fun h => by rw [h]⟩
      rw [show S.shift α = S.maj.shift α from rfl, ShiftData.hop_shift, hX]
      by_cases hao : α = o
      · subst hao; simp
      · rw [if_neg hao, mul_zero]
        exact (if_neg (fun h => hao (hiff.mp h))).symm
    · rw [ShiftData.hop_eq_zero _ _ (by simpa using hb)]
      exact (if_neg (fun h => hb ⟨o, h.symm⟩)).symm
  rw [SignedHop.hFun, h1, h2]

/-- The coordinates of the Hamiltonian of a finite family: the sum of the
coordinates of the members. -/
theorem listH_coe {sym : ι → ℝ} (L : List (SignedHop ι sym)) (x : maxDom sym) (γ : ι) :
    ((listH L x : L2I ι) : ι → ℂ) γ
      = (L.map (fun S => S.hFun ((x : L2I ι) : ι → ℂ) γ)).sum := by
  induction L with
  | nil => simp [listH]
  | cons S L ih =>
      rw [listH_cons]
      simp only [LinearMap.add_apply, lp.coeFn_add, Pi.add_apply, List.map_cons,
        List.sum_cons, SignedHop.hopH_coe, ih]

/-! ## The affine fiber field with coefficients of **arbitrary sign**

The affine fiber Hamiltonian `½(π V + V π)` for `V(u) = κ u + c` was built in
`BookProof.ChapterNavierStokesAffineFiberEsa` under `κ ≥ 0` and `c ≥ 0`, and the
sign of `c` was removed by the sign-flip unitary of
`BookProof.ChapterNavierStokesSignFlip`.  The signed instrument above removes
both signs at once: the two hopping amplitudes `(κ/2)√((n+1)(n+2))` and
`(c/√2)√(n+1)` are dominated in absolute value by the comparison symbol built
from `|κ|` and `|c|`, whatever their signs. -/

section GeneralAffine

open HermiteFarisLavine

variable (kap cst : ℝ)

/-- The comparison symbol of the affine fiber field with coefficients of
arbitrary sign: the number operator built from `|κ|` and `|c|`. -/
noncomputable def gsym : ℕ → ℝ := oscSymbol (affMu |kap| |cst|)

theorem gsym_ge_one (n : ℕ) : 1 ≤ gsym kap cst n :=
  oscSymbol_ge_one (by unfold affMu; positivity) n

theorem abs_amp_eq (n : ℕ) : |amp kap n| = amp |kap| n := by
  unfold amp
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_div]
  norm_num

theorem abs_shear_eq (n : ℕ) : |shear cst n| = shear |cst| n := by
  unfold shear
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_div,
    abs_of_nonneg (Real.sqrt_nonneg 2)]

/-- The `±2`-hopping of the linear part, with a strain rate of arbitrary
sign. -/
noncomputable def gLinHop : SignedHop ℕ (gsym kap cst) where
  shift := fun n => n + 2
  amp := amp kap
  K := |kap| + |cst|
  step := 4 * affMu |kap| |cst|
  shift_injective := fun a b hab => by simpa using hab
  K_nonneg := by positivity
  step_nonneg := by unfold affMu; positivity
  sym_ge_one := gsym_ge_one kap cst
  abs_amp_le := fun n => by
    rw [abs_amp_eq, gsym]
    exact amp_le_affine (abs_nonneg kap) (abs_nonneg cst) n
  sym_step := fun n => oscSymbol_step n

/-- The `±1`-hopping of the constant part, with a constant of arbitrary
sign. -/
noncomputable def gShearHop : SignedHop ℕ (gsym kap cst) where
  shift := fun n => n + 1
  amp := shear cst
  K := |kap| + |cst|
  step := 2 * affMu |kap| |cst|
  shift_injective := fun a b hab => by simpa using hab
  K_nonneg := by positivity
  step_nonneg := by unfold affMu; positivity
  sym_ge_one := gsym_ge_one kap cst
  abs_amp_le := fun n => by
    rw [abs_shear_eq, gsym]
    exact shear_le (abs_nonneg cst) (abs_nonneg kap) n
  sym_step := fun n => by unfold gsym oscSymbol; push_cast; ring

/-- **The affine fiber Hamiltonian for an arbitrary real strain rate and an
arbitrary real constant** `V(u) = κ u + c`, on the maximal domain of the
comparison symbol built from `|κ|` and `|c|`. -/
noncomputable def gaffH : maxDom (gsym kap cst) →ₗ[ℂ] L2I ℕ :=
  listH [gLinHop kap cst, gShearHop kap cst]

theorem gaffH_symmetricOn : SymmetricOn (maxDom (gsym kap cst)) (gaffH kap cst) :=
  listH_symmetricOn _

/-- **No sign hypothesis at all**: for every real `κ` and every real `c` the
affine fiber Hamiltonian is essentially self-adjoint on the finite-mode core. -/
theorem gaffH_essentiallySelfAdjointOn_core :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      ((gaffH kap cst).comp (Submodule.inclusion (finiteModes_le_maxDom (gsym kap cst)))) :=
  listH_essentiallySelfAdjointOn_core _ (gsym_ge_one kap cst)

end GeneralAffine

end SignedShift

end BookProof.NavierStokesFlow
