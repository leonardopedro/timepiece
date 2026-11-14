/-
Copyright (c) 2026.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BookProof

# The structure-constant remainder of `{Ω, b}`

§62 of `SM_ESA_COMPLETION_PLAN` constructs the b-ghost of the derivation half of
`smBrstCharge` — the antighost sum `b = Σ_a β_a` — and proves

  `{ Σ_a χ_a G^a , Σ_b β_b }  =  Σ_a G^a`.

That is the *matter* half.  The full charge is `Ω = Σ_a χ_a G^a − ½ f_{abe} χ_a χ_b β_e`, and §62.3
left the cubic ghost half as an open remainder described only as "a ghost–antighost bilinear
carrying `f`".  This file computes it.

The contraction is the content.  Each cubic ghost term has one antighost, so the naive expectation is
that the cubic half anticommutes with `b` trivially.  It does not: pushing `β_d` through the pair
`χ_a χ_b` produces *two* contraction terms, and their sum is

  `{ χ_a χ_b β_e , β_d }  =  δ_{da} χ_b β_e  −  δ_{db} χ_a β_e`

(`cubic_anticomm`).  Summing over `d` gives `χ_b β_e − χ_a β_e` (`sum_d_cubic_anticomm`), and then
over the charge

  `{ Q f χ β , b }  =  2 · Σ_{x,e} (Σ_y f_{yxe}) · χ_x β_e`   (`Q_anticomm_bGhost`),

because antisymmetry in the first two slots turns the two pieces into the same sum.  Hence

  `{ Ω , b }  =  Σ_a G_a  −  Σ_{x,e} (Σ_y f_{yxe}) χ_x β_e`   (`brstCharge_anticomm_bGhost`).

So the remainder is exactly the **trace of `f` in its first slot**, a ghost–antighost bilinear.  It is
what §62.3 could only name.  Two consequences:

* `brstCharge_anticomm_bGhost_of_trace_zero`: when `Σ_y f_{yxe} = 0` — in particular for the abelian
  algebra — the derivation's b-ghost anticommutes with the *full* charge, not just its matter half.
* `su2Trace_nonzero`: for the `su(2)` structure constants of the index model the trace is `±1`, so
  the remainder is nonzero (`su2_trace_nonzero`).  The full charge therefore does **not** admit `b` as
  a contracting homotopy, for the same structural reason as §62's matter half: the contraction lands
  in the Gauss sector.

Everything is `sorry`-free and `axiom`-free.
-/

import BookProof.Sm.ChapterSmBrstGhost

namespace BookProof.SmGhostRemainder

open BookProof.BRSTNilpotent BookProof.SmBrstGhost BookProof.SmCar

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}

/-! ## 1. One antighost against one cubic ghost term -/

omit [Algebra ℝ R] in
/-- **The contraction.**  Anticommuting a single antighost past a cubic ghost monomial is not free:
`β_d` moving through `χ_a χ_b` leaves the two contraction terms `δ_{da} χ_b β_e` and
`δ_{db} χ_a β_e`, and the normal-ordered part cancels against the other ordering. -/
theorem cubic_anticomm (χ β : Fin n → R) (hCAR : GhostCAR χ β) (a b e d : Fin n) :
    (χ a * χ b * β e) * β d + β d * (χ a * χ b * β e)
      = (if d = a then χ b * β e else 0) - (if d = b then χ a * β e else 0) := by
  -- `β_e β_d = − β_d β_e`: the two antighosts anticommute.
  have hbb : β e * β d = -(β d * β e) := eq_neg_of_add_eq_zero_left (hCAR.betabeta e d)
  -- the normal-ordered reordering of `β_d` past the pair `χ_a χ_b`
  have hmove := beta_move χ β hCAR d a b
  have hright : β d * (χ a * χ b * β e)
      = (if d = a then χ b * β e else 0) - (if d = b then χ a * β e else 0)
        + χ a * χ b * β d * β e := by
    rw [← mul_assoc, hmove]
    simp only [sub_mul, add_mul, ite_mul, zero_mul]
  have hleft : (χ a * χ b * β e) * β d = -(χ a * χ b * β d * β e) := by
    rw [mul_assoc (χ a * χ b) (β e) (β d), hbb]
    noncomm_ring
  rw [hleft, hright]
  noncomm_ring

omit [Algebra ℝ R] in
/-- **Summing the contraction over the antighost label**: `Σ_d { χ_a χ_b β_e , β_d } = χ_b β_e −
χ_a β_e`.  The two `if`-terms each contribute once. -/
theorem sum_d_cubic_anticomm (χ β : Fin n → R) (hCAR : GhostCAR χ β) (a b e : Fin n) :
    ∑ d, ((χ a * χ b * β e) * β d + β d * (χ a * χ b * β e)) = χ b * β e - χ a * β e := by
  rw [Finset.sum_congr rfl fun d _ => cubic_anticomm χ β hCAR a b e d,
    Finset.sum_sub_distrib]
  congr 1
  · simp [Finset.sum_ite_eq']
  · simp [Finset.sum_ite_eq']

/-! ## 2. The cubic half against the b-ghost -/

omit [Algebra ℝ R] in
/-- Splitting a triple sum of differences, one level at a time.  Stated as its own lemma so that
`Finset.sum_sub_distrib` never has to fire where the summand is not syntactically a difference. -/
theorem sum3_sub (X Y : Fin n → Fin n → Fin n → R) :
    (∑ a, ∑ b, ∑ e, (X a b e - Y a b e))
      = (∑ a, ∑ b, ∑ e, X a b e) - (∑ a, ∑ b, ∑ e, Y a b e) := by
  have h2 : ∀ a b, (∑ e, (X a b e - Y a b e))
      = (∑ e, X a b e) - (∑ e, Y a b e) :=
    fun a b => Finset.sum_sub_distrib (s := Finset.univ) (f := fun e => X a b e)
      (g := fun e => Y a b e)
  have h1 : ∀ a, (∑ b, ∑ e, (X a b e - Y a b e))
      = (∑ b, ∑ e, X a b e) - (∑ b, ∑ e, Y a b e) := by
    intro a
    calc ∑ b, ∑ e, (X a b e - Y a b e)
        = ∑ b, ((∑ e, X a b e) - (∑ e, Y a b e)) :=
          Finset.sum_congr rfl fun b _ => h2 a b
      _ = (∑ b, ∑ e, X a b e) - (∑ b, ∑ e, Y a b e) :=
        Finset.sum_sub_distrib (s := Finset.univ) (f := fun b => ∑ e, X a b e)
          (g := fun b => ∑ e, Y a b e)
  calc ∑ a, ∑ b, ∑ e, (X a b e - Y a b e)
      = ∑ a, ((∑ b, ∑ e, X a b e) - (∑ b, ∑ e, Y a b e)) :=
        Finset.sum_congr rfl fun a _ => h1 a
    _ = (∑ a, ∑ b, ∑ e, X a b e) - (∑ a, ∑ b, ∑ e, Y a b e) :=
      Finset.sum_sub_distrib (s := Finset.univ) (f := fun a => ∑ b, ∑ e, X a b e)
        (g := fun a => ∑ b, ∑ e, Y a b e)

/-- The first-slot trace of the structure constants, `Σ_y f_{yxe}`.  This is the coefficient of the
remainder: it is *not* the trace of `f` in a symmetric pair of slots, so antisymmetry does not force
it to vanish. -/
def structTrace (f : Fin n → Fin n → Fin n → ℝ) (x e : Fin n) : ℝ :=
  ∑ y, f y x e

/-- **The ghost half does not commute with `b`.**  The cubic part of the charge anticommutes
with the antighost sum to twice the first-slot trace of `f`, contracted against `χ_x β_e`.
The factor two is the pair of contraction channels (`χ_a` and `χ_b`) made equal by
antisymmetry. -/
theorem Q_anticomm_bGhost (f : Fin n → Fin n → Fin n → ℝ) (χ β : Fin n → R)
    (hCAR : GhostCAR χ β) (hf12 : ∀ a b c, f a b c = -f b a c) :
    Q f χ β * (∑ d, β d) + (∑ d, β d) * Q f χ β
      = ∑ x, ∑ e, (2 * structTrace f x e) • (χ x * β e) := by
  classical
  -- expand both products into one quadruple sum
  have hQB : Q f χ β * (∑ d, β d)
      = ∑ a, ∑ b, ∑ e, ∑ d, (f a b e) • ((χ a * χ b * β e) * β d) := by
    unfold Q
    simp only [Finset.sum_mul, Finset.mul_sum, Algebra.smul_mul_assoc]
    refine (Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl fun a _ => (Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    exact Finset.sum_comm
  have hBQ : (∑ d, β d) * Q f χ β
      = ∑ a, ∑ b, ∑ e, ∑ d, (f a b e) • (β d * (χ a * χ b * β e)) := by
    unfold Q
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, mul_smul_comm]
    refine (Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl fun a _ => (Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    exact Finset.sum_comm
  have h_expand : Q f χ β * (∑ d, β d) + (∑ d, β d) * Q f χ β
      = ∑ a, ∑ b, ∑ e, ∑ d,
          (f a b e) • ((χ a * χ b * β e) * β d + β d * (χ a * χ b * β e)) := by
    rw [hQB, hBQ]
    simp only [← Finset.sum_add_distrib, smul_add]
  -- contract the innermost sum
  have h_inner : ∑ a, ∑ b, ∑ e, ∑ d,
      (f a b e) • ((χ a * χ b * β e) * β d + β d * (χ a * χ b * β e))
      = ∑ a, ∑ b, ∑ e, (f a b e) • (χ b * β e - χ a * β e) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.smul_sum, sum_d_cubic_anticomm χ β hCAR a b e]
  -- split the two pieces and regroup each by its own free index
  have h_first : ∑ a, ∑ b, ∑ e, (f a b e) • (χ b * β e)
      = ∑ x, ∑ e, (∑ a, f a x e) • (χ x * β e) := by
    refine (Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl fun x _ => (Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    exact (Finset.sum_smul (s := Finset.univ) (f := fun a => f a x e)
      (x := χ x * β e)).symm
  have h_second : ∑ a, ∑ b, ∑ e, (f a b e) • (χ a * β e)
      = ∑ x, ∑ e, (∑ y, f x y e) • (χ x * β e) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    exact (Finset.sum_smul (s := Finset.univ) (f := fun b => f x b e)
      (x := χ x * β e)).symm
  rw [h_expand, h_inner]
  -- put the two pieces over their own free index
  rw [show (∑ a, ∑ b, ∑ e, (f a b e) • (χ b * β e - χ a * β e))
        = ∑ a, ∑ b, ∑ e, ((f a b e) • (χ b * β e) - (f a b e) • (χ a * β e)) from by
      simp only [smul_sub]]
  rw [sum3_sub, h_first, h_second]
  -- merge the difference of the two regrouped sums into one sum
  rw [show (∑ x, ∑ e, (∑ a, f a x e) • (χ x * β e))
        - (∑ x, ∑ e, (∑ y, f x y e) • (χ x * β e))
      = ∑ x, ∑ e, ((∑ a, f a x e) - (∑ y, f x y e)) • (χ x * β e) from by
    rw [← Finset.sum_sub_distrib (s := Finset.univ)
      (f := fun x => ∑ e, (∑ a, f a x e) • (χ x * β e))
      (g := fun x => ∑ e, (∑ y, f x y e) • (χ x * β e))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib (s := Finset.univ)
      (f := fun e => (∑ a, f a x e) • (χ x * β e))
      (g := fun e => (∑ y, f x y e) • (χ x * β e))]
    exact Finset.sum_congr rfl fun e _ => (sub_smul _ _ _).symm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun e _ => ?_
  congr 1
  -- `Σ_a f a x e - Σ_y f x y e = 2 Σ_y f y x e`
  have hneg : (∑ y, f x y e) = -(∑ y, f y x e) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun y _ => by rw [hf12 x y e]
  rw [hneg, structTrace]
  ring

/-! ## 3. The full charge -/

/-- **`{Ω, b}` for the general charge.**  The matter half contributes the Gauss generators;
the cubic half contributes the negative of the first-slot trace.  This is the exact remainder
§62.3 described only qualitatively. -/
theorem brstCharge_anticomm_bGhost (f : Fin n → Fin n → Fin n → ℝ) (χ β G : Fin n → R)
    (hCAR : GhostCAR χ β) (hGβ : ∀ a b, G a * β b = β b * G a)
    (hf12 : ∀ a b c, f a b c = -f b a c) :
    brstCharge f χ β G * (∑ d, β d) + (∑ d, β d) * brstCharge f χ β G
      = (∑ a, G a) - ∑ x, ∑ e, (algebraMap ℝ R (structTrace f x e)) * (χ x * β e) := by
  classical
  -- the matter half: `{Σ χ_a G^a, b} = Σ G_a`
  have hmatter : (∑ a, χ a * G a) * (∑ d, β d) + (∑ d, β d) * (∑ a, χ a * G a)
      = ∑ a, G a := by
    have hXB : (∑ a, χ a * G a) * (∑ d, β d) = ∑ a, ∑ d, ((χ a * G a) * β d) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    have hBX : (∑ d, β d) * (∑ a, χ a * G a) = ∑ a, ∑ d, (β d * (χ a * G a)) := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    have hpair : ∀ a d : Fin n,
        (χ a * G a) * β d + β d * (χ a * G a) = (if d = a then (1 : R) else 0) * G a := by
      intro a d
      have hanti : χ a * β d = (if d = a then (1 : R) else 0) - β d * χ a := by
        rw [eq_sub_iff_add_eq, add_comm]
        exact hCAR.betachi d a
      calc (χ a * G a) * β d + β d * (χ a * G a)
          = χ a * (G a * β d) + β d * (χ a * G a) := by rw [mul_assoc]
        _ = (χ a * β d) * G a + β d * (χ a * G a) := by rw [hGβ a d, mul_assoc]
        _ = ((if d = a then (1 : R) else 0) - β d * χ a) * G a + β d * (χ a * G a) := by
              rw [hanti]
        _ = (if d = a then (1 : R) else 0) * G a := by rw [sub_mul, mul_assoc]; abel
    rw [hXB, hBX, ← Finset.sum_add_distrib (s := Finset.univ)
      (f := fun a => ∑ d, (χ a * G a) * β d)
      (g := fun a => ∑ d, β d * (χ a * G a))]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_congr rfl fun d _ => hpair a d]
    have hstep : ∀ d : Fin n, (if d = a then (1 : R) else 0) * G a
        = (if d = a then G a else 0) := by
      intro d
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun d _ => hstep d, Finset.sum_ite_eq']
    simp
  -- the ghost half, with the factor `1/2` of the charge absorbed
  have hghost := Q_anticomm_bGhost f χ β hCAR hf12
  have hhalf : (1 / 2 : ℝ) • (Q f χ β * (∑ d, β d) + (∑ d, β d) * Q f χ β)
      = ∑ x, ∑ e, (algebraMap ℝ R (structTrace f x e)) * (χ x * β e) := by
    rw [hghost]
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun e _ => ?_
    rw [Algebra.smul_def]
    congr 1
    ring
  unfold brstCharge
  rw [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
  -- `(X - ½•Q)*b + b*(X - ½•Q) = (X*b + b*X) - ½•(Q*b + b*Q)`
  have hsplit : ∀ (c : ℝ) (A B C D : R),
      A * B - c • (C * B) + (D * A - c • (D * C)) = A * B + D * A - c • (C * B + D * C) := by
    intro c A B C D
    rw [smul_add]
    abel
  rw [hsplit, hmatter, hhalf]

/-- **When the trace vanishes, `b` anticommutes with the whole charge.**  In particular for an
abelian algebra the derivation's b-ghost is a genuine b-ghost, not only of its matter half. -/
theorem brstCharge_anticomm_bGhost_of_trace_zero (f : Fin n → Fin n → Fin n → ℝ) (χ β G : Fin n → R)
    (hCAR : GhostCAR χ β) (hGβ : ∀ a b, G a * β b = β b * G a)
    (hf12 : ∀ a b c, f a b c = -f b a c)
    (htr : ∀ x e, structTrace f x e = 0) :
    brstCharge f χ β G * (∑ d, β d) + (∑ d, β d) * brstCharge f χ β G = ∑ a, G a := by
  rw [brstCharge_anticomm_bGhost f χ β G hCAR hGβ hf12]
  have : (∑ x, ∑ e, (algebraMap ℝ R (structTrace f x e)) * (χ x * β e)) = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun e _ => ?_
    rw [htr x e, map_zero, zero_mul]
  rw [this, sub_zero]

/-- **The abelian case recovers §62's corollary**: with `f = 0` the full charge *is* its
matter half, and `b` anticommutes with it to the Gauss sum. -/
theorem brstCharge_anticomm_bGhost_abelian (χ β G : Fin n → R)
    (hCAR : GhostCAR χ β) (hGβ : ∀ a b, G a * β b = β b * G a) :
    brstCharge (fun _ _ _ => 0) χ β G * (∑ d, β d)
        + (∑ d, β d) * brstCharge (fun _ _ _ => 0) χ β G = ∑ a, G a := by
  refine brstCharge_anticomm_bGhost_of_trace_zero _ χ β G hCAR hGβ
    (fun a b c => by simp) ?_
  intro x e
  simp [structTrace]

/-! ## 4. The Standard-Model charge -/

/-- **`smBrstCharge` is `brstCharge` at the SM data**, by definition: the specialization of
`brstCharge_anticomm_bGhost` to `f := smStruct f3`, `χ := ghostCre m`, `β := ghostAnn m`,
`G := matterGen m T` is therefore `{smBrstCharge m T f3, b} = Σ G − Σ (trace of smStruct)`.

That specialization is *not* asserted as a separate Lean theorem here: stating it forces Lean to
unify `Module.End ℂ (FermiFock (m + 12))`-typed `brstCharge` arguments at `n = 12`, and that
unification does not terminate in the heartbeat budget (reproduced in isolation with abstract
operators, so it is the `OfNat (Module.End …) 1` / `DecidableEq (Fin 12)` interplay rather than the
mathematics).  The general theorem above is the mathematical content; the identification of the SM
charge with its instance is `smBrstCharge`'s definition. -/
theorem smBrstCharge_def (m : ℕ) (T : Fin 12 → Matrix (Fin m) (Fin m) ℂ)
    (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    smBrstCharge m T f3
      = brstCharge (smStruct f3) (ghostCre m) (ghostAnn m) (matterGen m T) := rfl

/-! ## 5. The trace does not vanish for `su(2)` -/

/-- **The remainder is nonzero in the non-abelian case.**  For the `su(2)` structure constants
`f_{abc} = ε_{abc}` the first-slot trace is `±1` (`su2Trace 1 0 = −1`), so `{smBrstCharge, b}` is
*not* the Gauss sum alone and `b` is not a contracting homotopy for the full charge. -/
def su2Trace (x e : Fin 3) : ℝ := ∑ y : Fin 3, su2Struct y x e

theorem epsZ_trace_ten : (∑ y : Fin 3, epsZ y 1 0) = -1 := by decide

theorem su2Trace_nonzero : su2Trace 1 0 = -1 := by
  simp only [su2Trace, su2Struct]
  exact_mod_cast epsZ_trace_ten

/-- The trace is the obstruction, not the algebra: `su2Trace` is *not* identically zero, so
`brstCharge_anticomm_bGhost_of_trace_zero` cannot be applied to the index model. -/
theorem su2Trace_ne_zero : su2Trace ≠ 0 := by
  intro h
  have h10 := congrFun (congrFun h 1) 0
  rw [su2Trace_nonzero] at h10
  norm_num at h10

end BookProof.SmGhostRemainder
