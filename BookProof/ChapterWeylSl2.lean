import Mathlib

/-!
# Weyl's complete reducibility theorem for `sl(2,ℂ)`

`book.tex` states (Note 23, "Weyl theorem"):

> *All finite-dimensional representations of a semi-simple Lie group (such as SL(2,C))
> are completely reducible.*

and `BookProof.ChapterA3w` carries this as the named external hypothesis
`WeylCompleteReducibility`.  This file **proves** the theorem for the Lie algebra
`sl(2,ℂ)`, i.e. for every finite-dimensional complex vector space carrying operators
`E`, `F`, `H` with the `sl₂` commutation relations

`[H, E] = 2E`,  `[H, F] = -2F`,  `[E, F] = H`,

every invariant subspace has an invariant complement (`weyl_complete_reducibility`).

The proof is the classical Casimir argument, developed from scratch (Mathlib has no
Casimir element and no Weyl theorem):

* `cas` — the Casimir operator `2(EF + FE) + H²`, shown to commute with `E`, `F`, `H`;
* `exists_highestWeight` — every nonzero invariant subspace contains a vector `w ≠ 0`
  with `E w = 0` and `H w = lam • w`;
* `sl2_string_H`, `sl2_string_E` — the `sl₂`-string relations for `Fᵏ w`, giving
  `lam = m` for a natural number `m` and `F^(m+1) w = 0`;
* `cas_highestWeight` — the Casimir acts on such a `w` by `m² + 2m`, which vanishes
  only for the trivial module;
* `codim_one` — the codimension-one case, by induction on the dimension using
  quotient and sub-representations;
* `weyl_complete_reducibility` — the general case, via the `sl₂`-action
  `X · f = X f - f X` on `End V` applied to the space of operators that map `V` into
  `W` and act on `W` by a scalar.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ChapterWeylSl2

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- A representation of the Lie algebra `sl(2,ℂ)` on `V`: a triple of operators with the
standard commutation relations. -/
structure Sl2Rep (V : Type u) [AddCommGroup V] [Module ℂ V] where
  /-- The raising operator. -/
  E : Module.End ℂ V
  /-- The lowering operator. -/
  F : Module.End ℂ V
  /-- The Cartan (weight) operator. -/
  H : Module.End ℂ V
  /-- `[H, E] = 2E`. -/
  he : H * E - E * H = 2 • E
  /-- `[H, F] = -2F`. -/
  hf : H * F - F * H = -(2 • F)
  /-- `[E, F] = H`. -/
  hef : E * F - F * E = H

namespace Sl2Rep

variable (R : Sl2Rep V)

/-- A subspace is **invariant** iff it is stable under `E`, `F` and `H`. -/
def IsInv (W : Submodule ℂ V) : Prop :=
  (∀ x ∈ W, R.E x ∈ W) ∧ (∀ x ∈ W, R.F x ∈ W) ∧ (∀ x ∈ W, R.H x ∈ W)

/-- The **Casimir operator** `2(EF + FE) + H²`. -/
def cas : Module.End ℂ V := 2 • (R.E * R.F + R.F * R.E) + R.H * R.H

variable {R}

theorem he' : R.H * R.E = R.E * R.H + 2 • R.E := by rw [← R.he]; abel

theorem hf' : R.H * R.F = R.F * R.H - 2 • R.F := by
  have h := R.hf
  rw [eq_neg_iff_add_eq_zero] at h
  rw [← sub_eq_zero]
  rw [← h]; abel

theorem eh' : R.E * R.H - R.H * R.E = -(2 • R.E) := by rw [← neg_sub (R.H * R.E), R.he]

theorem fh' : R.F * R.H - R.H * R.F = 2 • R.F := by
  rw [← neg_sub (R.H * R.F), R.hf, neg_neg]

/-! ### The Casimir operator is central -/

theorem cas_comm_E : R.cas * R.E = R.E * R.cas := by
  have k1 : R.E * R.E - R.E * R.E = 0 := sub_self _
  have key : R.E * R.cas - R.cas * R.E
      = 2 • (((R.E * R.E - R.E * R.E) * R.F + R.E * (R.E * R.F - R.F * R.E))
          + ((R.E * R.F - R.F * R.E) * R.E + R.F * (R.E * R.E - R.E * R.E)))
        + ((R.E * R.H - R.H * R.E) * R.H + R.H * (R.E * R.H - R.H * R.E)) := by
    simp only [cas]; noncomm_ring
  rw [k1, R.hef, eh'] at key
  have h0 : R.E * R.cas - R.cas * R.E = 0 := by rw [key]; noncomm_ring
  exact (sub_eq_zero.mp h0).symm

theorem cas_comm_F : R.cas * R.F = R.F * R.cas := by
  have k1 : R.F * R.F - R.F * R.F = 0 := sub_self _
  have k2 : R.F * R.E - R.E * R.F = -R.H := by rw [← neg_sub (R.E * R.F), R.hef]
  have key : R.F * R.cas - R.cas * R.F
      = 2 • (((R.F * R.E - R.E * R.F) * R.F + R.E * (R.F * R.F - R.F * R.F))
          + ((R.F * R.F - R.F * R.F) * R.E + R.F * (R.F * R.E - R.E * R.F)))
        + ((R.F * R.H - R.H * R.F) * R.H + R.H * (R.F * R.H - R.H * R.F)) := by
    simp only [cas]; noncomm_ring
  rw [k1, k2, fh'] at key
  have h0 : R.F * R.cas - R.cas * R.F = 0 := by rw [key]; noncomm_ring
  exact (sub_eq_zero.mp h0).symm

theorem cas_comm_H : R.cas * R.H = R.H * R.cas := by
  have k1 : R.H * R.H - R.H * R.H = 0 := sub_self _
  have key : R.H * R.cas - R.cas * R.H
      = 2 • (((R.H * R.E - R.E * R.H) * R.F + R.E * (R.H * R.F - R.F * R.H))
          + ((R.H * R.F - R.F * R.H) * R.E + R.F * (R.H * R.E - R.E * R.H)))
        + ((R.H * R.H - R.H * R.H) * R.H + R.H * (R.H * R.H - R.H * R.H)) := by
    simp only [cas]; noncomm_ring
  rw [k1, R.he, R.hf] at key
  have h0 : R.H * R.cas - R.cas * R.H = 0 := by rw [key]; noncomm_ring
  exact (sub_eq_zero.mp h0).symm

/-! ### Sub- and quotient representations -/

/-- The restriction of a representation to an invariant subspace. -/
def restr (R : Sl2Rep V) (W : Submodule ℂ V) (hW : R.IsInv W) : Sl2Rep ↥W where
  E := R.E.restrict hW.1
  F := R.F.restrict hW.2.1
  H := R.H.restrict hW.2.2
  he := by
    ext x
    have h := congrArg (fun T : Module.End ℂ V => T (x : V)) R.he
    simpa [LinearMap.restrict_coe_apply] using h
  hf := by
    ext x
    have h := congrArg (fun T : Module.End ℂ V => T (x : V)) R.hf
    simpa [LinearMap.restrict_coe_apply] using h
  hef := by
    ext x
    have h := congrArg (fun T : Module.End ℂ V => T (x : V)) R.hef
    simpa [LinearMap.restrict_coe_apply] using h

@[simp] theorem restr_E_coe (R : Sl2Rep V) (W : Submodule ℂ V) (hW : R.IsInv W) (x : ↥W) :
    ((R.restr W hW).E x : V) = R.E (x : V) := rfl

@[simp] theorem restr_F_coe (R : Sl2Rep V) (W : Submodule ℂ V) (hW : R.IsInv W) (x : ↥W) :
    ((R.restr W hW).F x : V) = R.F (x : V) := rfl

@[simp] theorem restr_H_coe (R : Sl2Rep V) (W : Submodule ℂ V) (hW : R.IsInv W) (x : ↥W) :
    ((R.restr W hW).H x : V) = R.H (x : V) := rfl

/-- The quotient representation on `V ⧸ W` for an invariant subspace `W`. -/
def quot (R : Sl2Rep V) (W : Submodule ℂ V) (hW : R.IsInv W) : Sl2Rep (V ⧸ W) where
  E := W.mapQ W R.E hW.1
  F := W.mapQ W R.F hW.2.1
  H := W.mapQ W R.H hW.2.2
  he := by
    refine LinearMap.ext fun x => Quotient.inductionOn' x fun v => ?_
    have h := congrArg (fun T : Module.End ℂ V => T v) R.he
    simp only [Module.End.mul_apply, LinearMap.sub_apply, two_nsmul, LinearMap.add_apply] at h
    simp only [Submodule.Quotient.mk''_eq_mk, Module.End.mul_apply, LinearMap.sub_apply,
      two_nsmul, LinearMap.add_apply, Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub,
      ← Submodule.Quotient.mk_add, h]
  hf := by
    refine LinearMap.ext fun x => Quotient.inductionOn' x fun v => ?_
    have h := congrArg (fun T : Module.End ℂ V => T v) R.hf
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.neg_apply, two_nsmul,
      LinearMap.add_apply] at h
    simp only [Submodule.Quotient.mk''_eq_mk, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.neg_apply, two_nsmul, LinearMap.add_apply, Submodule.mapQ_apply,
      ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_neg, h]
  hef := by
    refine LinearMap.ext fun x => Quotient.inductionOn' x fun v => ?_
    have h := congrArg (fun T : Module.End ℂ V => T v) R.hef
    simp only [Module.End.mul_apply, LinearMap.sub_apply] at h
    simp only [Submodule.Quotient.mk''_eq_mk, Module.End.mul_apply, LinearMap.sub_apply,
      Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub, h]

@[simp] theorem quot_E_mk (R : Sl2Rep V) (W : Submodule ℂ V) (hW : R.IsInv W) (v : V) :
    (R.quot W hW).E (Submodule.Quotient.mk v) = Submodule.Quotient.mk (R.E v) := rfl

@[simp] theorem quot_F_mk (R : Sl2Rep V) (W : Submodule ℂ V) (hW : R.IsInv W) (v : V) :
    (R.quot W hW).F (Submodule.Quotient.mk v) = Submodule.Quotient.mk (R.F v) := rfl

@[simp] theorem quot_H_mk (R : Sl2Rep V) (W : Submodule ℂ V) (hW : R.IsInv W) (v : V) :
    (R.quot W hW).H (Submodule.Quotient.mk v) = Submodule.Quotient.mk (R.H v) := rfl

/-! ### Weights, highest-weight vectors and `sl₂`-strings -/

section Weights

variable {R : Sl2Rep V}

theorem apply_H_E (v : V) : R.H (R.E v) = R.E (R.H v) + 2 • R.E v := by
  have h := congrArg (fun T : Module.End ℂ V => T v) (he' (R := R))
  simpa [Module.End.mul_apply] using h

theorem apply_H_F (v : V) : R.H (R.F v) = R.F (R.H v) - 2 • R.F v := by
  have h := congrArg (fun T : Module.End ℂ V => T v) (hf' (R := R))
  simpa [Module.End.mul_apply] using h

theorem apply_E_F (v : V) : R.E (R.F v) = R.F (R.E v) + R.H v := by
  have h := congrArg (fun T : Module.End ℂ V => T v) R.hef
  simp only [Module.End.mul_apply, LinearMap.sub_apply] at h
  linear_combination (norm := abel) h

theorem pow_succ_apply (T : Module.End ℂ V) (k : ℕ) (v : V) :
    (T ^ (k + 1)) v = T ((T ^ k) v) := by
  rw [pow_succ']
  rfl

/-- `E` raises the weight by `2`. -/
theorem H_pow_E {w : V} {lam : ℂ} (h : R.H w = lam • w) (k : ℕ) :
    R.H ((R.E ^ k) w) = (lam + 2 * k) • (R.E ^ k) w := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      rw [pow_succ_apply, apply_H_E, ih, map_smul, two_nsmul]
      push_cast
      module

/-- `F` lowers the weight by `2`. -/
theorem H_pow_F {w : V} {lam : ℂ} (h : R.H w = lam • w) (k : ℕ) :
    R.H ((R.F ^ k) w) = (lam - 2 * k) • (R.F ^ k) w := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      rw [pow_succ_apply, apply_H_F, ih, map_smul, two_nsmul]
      push_cast
      module

/-- The `sl₂`-string relation `E Fᵏ⁺¹ w = (k+1)(lam - k) Fᵏ w` at a highest-weight vector. -/
theorem E_pow_F {w : V} {lam : ℂ} (hE : R.E w = 0) (h : R.H w = lam • w) (k : ℕ) :
    R.E ((R.F ^ (k + 1)) w) = ((k + 1 : ℂ) * (lam - k)) • (R.F ^ k) w := by
  induction k with
  | zero =>
      rw [pow_succ_apply, pow_zero, Module.End.one_apply, apply_E_F, hE, h, map_zero]
      push_cast
      module
  | succ k ih =>
      have hstep : R.E ((R.F ^ (k + 2)) w) = R.F (R.E ((R.F ^ (k + 1)) w))
          + R.H ((R.F ^ (k + 1)) w) := by
        rw [show k + 2 = (k + 1) + 1 from rfl, pow_succ_apply, apply_E_F]
      rw [hstep, ih, H_pow_F h (k + 1), map_smul, ← pow_succ_apply]
      push_cast
      module

/-- A nonzero finite-dimensional representation has a **highest-weight vector**. -/
theorem exists_highestWeight [FiniteDimensional ℂ V] [Nontrivial V] (R : Sl2Rep V) :
    ∃ (w : V) (lam : ℂ), w ≠ 0 ∧ R.E w = 0 ∧ R.H w = lam • w := by
  classical
  obtain ⟨mu, hmu⟩ := R.H.exists_eigenvalue
  obtain ⟨v, hv, hv0⟩ := hmu.exists_hasEigenvector
  have hvH : R.H v = mu • v := Module.End.mem_eigenspace_iff.mp hv
  by_cases hall : ∀ k : ℕ, (R.E ^ k) v ≠ 0
  · exfalso
    have hLI : LinearIndependent ℂ (fun k : ℕ => (R.E ^ k) v) := by
      refine Module.End.eigenvectors_linearIndependent' R.H (fun k : ℕ => mu + 2 * k) ?_ _ ?_
      · intro a b hab
        simp only at hab
        have h1 : (2 : ℂ) * a = 2 * b := add_left_cancel hab
        have h2 : (a : ℂ) = b := mul_left_cancel₀ two_ne_zero h1
        exact_mod_cast h2
      · intro k
        exact ⟨Module.End.mem_eigenspace_iff.mpr (H_pow_E hvH k), hall k⟩
    have hfin : LinearIndependent ℂ (fun i : Fin (Module.finrank ℂ V + 1) => (R.E ^ (i : ℕ)) v) :=
      hLI.comp _ Fin.val_injective
    have hcard := hfin.fintype_card_le_finrank
    simp at hcard
  · push_neg at hall
    obtain ⟨k0, hk0⟩ := hall
    have hex : ∃ k : ℕ, (R.E ^ k) v = 0 := ⟨k0, hk0⟩
    have hpos : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0, pow_zero, Module.End.one_apply] at this
      exact hv0 this
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    refine ⟨(R.E ^ n) v, mu + 2 * n, ?_, ?_, H_pow_E hvH n⟩
    · have := Nat.find_min hex (m := n) (by omega)
      exact this
    · have := Nat.find_spec hex
      rw [hn, pow_succ_apply] at this
      exact this

/-- The highest weight of a finite-dimensional representation is a natural number `m`, and the
`sl₂`-string stops after `m` steps. -/
theorem highestWeight_nat [FiniteDimensional ℂ V] {R : Sl2Rep V} {w : V} {lam : ℂ}
    (hw : w ≠ 0) (hE : R.E w = 0) (h : R.H w = lam • w) :
    ∃ m : ℕ, lam = (m : ℂ) ∧ (R.F ^ (m + 1)) w = 0 := by
  classical
  have hex : ∃ k : ℕ, (R.F ^ (k + 1)) w = 0 := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ k : ℕ, (R.F ^ k) w ≠ 0 := by
      intro k
      cases k with
      | zero => simpa using hw
      | succ n => exact hcon n
    have hLI : LinearIndependent ℂ (fun k : ℕ => (R.F ^ k) w) := by
      refine Module.End.eigenvectors_linearIndependent' R.H (fun k : ℕ => lam - 2 * k) ?_ _ ?_
      · intro a b hab
        simp only [sub_right_inj] at hab
        have h2 : (a : ℂ) = b := mul_left_cancel₀ two_ne_zero hab
        exact_mod_cast h2
      · intro k
        exact ⟨Module.End.mem_eigenspace_iff.mpr (H_pow_F h k), hall k⟩
    have hfin : LinearIndependent ℂ (fun i : Fin (Module.finrank ℂ V + 1) => (R.F ^ (i : ℕ)) w) :=
      hLI.comp _ Fin.val_injective
    have hcard := hfin.fintype_card_le_finrank
    simp at hcard
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  set m := Nat.find hex with hm
  have hmne : (R.F ^ m) w ≠ 0 := by
    cases hm0 : m with
    | zero => simpa [hm0] using hw
    | succ n =>
        have := Nat.find_min hex (m := n) (by omega)
        exact this
  have key := E_pow_F hE h m
  rw [Nat.find_spec hex, map_zero] at key
  rcases smul_eq_zero.mp key.symm with hc | hc
  · have hne : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
    exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left hne)
  · exact absurd hc hmne

/-- The Casimir operator acts on a highest-weight vector of weight `lam` by `lam² + 2 lam`. -/
theorem cas_highestWeight {R : Sl2Rep V} {w : V} {lam : ℂ} (hE : R.E w = 0)
    (h : R.H w = lam • w) : R.cas w = (lam ^ 2 + 2 * lam) • w := by
  have h1 : (R.E * R.F) w = lam • w := by
    rw [Module.End.mul_apply, apply_E_F, hE, map_zero, h, zero_add]
  have h2 : (R.F * R.E) w = 0 := by rw [Module.End.mul_apply, hE, map_zero]
  have h3 : (R.H * R.H) w = (lam ^ 2) • w := by
    rw [Module.End.mul_apply, h, map_smul, h, smul_smul, sq]
  simp only [cas, LinearMap.add_apply, two_nsmul, h1, h2, h3]
  module

end Weights

/-! ### Invariance of the kernel of the Casimir, and trivial modules -/

section Structure

variable {R : Sl2Rep V}

theorem eq_zero_of_add_self {x : V} (h : x + x = 0) : x = 0 := by
  have h2 : (2 : ℂ) • x = 0 := by rw [two_smul]; exact h
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem cas_comm_apply_E (v : V) : R.cas (R.E v) = R.E (R.cas v) :=
  congrArg (fun T : Module.End ℂ V => T v) cas_comm_E

theorem cas_comm_apply_F (v : V) : R.cas (R.F v) = R.F (R.cas v) :=
  congrArg (fun T : Module.End ℂ V => T v) cas_comm_F

theorem cas_comm_apply_H (v : V) : R.cas (R.H v) = R.H (R.cas v) :=
  congrArg (fun T : Module.End ℂ V => T v) cas_comm_H

/-- The kernel of the Casimir operator is invariant. -/
theorem isInv_ker_cas (R : Sl2Rep V) : R.IsInv (LinearMap.ker R.cas) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩ <;>
    rw [LinearMap.mem_ker] at hx ⊢
  · rw [cas_comm_apply_E, hx, map_zero]
  · rw [cas_comm_apply_F, hx, map_zero]
  · rw [cas_comm_apply_H, hx, map_zero]

/-- If all three operators map `V` into `W` and vanish on `W`, they vanish identically. -/
theorem ops_zero_of_trivial {W : Submodule ℂ V}
    (hmaps : ∀ v : V, R.E v ∈ W ∧ R.F v ∈ W ∧ R.H v ∈ W)
    (hzero : ∀ x ∈ W, R.E x = 0 ∧ R.F x = 0 ∧ R.H x = 0) (v : V) :
    R.E v = 0 ∧ R.F v = 0 ∧ R.H v = 0 := by
  have hHE : R.H (R.E v) = 0 := (hzero _ (hmaps v).1).2.2
  have hEH : R.E (R.H v) = 0 := (hzero _ (hmaps v).2.2).1
  have hFH : R.F (R.H v) = 0 := (hzero _ (hmaps v).2.2).2.1
  have hHF : R.H (R.F v) = 0 := (hzero _ (hmaps v).2.1).2.2
  have hE : R.E v = 0 := by
    have h := apply_H_E (R := R) v
    rw [hHE, hEH, zero_add, two_nsmul, eq_comm] at h
    exact eq_zero_of_add_self h
  have hF : R.F v = 0 := by
    have h := apply_H_F (R := R) v
    rw [hHF, hFH, zero_sub, two_nsmul, eq_comm, neg_eq_zero] at h
    exact eq_zero_of_add_self h
  refine ⟨hE, hF, ?_⟩
  have h := apply_E_F (R := R) v
  rw [hF, hE, map_zero, map_zero, zero_add, eq_comm] at h
  exact h

/-- A minimal invariant subspace on which the Casimir vanishes is a trivial module. -/
theorem ops_zero_of_minimal_cas_zero [FiniteDimensional ℂ V] {W : Submodule ℂ V}
    (hW : R.IsInv W) (hne : W ≠ ⊥) (hmin : ∀ U ≤ W, R.IsInv U → U = ⊥ ∨ U = W)
    (hcas : ∀ x ∈ W, R.cas x = 0) : ∀ x ∈ W, R.E x = 0 ∧ R.F x = 0 ∧ R.H x = 0 := by
  haveI : Nontrivial ↥W := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨ws, lam, hws0, hwsE, hwsH⟩ := (R.restr W hW).exists_highestWeight
  set w : V := (ws : V) with hwdef
  have hw0 : w ≠ 0 := by
    simpa [hwdef, Submodule.coe_eq_zero] using hws0
  have hwW : w ∈ W := ws.2
  have hwE : R.E w = 0 := by
    have := congrArg (fun y : ↥W => (y : V)) hwsE
    simpa [hwdef] using this
  have hwH : R.H w = lam • w := by
    have := congrArg (fun y : ↥W => (y : V)) hwsH
    simpa [hwdef] using this
  obtain ⟨m, hlam, hFm⟩ := highestWeight_nat hw0 hwE hwH
  have hcw : R.cas w = 0 := hcas w hwW
  have hval : (lam ^ 2 + 2 * lam) • w = 0 := by rw [← cas_highestWeight hwE hwH, hcw]
  have hzero : lam ^ 2 + 2 * lam = 0 := by
    rcases smul_eq_zero.mp hval with h | h
    · exact h
    · exact absurd h hw0
  have hm0 : m = 0 := by
    rw [hlam] at hzero
    have hfac : (m : ℂ) * ((m : ℂ) + 2) = 0 := by linear_combination hzero
    rcases mul_eq_zero.mp hfac with h | h
    · exact_mod_cast h
    · exfalso
      have : ((m : ℂ) + 2) ≠ 0 := by
        intro hc
        have hre : ((m : ℝ) + 2) = 0 := by
          have := congrArg Complex.re hc
          simpa using this
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      exact this h
  have hlam0 : lam = 0 := by rw [hlam, hm0]; simp
  have hwF : R.F w = 0 := by
    rw [hm0, zero_add, pow_one] at hFm
    exact hFm
  have hwH0 : R.H w = 0 := by rw [hwH, hlam0, zero_smul]
  have hspan : (Submodule.span ℂ {w} : Submodule ℂ V) = W := by
    have hle : (Submodule.span ℂ {w} : Submodule ℂ V) ≤ W := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hwW
    have hinv : R.IsInv (Submodule.span ℂ {w}) := by
      refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩ <;>
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      · rw [map_smul, hwE, smul_zero]; exact Submodule.zero_mem _
      · rw [map_smul, hwF, smul_zero]; exact Submodule.zero_mem _
      · rw [map_smul, hwH0, smul_zero]; exact Submodule.zero_mem _
    rcases hmin _ hle hinv with h | h
    · exact absurd h (by
        intro hc
        rw [Submodule.span_singleton_eq_bot] at hc
        exact hw0 hc)
    · exact h
  intro x hx
  rw [← hspan] at hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  refine ⟨?_, ?_, ?_⟩ <;> rw [map_smul]
  · rw [hwE, smul_zero]
  · rw [hwF, smul_zero]
  · rw [hwH0, smul_zero]

theorem IsInv.inf {R : Sl2Rep V} {U W : Submodule ℂ V} (hU : R.IsInv U) (hW : R.IsInv W) :
    R.IsInv (U ⊓ W) :=
  ⟨fun x hx => ⟨hU.1 x hx.1, hW.1 x hx.2⟩, fun x hx => ⟨hU.2.1 x hx.1, hW.2.1 x hx.2⟩,
    fun x hx => ⟨hU.2.2 x hx.1, hW.2.2 x hx.2⟩⟩

theorem cas_apply_eq {R : Sl2Rep V} (v : V) :
    R.cas v = 2 • (R.E (R.F v) + R.F (R.E v)) + R.H (R.H v) := rfl

/-! ### The codimension-one case -/

/-- **Weyl's theorem, codimension-one case.**  If a linear functional `phi` on `V` is onto and
all three operators map `V` into `ker phi`, then there is a vector `v` with `phi v = 1`
annihilated by the representation; equivalently, the invariant hyperplane `ker phi` has an
invariant (necessarily trivial) line as a complement.  The proof is by induction on
`finrank (ker phi)`. -/
theorem codim_one : ∀ (n : ℕ) {V : Type u} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (R : Sl2Rep V) (phi : V →ₗ[ℂ] ℂ) (v0 : V), phi v0 = 1 →
    (∀ v, phi (R.E v) = 0) → (∀ v, phi (R.F v) = 0) → (∀ v, phi (R.H v) = 0) →
    Module.finrank ℂ (LinearMap.ker phi) ≤ n →
    ∃ v : V, phi v = 1 ∧ R.E v = 0 ∧ R.F v = 0 ∧ R.H v = 0 := by
  intro n
  induction n with
  | zero =>
      intro V _ _ _ R phi v0 hv0 hE hF hH hrank
      have hker : LinearMap.ker phi = ⊥ := by
        rw [← Submodule.finrank_eq_zero]
        omega
      have hz : ∀ x : V, phi x = 0 → x = 0 := by
        intro x hx
        have hmem : x ∈ LinearMap.ker phi := hx
        rw [hker, Submodule.mem_bot] at hmem
        exact hmem
      exact ⟨v0, hv0, hz _ (hE v0), hz _ (hF v0), hz _ (hH v0)⟩
  | succ n ih =>
      intro V _ _ _ R phi v0 hv0 hE hF hH hrank
      classical
      have hmapE : ∀ v : V, R.E v ∈ LinearMap.ker phi := fun v => hE v
      have hmapF : ∀ v : V, R.F v ∈ LinearMap.ker phi := fun v => hF v
      have hmapH : ∀ v : V, R.H v ∈ LinearMap.ker phi := fun v => hH v
      have hWinv : R.IsInv (LinearMap.ker phi) :=
        ⟨fun x _ => hmapE x, fun x _ => hmapF x, fun x _ => hmapH x⟩
      -- the hyperplane has codimension one
      have hrangetop : LinearMap.range phi = ⊤ :=
        LinearMap.range_eq_top.mpr fun c => ⟨c • v0, by rw [map_smul, hv0, smul_eq_mul, mul_one]⟩
      have hWrank : Module.finrank ℂ (LinearMap.ker phi) + 1 = Module.finrank ℂ V := by
        have h := LinearMap.finrank_range_add_finrank_ker phi
        rw [hrangetop, finrank_top, Module.finrank_self] at h
        omega
      by_cases hsub : ∃ W' : Submodule ℂ V, R.IsInv W' ∧ W' ≠ ⊥ ∧ W' < LinearMap.ker phi
      · obtain ⟨W', hW'inv, hW'ne, hW'lt⟩ := hsub
        have hW'le : W' ≤ LinearMap.ker phi := le_of_lt hW'lt
        have hW'pos : 0 < Module.finrank ℂ ↥W' := by
          have := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.mpr hW'ne)
          simpa using this
        -- Step 1: pass to the quotient by `W'`
        set R' := R.quot W' hW'inv with hR'
        set phi' : (V ⧸ W') →ₗ[ℂ] ℂ := W'.liftQ phi hW'le with hphi'
        have hv0' : phi' (Submodule.Quotient.mk v0) = 1 := hv0
        have hE' : ∀ x, phi' (R'.E x) = 0 := by
          refine fun x => Quotient.inductionOn' x fun v => ?_
          exact hE v
        have hF' : ∀ x, phi' (R'.F x) = 0 := by
          refine fun x => Quotient.inductionOn' x fun v => ?_
          exact hF v
        have hH' : ∀ x, phi' (R'.H x) = 0 := by
          refine fun x => Quotient.inductionOn' x fun v => ?_
          exact hH v
        have hquot : Module.finrank ℂ (V ⧸ W') + Module.finrank ℂ ↥W' = Module.finrank ℂ V :=
          Submodule.finrank_quotient_add_finrank W'
        have hkerlt : Module.finrank ℂ ↥(LinearMap.ker phi') < Module.finrank ℂ (V ⧸ W') := by
          have hne : LinearMap.ker phi' ≠ ⊤ := by
            intro hc
            have : (Submodule.Quotient.mk v0 : V ⧸ W') ∈ LinearMap.ker phi' := by rw [hc]; trivial
            rw [LinearMap.mem_ker, hv0'] at this
            exact one_ne_zero this
          have := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hne)
          simpa using this
        have hrank' : Module.finrank ℂ (LinearMap.ker phi') ≤ n := by omega
        obtain ⟨u, hu1, huE, huF, huH⟩ :=
          ih R' phi' (Submodule.Quotient.mk v0) hv0' hE' hF' hH' hrank'
        obtain ⟨v, rfl⟩ := W'.mkQ_surjective u
        have hv1 : phi v = 1 := hu1
        have hvE : R.E v ∈ W' := by
          have : (Submodule.Quotient.mk (R.E v) : V ⧸ W') = 0 := huE
          rwa [Submodule.Quotient.mk_eq_zero] at this
        have hvF : R.F v ∈ W' := by
          have : (Submodule.Quotient.mk (R.F v) : V ⧸ W') = 0 := huF
          rwa [Submodule.Quotient.mk_eq_zero] at this
        have hvH : R.H v ∈ W' := by
          have : (Submodule.Quotient.mk (R.H v) : V ⧸ W') = 0 := huH
          rwa [Submodule.Quotient.mk_eq_zero] at this
        -- Step 2: work inside `U = W' + ℂ v`
        set U : Submodule ℂ V := W' ⊔ Submodule.span ℂ {v} with hU
        have hW'leU : W' ≤ U := le_sup_left
        have hvU : v ∈ U :=
          (le_sup_right : Submodule.span ℂ {v} ≤ U) (Submodule.mem_span_singleton_self v)
        have hUinv : R.IsInv U := by
          refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩ <;>
            obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx <;>
            obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb <;>
            rw [map_add, map_smul]
          · exact U.add_mem (hW'leU (hW'inv.1 a ha)) (U.smul_mem c (hW'leU hvE))
          · exact U.add_mem (hW'leU (hW'inv.2.1 a ha)) (U.smul_mem c (hW'leU hvF))
          · exact U.add_mem (hW'leU (hW'inv.2.2 a ha)) (U.smul_mem c (hW'leU hvH))
        set RU := R.restr U hUinv with hRU
        set phiU : ↥U →ₗ[ℂ] ℂ := phi.comp U.subtype with hphiU
        have hkerU : LinearMap.ker phiU = Submodule.comap U.subtype W' := by
          apply le_antisymm
          · intro x hx
            have hx0 : phi (x : V) = 0 := hx
            obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp x.2
            obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
            have hphia : phi a = 0 := hW'le ha
            have : c = 0 := by
              have := congrArg phi hab
              rw [map_add, map_smul, hphia, hv1, zero_add, smul_eq_mul, mul_one, hx0] at this
              exact this
            rw [this, zero_smul, add_zero] at hab
            change (x : V) ∈ W'
            rw [← hab]
            exact ha
          · intro x hx
            change phi (x : V) = 0
            exact hW'le hx
        have hrankU : Module.finrank ℂ (LinearMap.ker phiU) ≤ n := by
          rw [hkerU]
          have hequiv := Submodule.comapSubtypeEquivOfLe hW'leU
          rw [hequiv.finrank_eq]
          have := Submodule.finrank_lt_finrank_of_lt hW'lt
          omega
        obtain ⟨x, hx1, hxE, hxF, hxH⟩ :=
          ih RU phiU ⟨v, hvU⟩ (by exact hv1) (fun y => hE _) (fun y => hF _) (fun y => hH _) hrankU
        refine ⟨(x : V), hx1, ?_, ?_, ?_⟩
        · have := congrArg (fun y : ↥U => (y : V)) hxE
          simpa [hRU] using this
        · have := congrArg (fun y : ↥U => (y : V)) hxF
          simpa [hRU] using this
        · have := congrArg (fun y : ↥U => (y : V)) hxH
          simpa [hRU] using this
      · -- `ker phi` is minimal
        push_neg at hsub
        have hmin : ∀ U ≤ LinearMap.ker phi, R.IsInv U → U = ⊥ ∨ U = LinearMap.ker phi := by
          intro U hle hinv
          by_cases h0 : U = ⊥
          · exact Or.inl h0
          · refine Or.inr ?_
            by_contra hne
            exact absurd (lt_of_le_of_ne hle hne) (hsub U hinv h0)
        have hKW : R.IsInv (LinearMap.ker R.cas ⊓ LinearMap.ker phi) :=
          (isInv_ker_cas R).inf hWinv
        rcases hmin _ inf_le_right hKW with hcase | hcase
        · -- the Casimir is injective on the hyperplane: split off its kernel
          have hcasW : ∀ v : V, R.cas v ∈ LinearMap.ker phi := by
            intro v
            rw [cas_apply_eq, two_nsmul]
            exact Submodule.add_mem _ (Submodule.add_mem _
              (Submodule.add_mem _ (hmapE _) (hmapF _))
              (Submodule.add_mem _ (hmapE _) (hmapF _))) (hmapH _)
          have hnotinj : ¬ Function.Injective R.cas := by
            intro hinj
            obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective).mp hinj v0
            have hmem : v0 ∈ LinearMap.ker phi := hu ▸ hcasW u
            rw [LinearMap.mem_ker, hv0] at hmem
            exact one_ne_zero hmem
          have hkerne : LinearMap.ker R.cas ≠ ⊥ := by
            intro hc
            exact hnotinj (LinearMap.ker_eq_bot.mp hc)
          obtain ⟨u, hu, hune⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hkerne
          have hphiu : phi u ≠ 0 := by
            intro h0
            apply hune
            have hmem : u ∈ LinearMap.ker R.cas ⊓ LinearMap.ker phi := ⟨hu, h0⟩
            rw [hcase, Submodule.mem_bot] at hmem
            exact hmem
          have hzero : ∀ y : V, y ∈ LinearMap.ker R.cas → y ∈ LinearMap.ker phi → y = 0 := by
            intro y h1 h2
            have hmem : y ∈ LinearMap.ker R.cas ⊓ LinearMap.ker phi := ⟨h1, h2⟩
            rwa [hcase, Submodule.mem_bot] at hmem
          refine ⟨(phi u)⁻¹ • u, ?_, ?_, ?_, ?_⟩
          · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hphiu]
          · rw [map_smul, hzero _ ((isInv_ker_cas R).1 u hu) (hmapE u), smul_zero]
          · rw [map_smul, hzero _ ((isInv_ker_cas R).2.1 u hu) (hmapF u), smul_zero]
          · rw [map_smul, hzero _ ((isInv_ker_cas R).2.2 u hu) (hmapH u), smul_zero]
        · -- the Casimir vanishes on the hyperplane, which is therefore a trivial module
          have hWK : ∀ x ∈ LinearMap.ker phi, R.cas x = 0 := by
            intro x hx
            have hmem : x ∈ LinearMap.ker R.cas ⊓ LinearMap.ker phi := by rw [hcase]; exact hx
            exact hmem.1
          have htriv : ∀ x ∈ LinearMap.ker phi, R.E x = 0 ∧ R.F x = 0 ∧ R.H x = 0 := by
            by_cases hWbot : LinearMap.ker phi = ⊥
            · intro x hx
              rw [hWbot, Submodule.mem_bot] at hx
              subst hx
              simp
            · exact ops_zero_of_minimal_cas_zero hWinv hWbot hmin hWK
          have hall := ops_zero_of_trivial (fun v => ⟨hmapE v, hmapF v, hmapH v⟩) htriv
          exact ⟨v0, hv0, (hall v0).1, (hall v0).2.1, (hall v0).2.2⟩

/-! ### The adjoint action on operators -/

/-- The adjoint action `ad a : f ↦ a f - f a` of an operator on all operators. -/
def ad (a : Module.End ℂ V) : Module.End ℂ (Module.End ℂ V) :=
  LinearMap.mulLeft ℂ a - LinearMap.mulRight ℂ a

@[simp] theorem ad_apply (a f : Module.End ℂ V) : ad a f = a * f - f * a := by
  simp [ad, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]

theorem ad_add (a b : Module.End ℂ V) : ad (a + b) = ad a + ad b := by
  refine LinearMap.ext fun f => ?_
  simp only [ad_apply, LinearMap.add_apply]
  noncomm_ring

theorem ad_neg (a : Module.End ℂ V) : ad (-a) = -ad a := by
  refine LinearMap.ext fun f => ?_
  simp only [ad_apply, LinearMap.neg_apply]
  noncomm_ring

theorem ad_two_nsmul (a : Module.End ℂ V) : ad (2 • a) = 2 • ad a := by
  rw [two_nsmul, ad_add, two_nsmul]

/-- `ad` is a homomorphism of Lie algebras. -/
theorem ad_bracket (a b : Module.End ℂ V) : ad a * ad b - ad b * ad a = ad (a * b - b * a) := by
  refine LinearMap.ext fun f => ?_
  simp only [Module.End.mul_apply, LinearMap.sub_apply, ad_apply]
  noncomm_ring

/-- The `sl₂`-representation induced on the space of all operators. -/
def adRep (R : Sl2Rep V) : Sl2Rep (Module.End ℂ V) where
  E := ad R.E
  F := ad R.F
  H := ad R.H
  he := by rw [ad_bracket, R.he, ad_two_nsmul]
  hf := by rw [ad_bracket, R.hf, ad_neg, ad_two_nsmul]
  hef := by rw [ad_bracket, R.hef]

@[simp] theorem adRep_E (R : Sl2Rep V) (f : Module.End ℂ V) :
    (adRep R).E f = R.E * f - f * R.E := ad_apply _ _

@[simp] theorem adRep_F (R : Sl2Rep V) (f : Module.End ℂ V) :
    (adRep R).F f = R.F * f - f * R.F := ad_apply _ _

@[simp] theorem adRep_H (R : Sl2Rep V) (f : Module.End ℂ V) :
    (adRep R).H f = R.H * f - f * R.H := ad_apply _ _

/-- The operators that map `V` into `W` and act on `W` by a scalar. -/
def scalarOps (W : Submodule ℂ V) : Submodule ℂ (Module.End ℂ V) where
  carrier := {f | (∀ v : V, f v ∈ W) ∧ ∃ c : ℂ, ∀ w ∈ W, f w = c • w}
  add_mem' := by
    rintro f g ⟨hf1, cf, hf2⟩ ⟨hg1, cg, hg2⟩
    exact ⟨fun v => W.add_mem (hf1 v) (hg1 v), cf + cg, fun w hw => by
      simp [hf2 w hw, hg2 w hw, add_smul]⟩
  zero_mem' := ⟨fun _ => W.zero_mem, 0, fun w _ => by simp⟩
  smul_mem' := by
    rintro a f ⟨hf1, cf, hf2⟩
    exact ⟨fun v => W.smul_mem a (hf1 v), a * cf, fun w hw => by
      simp [hf2 w hw, mul_smul]⟩

theorem mem_scalarOps {W : Submodule ℂ V} {f : Module.End ℂ V} :
    f ∈ scalarOps W ↔ (∀ v : V, f v ∈ W) ∧ ∃ c : ℂ, ∀ w ∈ W, f w = c • w := Iff.rfl

/-- The space `scalarOps W` is invariant under the adjoint action, and the action lands in the
operators vanishing on `W`. -/
theorem isInv_scalarOps {R : Sl2Rep V} {W : Submodule ℂ V} (hW : R.IsInv W) :
    (adRep R).IsInv (scalarOps W) := by
  have key : ∀ (a : Module.End ℂ V), (∀ x ∈ W, a x ∈ W) → ∀ f ∈ scalarOps W,
      (a * f - f * a) ∈ scalarOps W := by
    rintro a ha f ⟨hf1, c, hf2⟩
    refine ⟨fun v => ?_, 0, fun w hw => ?_⟩
    · simp only [Module.End.mul_apply, LinearMap.sub_apply]
      exact W.sub_mem (ha _ (hf1 v)) (hf1 _)
    · simp only [Module.End.mul_apply, LinearMap.sub_apply]
      rw [hf2 w hw, hf2 _ (ha w hw), map_smul, sub_self, zero_smul]
  exact ⟨fun f hf => by rw [adRep_E]; exact key R.E hW.1 f hf,
    fun f hf => by rw [adRep_F]; exact key R.F hW.2.1 f hf,
    fun f hf => by rw [adRep_H]; exact key R.H hW.2.2 f hf⟩

/-! ### Weyl's theorem -/

/-- **Weyl's complete reducibility theorem for `sl(2,ℂ)`.**  In a finite-dimensional complex
representation of `sl(2,ℂ)` every invariant subspace has an invariant complement. -/
theorem weyl_complete_reducibility [FiniteDimensional ℂ V] (R : Sl2Rep V) (W : Submodule ℂ V)
    (hW : R.IsInv W) : ∃ W' : Submodule ℂ V, R.IsInv W' ∧ IsCompl W W' := by
  classical
  by_cases hWbot : W = ⊥
  · refine ⟨⊤, ⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩, ?_⟩
    rw [hWbot]
    exact isCompl_bot_top
  obtain ⟨w0, hw0W, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWbot
  obtain ⟨psi, hpsi⟩ := Module.Projective.exists_dual_eq_one ℂ hw0
  -- a vector-space projection onto `W`
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  set p : Module.End ℂ V := W.subtype ∘ₗ W.linearProjOfIsCompl C hC with hp
  have hpW : ∀ v : V, p v ∈ W := fun v => (W.linearProjOfIsCompl C hC v).2
  have hpid : ∀ w ∈ W, p w = w := by
    intro w hw
    have := Submodule.linearProjOfIsCompl_apply_left hC ⟨w, hw⟩
    simpa [hp] using congrArg (fun y : ↥W => (y : V)) this
  have hpmem : p ∈ scalarOps W := ⟨hpW, 1, fun w hw => by rw [hpid w hw, one_smul]⟩
  -- the codimension-one situation inside `scalarOps W`
  set S := scalarOps W with hS
  have hSinv : (adRep R).IsInv S := isInv_scalarOps hW
  set RS := (adRep R).restr S hSinv with hRS
  set phi : ↥S →ₗ[ℂ] ℂ :=
    { toFun := fun f => psi ((f : Module.End ℂ V) w0)
      map_add' := by intro f g; simp
      map_smul' := by intro a f; simp } with hphi
  have hphi_apply : ∀ f : ↥S, phi f = psi ((f : Module.End ℂ V) w0) := fun _ => rfl
  have hscal : ∀ (f : ↥S) (w : V), w ∈ W → (f : Module.End ℂ V) w = phi f • w := by
    intro f w hw
    obtain ⟨-, c, hc⟩ := f.2
    have hc0 : phi f = c := by
      rw [hphi_apply, hc w0 hw0W, map_smul, hpsi, smul_eq_mul, mul_one]
    rw [hc0, hc w hw]
  have hv0 : phi ⟨p, hpmem⟩ = 1 := by
    rw [hphi_apply]
    exact (congrArg psi (hpid w0 hw0W)).trans hpsi
  have hann : ∀ (a : Module.End ℂ V), (∀ x ∈ W, a x ∈ W) → ∀ f : ↥S,
      psi ((a * (f : Module.End ℂ V) - (f : Module.End ℂ V) * a) w0) = 0 := by
    intro a ha f
    simp only [Module.End.mul_apply, LinearMap.sub_apply]
    rw [hscal f w0 hw0W, hscal f _ (ha w0 hw0W), map_smul, sub_self, map_zero]
  have hE : ∀ f : ↥S, phi (RS.E f) = 0 := fun f => hann R.E hW.1 f
  have hF : ∀ f : ↥S, phi (RS.F f) = 0 := fun f => hann R.F hW.2.1 f
  have hH : ∀ f : ↥S, phi (RS.H f) = 0 := fun f => hann R.H hW.2.2 f
  obtain ⟨x, hx1, hxE, hxF, hxH⟩ :=
    codim_one (Module.finrank ℂ (LinearMap.ker phi)) RS phi ⟨p, hpmem⟩ hv0 hE hF hH le_rfl
  set f : Module.End ℂ V := (x : Module.End ℂ V) with hf
  have hfW : ∀ v : V, f v ∈ W := x.2.1
  have hfid : ∀ w ∈ W, f w = w := by
    intro w hw
    rw [hf, hscal x w hw, hx1, one_smul]
  have hfE : ∀ v : V, f (R.E v) = R.E (f v) := by
    have h0 : R.E * f - f * R.E = 0 := by
      have := congrArg (fun y : ↥S => (y : Module.End ℂ V)) hxE
      simpa [hRS, hf] using this
    intro v
    have h1 := congrArg (fun T : Module.End ℂ V => T v) h0
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at h1
    exact (sub_eq_zero.mp h1).symm
  have hfF : ∀ v : V, f (R.F v) = R.F (f v) := by
    have h0 : R.F * f - f * R.F = 0 := by
      have := congrArg (fun y : ↥S => (y : Module.End ℂ V)) hxF
      simpa [hRS, hf] using this
    intro v
    have h1 := congrArg (fun T : Module.End ℂ V => T v) h0
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at h1
    exact (sub_eq_zero.mp h1).symm
  have hfH : ∀ v : V, f (R.H v) = R.H (f v) := by
    have h0 : R.H * f - f * R.H = 0 := by
      have := congrArg (fun y : ↥S => (y : Module.End ℂ V)) hxH
      simpa [hRS, hf] using this
    intro v
    have h1 := congrArg (fun T : Module.End ℂ V => T v) h0
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at h1
    exact (sub_eq_zero.mp h1).symm
  -- `f` is an equivariant projection onto `W`, so its kernel is an invariant complement
  refine ⟨LinearMap.ker f, ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩, ⟨?_, ?_⟩⟩
  · rw [LinearMap.mem_ker] at hv ⊢
    rw [hfE, hv, map_zero]
  · rw [LinearMap.mem_ker] at hv ⊢
    rw [hfF, hv, map_zero]
  · rw [LinearMap.mem_ker] at hv ⊢
    rw [hfH, hv, map_zero]
  · refine Submodule.disjoint_def.mpr fun y hyW hyker => ?_
    rw [LinearMap.mem_ker] at hyker
    rw [← hfid y hyW, hyker]
  · refine codisjoint_iff.mpr (eq_top_iff.mpr fun v _ => ?_)
    refine Submodule.mem_sup.mpr ⟨f v, hfW v, v - f v, ?_, by abel⟩
    rw [LinearMap.mem_ker, map_sub, hfid (f v) (hfW v), sub_self]

end Structure

end Sl2Rep

end BookProof.ChapterWeylSl2
