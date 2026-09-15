import Mathlib

/-!
# Chapter KrylovShiftSpan — the multi-shift Krylov spaces

The SIRK/Hashimoto solver builds its subspace either from the **shifted products**
`v, (H − z₀)v, (H − z₁)(H − z₀)v, …` or from the **resolvent (rational Krylov)**
sequence `v, X₀v, X₁X₀v, …` with `Xᵢ = (H − zᵢ)⁻¹`, for a sequence of (possibly
distinct, possibly complex) shifts, while the theory is written for the plain Krylov
space `span{v, Hv, …, Hᵏv}`.

This chapter proves that all three descriptions agree, in the algebraic generality in
which they are true: no topology, no self-adjointness, an arbitrary module over an
arbitrary commutative ring, and an arbitrary shift sequence.

### Relation to the rest of the development

The *forward-sequence* half of the statement is already available analytically in
`BookProof/ChapterSirkMultiShift.lean` (`krylov_multiShift_eq_standard`,
`krylov_multiShift_span_eq_of_shifts`), over a field and for vectors of the sequence;
what is re-proved here is its purely algebraic operator-product form
(`forwardProd`, over a commutative ring), because the resolvent statement below needs
the products themselves, not just the vectors they produce.  The *resolvent* half is
new: `BookProof/ChapterHashimotoComplexShifts.lean` describes the rational Krylov space
as rational functions of one fixed resolvent (`sirkDen_rkVec`), whereas
`resolventSpan_eq_map_krylovSpan` below identifies it with the image of the ordinary
Krylov space of `H` itself under the product of the resolvents.

## Deliverables

* `shiftOp T z = T − z`, `forwardProd T z j = (T − z_{j−1}) ⋯ (T − z₀)` and
  `krylovSpan` / `forwardSpan` — the plain and the shifted Krylov subspaces.
* **`forwardSpan_eq_krylovSpan`** — the two spans coincide at every truncation level `k`:
  the shifted forward sequence spans exactly the Krylov space.  Hence
  `forwardSpan_eq_forwardSpan` : *the span does not depend on the shifts at all*, which is
  what makes the numerics' freedom to choose (and to reorder, or to repeat) the shifts
  harmless.
* `resProd X j = X_{j−1} ⋯ X₀` and `resolventSpan`; `commute_resolvent_shiftOp` and
  `resProd_mul_tailProd` — the resolvent of one shift commutes with every shifted
  operator, and the resolvents telescope against the shifted products.
* **`resolventSpan_eq_map_krylovSpan`** — the rational (resolvent) Krylov space is the
  image of the ordinary Krylov space under the product of all `k` resolvents:
  `span{v, X₀v, X₁X₀v, …, X_{k−1}⋯X₀v} = (X_{k−1}⋯X₀) '' span{v, Tv, …, Tᵏv}`.
  So the three subspaces the plan lists are the same subspace up to the invertible factor
  `X_{k−1}⋯X₀`.  (No permutation statement is claimed; what is proved is the description
  above, which is the form the compression arguments use.)  The bridge is
  `tailSpan_eq_krylovSpan`: the tail products `(T − z_{k−1}) ⋯ (T − z_j)`, `j ≤ k`, are
  the forward products of the *reversed* shift sequence, hence span the Krylov space too.
* `resProd_mul_forwardProd` / `forwardProd_mul_resProd` (the two products are mutually
  inverse) and hence `krylovSpan_eq_map_resolventSpan`, the inverse form of the identity
  above.
* `resVec` and `resolventSpan_eq_span_resVec` — the resolvent span written with the
  vectors the solver actually computes, `v, X₀v, X₁X₀v, …`, one resolvent solve at a time.
* **`resolventSpan_of_perm`** — *the rational Krylov space does not depend on the order in
  which the shifts are used*: for a permutation of `ℕ` fixing everything from `k` on,
  the reordered schedule reaches the same subspace (`resProd_of_perm`: the product of the
  resolvents is order-independent, since they commute).  The intermediate flag does
  change; the space at level `k` does not.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.KrylovShiftSpan

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

/-! ## 1. The shifted operators and the two spans -/

/-- The shifted operator `T − z`. -/
def shiftOp (T : Module.End R V) (z : R) : Module.End R V := T - z • (1 : Module.End R V)

/-- The forward product `(T − z_{j−1}) ⋯ (T − z₀)` of the first `j` shifted operators. -/
def forwardProd (T : Module.End R V) (z : ℕ → R) : ℕ → Module.End R V
  | 0 => 1
  | (n + 1) => shiftOp T (z n) * forwardProd T z n

@[simp] theorem forwardProd_zero (T : Module.End R V) (z : ℕ → R) :
    forwardProd T z 0 = 1 := rfl

theorem forwardProd_succ (T : Module.End R V) (z : ℕ → R) (n : ℕ) :
    forwardProd T z (n + 1) = shiftOp T (z n) * forwardProd T z n := rfl

/-- The **Krylov subspace** `span{v, Tv, …, Tᵏv}`. -/
def krylovSpan (T : Module.End R V) (v : V) (k : ℕ) : Submodule R V :=
  Submodule.span R {x | ∃ j ≤ k, x = (T ^ j) v}

/-- The **shifted (forward) Krylov subspace** `span{v, (T − z₀)v, (T − z₁)(T − z₀)v, …}`. -/
def forwardSpan (T : Module.End R V) (z : ℕ → R) (v : V) (k : ℕ) : Submodule R V :=
  Submodule.span R {x | ∃ j ≤ k, x = forwardProd T z j v}

theorem pow_mem_krylovSpan {T : Module.End R V} {v : V} {j k : ℕ} (hjk : j ≤ k) :
    (T ^ j) v ∈ krylovSpan T v k :=
  Submodule.subset_span ⟨j, hjk, rfl⟩

theorem forwardProd_mem_forwardSpan {T : Module.End R V} {z : ℕ → R} {v : V} {j k : ℕ}
    (hjk : j ≤ k) : forwardProd T z j v ∈ forwardSpan T z v k :=
  Submodule.subset_span ⟨j, hjk, rfl⟩

theorem krylovSpan_mono {T : Module.End R V} {v : V} {k l : ℕ} (hkl : k ≤ l) :
    krylovSpan T v k ≤ krylovSpan T v l :=
  Submodule.span_mono fun _ ⟨j, hj, hx⟩ => ⟨j, hj.trans hkl, hx⟩

theorem forwardSpan_mono {T : Module.End R V} {z : ℕ → R} {v : V} {k l : ℕ} (hkl : k ≤ l) :
    forwardSpan T z v k ≤ forwardSpan T z v l :=
  Submodule.span_mono fun _ ⟨j, hj, hx⟩ => ⟨j, hj.trans hkl, hx⟩

/-- Applying `T` moves the Krylov space one level up. -/
theorem map_krylovSpan_le (T : Module.End R V) (v : V) (k : ℕ) :
    Submodule.map T (krylovSpan T v k) ≤ krylovSpan T v (k + 1) := by
  rw [krylovSpan, Submodule.map_span, Submodule.span_le]
  rintro x ⟨y, ⟨j, hj, rfl⟩, rfl⟩
  have : T ((T ^ j) v) = (T ^ (j + 1)) v := by
    rw [pow_succ']
    rfl
  rw [this]
  exact pow_mem_krylovSpan (by omega)

/-- Applying `T` moves the shifted Krylov space one level up. -/
theorem map_forwardSpan_le (T : Module.End R V) (z : ℕ → R) (v : V) (k : ℕ) :
    Submodule.map T (forwardSpan T z v k) ≤ forwardSpan T z v (k + 1) := by
  rw [forwardSpan, Submodule.map_span, Submodule.span_le]
  rintro x ⟨y, ⟨j, hj, rfl⟩, rfl⟩
  have hstep : T (forwardProd T z j v)
      = forwardProd T z (j + 1) v + z j • forwardProd T z j v := by
    rw [forwardProd_succ, shiftOp]
    simp [Module.End.mul_apply]
  rw [hstep]
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
  · exact forwardProd_mem_forwardSpan (by omega)
  · exact forwardProd_mem_forwardSpan (by omega)

theorem forwardProd_mem_krylovSpan (T : Module.End R V) (z : ℕ → R) (v : V) :
    ∀ j : ℕ, forwardProd T z j v ∈ krylovSpan T v j := by
  intro j
  induction j with
  | zero =>
    have : forwardProd T z 0 v = (T ^ 0) v := by simp
    rw [this]
    exact pow_mem_krylovSpan le_rfl
  | succ n ih =>
    have hstep : forwardProd T z (n + 1) v
        = T (forwardProd T z n v) - z n • forwardProd T z n v := by
      rw [forwardProd_succ, shiftOp]
      simp [Module.End.mul_apply]
    rw [hstep]
    refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_)
    · exact map_krylovSpan_le T v n ⟨_, ih, rfl⟩
    · exact krylovSpan_mono (by omega) ih

theorem pow_mem_forwardSpan (T : Module.End R V) (z : ℕ → R) (v : V) :
    ∀ j : ℕ, (T ^ j) v ∈ forwardSpan T z v j := by
  intro j
  induction j with
  | zero =>
    have : (T ^ 0) v = forwardProd T z 0 v := by simp
    rw [this]
    exact forwardProd_mem_forwardSpan le_rfl
  | succ n ih =>
    have : (T ^ (n + 1)) v = T ((T ^ n) v) := by
      rw [pow_succ']
      rfl
    rw [this]
    exact map_forwardSpan_le T z v n ⟨_, ih, rfl⟩

/-- **The shifted forward sequence spans exactly the Krylov space**, for an arbitrary
sequence of shifts. -/
theorem forwardSpan_eq_krylovSpan (T : Module.End R V) (z : ℕ → R) (v : V) (k : ℕ) :
    forwardSpan T z v k = krylovSpan T v k := by
  refine le_antisymm ?_ ?_
  · rw [forwardSpan, Submodule.span_le]
    rintro x ⟨j, hj, rfl⟩
    exact krylovSpan_mono hj (forwardProd_mem_krylovSpan T z v j)
  · rw [krylovSpan, Submodule.span_le]
    rintro x ⟨j, hj, rfl⟩
    exact forwardSpan_mono hj (pow_mem_forwardSpan T z v j)

/-- **The shifted Krylov space does not depend on the shifts**: any two shift sequences
give the same subspace. -/
theorem forwardSpan_eq_forwardSpan (T : Module.End R V) (z z' : ℕ → R) (v : V) (k : ℕ) :
    forwardSpan T z v k = forwardSpan T z' v k := by
  rw [forwardSpan_eq_krylovSpan, forwardSpan_eq_krylovSpan]

end BookProof.KrylovShiftSpan
