import Mathlib
import BookProof.Sm.ChapterSmGradDomTransfer
import BookProof.Qym.ChapterYangMillsNonAbelianEsa

/-!
# The per-form `pderiv` table for the 49 Standard-Model forms

§48–§52 reduced the reverse elliptic estimate for the Standard Model potential to a single input:
for `j ∈ smS`, each derivative `∂_j Φ_r` of the 49 forms is a linear form supported in `smS`.  §51
showed that such a table *is* `GradBound`, and §52 that `GradBound` *is* `PotSelfBound`.  This
module supplies the table itself, so `PotSelfBound` stops being a hypothesis.

The table is not written out form by form.  Instead every form is recognised as an element of a
*normal form* — a constant, plus a complex-linear combination of `X u` with `u` in a "linear atom
set" `T`, plus a bilinear combination of `X u * X v` with `u, v` in a "quadratic atom set" `A` —
carried as **data** (`Biform`), so the derivative's coefficients can be *read off* rather than
computed.  Two facts then finish the job:

* `Biform.pderiv_eq` — for `j ∈ A` the derivative is `∑ v, C (sqf j v + sqf v j) * X v`, with the
  linear part contributing `linf j = 0` because `T` and `A` are disjoint;
* `Biform.sq_le` — Cauchy–Schwarz, `(∑_{v∈A} c_v x_v)² ≤ (∑_{v∈A} c_v²)(1 + ∑_{v∈A} x_v²)`, which
  is `GradBound`'s shape.

The five families of the Hamiltonian are then `Biform smS smSᶜ` instances by shape alone: a
constant, sums over the `Fin 3`/`Fin 8` index sets, real scalar multiples, products of two atoms of
`smS`, and single atoms of the derivative coordinates `smSᶜ`.  No index arithmetic and no `levi`,
`fabc`, `eabc`, `tgen` or `ygen` bookkeeping appears anywhere: the coefficients are *whatever they
are*, and only their squares enter the constant.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmGradTable

open MvPolynomial BookProof.HermiteProductCore BookProof.DegSchrodinger
open BookProof.SmGradDomStructural

variable {d : ℕ}

/-! ## 1. The normal form -/

/-- A polynomial with *coefficient data*: a constant, coefficients for linear atoms and
coefficients for bilinear atoms, with the linear atoms restricted to `T` and the bilinear ones to
`A`.  Data rather than a `Prop`, because the derivative coefficients are read off it: for `j ∈ A`
the derivative of the third summand is the row plus the column of `sqf` at `j`. -/
structure Biform (A T : Finset (Fin d)) where
  /-- the polynomial -/
  poly : MvPolynomial (Fin d) ℂ
  /-- the constant term -/
  cst : ℂ
  /-- the coefficients of the linear terms -/
  linf : Fin d → ℂ
  /-- the coefficients of the bilinear terms -/
  sqf : Fin d → Fin d → ℂ
  /-- linear terms use only the atoms of `T` -/
  lin_supp : ∀ v, v ∉ T → linf v = 0
  /-- bilinear terms use only the atoms of `A` on the left -/
  sq_supp₁ : ∀ u v, u ∉ A → sqf u v = 0
  /-- bilinear terms use only the atoms of `A` on the right -/
  sq_supp₂ : ∀ u v, v ∉ A → sqf u v = 0
  /-- the data represents the polynomial -/
  rep : poly = C cst + ∑ a, C (linf a) * X a
      + ∑ a, ∑ c, C (sqf a c) * (X a * X c)


namespace Biform

variable {A T : Finset (Fin d)} {β : Type}

theorem zero_lin_sum : (∑ a : Fin d, C ((0 : Fin d → ℂ) a) * X a)
    = (0 : MvPolynomial (Fin d) ℂ) := by simp

theorem zero_sq_sum :
    (∑ a : Fin d, ∑ c : Fin d, C ((0 : Fin d → Fin d → ℂ) a c) * (X a * X c))
      = (0 : MvPolynomial (Fin d) ℂ) := by simp

/-- The constant `c`. -/
noncomputable def const (c : ℂ) : Biform A T where
  poly := C c
  cst := c
  linf := 0
  sqf := 0
  lin_supp := fun _ _ => rfl
  sq_supp₁ := fun _ _ _ => rfl
  sq_supp₂ := fun _ _ _ => rfl
  rep := by rw [zero_lin_sum, zero_sq_sum]; simp

/-- A single linear atom `C c * X u` with `u ∈ T`. -/
noncomputable def lin (u : Fin d) (hu : u ∈ T) (c : ℂ) : Biform A T where
  poly := C c * X u
  cst := 0
  linf := fun a => if a = u then c else 0
  sqf := 0
  lin_supp := by
    intro a ha
    by_cases h : a = u
    · exact absurd (h ▸ hu) ha
    · simp [h]
  sq_supp₁ := fun _ _ _ => rfl
  sq_supp₂ := fun _ _ _ => rfl
  rep := by
    rw [zero_sq_sum, add_zero, map_zero, zero_add, Finset.sum_eq_single u]
    · simp
    · intro a _ ha; simp [ha]
    · intro h; simp at h

/-- A single bilinear atom `C c * (X u * X v)` with `u, v ∈ A`. -/
noncomputable def sq (u v : Fin d) (hu : u ∈ A) (hv : v ∈ A) (c : ℂ) : Biform A T where
  poly := C c * (X u * X v)
  cst := 0
  linf := 0
  sqf := fun a b => if a = u then (if b = v then c else 0) else 0
  lin_supp := fun _ _ => rfl
  sq_supp₁ := by
    intro a b ha
    by_cases h : a = u
    · exact absurd (h ▸ hu) ha
    · simp [h]
  sq_supp₂ := by
    intro a b hb
    by_cases h : a = u
    · by_cases h2 : b = v
      · exact absurd (h2 ▸ hv) hb
      · simp [h, h2]
    · simp [h]
  rep := by
    rw [zero_lin_sum, map_zero, zero_add, Finset.sum_eq_single u]
    · rw [Finset.sum_eq_single v]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; simp at h
    · intro a _ ha; simp [ha]
    · intro h; simp at h

/-- The linear atom `X u` itself, with `u ∈ T`. -/
noncomputable def atom (u : Fin d) (hu : u ∈ T) : Biform A T where
  poly := X u
  cst := 0
  linf := fun a => if a = u then 1 else 0
  sqf := 0
  lin_supp := by
    intro a ha
    by_cases h : a = u
    · exact absurd (h ▸ hu) ha
    · simp [h]
  sq_supp₁ := fun _ _ _ => rfl
  sq_supp₂ := fun _ _ _ => rfl
  rep := by
    rw [zero_sq_sum, add_zero, map_zero, zero_add, Finset.sum_eq_single u]
    · simp
    · intro a _ ha; simp [ha]
    · intro h; simp at h

/-- The bilinear atom `X u * X v` itself, with `u, v ∈ A`. -/
noncomputable def atomSq (u v : Fin d) (hu : u ∈ A) (hv : v ∈ A) : Biform A T where
  poly := X u * X v
  cst := 0
  linf := 0
  sqf := fun a c => if a = u then (if c = v then 1 else 0) else 0
  lin_supp := fun _ _ => rfl
  sq_supp₁ := by
    intro a c ha
    by_cases h : a = u
    · exact absurd (h ▸ hu) ha
    · simp [h]
  sq_supp₂ := by
    intro a c hc
    by_cases h : a = u
    · by_cases h2 : c = v
      · exact absurd (h2 ▸ hv) hc
      · simp [h, h2]
    · simp [h]
  rep := by
    rw [zero_lin_sum, map_zero, zero_add, Finset.sum_eq_single u]
    · rw [Finset.sum_eq_single v]
      · simp
      · intro c _ hc; simp [hc]
      · intro h; simp at h
    · intro a _ ha; simp [ha]
    · intro h; simp at h

/-- The difference of two normal forms. -/
noncomputable def sub (a b : Biform A T) : Biform A T where
  poly := a.poly - b.poly
  cst := a.cst - b.cst
  linf := fun v => a.linf v - b.linf v
  sqf := fun u v => a.sqf u v - b.sqf u v
  lin_supp := fun v hv => by rw [a.lin_supp v hv, b.lin_supp v hv, sub_zero]
  sq_supp₁ := fun u v hu => by rw [a.sq_supp₁ u v hu, b.sq_supp₁ u v hu, sub_zero]
  sq_supp₂ := fun u v hv => by rw [a.sq_supp₂ u v hv, b.sq_supp₂ u v hv, sub_zero]
  rep := by
    rw [a.rep, b.rep]
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    abel

theorem sum_lin_swap (s : Finset β) (l : β → Fin d → ℂ) :
    (∑ i ∈ s, ∑ v, C (l i v) * X v) = ∑ v, C (∑ i ∈ s, l i v) * X v := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_mul, ← map_sum]

theorem sum_sq_swap (s : Finset β) (q : β → Fin d → Fin d → ℂ) :
    (∑ i ∈ s, ∑ a, ∑ c, C (q i a c) * (X a * X c))
      = ∑ a, ∑ c, C (∑ i ∈ s, q i a c) * (X a * X c) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_mul, ← map_sum]

/-- The sum of two normal forms. -/
noncomputable def add (a b : Biform A T) : Biform A T where
  poly := a.poly + b.poly
  cst := a.cst + b.cst
  linf := fun v => a.linf v + b.linf v
  sqf := fun u v => a.sqf u v + b.sqf u v
  lin_supp := fun v hv => by rw [a.lin_supp v hv, b.lin_supp v hv, add_zero]
  sq_supp₁ := fun u v hu => by rw [a.sq_supp₁ u v hu, b.sq_supp₁ u v hu, add_zero]
  sq_supp₂ := fun u v hv => by rw [a.sq_supp₂ u v hv, b.sq_supp₂ u v hv, add_zero]
  rep := by
    rw [a.rep, b.rep]
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    abel

/-- The sum of a family of normal forms. -/
noncomputable def sum (s : Finset β) (h : β → Biform A T) : Biform A T where
  poly := ∑ i ∈ s, (h i).poly
  cst := ∑ i ∈ s, (h i).cst
  linf := fun v => ∑ i ∈ s, (h i).linf v
  sqf := fun u v => ∑ i ∈ s, (h i).sqf u v
  lin_supp := fun v hv => Finset.sum_eq_zero fun i _ => (h i).lin_supp v hv
  sq_supp₁ := fun u v hu => Finset.sum_eq_zero fun i _ => (h i).sq_supp₁ u v hu
  sq_supp₂ := fun u v hv => Finset.sum_eq_zero fun i _ => (h i).sq_supp₂ u v hv
  rep := by
    conv_lhs => rw [Finset.sum_congr rfl fun i (_ : i ∈ s) => (h i).rep]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← map_sum, sum_lin_swap, sum_sq_swap]

/-- A complex multiple of a normal form. -/
noncomputable def smul (c : ℂ) (a : Biform A T) : Biform A T where
  poly := c • a.poly
  cst := c * a.cst
  linf := fun v => c * a.linf v
  sqf := fun u v => c * a.sqf u v
  lin_supp := fun v hv => by rw [a.lin_supp v hv, mul_zero]
  sq_supp₁ := fun u v hu => by rw [a.sq_supp₁ u v hu, mul_zero]
  sq_supp₂ := fun u v hv => by rw [a.sq_supp₂ u v hv, mul_zero]
  rep := by
    rw [a.rep, smul_eq_C_mul]
    simp only [mul_add, Finset.mul_sum, ← mul_assoc, ← map_mul]

end Biform

/-! ## 2. The derivative of a normal form -/

theorem pderiv_X' (i j : Fin d) :
    pderiv i (X j : MvPolynomial (Fin d) ℂ) = if i = j then 1 else 0 := by
  rw [pderiv_X, Pi.single_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

theorem pderiv_C_mul (c : ℂ) (p : MvPolynomial (Fin d) ℂ) (j : Fin d) :
    pderiv j (C c * p) = C c * pderiv j p := by
  rw [Derivation.leibniz]
  simp

theorem pderiv_lin_sum (j : Fin d) (l : Fin d → ℂ) :
    pderiv j (∑ v, C (l v) * X v : MvPolynomial (Fin d) ℂ) = C (l j) := by
  rw [map_sum]
  have h : ∀ v, pderiv j (C (l v) * X v : MvPolynomial (Fin d) ℂ)
      = C (l v) * (if j = v then 1 else 0) := by
    intro v
    rw [pderiv_C_mul, pderiv_X']
  simp only [h]
  rw [Finset.sum_eq_single j]
  · simp
  · intro v _ hv
    rw [if_neg (Ne.symm hv), mul_zero]
  · intro h; simp at h

theorem pderiv_sq_sum (j : Fin d) (q : Fin d → Fin d → ℂ) :
    pderiv j (∑ a, ∑ c, C (q a c) * (X a * X c) : MvPolynomial (Fin d) ℂ)
      = ∑ c, C (q j c) * X c + ∑ a, C (q a j) * X a := by
  rw [map_sum]
  have hterm : ∀ a, pderiv j (∑ c, C (q a c) * (X a * X c) : MvPolynomial (Fin d) ℂ)
      = (∑ c, C (q a c) * ((if j = a then 1 else 0) * X c))
        + ∑ c, C (q a c) * (X a * (if j = c then 1 else 0)) := by
    intro a
    rw [map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [pderiv_C_mul, Derivation.leibniz]
    simp only [pderiv_X', smul_eq_mul, mul_add]
    ring
  simp only [hterm, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro a _ ha
      rw [if_neg (Ne.symm ha), zero_mul, mul_zero]
    · intro h; simp at h
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro c _ hc
      rw [if_neg (Ne.symm hc), mul_zero, mul_zero]
    · intro h; simp at h

/-- **The derivative of a normal form is a linear form.**  For `j` in the quadratic atom set, the
linear part contributes nothing (`j ∉ T` by disjointness) and the bilinear part contributes two
linear terms per atom: the row and the column of `sqf` at `j`. -/
theorem pderiv_eq {A T : Finset (Fin d)} (b : Biform A T) (hdisj : Disjoint A T) {j : Fin d}
    (hj : j ∈ A) :
    pderiv j b.poly = ∑ v, C (b.sqf j v + b.sqf v j) * X v := by
  have hjT : j ∉ T := Finset.disjoint_left.mp hdisj hj
  rw [b.rep]
  simp only [map_add, pderiv_lin_sum, pderiv_sq_sum, b.lin_supp j hjT, pderiv_C, map_zero,
    zero_add, add_zero]
  have h : (∑ v, (C (b.sqf j v) * X v : MvPolynomial (Fin d) ℂ))
      + ∑ v, (C (b.sqf v j) * X v : MvPolynomial (Fin d) ℂ)
      = ∑ v, (C (b.sqf j v) + C (b.sqf v j)) * X v := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by rw [add_mul]
  exact h

/-! ## 3. The pointwise bound -/

/-- The value of `C c * X v` is the real part of `c` times `x v`. -/
theorem polyW_C_mul_X (c : ℂ) (v : Fin d) (x : Vd d) :
    polyW (C c * X v : MvPolynomial (Fin d) ℂ) x = c.re * x v := by
  have h : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (C c * X v : MvPolynomial (Fin d) ℂ)
      = c * ((x v : ℝ) : ℂ) := by
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [polyW, h, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- **`GradBound`'s pointwise shape for a normal form.**  The derivative at `j ∈ A` is a linear
form supported in `A`, so Cauchy–Schwarz bounds its square by its coefficient squares times the
coercive quadratic on `A`; the derivative coordinates, which is what makes the estimate possible,
do not appear. -/
theorem sq_le {A T : Finset (Fin d)} (b : Biform A T) (hdisj : Disjoint A T) {j : Fin d}
    (hj : j ∈ A) (x : Vd d) :
    (polyW (pderiv j b.poly) x) ^ 2
      ≤ (∑ v ∈ A, ((b.sqf j v + b.sqf v j).re) ^ 2) * (1 + ∑ m ∈ A, (x m) ^ 2) := by
  set c : Fin d → ℂ := fun v => b.sqf j v + b.sqf v j with hc
  have hsupp : ∀ v, v ∉ A → c v = 0 := by
    intro v hv
    rw [hc]
    simp [b.sq_supp₁ v j hv, b.sq_supp₂ j v hv]
  have hcollapse : (∑ v, C (c v) * X v : MvPolynomial (Fin d) ℂ) = ∑ v ∈ A, C (c v) * X v := by
    symm
    refine Finset.sum_subset (Finset.subset_univ A) ?_
    intro v _ hv
    rw [hsupp v hv, map_zero, zero_mul]
  have hval : polyW (pderiv j b.poly) x = ∑ v ∈ A, (c v).re * x v := by
    rw [pderiv_eq b hdisj hj, hcollapse, polyW_sum]
    exact Finset.sum_congr rfl fun v _ => polyW_C_mul_X (c v) v x
  rw [hval]
  have hcs : (∑ v ∈ A, (c v).re * x v) ^ 2
      ≤ (∑ v ∈ A, ((c v).re) ^ 2) * ∑ v ∈ A, (x v) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hnn : (0 : ℝ) ≤ ∑ v ∈ A, ((c v).re) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hmono : (∑ v ∈ A, ((c v).re) ^ 2) * ∑ v ∈ A, (x v) ^ 2
      ≤ (∑ v ∈ A, ((c v).re) ^ 2) * (1 + ∑ m ∈ A, (x m) ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ hnn
    have := Finset.sum_nonneg (f := fun m : Fin d => (x m) ^ 2) (s := A) fun i _ => sq_nonneg _
    linarith
  exact hcs.trans hmono

/-! ## 4. The 49 Standard-Model forms as normal forms -/

open BookProof.SmOneParticle BookProof.SmHamiltonian BookProof.SmFarisLavine
open BookProof.YangMillsHermite
open BookProof.SmFullMatter BookProof.SmFullCoupledCore BookProof.FarisLavine
open BookProof.SmFullNormalFormBounds

/-- The *derivative* coordinates: everything except the 40 momentum-carrying coordinates. -/
noncomputable def smT : Finset (Fin 163) := Finset.univ \ BookProof.SmComparisonEsa.smS

theorem disjoint_smS_smT : Disjoint BookProof.SmComparisonEsa.smS smT := Finset.disjoint_sdiff

theorem mem_smT {u : Fin 163} (h : u ∉ BookProof.SmComparisonEsa.smS) : u ∈ smT :=
  Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, h⟩

theorem mem_smS {u : Fin 163} (x : SmMom) (hx : smMomCoord x = u) :
    u ∈ BookProof.SmComparisonEsa.smS := by
  refine Finset.mem_image.mpr ⟨smMomFin x, Finset.mem_univ _, ?_⟩
  simpa [smCoord] using hx

theorem notMem_of_coord {u : Fin 163} (h : ∀ x : SmMom, smMomCoord x ≠ u) :
    u ∉ BookProof.SmComparisonEsa.smS := by
  intro hu
  obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hu
  exact h (smMomFin.symm m) hm

theorem smDG_notMem (a : Fin 8) (k j : Fin 3) : smDG a k j ∉ BookProof.SmComparisonEsa.smS := by
  refine notMem_of_coord fun x => ?_
  rcases x with ⟨a', i'⟩ | ⟨k', i'⟩ | i' | a'
  · intro h; simp only [smMomCoord, smG, smDG] at h; exact absurd (smIdx.injective h) (by simp)
  · intro h; simp only [smMomCoord, smW, smDG] at h; exact absurd (smIdx.injective h) (by simp)
  · intro h; simp only [smMomCoord, smB, smDG] at h; exact absurd (smIdx.injective h) (by simp)
  · intro h; simp only [smMomCoord, smPhi, smDG] at h; exact absurd (smIdx.injective h) (by simp)

theorem smDW_notMem (k i j : Fin 3) : smDW k i j ∉ BookProof.SmComparisonEsa.smS := by
  refine notMem_of_coord fun x => ?_
  rcases x with ⟨a', i'⟩ | ⟨k', i'⟩ | i' | a'
  · intro h; simp only [smMomCoord, smG, smDW] at h; exact absurd (smIdx.injective h) (by simp)
  · intro h; simp only [smMomCoord, smW, smDW] at h; exact absurd (smIdx.injective h) (by simp)
  · intro h; simp only [smMomCoord, smB, smDW] at h; exact absurd (smIdx.injective h) (by simp)
  · intro h; simp only [smMomCoord, smPhi, smDW] at h; exact absurd (smIdx.injective h) (by simp)

theorem smDB_notMem (k j : Fin 3) : smDB k j ∉ BookProof.SmComparisonEsa.smS := by
  refine notMem_of_coord fun x => ?_
  rcases x with ⟨a', i'⟩ | ⟨k', i'⟩ | i' | a'
  · intro h; simp only [smMomCoord, smG, smDB] at h; exact absurd (smIdx.injective h) (by simp)
  · intro h; simp only [smMomCoord, smW, smDB] at h; exact absurd (smIdx.injective h) (by simp)
  · intro h; simp only [smMomCoord, smB, smDB] at h; exact absurd (smIdx.injective h) (by simp)
  · intro h; simp only [smMomCoord, smPhi, smDB] at h; exact absurd (smIdx.injective h) (by simp)

theorem smDPhi_notMem (a : Fin 4) (j : Fin 3) :
    smDPhi a j ∉ BookProof.SmComparisonEsa.smS := by
  refine notMem_of_coord fun x => ?_
  rcases x with ⟨a', i'⟩ | ⟨k', i'⟩ | i' | a'
  · intro h; simp only [smMomCoord, smG, smDPhi] at h; exact absurd (smIdx.injective h) (by simp)
  · intro h; simp only [smMomCoord, smW, smDPhi] at h; exact absurd (smIdx.injective h) (by simp)
  · intro h; simp only [smMomCoord, smB, smDPhi] at h; exact absurd (smIdx.injective h) (by simp)
  · intro h; simp only [smMomCoord, smPhi, smDPhi] at h; exact absurd (smIdx.injective h) (by simp)

/-- The gluon coordinates lie in `smS`. -/
theorem smG_mem (a : Fin 8) (i : Fin 3) : smG a i ∈ BookProof.SmComparisonEsa.smS :=
  mem_smS (Sum.inl (a, i)) rfl

theorem smW_mem (k i : Fin 3) : smW k i ∈ BookProof.SmComparisonEsa.smS :=
  mem_smS (Sum.inr (Sum.inl (k, i))) rfl

theorem smB_mem (i : Fin 3) : smB i ∈ BookProof.SmComparisonEsa.smS :=
  mem_smS (Sum.inr (Sum.inr (Sum.inl i))) rfl

theorem smPhi_mem (a : Fin 4) : smPhi a ∈ BookProof.SmComparisonEsa.smS :=
  mem_smS (Sum.inr (Sum.inr (Sum.inr a))) rfl

/-- **The hypercharge magnetic form is a normal form.** -/
noncomputable def biform_smMagB (i : Fin 3) : Biform BookProof.SmComparisonEsa.smS smT := by
  refine Biform.smul ((1 / 2 : ℝ) : ℂ) ?_
  refine Biform.sum (s := (Finset.univ : Finset (Fin 3))) fun j => ?_
  refine Biform.sum (s := (Finset.univ : Finset (Fin 3))) fun k => ?_
  refine Biform.smul ((levi i j k : ℝ) : ℂ) ?_
  refine Biform.sub ?_ ?_
  · exact Biform.atom _ (mem_smT (smDB_notMem k j))
  · exact Biform.atom _ (mem_smT (smDB_notMem j k))

theorem biform_smMagB_poly (i : Fin 3) :
    (biform_smMagB i).poly = smMagB (id : Fin 163 → Fin 163) i := rfl

set_option maxHeartbeats 1000000 in
-- the nested `Fin 3`/`Fin 8` index sums exceed the default elaboration budget
/-- **The gluon magnetic form is a normal form.** -/
noncomputable def biform_smMagG (P : SmParams) (a : Fin 8) (i : Fin 3) :
    Biform BookProof.SmComparisonEsa.smS smT := by
  refine Biform.smul ((1 / 2 : ℝ) : ℂ) ?_
  refine Biform.sum (s := (Finset.univ : Finset (Fin 3))) fun j => ?_
  refine Biform.sum (s := (Finset.univ : Finset (Fin 3))) fun k => ?_
  refine Biform.smul ((levi i j k : ℝ) : ℂ) ?_
  refine Biform.add ?_ ?_
  · refine Biform.sub ?_ ?_
    · exact Biform.atom _ (mem_smT (smDG_notMem a k j))
    · exact Biform.atom _ (mem_smT (smDG_notMem a j k))
  · refine Biform.smul ((P.gs : ℝ) : ℂ) ?_
    refine Biform.sum (s := (Finset.univ : Finset (Fin 8))) fun b => ?_
    refine Biform.sum (s := (Finset.univ : Finset (Fin 8))) fun d => ?_
    refine Biform.smul ((P.fabc a b d : ℝ) : ℂ) ?_
    exact Biform.atomSq _ _ (smG_mem b j) (smG_mem d k)

set_option maxHeartbeats 1000000 in
-- the definitional unfolding of the nested index sums exceeds the default budget
theorem biform_smMagG_poly (P : SmParams) (a : Fin 8) (i : Fin 3) :
    (biform_smMagG P a i).poly = smMagG P (id : Fin 163 → Fin 163) a i := rfl

set_option maxHeartbeats 1000000 in
-- the nested `Fin 3` index sums exceed the default elaboration budget
/-- **The weak magnetic form is a normal form.** -/
noncomputable def biform_smMagW (P : SmParams) (m : Fin 3) (i : Fin 3) :
    Biform BookProof.SmComparisonEsa.smS smT := by
  refine Biform.smul ((1 / 2 : ℝ) : ℂ) ?_
  refine Biform.sum (s := (Finset.univ : Finset (Fin 3))) fun j => ?_
  refine Biform.sum (s := (Finset.univ : Finset (Fin 3))) fun k => ?_
  refine Biform.smul ((levi i j k : ℝ) : ℂ) ?_
  refine Biform.add ?_ ?_
  · refine Biform.sub ?_ ?_
    · exact Biform.atom _ (mem_smT (smDW_notMem m k j))
    · exact Biform.atom _ (mem_smT (smDW_notMem m j k))
  · refine Biform.smul ((P.gw : ℝ) : ℂ) ?_
    refine Biform.sum (s := (Finset.univ : Finset (Fin 3))) fun b => ?_
    refine Biform.sum (s := (Finset.univ : Finset (Fin 3))) fun d => ?_
    refine Biform.smul ((P.eabc m b d : ℝ) : ℂ) ?_
    exact Biform.atomSq _ _ (smW_mem b j) (smW_mem d k)

set_option maxHeartbeats 1000000 in
-- the definitional unfolding of the nested index sums exceeds the default budget
theorem biform_smMagW_poly (P : SmParams) (m : Fin 3) (i : Fin 3) :
    (biform_smMagW P m i).poly = smMagW P (id : Fin 163 → Fin 163) m i := rfl

set_option maxHeartbeats 1000000 in
-- the nested `Fin 3`/`Fin 4` index sums exceed the default elaboration budget
/-- **The covariant Higgs derivative is a normal form.** -/
noncomputable def biform_smCovD (P : SmParams) (a : Fin 4) (i : Fin 3) :
    Biform BookProof.SmComparisonEsa.smS smT := by
  refine Biform.add ?_ ?_
  · refine Biform.add ?_ ?_
    · exact Biform.atom _ (mem_smT (smDPhi_notMem a i))
    · refine Biform.smul ((P.gw : ℝ) : ℂ) ?_
      refine Biform.sum (s := (Finset.univ : Finset (Fin 3))) fun j => ?_
      refine Biform.sum (s := (Finset.univ : Finset (Fin 4))) fun b => ?_
      refine Biform.smul ((P.tgen j a b : ℝ) : ℂ) ?_
      exact Biform.atomSq _ _ (smW_mem j i) (smPhi_mem b)
  · refine Biform.smul ((P.gy : ℝ) : ℂ) ?_
    refine Biform.sum (s := (Finset.univ : Finset (Fin 4))) fun b => ?_
    refine Biform.smul ((P.ygen a b : ℝ) : ℂ) ?_
    exact Biform.atomSq _ _ (smB_mem i) (smPhi_mem b)

set_option maxHeartbeats 1000000 in
-- the definitional unfolding of the nested index sums exceeds the default budget
theorem biform_smCovD_poly (P : SmParams) (a : Fin 4) (i : Fin 3) :
    (biform_smCovD P a i).poly = smCovD P (id : Fin 163 → Fin 163) a i := rfl

set_option maxHeartbeats 1000000 in
-- the `Fin 4` index sum exceeds the default elaboration budget
/-- **The Higgs wall is a normal form.** -/
noncomputable def biform_smWall (P : SmParams) : Biform BookProof.SmComparisonEsa.smS smT := by
  refine Biform.smul ((Real.sqrt (P.lam / 2) : ℝ) : ℂ) ?_
  refine Biform.sub ?_ ?_
  · refine Biform.sum (s := (Finset.univ : Finset (Fin 4))) fun a => ?_
    exact Biform.atomSq _ _ (smPhi_mem a) (smPhi_mem a)
  · exact Biform.const ((P.vev ^ 2 : ℝ) : ℂ)

set_option maxHeartbeats 1000000 in
-- the definitional unfolding of the index sum exceeds the default budget
theorem biform_smWall_poly (P : SmParams) :
    (biform_smWall P).poly = smWall P (id : Fin 163 → Fin 163) := rfl

/-- **The normal form of a form label.** -/
noncomputable def biform_form (P : SmParams) : SmForm → Biform BookProof.SmComparisonEsa.smS smT
  | Sum.inl (a, i) => biform_smMagG P a i
  | Sum.inr (Sum.inl (k, i)) => biform_smMagW P k i
  | Sum.inr (Sum.inr (Sum.inl i)) => biform_smMagB i
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (a, i)))) => biform_smCovD P a i
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => biform_smWall P

theorem biform_form_poly (P : SmParams) (r : SmForm) :
    (biform_form P r).poly = smFormPoly P (id : Fin 163 → Fin 163) r := by
  rcases r with ⟨a, i⟩ | ⟨k, i⟩ | i | ⟨a, i⟩ | u
  · exact biform_smMagG_poly P a i
  · exact biform_smMagW_poly P k i
  · exact biform_smMagB_poly i
  · exact biform_smCovD_poly P a i
  · exact biform_smWall_poly P

/-- **Every one of the 49 forms is a normal form.** -/
noncomputable def biform_smPhi (P : SmParams) (r : Fin 49) :
    Biform BookProof.SmComparisonEsa.smS smT :=
  biform_form P (smFormFin.symm r)

theorem biform_smPhi_poly (P : SmParams) (r : Fin 49) :
    (biform_smPhi P r).poly = BookProof.SmComparisonEsa.smPhi P r :=
  biform_form_poly P (smFormFin.symm r)

/-- **The per-form gradient bound.**  The constant is the total sum of the squared derivative
coefficients, which is exactly what `Biform.sq_le` produces; no numerical value is needed. -/
theorem gradBound_smPhi (P : SmParams) :
    GradBound (fun r : Fin 49 => BookProof.SmComparisonEsa.smPhi P r)
      BookProof.SmComparisonEsa.smS
      (∑ j ∈ BookProof.SmComparisonEsa.smS, ∑ r : Fin 49,
        ∑ v ∈ BookProof.SmComparisonEsa.smS,
          (((biform_smPhi P r).sqf j v + (biform_smPhi P r).sqf v j).re) ^ 2) := by
  intro j hj r x
  rw [show (fun r : Fin 49 => BookProof.SmComparisonEsa.smPhi P r) r
      = BookProof.SmComparisonEsa.smPhi P r from rfl, ← biform_smPhi_poly P r]
  set S := BookProof.SmComparisonEsa.smS with hS
  set g : Fin 163 → Fin 49 → ℝ := fun j' r' => ∑ v ∈ S,
    (((biform_smPhi P r').sqf j' v + (biform_smPhi P r').sqf v j').re) ^ 2 with hg
  have h1 : g j r ≤ ∑ r' : Fin 49, g j r' :=
    Finset.single_le_sum (f := fun r' => g j r')
      (fun r' _ => Finset.sum_nonneg fun v _ => sq_nonneg _) (Finset.mem_univ r)
  have h2 : (∑ r' : Fin 49, g j r') ≤ ∑ j' ∈ S, ∑ r' : Fin 49, g j' r' :=
    Finset.single_le_sum (f := fun j' => ∑ r' : Fin 49, g j' r')
      (fun j' _ => Finset.sum_nonneg fun r' _ =>
        Finset.sum_nonneg fun v _ => sq_nonneg _) hj
  refine (sq_le (biform_smPhi P r) disjoint_smS_smT hj x).trans ?_
  refine mul_le_mul_of_nonneg_right (h1.trans h2) ?_
  have := Finset.sum_nonneg (f := fun m : Fin 163 => (x m) ^ 2) (s := S) fun i _ => sq_nonneg _
  linarith

set_option maxHeartbeats 1000000 in
-- the `163`-coordinate coefficient sums exceed the default elaboration budget
/-- **`PotSelfBound` for the Standard Model potential, with no hypothesis on the forms.**

This is the closure of the chain `§3b`–`§52` of the plan: the 49 forms are normal forms (§4), a
normal form's derivative at a momentum coordinate is a linear form supported in `smS`
(`Biform.pderiv_eq`, hence `sq_le`), that is `GradBound` (`gradBound_smPhi`), and `GradBound` is
`PotSelfBound` (`exists_potSelfBound_of_gradBound`).  The constant `C` is the total squared
coefficient, never a quoted number. -/
theorem exists_potSelfBound_sm (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0) :
    ∃ β, BookProof.SmKineticGarding.PotSelfBound P c0 β :=
  BookProof.SmGradDomTransfer.exists_potSelfBound_of_gradBound P hc0
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (gradBound_smPhi P)

/-! ## 5. What the discharge unlocks: the elliptic chain, instantiated

`PotSelfBound` is the last input of two theorems that were stated conditionally on it — §19's
`hpoly` (`kineticSum_norm_le_of_pot_self_bound`) and §15's second-order family bound
(`smNormalForm_norm_le_of_pot_self_bound`).  With `exists_potSelfBound_sm` both become theorems with
`0 ≤ c₀` as the only hypothesis on the potential.  The `β` is *produced*: its value is whatever the
constant of `gradBound_smPhi` gives, so the statements say `∃ β` rather than quoting one. -/

/-- **Monotonicity of the self-bound in `β`** — a larger constant is a weaker inequality, which is
what lets the produced `β` be replaced by its absolute value. -/
theorem PotSelfBound_mono {P : SmParams} {c0 β β' : ℝ} (h : β ≤ β')
    (hpot : BookProof.SmKineticGarding.PotSelfBound P c0 β) :
    BookProof.SmKineticGarding.PotSelfBound P c0 β' :=
  fun p => (hpot p).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))

/-- **The self-bound with a non-negative constant.**  The chain produces some `β`; replacing it by
`|β|` costs nothing because the inequality weakens as `β` grows. -/
theorem exists_potSelfBound_sm_nonneg (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0) :
    ∃ β, 0 ≤ β ∧ BookProof.SmKineticGarding.PotSelfBound P c0 β := by
  obtain ⟨β, hβ⟩ := exists_potSelfBound_sm P hc0
  exact ⟨|β|, abs_nonneg β, PotSelfBound_mono (le_abs_self β) hβ⟩

/-- **`hpoly` of §19, instantiated.**  The kinetic sum is bounded by `(1 + β)` times the shifted
comparison — no conditional self-bound, and no separate kinetic-sum estimate. -/
theorem exists_kineticSum_bound_sm (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0) :
    ∃ β, 0 ≤ β ∧ ∀ x : polyGaussCore (d := 163),
      ‖(((∑ m : Fin 40, smPi m (smPi m x)) : polyGaussCore (d := 163)) : L2d 163)‖
        ≤ (1 + β) * ‖smFlN P c0 x + ((x : polyGaussCore (d := 163)) : L2d 163)‖ := by
  obtain ⟨β, hβ, hpot⟩ := exists_potSelfBound_sm_nonneg P hc0
  exact ⟨β, hβ, fun x =>
    BookProof.SmKineticGarding.kineticSum_norm_le_of_pot_self_bound P c0 hβ hpot x⟩

/-- **The P2 second-order family bound, instantiated.**  §15's relative bound for the full normal
form is conditional on the `§15`/`§19` data (`D`'s support).  The potential's self-bound is no longer
among its hypotheses — it is discharged here with `∃ β`.  The four `_`-prefixed hypotheses
(`_hpos`, `_hkin`, `_hcoord`, `_hmass`) are carried by `smNormalForm_norm_le_of_pot_self_bound`'s
signature but not consumed by its proof; they are kept so this theorem is a drop-in replacement. -/
theorem exists_smNormalForm_norm_le (P : SmParams) (D : SmNormalFormData) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (hSmom : ∀ j ∉ Finset.image smMomCoordFin Finset.univ, D.mom j = 0)
    (Skin Scoord : Finset (Fin 163))
    (hSkin : ∀ j ∉ Skin, D.kinetic j = 0) (hScoord : ∀ j ∉ Scoord, D.coord j = 0) :
    ∃ β, 0 ≤ β ∧ ∀ f : SmCoupledCore,
      ∀ (_hpos : ∀ x : polyGaussCore (d := 163), 0 ≤ quadForm (smFlN P c0) x),
      ∀ (_hkin : ∀ j ∈ Skin, ∀ x : polyGaussCore (d := 163),
          ‖((smKinetic j x : polyGaussCore (d := 163)) : L2d 163)‖
            ≤ (1 + β) * ‖smFlN P c0 x + ((x : polyGaussCore (d := 163)) : L2d 163)‖),
      ∀ (_hcoord : ∀ j ∈ Scoord, ∀ x : polyGaussCore (d := 163),
          ‖((smPos j x : polyGaussCore (d := 163)) : L2d 163)‖
            ≤ (1 + β) * ‖smFlN P c0 x + ((x : polyGaussCore (d := 163)) : L2d 163)‖),
      ∀ (_hmass : ∀ x : polyGaussCore (d := 163),
          ‖((x : polyGaussCore (d := 163)) : L2d 163)‖
            ≤ (1 + β) * ‖smFlN P c0 x + ((x : polyGaussCore (d := 163)) : L2d 163)‖),
      ‖smNormalForm D f‖
        ≤ (1 + β) * normalFormConst D
          * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ := by
  obtain ⟨β, hβ, hpot⟩ := exists_potSelfBound_sm_nonneg P hc0
  refine ⟨β, hβ, fun f hpos hkin hcoord hmass => ?_⟩
  exact BookProof.SmKineticGarding.smNormalForm_norm_le_of_pot_self_bound P D c0 hβ hpot
    hpos hSmom Skin Scoord hSkin hScoord hkin hcoord hmass f

/-! ## 6. QYM and NS: the machinery transfers, the domination does not

The normal form is not an SM artefact.  `Biform A T`, `pderiv_eq` and `sq_le` are stated for an
arbitrary dimension, atom set and polynomial, so any form built from the constructors — the
magnetic field strengths, the covariant Higgs derivatives, and equally the QYM Weyl shapes and the NS
convection terms, all of which are "linear in a derivative, bilinear in a field" — is a normal form
with its derivative linear and its square bounded by Cauchy–Schwarz.  What does **not** transfer is
the *conclusion*, and the reason is structural rather than a gap in the proof: `sq_le` bounds
`(∂_j Φ)²` by the coercive quadratic `1 + ∑_{m∈A} x_m²`, and the domination needs a `W` that contains
that quadratic.  The Standard Model's `smPotPoly` carries `∑_m q_m²` (§49); the QYM comparison's
Weyl potential `weylPotPoly Φ = ∑_j Φ_j² + 1` (plan §3, `BookProof/Qym/ChapterYangMillsNonAbelianEsa`)
does not, and neither does an NS potential built from bilinear forms alone.

So for those two models there is no `GradDom` instance to prove — the pointwise domination is
**false**, by the same flat mechanism §48 exhibits.  The proof below is the QYM instance: `weylPotPoly`
at the single bilinear form `X 0 * X 1` is `(X₀X₁)² + 1`, whose gradient grows without bound on
`(t, 1/t)` while the potential stays `2`. -/

/-- The QYM Weyl potential at one bilinear form: `weylPotPoly (fun _ : Fin 1 => X 0 * X 1)`. -/
noncomputable def weylFlat : MvPolynomial (Fin 2) ℂ :=
  (X (0 : Fin 2) * X 1) * (X (0 : Fin 2) * X 1) + (1 : MvPolynomial (Fin 2) ℂ)

/-- `weylFlat` **is** the QYM potential `weylPotPoly` of the Weyl comparison, at the one bilinear form
`X 0 * X 1` — so the obstruction below is about that model's potential, not an analogue of it. -/
theorem weylFlat_eq_weylPotPoly :
    weylFlat = BookProof.YangMillsNonAbelianEsa.weylPotPoly
      (fun _ : Fin 1 => (X (0 : Fin 2) * X 1 : MvPolynomial (Fin 2) ℂ)) := by
  simp [weylFlat, BookProof.YangMillsNonAbelianEsa.weylPotPoly]

theorem weylFlat_eq_flat_add : weylFlat = BookProof.SmReverseEllipticQuartic.flatQuartic + 1 := by
  rw [weylFlat, BookProof.SmReverseEllipticQuartic.flatQuartic]
  ring

theorem evAt_add (x y : ℝ) (p q : MvPolynomial (Fin 2) ℂ) :
    BookProof.SmReverseEllipticQuartic.evAt x y (p + q)
      = BookProof.SmReverseEllipticQuartic.evAt x y p
        + BookProof.SmReverseEllipticQuartic.evAt x y q := by
  simp [BookProof.SmReverseEllipticQuartic.evAt, MvPolynomial.eval_add]

theorem eval_weylFlat_zero (x y : ℝ) :
    BookProof.SmReverseEllipticQuartic.evAt x y (pderiv 0 weylFlat)
      = ((2 * x * y ^ 2 : ℝ) : ℂ) := by
  rw [weylFlat_eq_flat_add, map_add, evAt_add,
    BookProof.SmReverseEllipticQuartic.eval_flat_zero]
  simp [BookProof.SmReverseEllipticQuartic.evAt]

theorem eval_weylFlat_one (x y : ℝ) :
    BookProof.SmReverseEllipticQuartic.evAt x y (pderiv 1 weylFlat)
      = ((2 * x ^ 2 * y : ℝ) : ℂ) := by
  rw [weylFlat_eq_flat_add, map_add, evAt_add,
    BookProof.SmReverseEllipticQuartic.eval_flat_one]
  simp [BookProof.SmReverseEllipticQuartic.evAt]

theorem eval_weylFlat_self (x y : ℝ) :
    BookProof.SmReverseEllipticQuartic.evAt x y weylFlat
      = ((x ^ 2 * y ^ 2 + 1 : ℝ) : ℂ) := by
  rw [weylFlat_eq_flat_add, evAt_add, BookProof.SmReverseEllipticQuartic.eval_flat_self]
  simp [BookProof.SmReverseEllipticQuartic.evAt]

/-- **The QYM/NS obstruction.**  For the Weyl-type potential — `Σ_j Φ_j² + c` with `Φ` bilinear, the
shape QYM's comparison and an NS potential of bilinear forms both have — **no** pair of constants
gives the pointwise gradient domination.  On `(t, 1/t)` the left side is `4/t² + 4t²` while the right
side is the constant `4a + b`.  Hence the SM's route (`GradBound` → `pointwise_dom_of_sq_sum` →
`GradDom`) is not available for those models: the coercive quadratic `∑_m q_m²` is what makes it work,
and they do not carry one. -/
theorem not_gradDom_weylFlat :
    ¬ ∃ a b : ℝ, ∀ x y : ℝ,
      ‖BookProof.SmReverseEllipticQuartic.evAt x y (pderiv 0 weylFlat)‖ ^ 2
          + ‖BookProof.SmReverseEllipticQuartic.evAt x y (pderiv 1 weylFlat)‖ ^ 2
        ≤ a * ‖BookProof.SmReverseEllipticQuartic.evAt x y weylFlat‖ ^ 2 + b := by
  rintro ⟨a, b, h⟩
  set t : ℝ := |a| + |b| + 2 with ht
  have ht1 : 1 ≤ t := by rw [ht]; have := abs_nonneg a; have := abs_nonneg b; linarith
  have ht0 : 0 < t := by linarith
  have hpt := h t (1 / t)
  rw [eval_weylFlat_zero, eval_weylFlat_one, eval_weylFlat_self] at hpt
  have h0 : ‖((2 * t * (1 / t) ^ 2 : ℝ) : ℂ)‖ ^ 2 = 4 / t ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    field_simp
    ring
  have h1 : ‖((2 * t ^ 2 * (1 / t) : ℝ) : ℂ)‖ ^ 2 = 4 * t ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    field_simp
    ring
  have hW : ‖((t ^ 2 * (1 / t) ^ 2 + 1 : ℝ) : ℂ)‖ ^ 2 = 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have htne : t ≠ 0 := by linarith
    field_simp
    ring
  rw [h0, h1, hW] at hpt
  have hpos : 0 ≤ 4 / t ^ 2 := by positivity
  have h1' : 4 * t ^ 2 ≤ 4 * a + b := by linarith
  have h3 : a ≤ |a| := le_abs_self a
  have h4 : b ≤ |b| := le_abs_self b
  have h6 : (0 : ℝ) ≤ |a| := abs_nonneg a
  have h7 : (0 : ℝ) ≤ |b| := abs_nonneg b
  have h2 : 4 * a + b ≤ 4 * t := by
    rw [ht]
    linarith
  have h5 : 4 * t < 4 * t ^ 2 := by
    nlinarith [mul_pos (by linarith : (0:ℝ) < t) (by linarith : (0:ℝ) < t - 1)]
  linarith

end BookProof.SmGradTable
