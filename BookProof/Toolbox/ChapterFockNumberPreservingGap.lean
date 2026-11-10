import Mathlib
import BookProof.Toolbox.ChapterFockOneParticleGap

/-!
# Chapter FockNumberPreservingGap — the `dΓ` lift beyond the diagonal case

/-!
The final Hamiltonian convention is uniform across QYM, QED, QG, and NS:
the one-particle Hamiltonian is enclosed by outer creation on the left and
outer annihilation on the right. Inner pair terms are retained in the
one-particle operator; the outer annihilator, not an inner normal-ordering
rewrite, proves that the outer vacuum is an exact zero-energy eigenstate.
-/!

`CONSOLIDATED_PLAN.md` (top work package, status update 2026-08-28) lists two remaining
inputs.  The per-order finite certificate is discharged in `ChapterRitzCertificate`; this
chapter weakens the second one as far as it honestly can be weakened.

`ChapterFockOneParticleGap` proves the free `dΓ` lift for a one-particle Hamiltonian
`diagCol e` that is **diagonal** in the chosen occupation-number basis.  That is stronger
than the plan's free/number-preserving hypothesis needs: the lift only requires the
one-particle matrix to be *number preserving* (`dΓ` of a one-particle matrix, i.e. built
from `a†_j a_k`), Hermitian, and to have a **one-particle gap**.  Here the gap is expressed
exactly as it is checked numerically, as positive semidefiniteness of the shifted matrix

  `h − μ ≥ 0`   (`IsPosCol (shiftCol col mu)`),

with no diagonalization and no eigenbasis anywhere.

## Deliverables

* `shiftCol` — the shifted one-particle matrix `h − μ`, and `shiftCol_diagCol` /
  `isPosCol_shiftCol_diagCol`, which show the diagonal case of
  `ChapterFockOneParticleGap` is an instance;
* `creVec_sub`, `dGamma_shiftCol` — `dΓ` is linear in the one-particle matrix:
  `dΓ(h − μ) = dΓ(h) − μN`, the general form of `dGamma_diagCol_shift`;
* `creVec_add`, `dGamma_add_col`, `dGamma_smul_col`, **`dGamma_shiftPlus`** — additivity and
  homogeneity in the matrix, and the scalar shift in the additive form `dΓ(h + c·1) = dΓ(h) + cN`;
* **`colMul`, `onePartVec`, `dGamma_comp_one_particle`, `dGamma_comp_defect`** — composition is
  multiplicative on the one-particle sector, `dΓ(M) dΓ(N)|e_k⟩ = dΓ(M·N)|e_k⟩`, and its failure on
  two-particle states is a theorem: `N² ≠ N` there;
* `dGamma_vac` — the vacuum is annihilated by `dΓ(h)` for **every** one-particle matrix;
* `number_quadForm_ge` — `⟪u, N u⟫ ≥ ‖u‖²` on vacuum-orthogonal states;
* **`InSector`, `dGamma_mem_sector`, `numberOp_dGamma_sector`** — `dΓ` maps the `m`-particle
  sector of `Conf` into itself, so the outer Hamiltonian's number conservation is a lemma
  rather than a construction remark: `N (dΓ(h) u) = m · dΓ(h) u` on sector `m`;
* **`sectorPart`, `sum_sectorPart`, `dGamma_numberCol_of_sector`, `numberOp_commute`** —
  every state is a finite sum of sector parts, so the sector statement extends to all of
  `Conf`: `N (dΓ(h) u) = dΓ(h) (N u)` for every `u`, i.e. `dΓ` commutes with the number
  operator with no sector hypothesis;
* **`fock_gap_of_number_preserving`** — the lift: if `h − μ ≥ 0` as a one-particle matrix
  and `μ ≥ 0`, then every vacuum-orthogonal finite-particle state has Fock energy at least
  `μ‖u‖²`;
* **`fock_gap_of_number_preserving_op`** — the same statement on the Fock space, with the
  vacuum energy `0`, in the form the Friedrichs machinery consumes.
* **`NumberPreserving`**, `numberPreserving_id`, `NumberPreserving.comp`,
  `NumberPreserving.sum`, **`numberPreserving_creVec_annA`**, `numberPreserving_dGamma`,
  **`numberPreserving_prod_pairs`**, **`numberPreserving_nestedHamiltonian`** — the *nested*
  reading of the same fact: an outer one-particle mode is a pair `(field label, inner Fock
  state)`, the Hamiltonian is the inner operator enclosed by outer creation on the left and outer
  annihilation on the right, i.e. a sum of **products of pairs** `C†(e_i) A(e_j)` of outer
  operators.  Each member of a pair changes the outer number (`confNumber_up`,
  `confNumber_dn_of_pos`) and only the pair conserves it; with `annA_vac` and
  `eq_smul_vac_of_sector_zero` closing the vacuum sector, products and finite sums of pairs are
  number preserving, so the nested Hamiltonian is.

## Honest boundary

Number preservation is still assumed: everything here is `dΓ` of a one-particle matrix, so
pair creation and other particle-number-changing interactions are **excluded**, exactly as
the plan states.  What is removed is only the diagonal/eigenbasis restriction.  No mass gap
of the physical Yang–Mills Hamiltonian is claimed.

In the nested reading of §3c the *inner* operator is carried as an opaque coefficient (the outer
one-particle mode is the pair `(label, inner state)`, so the inner data lives in the
`creVec`/`annA` mode indices), and the product-of-pairs statement is formalized as products of
number-preserving maps.  No operator structure on the inner Fock space itself is built, and no
claim is made about inner-number conservation coupled to the outer one.

Everything is `sorry`-free and introduces no axioms.
-/

noncomputable section

namespace BookProof.FockNumberPreservingGap

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

/-! ## 1. The shifted one-particle matrix -/

/-- The one-particle matrix `h − μ`, whose positivity is the numerically checked form of
the one-particle gap `h ≥ μ`. -/
def shiftCol (col : ℕ → (ℕ →₀ ℂ)) (mu : ℝ) : ℕ → (ℕ →₀ ℂ) :=
  fun k => col k - ((mu : ℝ) : ℂ) • Finsupp.single k 1

theorem numberCol_eq (k : ℕ) : numberCol k = Finsupp.single k (1 : ℂ) := by
  simp [numberCol, diagCol]

theorem shiftCol_apply (col : ℕ → (ℕ →₀ ℂ)) (mu : ℝ) (k : ℕ) :
    shiftCol col mu k = col k - ((mu : ℝ) : ℂ) • numberCol k := by
  rw [shiftCol, numberCol_eq]

/-- The diagonal one-particle matrix shifts diagonally. -/
theorem shiftCol_diagCol (e : ℕ → ℝ) (mu : ℝ) :
    shiftCol (diagCol e) mu = diagCol fun k => e k - mu := by
  funext k
  refine Finsupp.ext fun j => ?_
  simp only [shiftCol, diagCol, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul]
  split_ifs with h
  · push_cast; ring
  · ring

/-! ## 2. `dΓ` is linear in the one-particle matrix -/

theorem creVec_eq_sum_of_subset (v : ℕ →₀ ℂ) (x : FockAlg) {s : Finset ℕ}
    (h : v.support ⊆ s) : creVec v x = ∑ j ∈ s, v j • creA j x := by
  rw [creVec_apply]
  exact Finset.sum_subset h fun j _ hj => by
    rw [Finsupp.notMem_support_iff.mp hj, zero_smul]

theorem creVec_sub (v w : ℕ →₀ ℂ) (x : FockAlg) :
    creVec (v - w) x = creVec v x - creVec w x := by
  classical
  set s : Finset ℕ := (v - w).support ∪ (v.support ∪ w.support) with hs
  have h1 : (v - w).support ⊆ s := Finset.subset_union_left
  have h2 : v.support ⊆ s := fun j hj =>
    Finset.mem_union_right _ (Finset.mem_union_left _ hj)
  have h3 : w.support ⊆ s := fun j hj =>
    Finset.mem_union_right _ (Finset.mem_union_right _ hj)
  have hterm : ∀ j : ℕ, ((v - w) j) • creA j x = v j • creA j x - w j • creA j x := by
    intro j
    rw [Finsupp.sub_apply, sub_smul]
  rw [creVec_eq_sum_of_subset _ _ h1, creVec_eq_sum_of_subset _ _ h2,
    creVec_eq_sum_of_subset _ _ h3]
  simp only [hterm]
  rw [Finset.sum_sub_distrib]

theorem creVec_smul (c : ℂ) (v : ℕ →₀ ℂ) (x : FockAlg) :
    creVec (c • v) x = c • creVec v x := by
  classical
  have h1 : (c • v).support ⊆ v.support := Finsupp.support_smul
  rw [creVec_eq_sum_of_subset _ _ h1, creVec_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, mul_smul]

/-- **`dΓ` is linear in the one-particle matrix**: `dΓ(h − μ) = dΓ(h) − μ N`.  This is the
general (non-diagonal) form of `FockOneParticleGap.dGamma_diagCol_shift`. -/
theorem dGamma_shiftCol (col : ℕ → (ℕ →₀ ℂ)) (mu : ℝ) (u : FockAlg) :
    dGamma (shiftCol col mu) u
      = dGamma col u - ((mu : ℝ) : ℂ) • dGamma numberCol u := by
  classical
  have hmod : modes u ⊆ modes u := subset_rfl
  have hterm : ∀ k : ℕ, creVec (shiftCol col mu k) (annA k u)
      = creVec (col k) (annA k u) - ((mu : ℝ) : ℂ) • creVec (numberCol k) (annA k u) := by
    intro k
    rw [shiftCol_apply, creVec_sub, creVec_smul]
  rw [dGamma_eq_sum (shiftCol col mu) hmod, dGamma_eq_sum col hmod,
    dGamma_eq_sum numberCol hmod, Finset.smul_sum]
  simp only [hterm]
  rw [Finset.sum_sub_distrib]

/-! ## 2b. The scalar shift in additive form, and where composition stops

`dGamma_shiftCol` is the scalar shift read subtractively.  The additive form below is the one the
operator contract uses: an inner energy shift moves the outer Hamiltonian by `c N` and by nothing
else.  The second half of this section is the *one-particle restriction* of composition and its
failure beyond it: `dΓ` is a representation of the one-particle algebra on `|e_k⟩`, while on a
two-particle state `dΓ(I) ∘ dΓ(I) = N²` differs from `dΓ(I ∘ I) = N`. -/

/-- **`creVec` is additive in its one-particle vector.** -/
theorem creVec_add (v w : ℕ →₀ ℂ) (x : FockAlg) :
    creVec (v + w) x = creVec v x + creVec w x := by
  classical
  have h1 : (v + w).support ⊆ v.support ∪ w.support := by
    intro j hj
    have hj' : (v + w) j ≠ 0 := Finsupp.mem_support_iff.mp hj
    rw [Finsupp.add_apply] at hj'
    by_cases hv : v j = 0
    · refine Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr ?_)
      rwa [hv, zero_add] at hj'
    · exact Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hv)
  rw [creVec_eq_sum_of_subset _ _ h1, creVec_eq_sum_of_subset _ _ Finset.subset_union_left,
    creVec_eq_sum_of_subset _ _ Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [Finsupp.add_apply, add_smul]

@[simp] theorem creVec_zero (x : FockAlg) : creVec (0 : ℕ →₀ ℂ) x = 0 := by
  rw [creVec_apply]
  simp

/-- `creVec` of a finite linear combination of one-particle vectors. -/
theorem creVec_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (v : ι → ℕ →₀ ℂ)
    (x : FockAlg) :
    creVec (∑ j ∈ s, a j • v j) x = ∑ j ∈ s, a j • creVec (v j) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, creVec_add, creVec_smul, ih]

/-- **`dΓ` is additive in the one-particle matrix.** -/
theorem dGamma_add_col (col₁ col₂ : ℕ → (ℕ →₀ ℂ)) :
    dGamma (fun k => col₁ k + col₂ k) = dGamma col₁ + dGamma col₂ := by
  refine LinearMap.ext fun u => ?_
  rw [LinearMap.add_apply,
    dGamma_eq_sum (fun k => col₁ k + col₂ k) (K := modes u) (Finset.Subset.refl _),
    dGamma_eq_sum col₁ (K := modes u) (Finset.Subset.refl _),
    dGamma_eq_sum col₂ (K := modes u) (Finset.Subset.refl _), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => creVec_add (col₁ k) (col₂ k) (annA k u)

/-- **`dΓ` is homogeneous in the one-particle matrix.** -/
theorem dGamma_smul_col (c : ℂ) (col : ℕ → (ℕ →₀ ℂ)) :
    dGamma (fun k => c • col k) = c • dGamma col := by
  refine LinearMap.ext fun u => ?_
  rw [LinearMap.smul_apply,
    dGamma_eq_sum (fun k => c • col k) (K := modes u) (Finset.Subset.refl _),
    dGamma_eq_sum col (K := modes u) (Finset.Subset.refl _), Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => creVec_smul c (col k) (annA k u)

/-- **The scalar shift, additively**: `dΓ(A + c·1) = dΓ(A) + c·N` with `N = dΓ(numberCol)`.  This
is `dGamma_shiftCol` with the sign moved into `c`, and it is the whole of the `+c N_out` identity:
the shift produces no other outer operator. -/
theorem dGamma_shiftPlus (col : ℕ → (ℕ →₀ ℂ)) (c : ℂ) :
    dGamma (fun k => col k + c • numberCol k)
      = dGamma col + c • dGamma numberCol := by
  rw [dGamma_add_col, dGamma_smul_col]


/-! ## 3. The vacuum, and the number operator -/

/-- **The vacuum is annihilated by every number-preserving second quantization.** -/
theorem dGamma_vac (col : ℕ → (ℕ →₀ ℂ)) : dGamma col vac = 0 := by
  simp [vac, dGamma_single]

/-- **The number operator bounds the norm on vacuum-orthogonal states**: `⟪u, N u⟫ ≥ ‖u‖²`,
since every non-vacuum configuration carries at least one quantum. -/
theorem number_quadForm_ge {u : FockAlg} (h0 : u 0 = 0) :
    ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma numberCol u)) : ℂ).re := by
  have h := fock_gap_quadForm (e := fun _ => (1 : ℝ)) (mu := 1) zero_le_one
    (fun _ => le_rfl) h0
  rw [one_mul] at h
  exact h

/-! ## 3b. The sectors of `Conf`: `dΓ` maps the `m`-particle sector into itself

Number preservation has so far been *named* rather than proved: `dΓ` is a sum of `a†_k a_i`,
and the narrative reads off that such a sum cannot change the particle number.  This section
proves it.  A state is in the `m`-particle **sector** when every configuration it excites has
`confNumber = m` (`InSector`); `dΓ` is a finite sum of `creVec ∘ annA` terms (`dGamma_eq_sum`),
annihilation `annA` lowers the number by one and creation `creVec` raises it by one, so every
term of the sum lands back in the sector it started from.  On sector `m` this says that the
number operator `N = dΓ(numberCol)` acts on `dΓ(h)u` as multiplication by `m` — the outer
Hamiltonian is number conserving, as a theorem. -/

/-- **Adding a quantum in a mode raises the particle number by one.** -/
theorem confNumber_up (j : ℕ) (α : Conf) : confNumber (up j α) = confNumber α + 1 := by
  classical
  have hsupp : (up j α).support ⊆ insert j α.support := support_up j α
  have hsum : confNumber (up j α) = ∑ k ∈ insert j α.support, up j α k := by
    rw [confNumber]
    exact Finset.sum_subset hsupp
      (fun k _ hk => by simpa [Finsupp.mem_support_iff] using hk)
  rw [hsum]
  by_cases hj : j ∈ α.support
  · rw [Finset.insert_eq_of_mem hj, ← Finset.sum_erase_add _ _ hj]
    have hrest : ∑ k ∈ α.support.erase j, up j α k = ∑ k ∈ α.support.erase j, α k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      exact up_of_ne α (Finset.ne_of_mem_erase hk)
    rw [hrest, up_self]
    have hsplit : confNumber α = α j + ∑ k ∈ α.support.erase j, α k := by
      rw [confNumber, ← Finset.sum_erase_add _ _ hj]; ring
    omega
  · have hzero : α j = 0 := by
      by_contra h
      exact hj (Finsupp.mem_support_iff.mpr h)
    rw [Finset.sum_insert hj, up_self, hzero]
    rw [confNumber, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun k hk => up_of_ne α (by rintro rfl; exact hj hk)

/-- **Removing a quantum from a nonempty mode lowers the particle number by one.** -/
theorem confNumber_dn_of_pos {j : ℕ} {α : Conf} (h : 1 ≤ α j) :
    confNumber (dn j α) + 1 = confNumber α := by
  classical
  have hj : j ∈ α.support := Finsupp.mem_support_iff.mpr (by omega)
  have hsum : confNumber (dn j α) = ∑ k ∈ α.support, dn j α k := by
    rw [confNumber]
    exact Finset.sum_subset (support_dn j α)
      (fun k _ hk => by simpa [Finsupp.mem_support_iff] using hk)
  rw [hsum, ← Finset.sum_erase_add _ _ hj]
  have hrest : ∑ k ∈ α.support.erase j, dn j α k = ∑ k ∈ α.support.erase j, α k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    exact dn_of_ne α (Finset.ne_of_mem_erase hk)
  rw [hrest, dn_self]
  have hsplit : confNumber α = α j + ∑ k ∈ α.support.erase j, α k := by
    rw [confNumber, ← Finset.sum_erase_add _ _ hj]; ring
  omega

/-- **The `m`-particle sector of the algebraic Fock space**: every configuration that `u`
excites carries exactly `m` quanta. -/
def InSector (m : ℕ) (u : FockAlg) : Prop := ∀ β, u β ≠ 0 → confNumber β = m

theorem inSector_zero (m : ℕ) : InSector m (0 : FockAlg) := fun _ hβ => absurd rfl hβ

theorem InSector.add {m : ℕ} {u v : FockAlg} (hu : InSector m u) (hv : InSector m v) :
    InSector m (u + v) := by
  intro β hβ
  rw [Finsupp.add_apply] at hβ
  by_cases h : u β = 0
  · refine hv β ?_
    rwa [h, zero_add] at hβ
  · exact hu β h

theorem InSector.smul {m : ℕ} (c : ℂ) {u : FockAlg} (hu : InSector m u) :
    InSector m (c • u) := by
  intro β hβ
  rw [Finsupp.smul_apply, smul_eq_mul] at hβ
  refine hu β ?_
  intro h
  rw [h, mul_zero] at hβ
  exact hβ rfl

theorem InSector.sum {ι : Type*} {m : ℕ} {s : Finset ι} {f : ι → FockAlg}
    (h : ∀ i ∈ s, InSector m (f i)) : InSector m (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inSector_zero m
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Annihilation lowers the sector by one.** -/
theorem annA_mem_sector {m : ℕ} (k : ℕ) {u : FockAlg} (hu : InSector m u) :
    InSector (m - 1) (annA k u) := by
  intro β hβ
  rw [annA_apply] at hβ
  have hup : u (up k β) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hβ
    exact hβ rfl
  have hc := hu (up k β) hup
  rw [confNumber_up] at hc
  omega

/-- **Creation raises the sector by one.** -/
theorem creA_mem_sector {m : ℕ} (j : ℕ) {w : FockAlg} (hw : InSector m w) :
    InSector (m + 1) (creA j w) := by
  intro β hβ
  rw [creA_apply] at hβ
  have hcoef : ((Real.sqrt (β j) : ℝ) : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hβ
    exact hβ rfl
  have hsq : Real.sqrt (β j) ≠ 0 := by
    intro h
    exact hcoef (by rw [h]; simp)
  have hpos : 1 ≤ β j := by
    have hne : β j ≠ 0 := by
      intro h
      exact hsq ((Real.sqrt_eq_zero (Nat.cast_nonneg (β j : ℕ))).mpr (by exact_mod_cast h))
    exact Nat.one_le_iff_ne_zero.mpr hne
  have hw' : w (dn j β) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hβ
    exact hβ rfl
  have hc := hw (dn j β) hw'
  have hstep := confNumber_dn_of_pos hpos
  omega

/-- **Creation of a finite one-particle combination raises the sector by one.** -/
theorem creVec_mem_sector {m : ℕ} (v : ℕ →₀ ℂ) {w : FockAlg} (hw : InSector m w) :
    InSector (m + 1) (creVec v w) := by
  rw [creVec_apply]
  exact InSector.sum fun j _ => (creA_mem_sector j hw).smul (v j)

/-- **One term of `dΓ` conserves the sector**: `a†(A e_k) a_k` removes a quantum from the
mode `k` and creates one back, so it maps sector `m` (with `m ≥ 1`) into itself. -/
theorem creVec_annA_mem_sector {m : ℕ} (hm : 1 ≤ m) (k : ℕ) {u : FockAlg}
    (hu : InSector m u) (col : ℕ →₀ ℂ) :
    InSector m (creVec col (annA k u)) := by
  have h := creVec_mem_sector col (annA_mem_sector k hu)
  rwa [Nat.sub_add_cancel hm] at h

/-- **`dΓ` maps the `m`-particle sector into itself.**  The outer Hamiltonian is `dΓ` of a
one-particle matrix, hence number conserving: this is that statement as a lemma, not as a
remark about the construction. -/
theorem dGamma_mem_sector (col : ℕ → (ℕ →₀ ℂ)) {m : ℕ} {u : FockAlg} (hu : InSector m u) :
    InSector m (dGamma col u) := by
  classical
  rcases m with _ | m'
  · -- sector `0`: every excited configuration is the vacuum, which `dΓ` annihilates
    have hsupp : u.support ⊆ {(0 : Conf)} := by
      intro β hβ
      refine Finset.mem_singleton.mpr ?_
      by_contra hne
      have h1 := confNumber_pos hne
      have h0 := hu β (Finsupp.mem_support_iff.mp hβ)
      omega
    obtain ⟨c, hc⟩ := Finsupp.support_subset_singleton'.mp hsupp
    rw [hc, dGamma_single]
    have hzero : ((0 : Conf)).support = ∅ := Finsupp.support_zero
    rw [hzero, Finset.sum_empty, smul_zero]
    exact inSector_zero 0
  · rw [dGamma_eq_sum col (K := modes u) (Finset.Subset.refl _)]
    exact InSector.sum fun k _ =>
      creVec_annA_mem_sector (Nat.succ_le_succ (Nat.zero_le m')) k hu (col k)

/-- **Number conservation on a sector**: on the `m`-particle sector the number operator acts
on the outer Hamiltonian `dΓ(h)` as multiplication by `m`.  This is the operator form of
`dGamma_mem_sector`, and the reason the outer number operator is an admissible Faris–Lavine
comparison operator. -/
theorem numberOp_dGamma_sector (col : ℕ → (ℕ →₀ ℂ)) {m : ℕ} {u : FockAlg}
    (hu : InSector m u) :
    dGamma numberCol (dGamma col u) = ((m : ℕ) : ℂ) • dGamma col u := by
  refine Finsupp.ext fun β => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, numberCol, dGamma_diagCol_apply, confEnergy_one]
  by_cases h : (dGamma col u) β = 0
  · rw [h, mul_zero, mul_zero]
  · rw [dGamma_mem_sector col hu β h]
    push_cast
    ring

/-! ### From sectors to all of `Conf`: `dΓ` commutes with `N`

The sector statement is unconditional on sector vectors, but a general state is not
in a sector.  It is, however, a **finite** sum of sector parts — the support of a
`Finsupp` is finite, so only finitely many values of `confNumber` occur
(`sum_sectorPart`) — and on each part `N` is the scalar `m`
(`dGamma_numberCol_of_sector`).  Summing gives the operator identity
`N (dΓ(h) u) = dΓ(h) (N u)` for every `u : FockAlg`: the outer Hamiltonian
conserves the particle number, with no restriction to a sector and no assumption
on the one-particle matrix beyond it being a number-preserving `dΓ`. -/

/-- **Pointwise evaluation of a finite sum of Fock vectors.** -/
theorem sum_apply_fock (s : Finset ℕ) (f : ℕ → FockAlg) (β : Conf) :
    (∑ m ∈ s, f m) β = ∑ m ∈ s, f m β := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finsupp.add_apply, ih]

/-- **The `m`-sector part of a state**: keep the configurations that carry exactly `m`
quanta. -/
def sectorPart (m : ℕ) (u : FockAlg) : FockAlg := u.filter fun β => confNumber β = m

theorem sectorPart_apply (m : ℕ) (u : FockAlg) (β : Conf) :
    sectorPart m u β = if confNumber β = m then u β else 0 :=
  Finsupp.filter_apply (f := u) (p := fun β => confNumber β = m) β

/-- Each sector part really lies in its sector. -/
theorem sectorPart_mem_sector (m : ℕ) (u : FockAlg) : InSector m (sectorPart m u) := by
  intro β hβ
  by_contra hne
  rw [sectorPart_apply, if_neg hne] at hβ
  exact hβ rfl

/-- **Every state is the finite sum of its sector parts.**  Only the values of `confNumber`
on the (finite) support of `u` occur, so the sum is over a finite set: this is the grading
of the algebraic Fock space, obtained from finiteness alone. -/
theorem sum_sectorPart (u : FockAlg) :
    ∑ m ∈ u.support.image confNumber, sectorPart m u = u := by
  classical
  refine Finsupp.ext fun β => ?_
  rw [sum_apply_fock]
  by_cases hβ : β ∈ u.support
  · refine (Finset.sum_eq_single (confNumber β) ?_ ?_).trans ?_
    · intro m _ hm
      rw [sectorPart_apply, if_neg (Ne.symm hm)]
    · intro hnotin
      exact absurd (Finset.mem_image.mpr ⟨β, hβ, rfl⟩) hnotin
    · rw [sectorPart_apply, if_pos rfl]
  · have hzero : u β = 0 := by simpa [Finsupp.mem_support_iff] using hβ
    rw [hzero]
    refine (Finset.sum_eq_zero fun m _ => ?_).trans rfl
    rw [sectorPart_apply]
    by_cases hm : confNumber β = m
    · rw [if_pos hm, hzero]
    · rw [if_neg hm]

/-- **On a sector the number operator is the scalar `m`**: `N w = m · w`.  This is
`numberOp_dGamma_sector` without the `dΓ` in the middle, and it holds for `m = 0` too
(there the state is a multiple of the vacuum, which `N` kills). -/
theorem dGamma_numberCol_of_sector {m : ℕ} {w : FockAlg} (hw : InSector m w) :
    dGamma numberCol w = ((m : ℕ) : ℂ) • w := by
  refine Finsupp.ext fun β => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, numberCol, dGamma_diagCol_apply, confEnergy_one]
  by_cases h : w β = 0
  · rw [h, mul_zero, mul_zero]
  · rw [hw β h]
    push_cast
    ring

/-- **`dΓ` commutes with the number operator**, on all of `Conf`.  The sector statement
`numberOp_dGamma_sector` is unconditional only on sector vectors; a general state is a
finite sum of sector parts (`sum_sectorPart`), and on each part both sides are the scalar
`m` times `dΓ(h)` of that part.  This is the outer Hamiltonian's number conservation as
an operator identity, with no sector hypothesis. -/
theorem numberOp_commute (col : ℕ → (ℕ →₀ ℂ)) (u : FockAlg) :
    dGamma numberCol (dGamma col u) = dGamma col (dGamma numberCol u) := by
  classical
  set s : Finset ℕ := u.support.image confNumber with hs
  have hsum : ∑ m ∈ s, sectorPart m u = u := sum_sectorPart u
  have hdg : ∑ m ∈ s, dGamma col (sectorPart m u) = dGamma col u := by
    rw [← map_sum, hsum]
  have hNd : ∑ m ∈ s, dGamma numberCol (sectorPart m u) = dGamma numberCol u := by
    rw [← map_sum, hsum]
  calc dGamma numberCol (dGamma col u)
      = dGamma numberCol (∑ m ∈ s, dGamma col (sectorPart m u)) := by rw [hdg]
    _ = ∑ m ∈ s, dGamma numberCol (dGamma col (sectorPart m u)) := by rw [map_sum]
    _ = ∑ m ∈ s, ((m : ℕ) : ℂ) • dGamma col (sectorPart m u) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          exact numberOp_dGamma_sector col (sectorPart_mem_sector m u)
    _ = ∑ m ∈ s, dGamma col (((m : ℕ) : ℂ) • sectorPart m u) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [map_smul]
    _ = ∑ m ∈ s, dGamma col (dGamma numberCol (sectorPart m u)) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [dGamma_numberCol_of_sector (sectorPart_mem_sector m u)]
    _ = dGamma col (∑ m ∈ s, dGamma numberCol (sectorPart m u)) := by rw [map_sum]
    _ = dGamma col (dGamma numberCol u) := by rw [hNd]

/-! ### Composition on the one-particle sector, and where it stops -/

/-- Column `k` of the product of two one-particle matrices: `(M·N)_k = Σ_j (N_k)_j M_j`. -/
def colMul (M N : ℕ → (ℕ →₀ ℂ)) : ℕ → (ℕ →₀ ℂ) :=
  fun k => ∑ j ∈ (N k).support, (N k) j • M j

/-- The one-particle vector of a column, `Σ_j v_j |e_j⟩`, as a linear map. -/
def onePartVec : (ℕ →₀ ℂ) →ₗ[ℂ] FockAlg where
  toFun v := creVec v vac
  map_add' v w := creVec_add v w _
  map_smul' c v := creVec_smul c v _

/-- On the one-particle sector, `dΓ` is the one-particle vector of the column. -/
theorem onePartVec_eq_dGamma (col : ℕ → (ℕ →₀ ℂ)) (k : ℕ) :
    onePartVec (col k) = dGamma col (Finsupp.single (Finsupp.single k 1) (1 : ℂ)) := by
  change creVec (col k) vac = _
  rw [vac, dGamma_one_particle, creVec_apply]
  exact Finset.sum_congr rfl fun j _ => by simp [creA_single]

/-- The columns of a product act on the one-particle sector by the linear combination. -/
theorem onePartVec_colMul (M N : ℕ → (ℕ →₀ ℂ)) (k : ℕ) :
    onePartVec (colMul M N k) = ∑ j ∈ (N k).support, (N k) j • onePartVec (M j) := by
  rw [colMul, map_sum]
  exact Finset.sum_congr rfl fun j _ => map_smul onePartVec _ _

/-- **Composition restricts to the product on the one-particle sector**:
`dΓ(M) dΓ(N) |e_k⟩ = dΓ(M·N) |e_k⟩`. -/
theorem dGamma_comp_one_particle (M N : ℕ → (ℕ →₀ ℂ)) (k : ℕ) :
    dGamma M (dGamma N (Finsupp.single (Finsupp.single k 1) (1 : ℂ)))
      = dGamma (colMul M N) (Finsupp.single (Finsupp.single k 1) (1 : ℂ)) := by
  rw [dGamma_one_particle, map_sum]
  have hterm : ∀ j : ℕ,
      dGamma M ((N k) j • Finsupp.single (Finsupp.single j 1) (1 : ℂ))
        = (N k) j • onePartVec (M j) := by
    intro j
    rw [map_smul, onePartVec_eq_dGamma]
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← onePartVec_colMul,
    ← onePartVec_eq_dGamma]

/-- The identity matrix is a left unit for `colMul`. -/
theorem colMul_numberCol (M : ℕ → (ℕ →₀ ℂ)) : colMul M numberCol = M := by
  funext k
  rw [colMul, numberCol_eq, Finsupp.support_single_ne_zero k one_ne_zero,
    Finset.sum_singleton, Finsupp.single_eq_same, one_smul]

/-- **The composition defect on two-particle states**: `N² ≠ N`, so `dΓ` is not multiplicative
beyond the one-particle sector.  The proof is the sector eigenvalue `N = 2` on two quanta against
`N² = 4`. -/
theorem dGamma_comp_defect (k : ℕ) :
    dGamma numberCol (dGamma numberCol (Finsupp.single (Finsupp.single k 2) (1 : ℂ)))
      ≠ dGamma (colMul numberCol numberCol) (Finsupp.single (Finsupp.single k 2) (1 : ℂ)) := by
  have hw : InSector 2 (Finsupp.single (Finsupp.single k 2) (1 : ℂ)) := by
    intro β hβ
    have hβ' : β = Finsupp.single k 2 := by
      by_contra hne
      exact hβ (by simp [Finsupp.single_apply, hne])
    subst hβ'
    rw [confNumber, Finsupp.support_single_ne_zero k two_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same]
  have hN : dGamma numberCol (Finsupp.single (Finsupp.single k 2) (1 : ℂ))
      = (2 : ℂ) • Finsupp.single (Finsupp.single k 2) (1 : ℂ) :=
    dGamma_numberCol_of_sector hw
  rw [colMul_numberCol, hN, map_smul, hN]
  intro h
  have hc := congrArg (fun z : FockAlg => z (Finsupp.single k 2)) h
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at hc
  norm_num at hc
/-! ## 3c. The nested Fock space: the Hamiltonian is a sum of products of outer pairs

In the nested Fock space the outer one-particle space is itself a Fock space, so an outer
one-particle mode is a pair `(j, c)` — a field/parcel label `j` together with an inner Fock state
`c` — and the
outer creation operator `C†(e_c)` creates exactly one outer particle carrying the inner state `c`
(`ChapterNavierStokesFockSpace`).  The Hamiltonian is the inner one-particle operator **enclosed by
outer creation on the left and outer annihilation on the right**, i.e. a sum of *products of pairs*
`C†(e_i) A(e_j)` of outer operators, with the inner operator absorbed into the coefficient.

The two members of a pair each *change* the outer particle number: creation raises it by one
(`confNumber_up`), annihilation lowers it by one (`confNumber_dn_of_pos`), and only the pair
conserves it.  That is what the lemmas below record, in the form used by the sector argument:
`NumberPreserving` for maps that preserve every `m`-particle sector, the pair
(`numberPreserving_creVec_annA`), closure under composition (`NumberPreserving.comp`) and finite
sums (`NumberPreserving.sum`), and the nested Hamiltonian
(`numberPreserving_nestedHamiltonian`) as a sum of products of such pairs. -/

/-- **A map conserves the outer particle number** when it maps every `m`-particle sector into
itself.  This is the sector-valued form of `N ∘ T = T ∘ N`. -/
def NumberPreserving (T : FockAlg → FockAlg) : Prop :=
  ∀ (m : ℕ) (u : FockAlg), InSector m u → InSector m (T u)

theorem numberPreserving_id : NumberPreserving id := fun _ _ h => h
theorem numberPreserving_zero : NumberPreserving fun _ => (0 : FockAlg) :=
  fun m _ _ => inSector_zero m

/-- Products of number-conserving maps conserve the outer particle number. -/
theorem NumberPreserving.comp {S T : FockAlg → FockAlg}
    (hS : NumberPreserving S) (hT : NumberPreserving T) :
    NumberPreserving (fun u => S (T u)) := fun m u h => hS m _ (hT m u h)

/-- Sums of number-conserving maps conserve the outer particle number. -/
theorem NumberPreserving.sum {ι : Type*} {s : Finset ι} {T : ι → FockAlg → FockAlg}
    (h : ∀ i ∈ s, NumberPreserving (T i)) :
    NumberPreserving fun u => ∑ i ∈ s, T i u := by
  intro m u hu
  exact InSector.sum fun i hi => h i hi m u hu

/-- **The outer vacuum is annihilated by every ordinary annihilation operator.** -/
theorem annA_vac (j : ℕ) : annA j vac = 0 := by
  refine Finsupp.ext fun α => ?_
  have hne : up j α ≠ 0 := by
    intro h
    have h2 : (up j α) j = (0 : Conf) j := congrArg (fun β : Conf => β j) h
    rw [up_self, Finsupp.zero_apply] at h2
    omega
  simp only [annA_apply, Finsupp.zero_apply, vac, Finsupp.single_apply,
    if_neg (Ne.symm hne), mul_zero]

/-- A state in the zero-particle sector is a multiple of the vacuum. -/
theorem eq_smul_vac_of_sector_zero {u : FockAlg} (hu : InSector 0 u) :
    ∃ c : ℂ, u = c • vac := by
  have hsupp : u.support ⊆ {(0 : Conf)} := by
    intro β hβ
    refine Finset.mem_singleton.mpr ?_
    by_contra hne
    have h1 := confNumber_pos hne
    have h0 := hu β (Finsupp.mem_support_iff.mp hβ)
    omega
  obtain ⟨c, hc⟩ := Finsupp.support_subset_singleton'.mp hsupp
  refine ⟨c, ?_⟩
  rw [hc]
  simp [vac]

/-- **One outer creation–annihilation pair conserves the outer particle number.**  Neither factor
does on its own — `annA` lowers the sector, `creA` raises it — but the composition returns to the
sector it started from, which is the sense in which the pair *as a pair* is number preserving. -/
theorem numberPreserving_creVec_annA (v : ℕ →₀ ℂ) (k : ℕ) :
    NumberPreserving fun u => creVec v (annA k u) := by
  intro m u h
  rcases m with _ | m'
  · obtain ⟨c, rfl⟩ := eq_smul_vac_of_sector_zero h
    have hzero : annA k (c • vac) = 0 := by rw [map_smul, annA_vac, smul_zero]
    change InSector 0 (creVec v (annA k (c • vac)))
    rw [hzero, map_zero]
    exact inSector_zero 0
  · exact creVec_annA_mem_sector (Nat.succ_le_succ (Nat.zero_le m')) k h v

/-- **The outer Hamiltonian is `dΓ` of a one-particle matrix**, hence a sum of such pairs, and
conserves the outer particle number. -/
theorem numberPreserving_dGamma (col : ℕ → (ℕ →₀ ℂ)) : NumberPreserving (dGamma col) :=
  fun _ _ h => dGamma_mem_sector col h

/-- **Products of pairs conserve the outer particle number**: a finite sum of products of
number-preserving maps is number preserving.  This is the shape of the nested Hamiltonian, whose
terms are products of outer creation–annihilation pairs. -/
theorem numberPreserving_prod_pairs {ι : Type*} (s : Finset ι)
    (P Q : ι → FockAlg → FockAlg) (hP : ∀ i, NumberPreserving (P i))
    (hQ : ∀ i, NumberPreserving (Q i)) :
    NumberPreserving fun u => ∑ i ∈ s, P i (Q i u) :=
  NumberPreserving.sum fun i _ => (hP i).comp (hQ i)

/-- **The nested Hamiltonian conserves the outer particle number.**  Each term is a product of two
outer creation–annihilation pairs `C†(e_i) A(e_j)`, the coefficient vectors `colA`/`colB` carrying
the inner data; every term preserves the outer sector, so the sum does. -/
theorem numberPreserving_nestedHamiltonian {ι : Type*} (s : Finset ι)
    (colA colB : ι → ℕ →₀ ℂ) (kA kB : ι → ℕ) :
    NumberPreserving fun u =>
      ∑ i ∈ s, creVec (colA i) (annA (kA i) (creVec (colB i) (annA (kB i) u))) :=
  numberPreserving_prod_pairs s
    (fun i w => creVec (colA i) (annA (kA i) w))
    (fun i w => creVec (colB i) (annA (kB i) w))
    (fun i => numberPreserving_creVec_annA (colA i) (kA i))
    (fun i => numberPreserving_creVec_annA (colB i) (kB i))

/-! ## 3d. The operator structure on the inner Fock space

§3c closed the outer sector argument while treating the inner Fock space as *opaque*: the inner
data travelled as coefficients of `creVec` (a vector `ℕ →₀ ℂ`) and as mode labels of `annA`, so the
inner operator could only ever appear as the identity `creVec (colB i) (annA (kB i) ·)`.  Here the
inner Fock space gets its own operator algebra, and the pair is allowed to carry a general element
of it.

* **`InnerOp`** — the inner operator algebra: endomorphisms of `FockAlg` with multiplication given
  by composition (definitionally `Module.End ℂ FockAlg`, a ring).  The inner creation and
  annihilation operators `innerCre j`, `innerAnn j` and the inner number operator `innerNumber`
  are elements of it.
* **`InnerNumberPreserving`** — the inner analogue of `NumberPreserving`, and the algebra of such
  operators: closed under `0`, `1`, `+` and `*` (`InnerNumberPreserving.add`, `.mul`), containing
  the inner pairs `innerNumberPreserving_pair` and the inner Hamiltonian
  `innerNumberPreserving_dGamma`.
* **`sandwich v A = C†(v) A`** and the nested pair **`nestedPair v A k = C†(v) A a_k`**, with the
  multiplication law **`sandwich_mul`**: `sandwich v (A * B) = sandwich v A * B` — *products of
  pairs compose their inner operators*, which is the sense in which the inner algebra is a genuine
  algebra and not a coefficient ring.
* **`numberPreserving_nestedPair`** — an outer pair dressed by an inner operator conserves the
  outer number *whenever the inner operator conserves the inner number*, for an arbitrary
  `A : InnerOp`; with it the nested Hamiltonian `numberPreserving_nestedHamiltonian_op`.
* **`nestedHamiltonian_op_coeff`** — the opaque-coefficient Hamiltonian of §3c *is* this structure
  at `A i = creVec (colB i) * annA (kB i)`, so nothing of §3c is lost in the generalisation. -/

/-- **The operator algebra of the inner Fock space**: endomorphisms of `FockAlg = Conf →₀ ℂ`,
with multiplication given by composition.  Definitionally `Module.End ℂ FockAlg`, which is where the
ring structure (and hence the product of pairs) comes from. -/
abbrev InnerOp : Type := FockAlg →ₗ[ℂ] FockAlg

/-- The inner creation operator, as an element of the inner operator algebra. -/
def innerCre (j : ℕ) : InnerOp := creA j

/-- The inner annihilation operator, as an element of the inner operator algebra. -/
def innerAnn (j : ℕ) : InnerOp := annA j

/-- The inner number operator `Σ_k a†_k a_k`, as an element of the inner operator algebra. -/
def innerNumber : InnerOp := dGamma numberCol

/-- **An inner operator conserves the inner particle number** when it maps every inner sector into
itself — the inner counterpart of `NumberPreserving`. -/
def InnerNumberPreserving (A : InnerOp) : Prop := NumberPreserving fun u => A u

theorem innerNumberPreserving_zero : InnerNumberPreserving 0 := fun m _ _ => inSector_zero m

theorem innerNumberPreserving_one : InnerNumberPreserving (1 : InnerOp) := fun _ _ h => h

/-- Sums of inner number-conserving operators conserve the inner number. -/
theorem InnerNumberPreserving.add {A B : InnerOp} (hA : InnerNumberPreserving A)
    (hB : InnerNumberPreserving B) : InnerNumberPreserving (A + B) := by
  intro m u hu
  exact InSector.add (hA m u hu) (hB m u hu)

/-- **Products of inner number-conserving operators conserve the inner number**: this is where
composition — the multiplication of the inner algebra — enters. -/
theorem InnerNumberPreserving.mul {A B : InnerOp} (hA : InnerNumberPreserving A)
    (hB : InnerNumberPreserving B) : InnerNumberPreserving (A * B) := by
  intro m u hu
  exact hA m _ (hB m u hu)

/-- **An inner creation–annihilation pair conserves the inner number**, as an element of the inner
algebra: `(a†_k a_j)`. -/
theorem innerNumberPreserving_pair (v : ℕ →₀ ℂ) (k : ℕ) :
    InnerNumberPreserving (creVec v * annA k) := by
  intro m u hu
  exact numberPreserving_creVec_annA v k m u hu

/-- The inner Hamiltonian (`dΓ` of an inner one-particle matrix) conserves the inner number. -/
theorem innerNumberPreserving_dGamma (col : ℕ → (ℕ →₀ ℂ)) :
    InnerNumberPreserving (dGamma col) := fun _ _ h => dGamma_mem_sector col h

/-- The inner number operator conserves the inner number. -/
theorem innerNumberPreserving_number : InnerNumberPreserving innerNumber :=
  innerNumberPreserving_dGamma numberCol

/-- **The outer creation operator dressed by an inner operator**: `C†(v) A`.  In the algebra of
endomorphisms this is the product `creVec v * A`. -/
def sandwich (v : ℕ →₀ ℂ) (A : InnerOp) : InnerOp := creVec v * A

/-- **Composing pairs composes their inner operators**: `C†(v) (A * B) = (C†(v) A) * B`.  This is
associativity in the inner algebra read through the outer creation — the multiplication law of the
nested Fock algebra. -/
theorem sandwich_mul (v : ℕ →₀ ℂ) (A B : InnerOp) :
    sandwich v (A * B) = sandwich v A * B := by
  simp only [sandwich, mul_assoc]

/-- **A nested pair**: outer annihilation in the mode `k`, then the inner operator `A`, then the
outer creation `C†(v)` — the shape `C†(v) a_k A` in which the inner operator sits between the two
outer operators. -/
def nestedPair (v : ℕ →₀ ℂ) (A : InnerOp) (k : ℕ) : InnerOp := sandwich v (annA k * A)

/-- **A pair carrying the composed inner operator is the pair composed with the extra inner
operator**: `C†(v) a_k (A * B) = (C†(v) a_k A) * B`. -/
theorem nestedPair_mul (v : ℕ →₀ ℂ) (A B : InnerOp) (k : ℕ) :
    nestedPair v (A * B) k = nestedPair v A k * B := by
  simp only [nestedPair, sandwich, mul_assoc]

/-- A nested pair acts as `u ↦ C†(v) (a_k (A u))`. -/
theorem nestedPair_apply (v : ℕ →₀ ℂ) (A : InnerOp) (k : ℕ) (u : FockAlg) :
    nestedPair v A k u = creVec v (annA k (A u)) := by
  simp only [nestedPair, sandwich, Module.End.mul_apply]

/-- **An outer pair dressed by an inner number-conserving operator conserves the outer particle
number.**  The inner operator is arbitrary apart from conserving the inner number: the outer sector
argument never looks inside it. -/
theorem numberPreserving_nestedPair {v : ℕ →₀ ℂ} {A : InnerOp} {k : ℕ}
    (hA : InnerNumberPreserving A) :
    NumberPreserving fun u => nestedPair v A k u := by
  intro m u hu
  change InSector m (creVec v (annA k (A u)))
  rcases m with _ | m'
  · obtain ⟨c, rfl⟩ := eq_smul_vac_of_sector_zero hu
    have hA0 : InSector 0 (A (c • vac)) := hA 0 _ hu
    obtain ⟨c', hc'⟩ := eq_smul_vac_of_sector_zero hA0
    rw [hc', map_smul, annA_vac, smul_zero, map_zero]
    exact inSector_zero 0
  · have h1 : InSector m' (annA k (A u)) := by
      have := annA_mem_sector k (hA (m' + 1) u hu)
      rwa [Nat.succ_sub_one] at this
    exact creVec_mem_sector v h1

/-- **The nested Hamiltonian with operator coefficients conserves the outer particle number.**
Each term is a nested pair `C†(colA i) (A i) a_(kA i)`; the inner operators `A i` enter only
through `InnerNumberPreserving`. -/
theorem numberPreserving_nestedHamiltonian_op {ι : Type*} (s : Finset ι)
    (colA : ι → ℕ →₀ ℂ) (A : ι → InnerOp) (hA : ∀ i, InnerNumberPreserving (A i))
    (kA : ι → ℕ) :
    NumberPreserving fun u => ∑ i ∈ s, nestedPair (colA i) (A i) (kA i) u :=
  NumberPreserving.sum fun i _ => numberPreserving_nestedPair (hA i)

/-- **The opaque-coefficient Hamiltonian of §3c is the operator-coefficient one** at
`A i = creVec (colB i) * annA (kB i)`: the inner data that §3c carried as coefficients is an
element of the inner algebra. -/
theorem nestedHamiltonian_op_coeff {ι : Type*} (s : Finset ι) (colA colB : ι → ℕ →₀ ℂ)
    (kA kB : ι → ℕ) :
    (fun u => ∑ i ∈ s, creVec (colA i) (annA (kA i) (creVec (colB i) (annA (kB i) u))))
      = fun u => ∑ i ∈ s,
          nestedPair (colA i) (creVec (colB i) * annA (kB i)) (kA i) u := by
  funext u
  refine Finset.sum_congr rfl fun i _ => ?_
  change creVec (colA i) (annA (kA i) (creVec (colB i) (annA (kB i) u)))
      = creVec (colA i) (annA (kA i) ((creVec (colB i) * annA (kB i)) u))
  rw [Module.End.mul_apply]

/-- **§3c's nested Hamiltonian, re-derived through the inner operator algebra**: number
conservation follows from inner number preservation of the pair `creVec * annA`, not from the
coefficient shape. -/
theorem numberPreserving_nestedHamiltonian_op_coeff {ι : Type*} (s : Finset ι)
    (colA colB : ι → ℕ →₀ ℂ) (kA kB : ι → ℕ) :
    NumberPreserving fun u =>
      ∑ i ∈ s, creVec (colA i) (annA (kA i) (creVec (colB i) (annA (kB i) u))) := by
  rw [nestedHamiltonian_op_coeff]
  exact numberPreserving_nestedHamiltonian_op s colA _
    (fun i => innerNumberPreserving_pair (colB i) (kB i)) kA

/-! ## 4. The lift -/

/-- **The `dΓ` lift for an arbitrary number-preserving one-particle Hamiltonian.**  If the
one-particle matrix satisfies the gap condition `h − μ ≥ 0` (positive semidefinite on every
finite set of modes) with `μ ≥ 0`, then every vacuum-orthogonal finite-particle state has
Fock energy at least `μ‖u‖²`.

No diagonalization, no eigenbasis and no boundedness are used; only number preservation,
which is built into `dΓ`. -/
theorem fock_gap_of_number_preserving {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 ≤ mu)
    (hgap : IsPosCol (shiftCol col mu)) {u : FockAlg} (h0 : u 0 = 0) :
    mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re := by
  have hsplit : (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ)
      = inner ℂ (toLp u) (toLp (dGamma (shiftCol col mu) u))
        + ((mu : ℝ) : ℂ) * inner ℂ (toLp u) (toLp (dGamma numberCol u)) := by
    have hcol : dGamma col u
        = dGamma (shiftCol col mu) u + ((mu : ℝ) : ℂ) • dGamma numberCol u := by
      rw [dGamma_shiftCol, sub_add_cancel]
    have hadd : ∀ a b : FockAlg, toLp (a + b) = toLp a + toLp b := fun a b =>
      map_add toLpL a b
    have hsmul : ∀ (c : ℂ) (a : FockAlg), toLp (c • a) = c • toLp a := fun c a =>
      map_smul toLpL c a
    rw [hcol, hadd, hsmul, inner_add_right, inner_smul_right]
  rw [hsplit, Complex.add_re, Complex.re_ofReal_mul]
  have h1 : 0 ≤ (inner ℂ (toLp u) (toLp (dGamma (shiftCol col mu) u)) : ℂ).re :=
    inner_dGamma_nonneg hgap u
  have h2 := mul_le_mul_of_nonneg_left (number_quadForm_ge h0) hmu
  linarith

/-- **The lift on the Fock space.**  With the one-particle gap `h − μ ≥ 0`, `μ ≥ 0`: the
vacuum has energy `0`, and every vacuum-orthogonal finite-occupation state has energy at
least `μ‖x‖²` — the hypotheses the Friedrichs machinery of
`ChapterFockSecondQuantization` consumes. -/
theorem fock_gap_of_number_preserving_op {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 ≤ mu)
    (hgap : IsPosCol (shiftCol col mu)) :
    dGammaOp col (fockEquiv vac) = 0 ∧
      ∀ x : lpFiniteModes Conf, (inner ℂ (toLp vac) ((x : Fock)) : ℂ) = 0 →
        mu * ‖(x : Fock)‖ ^ 2 ≤ quadForm (dGammaOp col) x := by
  constructor
  · rw [coe_dGammaOp, LinearEquiv.symm_apply_apply, dGamma_vac]
    exact map_zero toLpL
  · intro x hx
    rw [quadForm, coe_dGammaOp, coe_fockEquiv_symm x]
    rw [coe_fockEquiv_symm x] at hx
    exact fock_gap_of_number_preserving hmu hgap (by rwa [inner_vac] at hx)

/-! ## 5. The diagonal case is an instance -/

/-- A diagonal one-particle matrix with all energies at least `μ` satisfies the gap
condition, so `ChapterFockOneParticleGap.fock_gap_quadForm` is the diagonal instance of
`fock_gap_of_number_preserving`. -/
theorem isPosCol_shiftCol_diagCol {e : ℕ → ℝ} {mu : ℝ} (he : ∀ k, mu ≤ e k) :
    IsPosCol (shiftCol (diagCol e) mu) := by
  classical
  intro S c
  rw [shiftCol_diagCol]
  have hcol : ∀ j k : ℕ, (diagCol (fun k => e k - mu) k) j
      = if j = k then (((e k - mu : ℝ)) : ℂ) else 0 := by
    intro j k
    rw [diagCol, Finsupp.single_apply]
    by_cases h : j = k
    · subst h; simp
    · rw [if_neg h, if_neg (fun hkj : k = j => h hkj.symm)]
  have hsum : (∑ j ∈ S, ∑ k ∈ S,
      (starRingEnd ℂ) (c j) * (diagCol (fun k => e k - mu) k) j * c k)
      = ∑ j ∈ S, (((e j - mu : ℝ)) : ℂ) * ((starRingEnd ℂ) (c j) * c j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.sum_eq_single j]
    · rw [hcol j j, if_pos rfl]; ring
    · intro k _ hkj
      rw [hcol j k, if_neg (fun h : j = k => hkj (h ▸ rfl))]
      ring
    · intro hj'; exact absurd hj hj'
  rw [hsum, Complex.re_sum]
  refine Finset.sum_nonneg fun j _ => ?_
  rw [Complex.re_ofReal_mul, conj_mul_re]
  exact mul_nonneg (by linarith [he j]) (sq_nonneg _)

/-! ## 6. From a one-particle *form* gap to the Fock gap

The certificate chain (`ChapterRitzCertificate`, `ChapterBandEnclosure`) delivers a bound of
exactly the shape `⟪x, h x⟫ ≥ μ‖x‖²` on the finite-mode core.  This section consumes it
directly: no eigenbasis, no diagonalization, no boundedness. -/

section FormGap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

open BookProof.HermiteGalerkin

/-- The matrix of the identity in an orthonormal basis is the identity matrix. -/
theorem opCol_id (b : HilbertBasis ℕ ℂ F) (k j : ℕ) :
    opCol b (LinearMap.id) k j = if j = k then (1 : ℂ) else 0 := by
  rw [opCol_apply]
  simpa using orthonormal_iff_ite.mp b.orthonormal j k

/-- Shifting the one-particle operator by `μ` shifts its matrix by `μ` times the identity
matrix. -/
theorem shiftCol_opCol (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b) (mu : ℝ) :
    shiftCol (opCol b A) mu = opCol b (A - ((mu : ℝ) : ℂ) • LinearMap.id) := by
  funext k
  refine Finsupp.ext fun j => ?_
  have hid : opCol b (((mu : ℝ) : ℂ) • LinearMap.id) k j
      = ((mu : ℝ) : ℂ) * (if j = k then (1 : ℂ) else 0) := by
    rw [opCol_apply]
    simp only [LinearMap.smul_apply, Submodule.coe_smul, inner_smul_right, LinearMap.id_apply]
    simpa using congrArg (fun z : ℂ => ((mu : ℝ) : ℂ) * z)
      (orthonormal_iff_ite.mp b.orthonormal j k)
  have hsub : opCol b (A - ((mu : ℝ) : ℂ) • LinearMap.id) k j
      = opCol b A k j - opCol b (((mu : ℝ) : ℂ) • LinearMap.id) k j := by
    rw [opCol_apply, opCol_apply, opCol_apply]
    simp only [LinearMap.sub_apply, Submodule.coe_sub, inner_sub_right]
  rw [hsub, hid, shiftCol]
  simp [Finsupp.single_apply, eq_comm]

/-- **From a one-particle form gap to the Fock gap.**  If the one-particle Hamiltonian on
the finite-mode core satisfies `⟪x, h x⟫ ≥ μ‖x‖²` with `μ ≥ 0`, then its second
quantization has vacuum energy `0` and Fock energy at least `μ‖u‖²` on every
vacuum-orthogonal finite-particle state.  This is the shape of bound the certificate chain
produces, consumed without any diagonalization. -/
theorem fock_gap_of_one_particle_form_gap (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b) {mu : ℝ} (hmu : 0 ≤ mu)
    (hgap : ∀ x : finiteModeDomain b,
      mu * ‖(x : F)‖ ^ 2 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x) :
    dGamma (opCol b A) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b A) u)) : ℂ).re := by
  have hpos : ∀ x : finiteModeDomain b,
      0 ≤ quadForm ((finiteModeDomain b).subtype.comp
        (A - ((mu : ℝ) : ℂ) • LinearMap.id)) x := by
    intro x
    have hval : quadForm ((finiteModeDomain b).subtype.comp
        (A - ((mu : ℝ) : ℂ) • LinearMap.id)) x
        = quadForm ((finiteModeDomain b).subtype.comp A) x - mu * ‖(x : F)‖ ^ 2 := by
      simp only [quadForm, LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_sub,
        Submodule.coe_smul, inner_sub_right, inner_smul_right, Complex.sub_re,
        Complex.re_ofReal_mul, inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [hval]
    linarith [hgap x]
  have hgapCol : IsPosCol (shiftCol (opCol b A) mu) := by
    rw [shiftCol_opCol]
    exact isPosCol_opCol hpos
  exact ⟨dGamma_vac _, fun u h0 => fock_gap_of_number_preserving hmu hgapCol h0⟩

end FormGap

end BookProof.FockNumberPreservingGap

end
