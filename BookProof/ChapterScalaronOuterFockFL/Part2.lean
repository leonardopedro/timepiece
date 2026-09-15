import Mathlib
import BookProof.ChapterScalaronFiberFL
import BookProof.ChapterDirectSumEsa
import BookProof.ChapterScalaronOuterFockFL.Part1

/-!
# The scalaron–vielbein quantum-gravity Hamiltonian on the outer Fock space

This module assembles the Faris–Lavine proof of essential self-adjointness of the full
quantum-gravity Hamiltonian in the representation the *scalaron* forces on us: the vielbein
sector in the occupation-number (mode) representation, the scalaron in position
representation carrying the **full exponential** Einstein-frame potential, with no Taylor
expansion and no relative-boundedness hypothesis on the wall.

The Hilbert space is the outer Fock space of the vielbein modes with values in the scalaron
line,

`𝓕 = ℓ²(ι ; L²(ℝ_φ))`,

`ι` the set of occupation-number configurations of the vielbein modes.  The comparison
operator is the `ℓ²`-lift of the Friedrichs extension of the positive one-particle operator

`N_a = −d²/dφ² + φ²/4 + V(φ) + σ_a`

on the fibre `a`, `σ_a ≥ 1` the vielbein energy of the configuration.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.ScalaronOuterFockFL

open MeasureTheory SchwartzMap
open BookProof.FarisLavine BookProof.ScalaronEsa
open BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.DirectSumEsa BookProof.ScalaronFiberFL
open BookProof.WallEsaSemibounded

noncomputable section

variable {ι : Type*}
variable (W : WallPot) (Q : QgModeData ι)
/-! ## 2. The mode operators -/

/-- The fibre of a core vector, as an element of the compactly supported smooth core. -/
def fibOf (x : secCore (ι := ι)) (a : ι) : ccDomain ℝ := ⟨(x : Sec ι) a, x.2.2 a⟩

@[simp] theorem fibOf_coe (x : secCore (ι := ι)) (a : ι) :
    ((fibOf x a : ccDomain ℝ) : L2R) = (x : Sec ι) a := rfl

theorem fibOf_eq_zero {x : secCore (ι := ι)} {a : ι} (h : (x : Sec ι) a = 0) :
    fibOf x a = 0 := Subtype.ext h

theorem fibOf_add (x y : secCore (ι := ι)) (a : ι) :
    fibOf (x + y) a = fibOf x a + fibOf y a := by
  refine Subtype.ext ?_
  change ((x : Sec ι) + (y : Sec ι)) a = ((fibOf x a : L2R) + (fibOf y a : L2R))
  rw [lp.coeFn_add]
  rfl

theorem fibOf_smul (c : ℂ) (x : secCore (ι := ι)) (a : ι) :
    fibOf (c • x) a = c • fibOf x a := by
  refine Subtype.ext ?_
  change (c • (x : Sec ι)) a = c • ((fibOf x a : L2R))
  rw [lp.coeFn_smul]
  rfl

/-- **A mode operator**: a banded mode matrix `M` acting on the vielbein modes, combined
with a fibre operator `Φ` acting on the scalaron line. -/
def modeOp (Φ : ccDomain ℝ →ₗ[ℂ] L2R) (M : ι → ι → ℂ) : secCore (ι := ι) →ₗ[ℂ] Sec ι where
  toFun x := ⟨fun a => ∑ b ∈ Q.nbr a, M a b • Φ (fibOf x b), by
    refine memLp_of_finite_support (Set.Finite.subset
      (Set.Finite.biUnion x.2.1 (fun b _ => (Q.nbr b).finite_toSet)) ?_)
    intro a ha
    simp only [Set.mem_setOf_eq] at ha
    by_contra hcon
    refine ha (Finset.sum_eq_zero fun b hb => ?_)
    have hb' : a ∈ Q.nbr b := (Q.mem_nbr_comm a b).mp hb
    have hxb : (x : Sec ι) b = 0 := by
      by_contra hne
      exact hcon (Set.mem_biUnion hne hb')
    rw [fibOf_eq_zero hxb, map_zero, smul_zero]⟩
  map_add' x y := by
    refine lp.ext (funext fun a => ?_)
    simp only [lp.coeFn_add, Pi.add_apply]
    change (∑ b ∈ Q.nbr a, M a b • Φ (fibOf (x + y) b))
      = (∑ b ∈ Q.nbr a, M a b • Φ (fibOf x b)) + ∑ b ∈ Q.nbr a, M a b • Φ (fibOf y b)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by rw [fibOf_add, map_add, smul_add]
  map_smul' c x := by
    refine lp.ext (funext fun a => ?_)
    simp only [RingHom.id_apply, lp.coeFn_smul, Pi.smul_apply]
    change (∑ b ∈ Q.nbr a, M a b • Φ (fibOf (c • x) b))
      = c • ∑ b ∈ Q.nbr a, M a b • Φ (fibOf x b)
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => by
      rw [fibOf_smul, map_smul, smul_comm]

@[simp] theorem modeOp_apply (Φ : ccDomain ℝ →ₗ[ℂ] L2R) (M : ι → ι → ℂ)
    (x : secCore (ι := ι)) (a : ι) :
    (modeOp Q Φ M x : Sec ι) a = ∑ b ∈ Q.nbr a, M a b • Φ (fibOf x b) := rfl

/-- The vielbein self-interaction term: all quadratic mode couplings of the gauge-fixed
gravity Hamiltonian, acting as a scalar on the scalaron fibre. -/
def secA : secCore (ι := ι) →ₗ[ℂ] Sec ι := modeOp Q ((ccDomain ℝ).subtype) Q.A

/-- The scalaron–vielbein coupling term: the mode matrix `B` acting together with
multiplication by the scalaron field `φ`. -/
def secB : secCore (ι := ι) →ₗ[ℂ] Sec ι := modeOp Q xCc Q.B

/-- **The full gauge-fixed quantum-gravity Hamiltonian on the outer Fock space**: the
fibrewise scalaron Hamiltonian with the full exponential wall, the vielbein
self-interaction and the scalaron–vielbein coupling. -/
def secHam : secCore (ι := ι) →ₗ[ℂ] Sec ι := secDiag W Q + secA Q + secB Q

@[simp] theorem secDiag_apply (x : secCore (ι := ι)) (a : ι) :
    (secDiag W Q x : Sec ι) a = W.ham (Q.sig a) (fibOf x a) := rfl

theorem secHam_apply (x : secCore (ι := ι)) (a : ι) :
    (secHam W Q x : Sec ι) a = W.ham (Q.sig a) (fibOf x a)
      + (∑ b ∈ Q.nbr a, Q.A a b • ((fibOf x b : ccDomain ℝ) : L2R))
      + ∑ b ∈ Q.nbr a, Q.B a b • xCc (fibOf x b) := by
  change ((secDiag W Q x + secA Q x + secB Q x : Sec ι)) a = _
  rw [lp.coeFn_add, lp.coeFn_add]
  rfl

/-! ### Finite bands -/

/-- Every core vector has a finite band: a finite set outside of which the vector and all
its neighbours vanish. -/
theorem exists_band (x : secCore (ι := ι)) :
    ∃ P : Finset ι, (∀ a, a ∉ P → (x : Sec ι) a = 0) ∧
      (∀ a, a ∉ P → ∀ b ∈ Q.nbr a, (x : Sec ι) b = 0) := by
  classical
  refine ⟨x.2.1.toFinset ∪ x.2.1.toFinset.biUnion Q.nbr, ?_, ?_⟩
  · intro a ha
    by_contra hne
    exact ha (Finset.mem_union_left _ (Set.Finite.mem_toFinset _ |>.mpr hne))
  · intro a ha b hb
    by_contra hne
    refine ha (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, ?_, ?_⟩))
    · exact (Set.Finite.mem_toFinset _).mpr hne
    · exact (Q.mem_nbr_comm a b).mp hb

/-- A sum over the band and a sum over a finite set agree as soon as the summand vanishes
outside each of them. -/
theorem sum_band_eq_sum {M : Type*} [AddCommMonoid M] (N P : Finset ι) (g : ι → M)
    (h1 : ∀ b, b ∉ N → g b = 0) (h2 : ∀ b, b ∉ P → g b = 0) :
    ∑ b ∈ N, g b = ∑ b ∈ P, g b := by
  classical
  have hN : ∑ b ∈ N ∩ P, g b = ∑ b ∈ N, g b :=
    Finset.sum_subset Finset.inter_subset_left fun b hb hnb =>
      h2 b fun hbP => hnb (Finset.mem_inter.mpr ⟨hb, hbP⟩)
  have hP : ∑ b ∈ N ∩ P, g b = ∑ b ∈ P, g b :=
    Finset.sum_subset Finset.inter_subset_right fun b hb hnb =>
      h1 b fun hbN => hnb (Finset.mem_inter.mpr ⟨hbN, hb⟩)
  rw [← hN, hP]

/-! ### Inner products and norms as finite sums -/

theorem inner_eq_sum_of_supp (P : Finset ι) (y z : Sec ι)
    (hy : ∀ a, a ∉ P → (y : ∀ _ : ι, L2R) a = 0) :
    (inner ℂ y z : ℂ) = ∑ a ∈ P, (inner ℂ ((y : ∀ _ : ι, L2R) a) ((z : ∀ _ : ι, L2R) a) : ℂ) := by
  rw [lp.inner_eq_tsum]
  exact tsum_eq_sum fun a ha => by rw [hy a ha, inner_zero_left]

theorem norm_sq_eq_sum_of_supp (P : Finset ι) (y : Sec ι)
    (hy : ∀ a, a ∉ P → (y : ∀ _ : ι, L2R) a = 0) :
    ‖y‖ ^ 2 = ∑ a ∈ P, ‖(y : ∀ _ : ι, L2R) a‖ ^ 2 := by
  have h2 : (inner ℂ y y : ℂ).re = ‖y‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) y
  rw [← h2, inner_eq_sum_of_supp P y y hy, Complex.re_sum]
  exact Finset.sum_congr rfl fun a _ => by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ((y : ∀ _ : ι, L2R) a)

/-! ## 3. The relative bound -/

theorem le_of_sq_le_sq_nonneg {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by nlinarith

/-- A sum over an arbitrary finite set is at most the sum over the band, for a non-negative
summand supported in the band. -/
theorem sum_le_sum_band (P N : Finset ι) (g : ι → ℝ) (hg : ∀ b, 0 ≤ g b)
    (h0 : ∀ b, b ∉ N → g b = 0) : ∑ b ∈ P, g b ≤ ∑ b ∈ N, g b := by
  classical
  have h1 : ∑ b ∈ P ∩ N, g b = ∑ b ∈ P, g b :=
    Finset.sum_subset Finset.inter_subset_left fun b hb hnb =>
      h0 b fun hbN => hnb (Finset.mem_inter.mpr ⟨hb, hbN⟩)
  rw [← h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun b _ _ => hg b

/-- **The Schur test**, in the weighted form the mode matrices satisfy. -/
theorem schur_sq_le (P : Finset ι) (c : ι → ι → ℝ) (v w : ι → ℝ) (K : ℝ)
    (hc : ∀ a b, 0 ≤ c a b) (hw : ∀ b, 0 < w b) (hK : 0 ≤ K)
    (hrow : ∀ a, ∑ b ∈ P, c a b / w b ≤ K)
    (hcol : ∀ b, ∑ a ∈ P, c a b ≤ K * w b) :
    ∑ a ∈ P, (∑ b ∈ P, c a b * v b) ^ 2 ≤ K ^ 2 * ∑ b ∈ P, (w b * v b) ^ 2 := by
  have step : ∀ a ∈ P, (∑ b ∈ P, c a b * v b) ^ 2
      ≤ K * ∑ b ∈ P, c a b * (w b * v b ^ 2) := by
    intro a _
    have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul P
      (r := fun b => c a b * v b) (f := fun b => c a b / w b)
      (g := fun b => c a b * (w b * v b ^ 2))
      (fun i _ => div_nonneg (hc a i) (hw i).le)
      (fun i _ => mul_nonneg (hc a i) (mul_nonneg (hw i).le (sq_nonneg _)))
      (fun i _ => by
        have hwi := (hw i).ne'
        field_simp)
    have hg0 : 0 ≤ ∑ b ∈ P, c a b * (w b * v b ^ 2) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hc a i) (mul_nonneg (hw i).le (sq_nonneg _))
    exact hCS.trans (mul_le_mul_of_nonneg_right (hrow a) hg0)
  calc ∑ a ∈ P, (∑ b ∈ P, c a b * v b) ^ 2
      ≤ ∑ a ∈ P, K * ∑ b ∈ P, c a b * (w b * v b ^ 2) := Finset.sum_le_sum step
    _ = K * ∑ b ∈ P, (∑ a ∈ P, c a b) * (w b * v b ^ 2) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => by rw [Finset.sum_mul]
    _ ≤ K * ∑ b ∈ P, (K * w b) * (w b * v b ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) hK
        exact mul_le_mul_of_nonneg_right (hcol b) (mul_nonneg (hw b).le (sq_nonneg _))
    _ = K ^ 2 * ∑ b ∈ P, (w b * v b) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring

/-- The Schur test for a banded mode matrix acting on a family of scalaron states. -/
theorem sum_norm_sq_mode_le (P : Finset ι) (M : ι → ι → ℂ) (y : ι → L2R) (w : ι → ℝ) (K : ℝ)
    (hw : ∀ b, 0 < w b) (hK : 0 ≤ K)
    (hrow : ∀ a, ∑ b ∈ P, ‖M a b‖ / w b ≤ K)
    (hcol : ∀ b, ∑ a ∈ P, ‖M a b‖ ≤ K * w b) :
    ∑ a ∈ P, ‖∑ b ∈ P, M a b • y b‖ ^ 2 ≤ K ^ 2 * ∑ b ∈ P, (w b * ‖y b‖) ^ 2 := by
  refine le_trans (Finset.sum_le_sum fun a _ => ?_)
    (schur_sq_le P (fun a b => ‖M a b‖) (fun b => ‖y b‖) w K
      (fun a b => norm_nonneg _) hw hK hrow hcol)
  have h1 : ‖∑ b ∈ P, M a b • y b‖ ≤ ∑ b ∈ P, ‖M a b‖ * ‖y b‖ := by
    calc ‖∑ b ∈ P, M a b • y b‖ ≤ ∑ b ∈ P, ‖M a b • y b‖ := norm_sum_le _ _
      _ = ∑ b ∈ P, ‖M a b‖ * ‖y b‖ := Finset.sum_congr rfl fun b _ => norm_smul _ _
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-! ### The three pieces of the Hamiltonian against the shift -/

theorem shift_fib (x : secCore (ι := ι)) (a : ι) :
    ((secDiag W Q x + (x : Sec ι) : Sec ι) : ∀ _ : ι, L2R) a
      = W.ham (Q.sig a) (fibOf x a) + ((fibOf x a : ccDomain ℝ) : L2R) := by
  rw [lp.coeFn_add]
  rfl

theorem shift_supp {P : Finset ι} {x : secCore (ι := ι)}
    (hP1 : ∀ a, a ∉ P → (x : Sec ι) a = 0) (a : ι) (ha : a ∉ P) :
    ((secDiag W Q x + (x : Sec ι) : Sec ι) : ∀ _ : ι, L2R) a = 0 := by
  rw [shift_fib, fibOf_eq_zero (hP1 a ha), map_zero]
  simp

theorem secDiag_supp {P : Finset ι} {x : secCore (ι := ι)}
    (hP1 : ∀ a, a ∉ P → (x : Sec ι) a = 0) (a : ι) (ha : a ∉ P) :
    (secDiag W Q x : Sec ι) a = 0 := by
  rw [secDiag_apply, fibOf_eq_zero (hP1 a ha), map_zero]

theorem modeOp_supp {P : Finset ι} {x : secCore (ι := ι)} (Φ : ccDomain ℝ →ₗ[ℂ] L2R)
    (M : ι → ι → ℂ) (hP2 : ∀ a, a ∉ P → ∀ b ∈ Q.nbr a, (x : Sec ι) b = 0)
    (a : ι) (ha : a ∉ P) : (modeOp Q Φ M x : Sec ι) a = 0 := by
  rw [modeOp_apply]
  refine Finset.sum_eq_zero fun b hb => ?_
  rw [fibOf_eq_zero (hP2 a ha b hb), map_zero, smul_zero]

/-- On the band, the sum over the neighbours of `a` may be taken over the band. -/
theorem modeOp_eq_sum_band {P : Finset ι} {x : secCore (ι := ι)} (Φ : ccDomain ℝ →ₗ[ℂ] L2R)
    (M : ι → ι → ℂ) (hM : ∀ a b, b ∉ Q.nbr a → M a b = 0)
    (hP1 : ∀ a, a ∉ P → (x : Sec ι) a = 0) (a : ι) :
    (modeOp Q Φ M x : Sec ι) a = ∑ b ∈ P, M a b • Φ (fibOf x b) := by
  rw [modeOp_apply]
  refine sum_band_eq_sum _ _ _ (fun b hb => ?_) (fun b hb => ?_)
  · rw [hM a b hb, zero_smul]
  · rw [fibOf_eq_zero (hP1 b hb), map_zero, smul_zero]

theorem norm_secDiag_le (x : secCore (ι := ι)) :
    ‖secDiag W Q x‖ ≤ ‖secDiag W Q x + (x : Sec ι)‖ := by
  obtain ⟨P, hP1, hP2⟩ := exists_band Q x
  refine le_of_sq_le_sq_nonneg (norm_nonneg _) ?_
  rw [norm_sq_eq_sum_of_supp P _ (secDiag_supp W Q hP1),
    norm_sq_eq_sum_of_supp P _ (shift_supp W Q hP1)]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [shift_fib, secDiag_apply]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_ham_le_shift W (Q.sig a) (Q.sig_nonneg a) (fibOf x a)) 2

theorem norm_secA_le (x : secCore (ι := ι)) :
    ‖secA Q x‖ ≤ Q.K * ‖secDiag W Q x + (x : Sec ι)‖ := by
  obtain ⟨P, hP1, hP2⟩ := exists_band Q x
  have hKT : 0 ≤ Q.K * ‖secDiag W Q x + (x : Sec ι)‖ :=
    mul_nonneg Q.K_nonneg (norm_nonneg _)
  refine le_of_sq_le_sq_nonneg hKT ?_
  have hsupp : ∀ a, a ∉ P → (secA Q x : Sec ι) a = 0 :=
    modeOp_supp Q _ _ hP2
  rw [norm_sq_eq_sum_of_supp P _ hsupp]
  have hval : ∀ a, (secA Q x : Sec ι) a
      = ∑ b ∈ P, Q.A a b • ((fibOf x b : ccDomain ℝ) : L2R) :=
    modeOp_eq_sum_band Q _ _ Q.A_off hP1
  have hrow : ∀ a, ∑ b ∈ P, ‖Q.A a b‖ / Q.sig b ≤ Q.K := by
    intro a
    refine le_trans (sum_le_sum_band P (Q.nbr a) _
      (fun b => div_nonneg (norm_nonneg _) (Q.sig_nonneg b)) fun b hb => ?_) (Q.A_rel_row a)
    rw [Q.A_off a b hb, norm_zero, zero_div]
  have hcol : ∀ b, ∑ a ∈ P, ‖Q.A a b‖ ≤ Q.K * Q.sig b := by
    intro b
    refine le_trans (sum_le_sum_band P (Q.nbr b) _ (fun a => norm_nonneg _) fun a ha => ?_) ?_
    · rw [Q.A_off a b fun hba => ha ((Q.mem_nbr_comm b a).mpr hba), norm_zero]
    · refine le_trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_)) (Q.A_rel_col b)
      rw [Q.A_herm b a]
      exact RCLike.norm_conj _
  have hschur := sum_norm_sq_mode_le P Q.A (fun b => ((fibOf x b : ccDomain ℝ) : L2R)) Q.sig Q.K
    Q.sig_pos Q.K_nonneg hrow hcol
  have hfib : ∑ b ∈ P, (Q.sig b * ‖((fibOf x b : ccDomain ℝ) : L2R)‖) ^ 2
      ≤ ∑ b ∈ P, ‖((secDiag W Q x + (x : Sec ι) : Sec ι) : ∀ _ : ι, L2R) b‖ ^ 2 := by
    refine Finset.sum_le_sum fun b _ => ?_
    rw [shift_fib]
    exact pow_le_pow_left₀ (mul_nonneg (Q.sig_nonneg b) (norm_nonneg _))
      (sig_norm_le_shift W (Q.sig b) (Q.sig_nonneg b) (fibOf x b)) 2
  rw [mul_pow, norm_sq_eq_sum_of_supp P _ (shift_supp W Q hP1)]
  calc ∑ a ∈ P, ‖(secA Q x : Sec ι) a‖ ^ 2
      = ∑ a ∈ P, ‖∑ b ∈ P, Q.A a b • ((fibOf x b : ccDomain ℝ) : L2R)‖ ^ 2 :=
        Finset.sum_congr rfl fun a _ => by rw [hval a]
    _ ≤ Q.K ^ 2 * ∑ b ∈ P, (Q.sig b * ‖((fibOf x b : ccDomain ℝ) : L2R)‖) ^ 2 := hschur
    _ ≤ Q.K ^ 2 * ∑ b ∈ P, ‖((secDiag W Q x + (x : Sec ι) : Sec ι) : ∀ _ : ι, L2R) b‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hfib (by positivity)

theorem norm_secB_le (x : secCore (ι := ι)) :
    ‖secB Q x‖ ≤ 2 * Q.K * ‖secDiag W Q x + (x : Sec ι)‖ := by
  obtain ⟨P, hP1, hP2⟩ := exists_band Q x
  have hKT : 0 ≤ 2 * Q.K * ‖secDiag W Q x + (x : Sec ι)‖ :=
    mul_nonneg (by linarith [Q.K_nonneg]) (norm_nonneg _)
  refine le_of_sq_le_sq_nonneg hKT ?_
  have hsupp : ∀ a, a ∉ P → (secB Q x : Sec ι) a = 0 := modeOp_supp Q _ _ hP2
  rw [norm_sq_eq_sum_of_supp P _ hsupp]
  have hval : ∀ a, (secB Q x : Sec ι) a = ∑ b ∈ P, Q.B a b • xCc (fibOf x b) :=
    modeOp_eq_sum_band Q _ _ Q.B_off hP1
  have hrow : ∀ a, ∑ b ∈ P, ‖Q.B a b‖ / (1 : ℝ) ≤ Q.K := by
    intro a
    simp only [div_one]
    refine le_trans (sum_le_sum_band P (Q.nbr a) _ (fun b => norm_nonneg _) fun b hb => ?_)
      (Q.B_rel a)
    rw [Q.B_off a b hb, norm_zero]
  have hcol : ∀ b, ∑ a ∈ P, ‖Q.B a b‖ ≤ Q.K * 1 := by
    intro b
    rw [mul_one]
    refine le_trans (sum_le_sum_band P (Q.nbr b) _ (fun a => norm_nonneg _) fun a ha => ?_) ?_
    · rw [Q.B_off a b fun hba => ha ((Q.mem_nbr_comm b a).mpr hba), norm_zero]
    · refine le_trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_)) (Q.B_rel b)
      rw [Q.B_herm b a]
      exact RCLike.norm_conj _
  have hschur := sum_norm_sq_mode_le P Q.B (fun b => xCc (fibOf x b)) (fun _ => (1 : ℝ)) Q.K
    (fun _ => one_pos) Q.K_nonneg hrow hcol
  have hfib : ∑ b ∈ P, ((1 : ℝ) * ‖xCc (fibOf x b)‖) ^ 2
      ≤ 2 * ∑ b ∈ P, ‖((secDiag W Q x + (x : Sec ι) : Sec ι) : ∀ _ : ι, L2R) b‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [shift_fib, one_mul]
    exact norm_xCc_sq_le_shift W (Q.sig b) (Q.sig_nonneg b) (fibOf x b)
  rw [mul_pow, norm_sq_eq_sum_of_supp P _ (shift_supp W Q hP1)]
  have hK2 : (0 : ℝ) ≤ Q.K ^ 2 := sq_nonneg _
  calc ∑ a ∈ P, ‖(secB Q x : Sec ι) a‖ ^ 2
      = ∑ a ∈ P, ‖∑ b ∈ P, Q.B a b • xCc (fibOf x b)‖ ^ 2 :=
        Finset.sum_congr rfl fun a _ => by rw [hval a]
    _ ≤ Q.K ^ 2 * ∑ b ∈ P, ((1 : ℝ) * ‖xCc (fibOf x b)‖) ^ 2 := hschur
    _ ≤ Q.K ^ 2 * (2 * ∑ b ∈ P,
          ‖((secDiag W Q x + (x : Sec ι) : Sec ι) : ∀ _ : ι, L2R) b‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hfib hK2
    _ ≤ (2 * Q.K) ^ 2 * ∑ b ∈ P,
          ‖((secDiag W Q x + (x : Sec ι) : Sec ι) : ∀ _ : ι, L2R) b‖ ^ 2 := by
        have hs : (0 : ℝ) ≤ ∑ b ∈ P,
            ‖((secDiag W Q x + (x : Sec ι) : Sec ι) : ∀ _ : ι, L2R) b‖ ^ 2 :=
          Finset.sum_nonneg fun b _ => sq_nonneg _
        nlinarith

/-- **The Faris–Lavine relative bound** for the full quantum-gravity Hamiltonian: the
Hamiltonian is bounded by the shift of the comparison operator, with constant `1 + 3K`. -/
theorem secHam_rel (x : secCore (ι := ι)) :
    ‖secHam W Q x‖ ≤ (1 + 3 * Q.K) * ‖secDiag W Q x + (x : Sec ι)‖ := by
  have hsplit : secHam W Q x = secDiag W Q x + secA Q x + secB Q x := rfl
  have h1 := norm_secDiag_le W Q x
  have h2 := norm_secA_le W Q x
  have h3 := norm_secB_le W Q x
  calc ‖secHam W Q x‖ = ‖secDiag W Q x + secA Q x + secB Q x‖ := by rw [hsplit]
    _ ≤ ‖secDiag W Q x + secA Q x‖ + ‖secB Q x‖ := norm_add_le _ _
    _ ≤ ‖secDiag W Q x‖ + ‖secA Q x‖ + ‖secB Q x‖ := by
        have := norm_add_le (secDiag W Q x) (secA Q x)
        linarith
    _ ≤ (1 + 3 * Q.K) * ‖secDiag W Q x + (x : Sec ι)‖ := by linarith

end

end BookProof.ScalaronOuterFockFL
