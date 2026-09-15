import Mathlib
import BookProof.ChapterScalaronFiberFL
import BookProof.ChapterDirectSumEsa
import BookProof.ChapterScalaronOuterFockFL.Part2

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
/-! ## 4. Symmetry -/

theorem xCc_symmetricOn : SymmetricOn (ccDomain ℝ) xCc :=
  smoothPotential_symmetric (fun x : ℝ => x) contDiff_id

/-- Two core vectors share a finite band. -/
theorem exists_band₂ (x y : secCore (ι := ι)) :
    ∃ P : Finset ι, (∀ a, a ∉ P → (x : Sec ι) a = 0) ∧
      (∀ a, a ∉ P → ∀ b ∈ Q.nbr a, (x : Sec ι) b = 0) ∧
      (∀ a, a ∉ P → (y : Sec ι) a = 0) ∧
      (∀ a, a ∉ P → ∀ b ∈ Q.nbr a, (y : Sec ι) b = 0) := by
  classical
  obtain ⟨Px, hx1, hx2⟩ := exists_band Q x
  obtain ⟨Py, hy1, hy2⟩ := exists_band Q y
  refine ⟨Px ∪ Py, ?_, ?_, ?_, ?_⟩ <;> intro a ha
  · exact hx1 a fun h => ha (Finset.mem_union_left _ h)
  · exact hx2 a fun h => ha (Finset.mem_union_left _ h)
  · exact hy1 a fun h => ha (Finset.mem_union_right _ h)
  · exact hy2 a fun h => ha (Finset.mem_union_right _ h)

theorem secHam_supp {P : Finset ι} {x : secCore (ι := ι)}
    (hP1 : ∀ a, a ∉ P → (x : Sec ι) a = 0)
    (hP2 : ∀ a, a ∉ P → ∀ b ∈ Q.nbr a, (x : Sec ι) b = 0) (a : ι) (ha : a ∉ P) :
    (secHam W Q x : Sec ι) a = 0 := by
  rw [secHam_apply]
  have h1 : W.ham (Q.sig a) (fibOf x a) = 0 := by
    rw [fibOf_eq_zero (hP1 a ha), map_zero]
  have h2 : ∑ b ∈ Q.nbr a, Q.A a b • ((fibOf x b : ccDomain ℝ) : L2R) = 0 :=
    Finset.sum_eq_zero fun b hb => by rw [fibOf_eq_zero (hP2 a ha b hb)]; simp
  have h3 : ∑ b ∈ Q.nbr a, Q.B a b • xCc (fibOf x b) = 0 :=
    Finset.sum_eq_zero fun b hb => by
      rw [fibOf_eq_zero (hP2 a ha b hb), map_zero, smul_zero]
  rw [h1, h2, h3]
  simp

/-- **The expansion of the Hamiltonian against an arbitrary vector**, as a finite sum over
the band. -/
theorem inner_secHam_expand (x : secCore (ι := ι)) (z : Sec ι) {P : Finset ι}
    (hP1 : ∀ a, a ∉ P → (x : Sec ι) a = 0)
    (hP2 : ∀ a, a ∉ P → ∀ b ∈ Q.nbr a, (x : Sec ι) b = 0) :
    (inner ℂ (secHam W Q x) z : ℂ)
      = (∑ a ∈ P, (inner ℂ (W.ham (Q.sig a) (fibOf x a)) ((z : ∀ _ : ι, L2R) a) : ℂ))
        + (∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
            (inner ℂ ((fibOf x b : ccDomain ℝ) : L2R) ((z : ∀ _ : ι, L2R) a) : ℂ))
        + ∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.B a b) *
            (inner ℂ (xCc (fibOf x b)) ((z : ∀ _ : ι, L2R) a) : ℂ) := by
  rw [inner_eq_sum_of_supp P _ z (secHam_supp W Q hP1 hP2)]
  have hterm : ∀ a ∈ P, (inner ℂ ((secHam W Q x : Sec ι) a) ((z : ∀ _ : ι, L2R) a) : ℂ)
      = (inner ℂ (W.ham (Q.sig a) (fibOf x a)) ((z : ∀ _ : ι, L2R) a) : ℂ)
        + (∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
            (inner ℂ ((fibOf x b : ccDomain ℝ) : L2R) ((z : ∀ _ : ι, L2R) a) : ℂ))
        + ∑ b ∈ P, (starRingEnd ℂ) (Q.B a b) *
            (inner ℂ (xCc (fibOf x b)) ((z : ∀ _ : ι, L2R) a) : ℂ) := by
    intro a _
    have hA : (secA Q x : Sec ι) a = ∑ b ∈ P, Q.A a b • ((fibOf x b : ccDomain ℝ) : L2R) :=
      modeOp_eq_sum_band Q _ _ Q.A_off hP1 a
    have hB : (secB Q x : Sec ι) a = ∑ b ∈ P, Q.B a b • xCc (fibOf x b) :=
      modeOp_eq_sum_band Q _ _ Q.B_off hP1 a
    have hsplit : (secHam W Q x : Sec ι) a
        = W.ham (Q.sig a) (fibOf x a) + (secA Q x : Sec ι) a + (secB Q x : Sec ι) a := by
      change ((secDiag W Q x + secA Q x + secB Q x : Sec ι)) a = _
      rw [lp.coeFn_add, lp.coeFn_add]
      rfl
    rw [hsplit, hA, hB, inner_add_left, inner_add_left, sum_inner, sum_inner]
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun b _ => inner_smul_left _ _ _
    · exact Finset.sum_congr rfl fun b _ => inner_smul_left _ _ _
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- **The full quantum-gravity Hamiltonian is symmetric on the finite-particle core.** -/
theorem secHam_symmetricOn : SymmetricOn (secCore (ι := ι)) (secHam W Q) := by
  intro x y
  obtain ⟨P, hx1, hx2, hy1, hy2⟩ := exists_band₂ Q x y
  have hL := inner_secHam_expand W Q x (y : Sec ι) hx1 hx2
  have hR := inner_secHam_expand W Q y (x : Sec ι) hy1 hy2
  have hconj : (inner ℂ ((x : Sec ι)) (secHam W Q y) : ℂ)
      = (starRingEnd ℂ) (inner ℂ (secHam W Q y) ((x : Sec ι)) : ℂ) :=
    (inner_conj_symm _ _).symm
  rw [hL, hconj, hR]
  simp only [map_add, map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun a _ => by
        rw [← fibOf_coe y a, ← fibOf_coe x a,
          W.ham_symmetricOn (Q.sig a) (fibOf x a) (fibOf y a), inner_conj_symm]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Q.A_herm b a, inner_conj_symm]
      simp
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← fibOf_coe y b, ← fibOf_coe x a, Q.B_herm b a, inner_conj_symm,
      xCc_symmetricOn (fibOf x a) (fibOf y b)]

/-! ## 5. The commutator bound -/

/-- The arithmetic–geometric mean bound for a symmetric double sum with row and column
sums bounded by `r`. -/
theorem double_sum_amgm (P : Finset ι) (w : ι → ι → ℝ) (f g r : ι → ℝ)
    (hw : ∀ a b, 0 ≤ w a b)
    (hrow : ∀ a, ∑ b ∈ P, w a b ≤ r a) (hcol : ∀ b, ∑ a ∈ P, w a b ≤ r b) :
    ∑ a ∈ P, ∑ b ∈ P, w a b * (f a * g b)
      ≤ (1 / 2) * ((∑ a ∈ P, r a * f a ^ 2) + ∑ b ∈ P, r b * g b ^ 2) := by
  have step1 : ∑ a ∈ P, ∑ b ∈ P, w a b * (f a * g b)
      ≤ ∑ a ∈ P, ∑ b ∈ P, ((w a b * f a ^ 2) / 2 + (w a b * g b ^ 2) / 2) := by
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    nlinarith [sq_nonneg (f a - g b), hw a b]
  have step2 : ∀ a, ∑ b ∈ P, ((w a b * f a ^ 2) / 2 + (w a b * g b ^ 2) / 2)
      = ((∑ b ∈ P, w a b) * f a ^ 2) / 2 + (∑ b ∈ P, w a b * g b ^ 2) / 2 := by
    intro a
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_mul]
  have step3 : ∑ a ∈ P, ∑ b ∈ P, ((w a b * f a ^ 2) / 2 + (w a b * g b ^ 2) / 2)
      = (∑ a ∈ P, (∑ b ∈ P, w a b) * f a ^ 2) / 2
        + (∑ b ∈ P, (∑ a ∈ P, w a b) * g b ^ 2) / 2 := by
    rw [Finset.sum_congr rfl fun a _ => step2 a, Finset.sum_add_distrib, ← Finset.sum_div,
      ← Finset.sum_div]
    congr 2
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [Finset.sum_mul]
  have step4 : (∑ a ∈ P, (∑ b ∈ P, w a b) * f a ^ 2) ≤ ∑ a ∈ P, r a * f a ^ 2 :=
    Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hrow a) (sq_nonneg _)
  have step5 : (∑ b ∈ P, (∑ a ∈ P, w a b) * g b ^ 2) ≤ ∑ b ∈ P, r b * g b ^ 2 :=
    Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hcol b) (sq_nonneg _)
  rw [step3] at step1
  linarith

theorem norm_sub_conj_eq (z : ℂ) : ‖z - (starRingEnd ℂ) z‖ = 2 * |z.im| := by
  rw [Complex.sub_conj]
  simp

/-- The vielbein self-interaction contributes at most `½K` times the quadratic form to the
commutator. -/
theorem imA_le (x : secCore (ι := ι)) (P : Finset ι) :
    |(∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
        (inner ℂ ((fibOf x b : ccDomain ℝ) : L2R) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im|
      ≤ (1 / 2) * Q.K * ∑ a ∈ P, quadForm (W.ham (Q.sig a)) (fibOf x a) := by
  classical
  set u : ι → ccDomain ℝ := fun a => fibOf x a with hu
  set T1 : ℂ := ∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
    (inner ℂ ((u b : ccDomain ℝ) : L2R) (W.ham 0 (u a)) : ℂ) with hT1def
  set T2 : ℂ := ∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
    (((Q.sig a : ℝ) : ℂ) * (inner ℂ ((u b : ccDomain ℝ) : L2R) ((u a : ccDomain ℝ) : L2R) : ℂ))
    with hT2def
  have hsplit : (∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
      (inner ℂ ((u b : ccDomain ℝ) : L2R) (W.ham (Q.sig a) (u a)) : ℂ)) = T1 + T2 := by
    rw [hT1def, hT2def, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ham_eq_ham_zero_add W (Q.sig a) (u a), inner_add_right, inner_smul_right]
    ring
  -- the `h₀` part is real
  have hT1real : (starRingEnd ℂ) T1 = T1 := by
    rw [hT1def]
    simp only [map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Q.A_herm a b, inner_conj_symm, W.ham_symmetricOn 0 (u b) (u a)]
  have hT1im : T1.im = 0 := Complex.conj_eq_iff_im.mp hT1real
  -- the shift part is controlled by the commutator hypothesis on `A`
  have hconjT2 : (starRingEnd ℂ) T2 = ∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
      (((Q.sig b : ℝ) : ℂ) *
        (inner ℂ ((u b : ccDomain ℝ) : L2R) ((u a : ccDomain ℝ) : L2R) : ℂ)) := by
    rw [hT2def]
    simp only [map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply,
      Complex.conj_ofReal]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Q.A_herm a b, inner_conj_symm]
  have hdiff : T2 - (starRingEnd ℂ) T2 = ∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
      ((((Q.sig a - Q.sig b : ℝ)) : ℂ) *
        (inner ℂ ((u b : ccDomain ℝ) : L2R) ((u a : ccDomain ℝ) : L2R) : ℂ)) := by
    rw [hT2def, hconjT2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  have hbound : ‖T2 - (starRingEnd ℂ) T2‖
      ≤ ∑ a ∈ P, ∑ b ∈ P, (‖Q.A a b‖ * |Q.sig a - Q.sig b|) *
        (‖((u a : ccDomain ℝ) : L2R)‖ * ‖((u b : ccDomain ℝ) : L2R)‖) := by
    rw [hdiff]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun a _ => ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun b _ => ?_)
    have hcs : ‖(inner ℂ ((u b : ccDomain ℝ) : L2R) ((u a : ccDomain ℝ) : L2R) : ℂ)‖
        ≤ ‖((u a : ccDomain ℝ) : L2R)‖ * ‖((u b : ccDomain ℝ) : L2R)‖ := by
      rw [mul_comm]
      exact norm_inner_le_norm _ _
    rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcs (abs_nonneg _))
      (norm_nonneg _)
  -- the Schur bounds for the weight
  have hwnn : ∀ a b, 0 ≤ ‖Q.A a b‖ * |Q.sig a - Q.sig b| := fun a b =>
    mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hwsymm : ∀ a b, ‖Q.A a b‖ * |Q.sig a - Q.sig b| = ‖Q.A b a‖ * |Q.sig b - Q.sig a| := by
    intro a b
    rw [Q.A_herm a b, RCLike.norm_conj, abs_sub_comm]
  have hrow : ∀ a, ∑ b ∈ P, ‖Q.A a b‖ * |Q.sig a - Q.sig b| ≤ Q.K * Q.sig a := by
    intro a
    refine le_trans (sum_le_sum_band P (Q.nbr a) _ (fun b => hwnn a b) fun b hb => ?_) ?_
    · rw [Q.A_off a b hb, norm_zero, zero_mul]
    · refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => mul_comm _ _)) (Q.A_comm a)
  have hcol : ∀ b, ∑ a ∈ P, ‖Q.A a b‖ * |Q.sig a - Q.sig b| ≤ Q.K * Q.sig b := by
    intro b
    rw [Finset.sum_congr rfl fun a _ => hwsymm a b]
    exact hrow b
  have hamgm := double_sum_amgm P (fun a b => ‖Q.A a b‖ * |Q.sig a - Q.sig b|)
    (fun a => ‖((u a : ccDomain ℝ) : L2R)‖) (fun b => ‖((u b : ccDomain ℝ) : L2R)‖)
    (fun a => Q.K * Q.sig a) hwnn hrow hcol
  have hq : ∀ a, Q.K * Q.sig a * ‖((u a : ccDomain ℝ) : L2R)‖ ^ 2
      ≤ Q.K * quadForm (W.ham (Q.sig a)) (u a) := by
    intro a
    have h := sig_mul_norm_sq_le_quadForm W (Q.sig a) (u a)
    have : Q.K * (Q.sig a * ‖((u a : ccDomain ℝ) : L2R)‖ ^ 2)
        ≤ Q.K * quadForm (W.ham (Q.sig a)) (u a) :=
      mul_le_mul_of_nonneg_left h Q.K_nonneg
    linarith [this]
  have hsum : ∑ a ∈ P, Q.K * Q.sig a * ‖((u a : ccDomain ℝ) : L2R)‖ ^ 2
      ≤ Q.K * ∑ a ∈ P, quadForm (W.ham (Q.sig a)) (u a) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => hq a
  have hfinal : ‖T2 - (starRingEnd ℂ) T2‖ ≤ Q.K * ∑ a ∈ P, quadForm (W.ham (Q.sig a)) (u a) := by
    refine le_trans hbound (le_trans hamgm ?_)
    linarith [hsum]
  rw [hsplit]
  have him : (T1 + T2).im = T2.im := by
    rw [Complex.add_im, hT1im, zero_add]
  rw [him]
  have h2 := norm_sub_conj_eq T2
  rw [h2] at hfinal
  linarith

/-- The scalaron–vielbein coupling contributes at most `9K/4` times the quadratic form to
the commutator.  The scalaron Hamiltonian and the coupling do **not** commute: the
commutator identity `[h_s, φ] = -2 d/dφ` produces the derivative term, which the quadratic
form controls uniformly in the wall. -/
theorem imB_le (x : secCore (ι := ι)) (P : Finset ι) :
    |(∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.B a b) *
        (inner ℂ (xCc (fibOf x b)) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im|
      ≤ (9 / 4) * Q.K * ∑ a ∈ P, quadForm (W.ham (Q.sig a)) (fibOf x a) := by
  classical
  set u : ι → ccDomain ℝ := fun a => fibOf x a with hu
  set U : ℂ := ∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.B a b) *
    (inner ℂ (xCc (u b)) (W.ham (Q.sig a) (u a)) : ℂ) with hUdef
  set S : ℝ := ∑ a ∈ P, quadForm (W.ham (Q.sig a)) (u a) with hSdef
  have hUswap : U = ∑ a ∈ P, ∑ b ∈ P, Q.B a b *
      (inner ℂ (xCc (u a)) (W.ham (Q.sig b) (u b)) : ℂ) := by
    rw [hUdef, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Q.B_herm a b]
    simp
  have hconjU : (starRingEnd ℂ) U = ∑ a ∈ P, ∑ b ∈ P, Q.B a b *
      ((inner ℂ (xCc (u a)) (W.ham (Q.sig a) (u b)) : ℂ)
        - 2 * (inner ℂ ((u a : ccDomain ℝ) : L2R) (dCc (u b)) : ℂ)) := by
    rw [hUdef]
    simp only [map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    congr 1
    have h := ham_x_comm_cc W (Q.sig a) (u a) (u b)
    linear_combination h
  have hfibdiff : ∀ a b, (inner ℂ (xCc (u a)) (W.ham (Q.sig b) (u b)) : ℂ)
      - (inner ℂ (xCc (u a)) (W.ham (Q.sig a) (u b)) : ℂ)
      = (((Q.sig b - Q.sig a : ℝ)) : ℂ) *
        (inner ℂ (xCc (u a)) ((u b : ccDomain ℝ) : L2R) : ℂ) := by
    intro a b
    rw [ham_eq_ham_zero_add W (Q.sig b) (u b), ham_eq_ham_zero_add W (Q.sig a) (u b),
      inner_add_right, inner_add_right, inner_smul_right, inner_smul_right]
    push_cast
    ring
  have hdiff : U - (starRingEnd ℂ) U = ∑ a ∈ P, ∑ b ∈ P, Q.B a b *
      ((((Q.sig b - Q.sig a : ℝ)) : ℂ) *
          (inner ℂ (xCc (u a)) ((u b : ccDomain ℝ) : L2R) : ℂ)
        + 2 * (inner ℂ ((u a : ccDomain ℝ) : L2R) (dCc (u b)) : ℂ)) := by
    rw [hconjU, hUswap, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    linear_combination (Q.B a b) * hfibdiff a b
  -- termwise bound
  have hterm : ∀ a b, ‖Q.B a b *
      ((((Q.sig b - Q.sig a : ℝ)) : ℂ) *
          (inner ℂ (xCc (u a)) ((u b : ccDomain ℝ) : L2R) : ℂ)
        + 2 * (inner ℂ ((u a : ccDomain ℝ) : L2R) (dCc (u b)) : ℂ))‖
      ≤ (‖Q.B a b‖ * |Q.sig a - Q.sig b|) * (‖xCc (u a)‖ * ‖((u b : ccDomain ℝ) : L2R)‖)
        + 2 * (‖Q.B a b‖ * (‖((u a : ccDomain ℝ) : L2R)‖ * ‖dCc (u b)‖)) := by
    intro a b
    have h1 : ‖(((Q.sig b - Q.sig a : ℝ)) : ℂ) *
        (inner ℂ (xCc (u a)) ((u b : ccDomain ℝ) : L2R) : ℂ)‖
        ≤ |Q.sig a - Q.sig b| * (‖xCc (u a)‖ * ‖((u b : ccDomain ℝ) : L2R)‖) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (abs_nonneg _)
    have h2 : ‖(2 : ℂ) * (inner ℂ ((u a : ccDomain ℝ) : L2R) (dCc (u b)) : ℂ)‖
        ≤ 2 * (‖((u a : ccDomain ℝ) : L2R)‖ * ‖dCc (u b)‖) := by
      rw [norm_mul]
      have : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [this]
      exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
    calc ‖Q.B a b * ((((Q.sig b - Q.sig a : ℝ)) : ℂ) *
            (inner ℂ (xCc (u a)) ((u b : ccDomain ℝ) : L2R) : ℂ)
          + 2 * (inner ℂ ((u a : ccDomain ℝ) : L2R) (dCc (u b)) : ℂ))‖
        = ‖Q.B a b‖ * ‖(((Q.sig b - Q.sig a : ℝ)) : ℂ) *
            (inner ℂ (xCc (u a)) ((u b : ccDomain ℝ) : L2R) : ℂ)
          + 2 * (inner ℂ ((u a : ccDomain ℝ) : L2R) (dCc (u b)) : ℂ)‖ := norm_mul _ _
      _ ≤ ‖Q.B a b‖ * (|Q.sig a - Q.sig b| * (‖xCc (u a)‖ * ‖((u b : ccDomain ℝ) : L2R)‖)
            + 2 * (‖((u a : ccDomain ℝ) : L2R)‖ * ‖dCc (u b)‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact le_trans (norm_add_le _ _) (by linarith)
      _ = (‖Q.B a b‖ * |Q.sig a - Q.sig b|) *
            (‖xCc (u a)‖ * ‖((u b : ccDomain ℝ) : L2R)‖)
          + 2 * (‖Q.B a b‖ * (‖((u a : ccDomain ℝ) : L2R)‖ * ‖dCc (u b)‖)) := by ring
  have hnormsum : ‖U - (starRingEnd ℂ) U‖
      ≤ (∑ a ∈ P, ∑ b ∈ P, (‖Q.B a b‖ * |Q.sig a - Q.sig b|) *
            (‖xCc (u a)‖ * ‖((u b : ccDomain ℝ) : L2R)‖))
        + 2 * ∑ a ∈ P, ∑ b ∈ P, ‖Q.B a b‖ *
            (‖((u a : ccDomain ℝ) : L2R)‖ * ‖dCc (u b)‖) := by
    rw [hdiff]
    refine le_trans (le_trans (norm_sum_le _ _)
      (Finset.sum_le_sum fun a _ => norm_sum_le _ _)) ?_
    have hstep : ∑ a ∈ P, ∑ b ∈ P, ‖Q.B a b *
        ((((Q.sig b - Q.sig a : ℝ)) : ℂ) *
            (inner ℂ (xCc (u a)) ((u b : ccDomain ℝ) : L2R) : ℂ)
          + 2 * (inner ℂ ((u a : ccDomain ℝ) : L2R) (dCc (u b)) : ℂ))‖
        ≤ ∑ a ∈ P, ∑ b ∈ P, ((‖Q.B a b‖ * |Q.sig a - Q.sig b|) *
              (‖xCc (u a)‖ * ‖((u b : ccDomain ℝ) : L2R)‖)
            + 2 * (‖Q.B a b‖ * (‖((u a : ccDomain ℝ) : L2R)‖ * ‖dCc (u b)‖))) :=
      Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
    refine le_trans hstep (le_of_eq ?_)
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  -- the two Schur bounds
  have hBnn : ∀ a b, 0 ≤ ‖Q.B a b‖ := fun a b => norm_nonneg _
  have hBsymm : ∀ a b, ‖Q.B a b‖ = ‖Q.B b a‖ := by
    intro a b
    rw [Q.B_herm a b, RCLike.norm_conj]
  have hw1nn : ∀ a b, 0 ≤ ‖Q.B a b‖ * |Q.sig a - Q.sig b| := fun a b =>
    mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hw1symm : ∀ a b, ‖Q.B a b‖ * |Q.sig a - Q.sig b| = ‖Q.B b a‖ * |Q.sig b - Q.sig a| := by
    intro a b
    rw [← hBsymm a b, abs_sub_comm]
  have hrow1 : ∀ a, ∑ b ∈ P, ‖Q.B a b‖ * |Q.sig a - Q.sig b| ≤ Q.K := by
    intro a
    refine le_trans (sum_le_sum_band P (Q.nbr a) _ (fun b => hw1nn a b) fun b hb => ?_) ?_
    · rw [Q.B_off a b hb, norm_zero, zero_mul]
    · refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => mul_comm _ _)) (Q.B_comm a)
  have hcol1 : ∀ b, ∑ a ∈ P, ‖Q.B a b‖ * |Q.sig a - Q.sig b| ≤ Q.K := by
    intro b
    rw [Finset.sum_congr rfl fun a _ => hw1symm a b]
    exact hrow1 b
  have hrow2 : ∀ a, ∑ b ∈ P, ‖Q.B a b‖ ≤ Q.K := by
    intro a
    refine le_trans (sum_le_sum_band P (Q.nbr a) _ (fun b => hBnn a b) fun b hb => ?_)
      (Q.B_rel a)
    rw [Q.B_off a b hb, norm_zero]
  have hcol2 : ∀ b, ∑ a ∈ P, ‖Q.B a b‖ ≤ Q.K := by
    intro b
    rw [Finset.sum_congr rfl fun a _ => hBsymm a b]
    exact hrow2 b
  have hS1 := double_sum_amgm P (fun a b => ‖Q.B a b‖ * |Q.sig a - Q.sig b|)
    (fun a => ‖xCc (u a)‖) (fun b => ‖((u b : ccDomain ℝ) : L2R)‖) (fun _ => Q.K)
    hw1nn hrow1 hcol1
  have hS2 := double_sum_amgm P (fun a b => ‖Q.B a b‖)
    (fun a => ‖((u a : ccDomain ℝ) : L2R)‖) (fun b => ‖dCc (u b)‖) (fun _ => Q.K)
    hBnn hrow2 hcol2
  -- the fibre estimates
  have hxc : ∑ a ∈ P, Q.K * ‖xCc (u a)‖ ^ 2 ≤ 4 * Q.K * S := by
    rw [hSdef, mul_assoc, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have h := norm_xCc_sq_le_cc W (Q.sig a) (Q.sig_nonneg a) (u a)
    have hk := mul_le_mul_of_nonneg_left h Q.K_nonneg
    linarith
  have hnrm : ∑ a ∈ P, Q.K * ‖((u a : ccDomain ℝ) : L2R)‖ ^ 2 ≤ Q.K * S := by
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have h := norm_sq_le_quadForm_cc W (Q.sig a) (Q.one_le_sig a) (u a)
    exact mul_le_mul_of_nonneg_left h Q.K_nonneg
  have hder : ∑ a ∈ P, Q.K * ‖dCc (u a)‖ ^ 2 ≤ Q.K * S := by
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have h := norm_dCc_sq_le_cc W (Q.sig a) (Q.sig_nonneg a) (u a)
    exact mul_le_mul_of_nonneg_left h Q.K_nonneg
  have hfinal : ‖U - (starRingEnd ℂ) U‖ ≤ (9 / 2) * Q.K * S := by
    refine le_trans hnormsum ?_
    have e1 := hS1
    have e2 := hS2
    linarith
  have h2 := norm_sub_conj_eq U
  rw [h2] at hfinal
  linarith

end

end BookProof.ScalaronOuterFockFL
