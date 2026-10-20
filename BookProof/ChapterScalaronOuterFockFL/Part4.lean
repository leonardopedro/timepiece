import Mathlib
import BookProof.ChapterScalaronFiberFL
import BookProof.ChapterDirectSumEsa
import BookProof.ChapterScalaronOuterFockFL.Part3

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
/-! ## 6. The Faris–Lavine commutator bound -/

/-- The quadratic form of the fibrewise Hamiltonian is the sum of the fibre quadratic
forms over any band of the core vector. -/
theorem quadForm_secDiag_eq (x : secCore (ι := ι)) {P : Finset ι}
    (hP1 : ∀ a, a ∉ P → (x : Sec ι) a = 0) :
    quadForm (secDiag W Q) x = ∑ a ∈ P, quadForm (W.ham (Q.sig a)) (fibOf x a) := by
  rw [quadForm, inner_eq_sum_of_supp P (x : Sec ι) (secDiag W Q x) hP1, Complex.re_sum]
  rfl

theorem quadForm_secDiag_nonneg (x : secCore (ι := ι)) : 0 ≤ quadForm (secDiag W Q) x := by
  obtain ⟨P, hP1, _⟩ := exists_band Q x
  rw [quadForm_secDiag_eq W Q x hP1]
  exact Finset.sum_nonneg fun a _ => ham_quadForm_nonneg W (Q.sig a) (Q.sig_nonneg a) _

/-- **The Faris–Lavine commutator bound for the full quantum-gravity Hamiltonian.**  The
fibrewise scalaron Hamiltonian commutes with itself, the vielbein self-interaction
contributes at most `½K` and the scalaron–vielbein coupling at most `9/4 K` times the
quadratic form; the total is bounded by `6K` times the quadratic form of the comparison
operator. -/
theorem secHam_commForm_le (x : secCore (ι := ι)) :
    |commForm (secHam W Q) (secDiag W Q) x| ≤ (6 * Q.K) * quadForm (secDiag W Q) x := by
  classical
  obtain ⟨P, hP1, hP2⟩ := exists_band Q x
  have hSq : quadForm (secDiag W Q) x
      = ∑ a ∈ P, quadForm (W.ham (Q.sig a)) (fibOf x a) := quadForm_secDiag_eq W Q x hP1
  have hSnn : (0 : ℝ) ≤ ∑ a ∈ P, quadForm (W.ham (Q.sig a)) (fibOf x a) :=
    Finset.sum_nonneg fun a _ => ham_quadForm_nonneg W (Q.sig a) (Q.sig_nonneg a) _
  have hexp := inner_secHam_expand W Q x (secDiag W Q x : Sec ι) hP1 hP2
  simp only [secDiag_apply] at hexp
  have h1 : (∑ a ∈ P, (inner ℂ (W.ham (Q.sig a) (fibOf x a))
      (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im = 0 := by
    rw [Complex.im_sum]
    exact Finset.sum_eq_zero fun a _ => by simpa using inner_self_im (𝕜 := ℂ) _
  have h2 := imA_le W Q x P
  have h3 := imB_le W Q x P
  have him : (inner ℂ (secHam W Q x) (secDiag W Q x : Sec ι) : ℂ).im
      = (∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
            (inner ℂ ((fibOf x b : ccDomain ℝ) : L2R) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im
        + (∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.B a b) *
            (inner ℂ (xCc (fibOf x b)) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im := by
    rw [hexp, Complex.add_im, Complex.add_im, h1, zero_add]
  have hKS : 0 ≤ Q.K * ∑ a ∈ P, quadForm (W.ham (Q.sig a)) (fibOf x a) :=
    mul_nonneg Q.K_nonneg hSnn
  rw [commForm_eq, him, hSq]
  have habs : |(-2 : ℝ) * ((∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
        (inner ℂ ((fibOf x b : ccDomain ℝ) : L2R) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im
      + (∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.B a b) *
        (inner ℂ (xCc (fibOf x b)) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im)|
      = 2 * |(∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
        (inner ℂ ((fibOf x b : ccDomain ℝ) : L2R) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im
      + (∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.B a b) *
        (inner ℂ (xCc (fibOf x b)) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im| := by
    rw [abs_mul]
    norm_num
  rw [habs]
  have htri := abs_add_le ((∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.A a b) *
        (inner ℂ ((fibOf x b : ccDomain ℝ) : L2R) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im)
      ((∑ a ∈ P, ∑ b ∈ P, (starRingEnd ℂ) (Q.B a b) *
        (inner ℂ (xCc (fibOf x b)) (W.ham (Q.sig a) (fibOf x a)) : ℂ)).im)
  linarith

/-! ## 7. Essential self-adjointness of the full quantum-gravity Hamiltonian -/

/-- **The Faris–Lavine core data of the gauge-fixed quantum-gravity Hamiltonian.**  The
comparison operator is the `ℓ²`-lift of the fibrewise Friedrichs extensions, the graph core
is the algebraic direct sum of the compactly supported smooth scalaron cores, and the
operator is the full Hamiltonian: fibrewise scalaron with the exponential Starobinsky wall,
vielbein self-interaction and scalaron–vielbein coupling. -/
def secData : CoreData (Sec ι) where
  C := secN W Q
  C₀ := secCore
  gc := secN_isGraphCore W Q
  H₀ := secHam W Q
  K := 1 + 3 * Q.K
  hK := by have := Q.K_nonneg; linarith
  rel := by
    intro p
    rw [secN_core W Q p]
    exact secHam_rel W Q p

@[simp] theorem secData_C : (secData W Q).C = secN W Q := rfl

@[simp] theorem secData_coreN (p : secCore (ι := ι)) :
    (secData W Q).coreN p = secDiag W Q p := secN_core W Q p

/-- The extension of the Hamiltonian from the finite-particle core to the whole domain of
the comparison operator restricts back to the Hamiltonian on the core. -/
theorem secData_ext_core (p : secCore (ι := ι)) :
    (secData W Q).ext ⟨(p : Sec ι), (secData W Q).gc.le p.2⟩ = secHam W Q p :=
  (secData W Q).ext_core p

/-- **Essential self-adjointness of the full gauge-fixed quantum-gravity Hamiltonian on the
outer Fock space.**

The Hamiltonian consists of the fibrewise scalaron operator `−∂²_φ + φ²/4 + V(φ) + σ_a`
with the *full exponential* Starobinsky wall (no Taylor truncation), the complete vielbein
self-interaction `A` and the scalaron–vielbein coupling `B`, all in the 3-dimensional
gauge-fixed formulation.  It is defined on the finite-particle core of the outer Fock space
`⊕_a L²(ℝ)` and extended, by its relative bound, to the whole domain of the lifted
Friedrichs extension `N`, where it is essentially self-adjoint by the Faris–Lavine
criterion: it is symmetric, relatively bounded by `N + 1`, and its commutator form with `N`
is dominated by `6K` times the quadratic form of `N`. -/
theorem secHam_essentiallySelfAdjointOn :
    EssentiallySelfAdjointOn (secN W Q).dom (secData W Q).ext := by
  refine (secData W Q).ext_essentiallySelfAdjointOn (secHam_symmetricOn W Q)
    (c := 6 * Q.K) (by have := Q.K_nonneg; linarith) ?_
  intro p
  have hc : commForm (secData W Q).H₀ (secData W Q).coreN p
      = commForm (secHam W Q) (secDiag W Q) p :=
    commForm_congr _ _ _ _ _ _ rfl (secData_coreN W Q p)
  have hq : quadForm (secData W Q).coreN p = quadForm (secDiag W Q) p :=
    quadForm_congr _ _ _ _ rfl (secData_coreN W Q p)
  rw [hc, hq]
  exact secHam_commForm_le W Q p

end

end BookProof.ScalaronOuterFockFL
