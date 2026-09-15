import Mathlib
import BookProof.ChapterScalaronFiberFL
import BookProof.ChapterDirectSumEsa

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

/-! ## 0. Generic estimates for a positive symmetric operator and its shift -/

section Shift

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

/-- The shift identity `‖Nu + u‖² = ‖Nu‖² + 2q(u) + ‖u‖²`. -/
theorem norm_shift_sq (N : D →ₗ[ℂ] F) (hsym : SymmetricOn D N) (u : D) :
    ‖N u + (u : F)‖ ^ 2 = ‖N u‖ ^ 2 + 2 * quadForm N u + ‖(u : F)‖ ^ 2 := by
  have h := norm_add_sq (𝕜 := ℂ) (N u) ((u : F))
  have hq : (inner ℂ (N u) (u : F) : ℂ).re = quadForm N u := by
    rw [quadForm, hsym u u]
  rw [h]
  simp only [RCLike.re_to_complex] at *
  rw [hq]

/-- The graph norm of the shift dominates the norm of the image. -/
theorem norm_op_le_shift (N : D →ₗ[ℂ] F) (hsym : SymmetricOn D N)
    (hpos : ∀ x : D, 0 ≤ quadForm N x) (u : D) : ‖N u‖ ≤ ‖N u + (u : F)‖ := by
  have h := norm_shift_sq N hsym u
  have h1 := hpos u
  have h2 : (0 : ℝ) ≤ ‖(u : F)‖ ^ 2 := by positivity
  nlinarith [norm_nonneg (N u), norm_nonneg (N u + (u : F))]

/-- The quadratic form is dominated by the graph norm of the shift. -/
theorem two_quadForm_le_shift_sq (N : D →ₗ[ℂ] F) (hsym : SymmetricOn D N) (u : D) :
    2 * quadForm N u ≤ ‖N u + (u : F)‖ ^ 2 := by
  have h := norm_shift_sq N hsym u
  nlinarith [norm_nonneg (N u), sq_nonneg ‖N u‖, sq_nonneg ‖(u : F)‖]

theorem quadForm_le_mul_norm (N : D →ₗ[ℂ] F) (u : D) :
    quadForm N u ≤ ‖(u : F)‖ * ‖N u‖ := by
  calc quadForm N u ≤ ‖(inner ℂ (u : F) (N u) : ℂ)‖ := Complex.re_le_norm _
    _ ≤ ‖(u : F)‖ * ‖N u‖ := norm_inner_le_norm _ _

/-- A lower form bound `σ‖u‖² ≤ q(u)` upgrades to the operator bound `σ‖u‖ ≤ ‖(N+1)u‖`. -/
theorem mul_norm_le_shift (N : D →ₗ[ℂ] F) (hsym : SymmetricOn D N)
    (hpos : ∀ x : D, 0 ≤ quadForm N x) {sg : ℝ} (u : D)
    (h : sg * ‖(u : F)‖ ^ 2 ≤ quadForm N u) : sg * ‖(u : F)‖ ≤ ‖N u + (u : F)‖ := by
  have hcs := quadForm_le_mul_norm N u
  have hop := norm_op_le_shift N hsym hpos u
  rcases eq_or_lt_of_le (norm_nonneg (u : F)) with h0 | h0
  · have hz : sg * ‖(u : F)‖ = 0 := by rw [← h0]; ring
    rw [hz]
    exact norm_nonneg _
  · have hle : sg * ‖(u : F)‖ ≤ ‖N u‖ := by
      have hm : sg * ‖(u : F)‖ * ‖(u : F)‖ ≤ ‖N u‖ * ‖(u : F)‖ := by nlinarith
      exact le_of_mul_le_mul_right hm h0
    linarith

end Shift

/-! ## 0b. The fibre estimates, in terms of core vectors -/

section Fibre

variable (W : WallPot) (s : ℝ)

theorem le_pot (x : ℝ) : s ≤ W.pot s x := by
  have h1 := W.nonneg x
  have h2 : (0 : ℝ) ≤ x ^ 2 / 4 := by positivity
  simp only [WallPot.pot]
  linarith

/-- Splitting off the vielbein energy: `h_s = h_0 + s`. -/
theorem ham_eq_ham_zero_add (u : ccDomain ℝ) :
    W.ham s u = W.ham 0 u + (s : ℂ) • (u : L2R) := by
  obtain ⟨f, rfl⟩ := (ccEquiv ℝ).surjective u
  rw [ham_eq_toLp, ham_eq_toLp, ccEquiv_coe]
  have hS : hamS W s f = hamS W 0 f + (s : ℂ) • (f : 𝓢(ℝ, ℂ)) := by
    refine SchwartzMap.ext fun x => ?_
    simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, hamS_apply, smul_eq_mul,
      WallPot.pot]
    push_cast
    ring
  rw [hS]
  have h1 := map_add (toLpCLM ℂ ℂ 2 (volume : Measure ℝ)) (hamS W 0 f)
    ((s : ℂ) • (f : 𝓢(ℝ, ℂ)))
  have h2 := map_smul (toLpCLM ℂ ℂ 2 (volume : Measure ℝ)) ((s : ℂ)) (f : 𝓢(ℝ, ℂ))
  rw [show ((hamS W 0 f + (s : ℂ) • (f : 𝓢(ℝ, ℂ))).toLp 2 (volume : Measure ℝ))
      = toLpCLM ℂ ℂ 2 (volume : Measure ℝ) (hamS W 0 f + (s : ℂ) • (f : 𝓢(ℝ, ℂ))) from rfl,
    h1, h2]
  rfl

/-- The vielbein energy is a lower bound for the fibre quadratic form. -/
theorem sig_mul_norm_sq_le_quadForm (u : ccDomain ℝ) :
    s * ‖(u : L2R)‖ ^ 2 ≤ quadForm (W.ham s) u := by
  obtain ⟨f, rfl⟩ := (ccEquiv ℝ).surjective u
  rw [ccEquiv_norm_sq, ham_quadForm]
  have hmono : (∫ x, s * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2) ≤ ∫ x, W.pot s x * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 := by
    refine integral_mono (cc_integrable f (W := fun _ => s) continuous_const)
      (cc_integrable f (W.pot_smooth s).continuous) fun x => ?_
    have h1 := le_pot W s x
    nlinarith [sq_nonneg ‖(f : 𝓢(ℝ, ℂ)) x‖]
  have hsplit : (∫ x, s * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2) = s * ∫ x, ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 :=
    integral_const_mul _ _
  have h1 := integral_deriv_nonneg f
  linarith

theorem norm_sq_le_quadForm_cc (hs : 1 ≤ s) (u : ccDomain ℝ) :
    ‖(u : L2R)‖ ^ 2 ≤ quadForm (W.ham s) u := by
  obtain ⟨f, rfl⟩ := (ccEquiv ℝ).surjective u
  exact norm_sq_le_quadForm W s hs f

theorem norm_xCc_sq_le_cc (hs : 0 ≤ s) (u : ccDomain ℝ) :
    ‖xCc u‖ ^ 2 ≤ 4 * quadForm (W.ham s) u := by
  obtain ⟨f, rfl⟩ := (ccEquiv ℝ).surjective u
  exact norm_xCc_sq_le W s hs f

/-- The derivative of a core vector. -/
def dCc (u : ccDomain ℝ) : L2R := derivL2 ((ccEquiv ℝ).symm u)

theorem dCc_eq (f : ccSchwartz ℝ) : dCc (ccEquiv ℝ f) = derivL2 f := by
  rw [dCc, LinearEquiv.symm_apply_apply]

theorem norm_dCc_sq_le_cc (hs : 0 ≤ s) (u : ccDomain ℝ) :
    ‖dCc u‖ ^ 2 ≤ quadForm (W.ham s) u := by
  obtain ⟨f, rfl⟩ := (ccEquiv ℝ).surjective u
  rw [dCc_eq]
  exact norm_derivL2_sq_le W s hs f

/-- The commutator identity `[h_s, φ] = -2 d/dφ`, for core vectors. -/
theorem ham_x_comm_cc (u v : ccDomain ℝ) :
    (starRingEnd ℂ) (inner ℂ (xCc v) (W.ham s u) : ℂ) - (inner ℂ (xCc u) (W.ham s v) : ℂ)
      = -2 * (inner ℂ (u : L2R) (dCc v) : ℂ) := by
  obtain ⟨f, rfl⟩ := (ccEquiv ℝ).surjective u
  obtain ⟨g, rfl⟩ := (ccEquiv ℝ).surjective v
  rw [dCc_eq]
  exact ham_x_comm W s f g

/-! The three relative bounds against the shift `h_s + 1`, uniform in `s`. -/

theorem norm_ham_le_shift (hs : 0 ≤ s) (u : ccDomain ℝ) :
    ‖W.ham s u‖ ≤ ‖W.ham s u + (u : L2R)‖ :=
  norm_op_le_shift _ (W.ham_symmetricOn s) (ham_quadForm_nonneg W s hs) u

theorem two_quadForm_le_shift (u : ccDomain ℝ) :
    2 * quadForm (W.ham s) u ≤ ‖W.ham s u + (u : L2R)‖ ^ 2 :=
  two_quadForm_le_shift_sq _ (W.ham_symmetricOn s) u

theorem sig_norm_le_shift (hs : 0 ≤ s) (u : ccDomain ℝ) :
    s * ‖(u : L2R)‖ ≤ ‖W.ham s u + (u : L2R)‖ :=
  mul_norm_le_shift _ (W.ham_symmetricOn s) (ham_quadForm_nonneg W s hs) u
    (sig_mul_norm_sq_le_quadForm W s u)

theorem norm_xCc_sq_le_shift (hs : 0 ≤ s) (u : ccDomain ℝ) :
    ‖xCc u‖ ^ 2 ≤ 2 * ‖W.ham s u + (u : L2R)‖ ^ 2 := by
  have h1 := norm_xCc_sq_le_cc W s hs u
  have h2 := two_quadForm_le_shift W s u
  linarith

end Fibre

variable {ι : Type*}

/-- The outer Fock space of the vielbein modes with values in the scalaron line. -/
abbrev Sec (ι : Type*) := lp (fun _ : ι => L2R) 2

/-- **The mode data of the gauge-fixed quantum-gravity Hamiltonian.**

`sig` is the vielbein energy of an occupation configuration, `A` the (Hermitian) mode matrix
of all vielbein self-interactions — it acts as a scalar on the scalaron fibre — and `B` the
(Hermitian) mode matrix of the scalaron–vielbein coupling, which acts by multiplication by
the scalaron field `φ`.  The band structure `nbr` makes every row and column finite, and the
five bounds are the Faris–Lavine input: the vielbein matrix is allowed to grow like the mode
energy (as the second quantization of a quadratic Hamiltonian does), the coupling matrix is
required to be Schur-bounded. -/
structure QgModeData (ι : Type*) where
  /-- The vielbein energy of a mode configuration. -/
  sig : ι → ℝ
  /-- The energies are at least one. -/
  one_le_sig : ∀ a, 1 ≤ sig a
  /-- The vielbein self-interaction matrix. -/
  A : ι → ι → ℂ
  /-- The scalaron–vielbein coupling matrix. -/
  B : ι → ι → ℂ
  /-- The band. -/
  nbr : ι → Finset ι
  /-- The band is symmetric. -/
  mem_nbr_comm : ∀ a b, b ∈ nbr a ↔ a ∈ nbr b
  /-- `A` vanishes outside the band. -/
  A_off : ∀ a b, b ∉ nbr a → A a b = 0
  /-- `B` vanishes outside the band. -/
  B_off : ∀ a b, b ∉ nbr a → B a b = 0
  /-- `A` is Hermitian. -/
  A_herm : ∀ a b, A b a = (starRingEnd ℂ) (A a b)
  /-- `B` is Hermitian. -/
  B_herm : ∀ a b, B b a = (starRingEnd ℂ) (B a b)
  /-- The uniform bound. -/
  K : ℝ
  /-- The uniform bound is non-negative. -/
  K_nonneg : 0 ≤ K
  /-- Row bound for `A`, weighted by the mode energy. -/
  A_rel_row : ∀ a, ∑ b ∈ nbr a, ‖A a b‖ / sig b ≤ K
  /-- Column bound for `A`. -/
  A_rel_col : ∀ a, ∑ b ∈ nbr a, ‖A a b‖ ≤ K * sig a
  /-- Commutator bound for `A`. -/
  A_comm : ∀ a, ∑ b ∈ nbr a, |sig a - sig b| * ‖A a b‖ ≤ K * sig a
  /-- Schur bound for the coupling `B`. -/
  B_rel : ∀ a, ∑ b ∈ nbr a, ‖B a b‖ ≤ K
  /-- Commutator bound for the coupling `B`. -/
  B_comm : ∀ a, ∑ b ∈ nbr a, |sig a - sig b| * ‖B a b‖ ≤ K

namespace QgModeData

variable (Q : QgModeData ι)

theorem sig_nonneg (a : ι) : (0 : ℝ) ≤ Q.sig a := le_trans zero_le_one (Q.one_le_sig a)

theorem sig_pos (a : ι) : (0 : ℝ) < Q.sig a := lt_of_lt_of_le zero_lt_one (Q.one_le_sig a)

end QgModeData

variable (W : WallPot) (Q : QgModeData ι)

/-- The fibre comparison operator: the Friedrichs extension of
`−d²/dφ² + φ²/4 + V(φ) + σ_a`. -/
def fibCompar (a : ι) : Comparison L2R := W.comparison (Q.sig a) (Q.sig_nonneg a)

/-- **The comparison operator on the outer Fock space**: the `ℓ²`-lift of the fibre
Friedrichs extensions. -/
def secN : Comparison (Sec ι) := dsComparison (fibCompar W Q)

/-- The algebraic direct sum of the compactly supported smooth cores. -/
def secCore : Submodule ℂ (Sec ι) := dsCore (fun _ : ι => ccDomain ℝ)

/-- The fibrewise Hamiltonian on the core. -/
def secDiag : secCore (ι := ι) →ₗ[ℂ] Sec ι := dsOp (fun a => W.ham (Q.sig a))

theorem secCore_le_dom : secCore (ι := ι) ≤ (secN W Q).dom := by
  rintro x ⟨hfin, hmem⟩
  refine ⟨fun a => W.core_le_dom (Q.sig a) (Q.sig_nonneg a) (hmem a), ?_⟩
  refine memLp_of_finite_support (Set.Finite.subset hfin fun a ha => ?_)
  simp only [Set.mem_setOf_eq] at ha ⊢
  intro h0
  refine ha ?_
  rw [opTot_of_mem _ (W.core_le_dom (Q.sig a) (Q.sig_nonneg a) (hmem a))]
  have hz : (⟨(x : ∀ _ : ι, L2R) a, W.core_le_dom (Q.sig a) (Q.sig_nonneg a) (hmem a)⟩ :
      (fibCompar W Q a).dom) = 0 := Subtype.ext h0
  rw [hz, map_zero]

theorem secN_core (p : secCore (ι := ι)) :
    (secN W Q).op ⟨(p : Sec ι), secCore_le_dom W Q p.2⟩ = secDiag W Q p := by
  refine lp.ext (funext fun a => ?_)
  have hcc : (p : ∀ _ : ι, L2R) a ∈ ccDomain ℝ := p.2.2 a
  have hd : (p : ∀ _ : ι, L2R) a ∈ (fibCompar W Q a).dom :=
    W.core_le_dom (Q.sig a) (Q.sig_nonneg a) hcc
  change opTot (fibCompar W Q a).op ((p : Sec ι) a) = _
  rw [opTot_of_mem _ hd]
  exact W.comparison_core (Q.sig a) (Q.sig_nonneg a) ⟨_, hcc⟩ hd

/-- **The algebraic direct sum of the compactly supported smooth cores is a graph core** for
the lifted Friedrichs extension.  Fibrewise essential self-adjointness of the scalaron
operator with the full exponential wall glues to the direct sum, and essential
self-adjointness on a subspace is exactly what makes it a graph core. -/
theorem secN_isGraphCore : IsGraphCore (secN W Q) (secCore (ι := ι)) :=
  isGraphCore_of_esa (secN W Q) (secCore (ι := ι)) (secCore_le_dom W Q) (secDiag W Q)
    (secN_core W Q)
    (dsOp_essentiallySelfAdjointOn _ fun a => W.ham_esa (Q.sig a) (Q.sig_nonneg a))

end

end BookProof.ScalaronOuterFockFL
