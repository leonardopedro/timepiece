import BookProof.Phi4.ChapterScalarOuter

/-!
# Positivity of the scalar Hamiltonian on symmetric outer sectors

The one-particle energy pairing is a sum of inner products. Tensoring each
factor with the other particle slots gives the same identity for entangled
polynomial states. Taking a diagonal yields positivity on every outer sector.
-/
namespace BookProof.Phi4.Model

open TensorCore SecondQuantizationCore FockStatistics ReducedEsa GraphCore
open YangMillsNonAbelianEsa YangMillsHermite YangMillsFriedrichs HermiteProductCore
open FarisLavine FriedrichsExtension EsaClosure
open scoped TensorProduct InnerProductSpace

noncomputable section
variable {d k r : ℕ} (M : Model d k r)

private abbrev fieldDom (d : ℕ) := domSpace (L2dSpace d) polyGaussCore

private def factor : Fin k ⊕ Fin r → polyGaussCore (d := d) →ₗ[ℂ] L2d d :=
  Sum.elim (fun i => polyGaussCore.subtype.comp ((coreRepPoly d).op (momOp (M.momentum i))))
    (fun j => polyGaussCore.subtype.comp ((coreRepPoly d).op (mulOp (M.form j))))

private theorem inner_pair (x y : polyGaussCore (d := d)) :
    inner ℂ (x : L2d d) (M.innerHam y) = (1/2 : ℂ) *
      ∑ i, inner ℂ (factor M i x) (factor M i y) := by
  rw [innerHam, weylPoly, weylOp_apply, inner_smul_right, inner_add_right, inner_sum, inner_sum]
  conv_rhs => arg 2; rw [Fintype.sum_sum_type]
  have hpi (i : Fin k) := (coreRepPoly d).symmetricOn_op
    (momOp_polySym (M.momentum i)) x ((coreRepPoly d).op (momOp (M.momentum i)) y)
  have hf (j : Fin r) := (coreRepPoly d).symmetricOn_op
    (mulOp_polySym (M.real_form j)) x ((coreRepPoly d).op (mulOp (M.form j)) y)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hpi hf
  simp only [factor, Sum.elim_inl, Sum.elim_inr, LinearMap.comp_apply, Submodule.subtype_apply,
    hpi, hf, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]

private def slot : ∀ (n : ℕ), Fin n → (Fin k ⊕ Fin r) →
    ((fieldDom d).pow n).carrier →ₗ[ℂ] ((L2dSpace d).pow n).carrier
  | 0, i => i.elim0
  | n+1, i => Fin.cases
      (fun j => TensorProduct.map (factor M j) (inclPow (L2dSpace d) polyGaussCore n).toLinearMap)
      (fun s j => TensorProduct.map polyGaussCore.subtype (slot n s j)) i

private theorem sector_pair (n : ℕ) (x y : ((fieldDom d).pow n).carrier) :
    inner ℂ (inclPow (L2dSpace d) polyGaussCore n x)
      (derPow (L2dSpace d) polyGaussCore M.innerHam n y) =
    (1/2 : ℂ) * ∑ s, ∑ j, inner ℂ (slot M n s j x) (slot M n s j y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x z hx hz =>
      simp only [map_add, inner_add_left, hx, hz, Finset.sum_add_distrib, mul_add]
    | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz =>
        simp only [map_add, inner_add_right, hy, hz, Finset.sum_add_distrib, mul_add]
      | tmul c e =>
        change polyGaussCore (d := d) at a c
        rw [inclPow_tmul, derPow_tmul, inner_add_right, TensorProduct.inner_tmul,
          TensorProduct.inner_tmul, Fin.sum_univ_succ]
        change _ = (1/2 : ℂ) * ((∑ j, inner ℂ
          ((factor M j a) ⊗ₜ[ℂ] inclPow (L2dSpace d) polyGaussCore n b)
          ((factor M j c) ⊗ₜ[ℂ] inclPow (L2dSpace d) polyGaussCore n e)) +
          ∑ s, ∑ j, inner ℂ ((a : L2d d) ⊗ₜ[ℂ] slot M n s j b)
            ((c : L2d d) ⊗ₜ[ℂ] slot M n s j e))
        simp only [TensorProduct.inner_tmul, LinearIsometry.inner_map_map]
        change inner ℂ (a : L2d d) (M.innerHam c) * inner ℂ b e +
          inner ℂ (a : L2d d) (c : L2d d) * inner ℂ
          (inclPow (L2dSpace d) polyGaussCore n b)
          (derPow (L2dSpace d) polyGaussCore M.innerHam n e) = _
        rw [inner_pair M a c, ih b e]
        rw [← Finset.sum_mul]
        have pull (q : ℂ) (f : Fin n → (Fin k ⊕ Fin r) → ℂ) :
            (∑ i, ∑ j, q * f i j) = q * ∑ i, ∑ j, f i j := by simp only [Finset.mul_sum]
        rw [pull (inner ℂ (a : L2d d) (c : L2d d))
          (fun i j => inner ℂ (slot M n i j b) (slot M n i j e))]
        ring


private theorem sector_nonneg (n : ℕ)
    (x : redDom (cbosonicProj (L2dSpace d) n) (fockSectorDom (L2dSpace d) polyGaussCore n)) :
    0 ≤ quadForm (cbosonicSectorOp (L2dSpace d) polyGaussCore M.innerHam n) x := by
  let Hs := L2dSpace d
  let D := polyGaussCore (d := d)
  let v := redIncl (cbosonicProj Hs n) (fockSectorDom Hs D n) x
  change 0 ≤ (inner ℂ (v : fockSector Hs n) (fockSectorOp Hs D M.innerHam n v)).re
  obtain ⟨z, hz, he⟩ := v.property
  rw [show fockSectorOp Hs D M.innerHam n v = sectorEmb Hs n
      (sectorOp Hs D M.innerHam n ⟨z, hz⟩) from pushOp_apply _ _ _ _ he.symm, ← he]
  change 0 ≤ (inner ℂ (sectorEmb Hs n z) (sectorEmb Hs n _)).re
  rw [LinearIsometry.inner_map_map]
  obtain ⟨s, hs⟩ := hz
  rw [sectorOp_apply Hs D M.innerHam n _ s hs.symm, ← hs]
  change 0 ≤ (inner ℂ (inclPow (L2dSpace d) polyGaussCore n s)
    (derPow (L2dSpace d) polyGaussCore M.innerHam n s)).re
  rw [sector_pair M n s s]
  rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
  simp only [Complex.re_sum]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => inner_self_nonneg (𝕜 := ℂ))


theorem outer_nonneg (x : hbosonicFockDom (L2dSpace d) polyGaussCore) :
    0 ≤ quadForm M.outerHam x :=
  QgOuterFock.dsOp_quadForm_nonneg _ (sector_nonneg M) x

theorem outer_positive_extension :
    ∃ (D : Submodule ℂ (hbosonicFock (L2dSpace d))) (A : D →ₗ[ℂ] hbosonicFock (L2dSpace d)),
      IsPositiveSelfAdjointExtension M.outerHam A :=
  friedrichs_extension_exists_of_complete_explicit
    ⟨_, M.outerHam, M.outer_symmetric, M.outer_nonneg⟩ (outerCore_dense d)

theorem outer_closure_nonneg (x : clDom M.outerHam) :
    0 ≤ quadForm (clExt M.outerHam (outerCore_dense d) M.outer_symmetric) x := by
  obtain ⟨D, A, hA⟩ := M.outer_positive_extension
  obtain ⟨hD, hval⟩ := positiveExtension_eq_closure_of_esa (outerCore_dense d) M.outer_symmetric
    M.outer_esa hA
  have hx : (x : hbosonicFock (L2dSpace d)) ∈ D := hD.symm ▸ x.property
  simpa only [quadForm, hval x hx x.property] using hA.2.2.1 ⟨x, hx⟩

/-- The closed nested Hamiltonian attains its lower bound zero in the unit outer vacuum. -/
theorem vacuum_ground :
    ∃ Ω : clDom M.outerHam, ‖(Ω : hbosonicFock (L2dSpace d))‖ = 1 ∧
      clExt M.outerHam (outerCore_dense d) M.outer_symmetric Ω = 0 ∧
      ∀ x, 0 ≤ quadForm (clExt M.outerHam (outerCore_dense d) M.outer_symmetric) x :=
  ⟨⟨vacuum d, coe_mem_clDom M.outerHam (vacuum d)⟩, vacuum_norm d,
    (clExt_extends M.outerHam (outerCore_dense d) M.outer_symmetric _).trans M.vacuum_energy_zero,
    M.outer_closure_nonneg⟩

end
end BookProof.Phi4.Model
