/-
prove2.me platform library module `Definitions.Def_TeschlQM_Free_freeHamiltonian`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Free_freeHamiltonian.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlQM.Free

open MeasureTheory FourierTransform

/-- The maximal domain `{φ ∈ L²(ℝⁿ) | g φ ∈ L²(ℝⁿ)}` of the multiplication operator by a function
`g : ℝⁿ → ℂ` (Teschl (7.24), p. 167, for `g(p) = p²`). -/
noncomputable def mulDomain (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℂ) :
    Submodule ℂ (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) where
  carrier := {φ | MemLp (fun x => g x * φ x) 2 volume}
  add_mem' := by
    intro a b ha hb
    refine (ha.add hb).ae_eq ?_
    filter_upwards [Lp.coeFn_add a b] with x hx
    simp only [Pi.add_apply, hx, mul_add]
  zero_mem' := by
    refine (MemLp.zero (ε := ℂ)).ae_eq ?_
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))] with x hx
    simp only [Pi.zero_apply, hx, mul_zero]
  smul_mem' := by
    intro c a ha
    refine (ha.const_smul c).ae_eq ?_
    filter_upwards [Lp.coeFn_smul c a] with x hx
    simp only [Pi.smul_apply, hx, smul_eq_mul]
    ring

theorem mem_mulDomain {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℂ}
    {φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))} :
    φ ∈ mulDomain n g ↔ MemLp (fun x => g x * φ x) 2 volume :=
  Iff.rfl

/-- Teschl (7.24), p. 167: the maximally defined multiplication operator by `g` in `L²(ℝⁿ)`,
`(g φ)(x) = g(x) φ(x)` with domain `{φ ∈ L² | g φ ∈ L²}`. -/
noncomputable def mulOp (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℂ) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →ₗ.[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) where
  domain := mulDomain n g
  toFun :=
    { toFun := fun φ => MemLp.toLp (fun x => g x * (φ : Lp ℂ 2 volume) x) (mem_mulDomain.1 φ.2)
      map_add' := by
        intro a b
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_add (a : Lp ℂ 2 _) (b : Lp ℂ 2 _)] with x hx
        simp only [Submodule.coe_add, Pi.add_apply, hx, mul_add]
      map_smul' := by
        intro c a
        rw [← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_smul c (a : Lp ℂ 2 _)] with x hx
        simp only [SetLike.val_smul, Pi.smul_apply, hx, smul_eq_mul, RingHom.id_apply]
        ring }

/-- Teschl (7.20)–(7.24), pp. 167–168: the **free Schrödinger operator** `H₀ = -Δ` on
`L²(ℝⁿ)` with domain `𝔇(H₀) = H²(ℝⁿ)`, defined as the Fourier conjugate of the maximally defined
multiplication operator by the symbol of `-Δ`: `H₀ = 𝓕⁻¹ ∘ M ∘ 𝓕` with domain
`{ψ ∈ L² | 𝓕ψ ∈ 𝔇(M)}`.

Here `𝓕` is Mathlib's unitary Fourier transform on `L²(ℝⁿ)` (normalization `e^{-2πi⟪x, ξ⟫}`),
under which `-Δ` is multiplication by `4π²‖ξ‖²`; this is the same operator as Teschl's
`F⁻¹ p² F` with his normalization (7.3), since `-Δ` does not depend on the normalization, and the
domain `{ψ | ‖ξ‖² 𝓕ψ(ξ) ∈ L²}` is Teschl's `H²(ℝⁿ) = {ψ ∈ L² | |p|² ψ̂(p) ∈ L²}` (7.12). -/
noncomputable def freeHamiltonian (n : ℕ) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →ₗ.[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) where
  domain := (mulDomain n fun ξ => ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)).comap
    (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) ℂ).toLinearEquiv.toLinearMap
  toFun :=
    (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) ℂ).symm.toLinearEquiv.toLinearMap ∘ₗ
      (mulOp n fun ξ => ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)).toFun ∘ₗ
        LinearMap.codRestrict (mulDomain n fun ξ => ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ))
          ((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) ℂ).toLinearEquiv.toLinearMap ∘ₗ
            Submodule.subtype _)
          (fun ψ => Submodule.mem_comap.1 ψ.2)

end TeschlQM.Free
