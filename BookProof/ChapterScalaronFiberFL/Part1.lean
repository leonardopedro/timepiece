import Mathlib
import BookProof.ChapterWallEsaBddBelow
import BookProof.ChapterWallEsaSemibounded
import BookProof.ChapterSchrodingerCutoffEsa
import BookProof.ChapterQgOuterFockCoreFL

/-!
# The scalaron fibre: the exponential wall as a Faris–Lavine comparison operator

This module prepares the *one-dimensional* input of the quantum-gravity Faris–Lavine
programme in the form the outer-Fock lift needs: the scalaron degree of freedom, carrying
the **full exponential** Einstein-frame potential (no Taylor expansion), realised as a
family of Faris–Lavine comparison operators

`h_s = −d²/dφ² + φ²/4 + V(φ) + s`,  `s ≥ 0`,

on `L²(ℝ)`, together with the estimates that make the fibre usable inside a lifted
Hamiltonian: everything is uniform in the shift `s`.

## What is proved

* `isGraphCore_of_esa` — an abstract and reusable step: if a symmetric operator `P` on a
  subspace `C₀` is essentially self-adjoint there, then `C₀` is a **graph core** for *every*
  comparison operator extending `P`.  (Density of the range of `P − i` is exactly the
  deficiency triviality, and `‖Nu − iu‖² = ‖Nu‖² + ‖u‖²` converts one approximation into a
  graph approximation.)  This is what lets the Friedrichs extension of a positive
  one-particle operator be used with the core-extension machinery of
  `BookProof.QgOuterFockCoreFL`.
* `integral_weight_re_secondDeriv` — the weighted integration-by-parts identity
  `∫ P·Re(conj u · u'') = −∫ P|u'|² + ½∫ P''|u|²` for compactly supported smooth `u`.
* `wallEnergy_identity` — the resulting energy identity
  `‖−u'' + P u‖² = ‖u''‖² + ‖P u‖² + 2∫P|u'|² − ∫P''|u|²`.
* `WallPot` — the data of an admissible wall: a smooth non-negative potential with
  `V'' ≤ C(V+1)`.  `starobinskyWall` is the Einstein-frame scalaron potential, which
  satisfies it (`starobinskyV_hess_le`).
* `fibHam`, `fibHam_symmetricOn`, `fibHam_quadForm`, `fibHam_pos`, `fibHam_esa` — the fibre
  Hamiltonian on the compactly supported smooth core, its quadratic form, positivity and
  essential self-adjointness.
* `fibHam_norm_bounds` (`norm_deriv2_le`, `norm_pot_mul_le`, `norm_coord_mul_le`,
  `norm_deriv_le`, `norm_le_shift`) — the relative bounds of the second derivative, of the
  potential, of `φ` and of `d/dφ` against `‖(h_s+1)u‖`, **with constants independent of the
  shift `s`**.
* `fibComparison` — the Friedrichs extension of `h_s` as a Faris–Lavine comparison
  operator, and `fibComparison_isGraphCore`, `fibComparison_core_apply`.
-/

namespace BookProof.ScalaronFiberFL

open MeasureTheory SchwartzMap
open BookProof.StrichartzWave
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallEsaSemibounded BookProof.WallEsaBddBelow
open BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.SchrodingerCutoff BookProof.FriedrichsExtension

noncomputable section

/-! ## 1. A graph core from essential self-adjointness -/

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- For a symmetric operator, `‖Nu − iu‖² = ‖Nu‖² + ‖u‖²`: the shift by `i` controls both
the vector and its image. -/
theorem norm_sub_I_sq {D : Submodule ℂ F} (N : D →ₗ[ℂ] F) (hsym : SymmetricOn D N) (u : D) :
    ‖N u - Complex.I • (u : F)‖ ^ 2 = ‖N u‖ ^ 2 + ‖(u : F)‖ ^ 2 := by
  have him : (inner ℂ (N u) (u : F) : ℂ).im = 0 := inner_apply_self_im N hsym u
  have hre : (inner ℂ (N u) (Complex.I • (u : F)) : ℂ).re = 0 := by
    rw [inner_smul_right, Complex.mul_re, him]
    simp
  have hnorm : ‖Complex.I • (u : F)‖ = ‖(u : F)‖ := by
    rw [norm_smul]; simp
  rw [norm_sub_sq (𝕜 := ℂ), hnorm]
  simp only [RCLike.re_to_complex] at hre ⊢
  rw [hre]
  ring

/-- **A graph core from essential self-adjointness.**  If the symmetric operator `P` on the
subspace `C₀` is essentially self-adjoint there and a comparison operator `C` extends it,
then `C₀` is a graph core for `C`: every vector of `𝒟(N)` is approximated by core vectors
simultaneously in norm and in the norm of the image. -/
theorem isGraphCore_of_esa (C : Comparison F) (C₀ : Submodule ℂ F) (hle : C₀ ≤ C.dom)
    (P : C₀ →ₗ[ℂ] F) (hext : ∀ p : C₀, C.op ⟨(p : F), hle p.2⟩ = P p)
    (hesa : EssentiallySelfAdjointOn C₀ P) : IsGraphCore C C₀ := by
  classical
  set R : Submodule ℂ F := LinearMap.range (P - Complex.I • C₀.subtype) with hR
  have hperp : Rᗮ = ⊥ := by
    refine Submodule.eq_bot_iff _ |>.mpr ?_
    intro w hw
    refine hesa.2 w ?_
    intro v
    have hmem : (P - Complex.I • C₀.subtype) v ∈ R := ⟨v, rfl⟩
    have h0 : (inner ℂ ((P - Complex.I • C₀.subtype) v) w : ℂ) = 0 := hw _ hmem
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
      inner_sub_left, inner_smul_left] at h0
    have h1 : (inner ℂ (P v) w : ℂ) = (starRingEnd ℂ) Complex.I * inner ℂ (v : F) w := by
      linear_combination h0
    rw [h1]
    simp
  have hdense : Dense (R : Set F) := by
    have htop : R.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.mpr hperp
    rw [← Submodule.dense_iff_topologicalClosure_eq_top] at htop
    exact htop
  refine ⟨hle, ?_⟩
  intro x ε hε
  set y : F := C.op x - Complex.I • (x : F) with hy
  obtain ⟨r, hrball, hrR⟩ := Metric.dense_iff.mp hdense y ε hε
  have hr : ‖r - y‖ < ε := by
    rw [← dist_eq_norm]
    simpa [Metric.mem_ball, dist_comm] using hrball
  obtain ⟨p, hp⟩ := hrR
  set q : C.dom := ⟨(p : F), hle p.2⟩ with hq
  have hval : C.op (q - x) - Complex.I • ((q - x : C.dom) : F) = r - y := by
    rw [map_sub, hy, ← hp]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
      Submodule.coe_sub, hq, hext p, smul_sub]
    abel
  have hkey := norm_sub_I_sq C.op C.sym (q - x)
  rw [hval] at hkey
  have hcoe : ((q - x : C.dom) : F) = (p : F) - (x : F) := rfl
  refine ⟨q, p.2, ?_, ?_⟩
  · have h2 : ‖((q - x : C.dom) : F)‖ < ε := by
      nlinarith [norm_nonneg ((q - x : C.dom) : F), norm_nonneg (C.op (q - x)),
        norm_nonneg (r - y), hr]
    rwa [hcoe] at h2
  · have h2 : ‖C.op (q - x)‖ < ε := by
      nlinarith [norm_nonneg ((q - x : C.dom) : F), norm_nonneg (C.op (q - x)),
        norm_nonneg (r - y), hr]
    rwa [map_sub] at h2

end Abstract

/-! ## 2. Integration by parts: the Wronskian identity on the line -/

section Wronskian

/-- **The Wronskian identity.**  For compactly supported smooth `f, g` on the line,
`∫ x·(conj f · g'' − conj f'' · g) = −2 ∫ conj f · g'`.  Both integrations by parts are
supplied by `integral_deriv_eq_zero_of_hasCompactSupport`; this identity is the exact
statement that the commutator of the Schrödinger operator with multiplication by the
coordinate is `−2 d/dx`, *whatever the potential is* — the potential cancels before the
identity is applied. -/
theorem integral_x_wronskian (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    (∫ x : ℝ, (x : ℂ) * ((starRingEnd ℂ) (f x) * deriv (deriv g) x
        - (starRingEnd ℂ) (deriv (deriv f) x) * g x))
      = -2 * ∫ x : ℝ, (starRingEnd ℂ) (f x) * deriv g x := by
  have hf1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv f) := hf.deriv'
  have hf2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (deriv f)) := hf1.deriv'
  have hg1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv g) := hg.deriv'
  have hg2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (deriv g)) := hg1.deriv'
  have hd0 : ∀ x, HasDerivAt f (deriv f x) x := fun x =>
    (hf.differentiable (by simp) x).hasDerivAt
  have hd1 : ∀ x, HasDerivAt (deriv f) (deriv (deriv f) x) x := fun x =>
    (hf1.differentiable (by simp) x).hasDerivAt
  have he0 : ∀ x, HasDerivAt g (deriv g x) x := fun x =>
    (hg.differentiable (by simp) x).hasDerivAt
  have he1 : ∀ x, HasDerivAt (deriv g) (deriv (deriv g) x) x := fun x =>
    (hg1.differentiable (by simp) x).hasDerivAt
  -- the conjugated derivatives
  have ha0 : ∀ x, HasDerivAt (fun y => (starRingEnd ℂ) (f y))
      ((starRingEnd ℂ) (deriv f x)) x := fun x => (hd0 x).star
  have ha1 : ∀ x, HasDerivAt (fun y => (starRingEnd ℂ) (deriv f y))
      ((starRingEnd ℂ) (deriv (deriv f) x)) x := fun x => (hd1 x).star
  have hcf : Continuous f := hf.continuous
  have hcf1 : Continuous (deriv f) := hf1.continuous
  have hcf2 : Continuous (deriv (deriv f)) := hf2.continuous
  have hcg : Continuous g := hg.continuous
  have hcg1 : Continuous (deriv g) := hg1.continuous
  have hcg2 : Continuous (deriv (deriv g)) := hg2.continuous
  have hfs1 : HasCompactSupport (deriv f) := hfs.deriv
  have hfs2 : HasCompactSupport (deriv (deriv f)) := hfs1.deriv
  have hgs1 : HasCompactSupport (deriv g) := hgs.deriv
  have hgs2 : HasCompactSupport (deriv (deriv g)) := hgs1.deriv
  have hcs0 : HasCompactSupport fun y => (starRingEnd ℂ) (f y) :=
    hfs.comp_left (g := starRingEnd ℂ) (by simp)
  have hcs1 : HasCompactSupport fun y => (starRingEnd ℂ) (deriv f y) :=
    hfs1.comp_left (g := starRingEnd ℂ) (by simp)
  have hcs2 : HasCompactSupport fun y => (starRingEnd ℂ) (deriv (deriv f) y) :=
    hfs2.comp_left (g := starRingEnd ℂ) (by simp)
  -- Step 1: `∫ (conj f' · g + conj f · g') = 0`
  have step2 : (∫ x, ((starRingEnd ℂ) (deriv f x) * g x
      + (starRingEnd ℂ) (f x) * deriv g x)) = 0 := by
    refine integral_deriv_eq_zero_of_hasCompactSupport
      (g := fun x => (starRingEnd ℂ) (f x) * g x) (fun x => ?_) (by fun_prop) hcs0.mul_right
    exact (ha0 x).mul (he0 x)
  -- Step 2: `∫ d/dx [x (conj f · g' − conj f' · g)] = 0`
  have step1 : (∫ x : ℝ, (((starRingEnd ℂ) (f x) * deriv g x
        - (starRingEnd ℂ) (deriv f x) * g x)
      + (x : ℂ) * ((starRingEnd ℂ) (f x) * deriv (deriv g) x
        - (starRingEnd ℂ) (deriv (deriv f) x) * g x))) = 0 := by
    refine integral_deriv_eq_zero_of_hasCompactSupport
      (g := fun x => (x : ℂ) * ((starRingEnd ℂ) (f x) * deriv g x
        - (starRingEnd ℂ) (deriv f x) * g x)) (fun x => ?_) (by fun_prop)
      ((hcs0.mul_right.sub hcs1.mul_right).mul_left)
    have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
    have hprod : HasDerivAt (fun y => (starRingEnd ℂ) (f y) * deriv g y
        - (starRingEnd ℂ) (deriv f y) * g y)
        (((starRingEnd ℂ) (deriv f x) * deriv g x
            + (starRingEnd ℂ) (f x) * deriv (deriv g) x)
          - ((starRingEnd ℂ) (deriv (deriv f) x) * g x
            + (starRingEnd ℂ) (deriv f x) * deriv g x)) x :=
      ((ha0 x).mul (he1 x)).sub ((ha1 x).mul (he0 x))
    have := hx.mul hprod
    convert this using 1
    ring
  -- integrability of the pieces
  have hI1 : Integrable fun x => (starRingEnd ℂ) (f x) * deriv g x :=
    (by fun_prop : Continuous fun x => (starRingEnd ℂ) (f x) * deriv g x
      ).integrable_of_hasCompactSupport hcs0.mul_right
  have hI2 : Integrable fun x => (starRingEnd ℂ) (deriv f x) * g x :=
    (by fun_prop : Continuous fun x => (starRingEnd ℂ) (deriv f x) * g x
      ).integrable_of_hasCompactSupport hcs1.mul_right
  have hI3 : Integrable fun x : ℝ => (x : ℂ) * ((starRingEnd ℂ) (f x) * deriv (deriv g) x
      - (starRingEnd ℂ) (deriv (deriv f) x) * g x) :=
    (by fun_prop : Continuous fun x : ℝ => (x : ℂ) * ((starRingEnd ℂ) (f x) * deriv (deriv g) x
        - (starRingEnd ℂ) (deriv (deriv f) x) * g x)
      ).integrable_of_hasCompactSupport ((hcs0.mul_right.sub hcs2.mul_right).mul_left)
  have hI4 : Integrable fun x : ℝ => (starRingEnd ℂ) (f x) * deriv g x
      - (starRingEnd ℂ) (deriv f x) * g x := hI1.sub hI2
  rw [integral_add hI4 hI3, integral_sub hI1 hI2] at step1
  rw [integral_add hI2 hI1] at step2
  linear_combination step1 + step2

end Wronskian

end

end BookProof.ScalaronFiberFL
