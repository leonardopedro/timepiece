import Mathlib
import BookProof.ChapterSchrodingerCutoffEsa.Part1

/-!
# The Simader–Faris–Lavine cutoff method for `-d²/dx² + V`

This module carries out, in one space dimension and with no unproved input, the
**cutoff / commutator energy argument** for essential self-adjointness of a
Schrödinger operator `H = -Δ + V` with a potential that is allowed to grow
arbitrarily fast — the motivating example being the non-polynomial
`V(x) = eˣ + e⁻ˣ`, for which none of the polynomial-growth criteria apply.

The mathematical content is the classical energy estimate: if `u` is a
square-integrable classical solution of `-u'' + V u = z u` with
`Re z + 1 ≤ V` pointwise, then testing the equation against `χ_R² ū`,
integrating by parts once, and absorbing the cross term by Young's inequality
gives

  `∫_{[-R,R]} |u|² ≤ ∫ χ_R² (V - Re z) |u|² ≤ (2C²/R²) ‖u‖²_{L²}`,

where `C` bounds `|χ'|` for a fixed smooth cutoff `χ` equal to `1` on `[-1,1]`
and supported in `[-2,2]`, and `χ_R(x) = χ(x/R)`.  Letting `R → ∞` forces
`u = 0`.  Applied to `z = ± i` — whose real part is `0`, so that the hypothesis
`Re z + 1 ≤ V` only asks `V ≥ 1` — this says exactly that the classical
deficiency spaces of `H` are trivial, which is the analytic heart of essential
self-adjointness.

## Contents

* `integral_deriv_eq_zero_of_hasCompactSupport` — the one-dimensional
  integration-by-parts engine: the integral over `ℝ` of the derivative of a
  compactly supported `C¹` function vanishes.
* The section "the cutoff family" — a concrete smooth cutoff `chi` built from
  Mathlib's `ContDiffBump`, its basic properties, the gradient bound
  `exists_deriv_chi_bound`, and the rescaled family `exists_scaled_cutoff`
  (Milestone 3 of the plan: `|χ_R'| ≤ C/R`).
* `hasDerivAt_reInner` — the derivative of the energy density
  `x ↦ Re(conj (u x) · u'(x))`.
* `schrodingerOp`, `integral_conj_secondDeriv_comm` and `schrodingerOp_symmetric`
  — Milestone 2: the operator `H f = -f'' + V f` on the compactly supported
  twice differentiable core, and its Hermitian symmetry there, for an arbitrary
  real continuous `V` (no growth restriction).
* `cutoff_energy_core` — Milestone 4 in its sharpest form: under the weaker
  hypothesis `Re z ≤ V` it bounds *both* the potential energy
  `∫_{[-R,R]} (V - Re z)|u|²` and the Dirichlet energy `∫_{[-R,R]} |u'|²` by a
  multiple of `‖u‖²_{L²}/R²`.
* `cutoff_energy_estimate` — Milestone 4: the estimate displayed above, for an
  arbitrary continuous `V` and arbitrary `z` with `Re z + 1 ≤ V`.
* `l2_classical_solution_eq_zero` — Milestone 5: the limit `R → ∞`, giving
  `u = 0`.
* `l2_classical_solution_eq_zero_of_nonneg` — the same conclusion under the
  weaker hypothesis `Re z ≤ V`, obtained by running the limit on the Dirichlet
  term instead: `u' ≡ 0`, so `u` is constant, and a constant in `L²(ℝ)` is `0`.
* `laplacian_deficiency_trivial` / `..._I` / `..._negI` — the `V = 0`
  specialisation: the free Laplacian `-d²/dx²` on the line has no nonzero
  square-integrable classical solution of `-u'' = z u` when `Re z ≤ 0`, in
  particular for `z = ± i`.
* `Vexp`, `two_le_Vexp` and `schrodinger_exp_deficiency_trivial` /
  `schrodinger_exp_deficiency_trivial_I` / `..._negI` — the motivating
  application: for `V(x) = eˣ + e⁻ˣ` the operator `-d²/dx² + V` has no nonzero
  square-integrable classical solution of `H u = ± i u`.

Nothing here is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.SchrodingerCutoff

open MeasureTheory Filter Complex
/-! ## Milestone 5: the limit `R → ∞` -/

/-- **The main vanishing theorem.**  A square-integrable classical solution of
`-u'' + V u = z u` on the line, with `Re z + 1 ≤ V` pointwise, is identically
zero. -/
theorem l2_classical_solution_eq_zero
    (V : ℝ → ℝ) (hV : Continuous V) (z : ℂ)
    (u u' u'' : ℝ → ℂ)
    (h1 : ∀ x, HasDerivAt u (u' x) x)
    (h2 : ∀ x, HasDerivAt u' (u'' x) x)
    (heq : ∀ x, -u'' x + (V x : ℂ) * u x = z * u x)
    (hVz : ∀ x, 1 ≤ V x - z.re)
    (hL2 : Integrable fun x => ‖u x‖ ^ 2) :
    u = 0 := by
  obtain ⟨C, hC0, hC⟩ := exists_deriv_chi_bound
  have hud : Differentiable ℝ u := fun x => (h1 x).differentiableAt
  have hucont : Continuous u := hud.continuous
  set A : ℝ := ∫ x, ‖u x‖ ^ 2 with hAdef
  have hA0 : 0 ≤ A := integral_nonneg fun x => by positivity
  -- the sets `Icc (-(n+1)) (n+1)` increase to the line
  have hmono : Monotone fun n : ℕ => Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
    intro m n hmn
    have hmn' : ((m : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hmn
    exact Set.Icc_subset_Icc (by linarith) (by linarith)
  have hunion : (⋃ n : ℕ, Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    exact Set.mem_iUnion.mpr ⟨n, ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩⟩
  have htend : Tendsto (fun n : ℕ => ∫ x in Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), ‖u x‖ ^ 2)
      atTop (nhds A) := by
    have h := tendsto_setIntegral_of_monotone (fun _ : ℕ => measurableSet_Icc) hmono
      (by rw [hunion]; exact hL2.integrableOn)
    rwa [hunion, setIntegral_univ, ← hAdef] at h
  have hbnd : Tendsto (fun n : ℕ => 2 * C ^ 2 / ((n : ℝ) + 1) ^ 2 * A) atTop (nhds 0) := by
    have hnn : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (n := 2) (by norm_num)).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have h := (tendsto_const_nhds (x := 2 * C ^ 2 * A) (f := atTop (α := ℕ))).div_atTop hnn
    refine h.congr fun n => ?_
    ring
  have hAle : A ≤ 0 := by
    refine le_of_tendsto_of_tendsto' htend hbnd fun n => ?_
    exact cutoff_energy_estimate V hV z u u' u'' h1 h2 heq hVz hL2 hC
      (by positivity)
  have hAzero : A = 0 := le_antisymm hAle hA0
  have hae : (fun x => ‖u x‖ ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hL2).mp hAzero
  have hu_ae : u =ᵐ[volume] 0 := by
    filter_upwards [hae] with x hx
    have : ‖u x‖ ^ 2 = 0 := hx
    have : ‖u x‖ = 0 := by nlinarith [norm_nonneg (u x)]
    simpa using this
  exact (Continuous.ae_eq_iff_eq volume hucont continuous_const).mp hu_ae

/-- A continuous nonnegative function on the line whose integral over every
interval `[-(n+1), n+1]` vanishes is identically zero. -/
theorem eq_zero_of_setIntegral_Icc_eq_zero {f : ℝ → ℝ} (hf : Continuous f)
    (h0 : ∀ x, 0 ≤ f x)
    (h : ∀ n : ℕ, ∫ x in Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), f x = 0) :
    f = 0 := by
  have key : ∀ n : ℕ, ∀ᵐ x, x ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) → f x = 0 := by
    intro n
    have hres := (setIntegral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => h0 x) hf.integrableOn_Icc).mp (h n)
    exact (ae_restrict_iff' measurableSet_Icc).mp hres
  have hall : ∀ᵐ x, ∀ n : ℕ, x ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) → f x = 0 :=
    ae_all_iff.mpr key
  have hae : f =ᵐ[volume] 0 := by
    filter_upwards [hall] with x hx
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    exact hx n ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  exact (Continuous.ae_eq_iff_eq volume hf continuous_const).mp hae

/-- **The vanishing theorem under the weaker hypothesis `Re z ≤ V`.**  Here the
potential-energy term need not control `|u|²` itself, so instead we run the
limit on the Dirichlet term: `∫_{[-R,R]} |u'|² ≤ (4C²/R²) ∫_ℝ |u|² → 0` forces
`u' ≡ 0`, hence `u` is constant, and a constant in `L²(ℝ)` is zero. -/
theorem l2_classical_solution_eq_zero_of_nonneg
    (V : ℝ → ℝ) (hV : Continuous V) (z : ℂ)
    (u u' u'' : ℝ → ℂ)
    (h1 : ∀ x, HasDerivAt u (u' x) x)
    (h2 : ∀ x, HasDerivAt u' (u'' x) x)
    (heq : ∀ x, -u'' x + (V x : ℂ) * u x = z * u x)
    (hVz : ∀ x, 0 ≤ V x - z.re)
    (hL2 : Integrable fun x => ‖u x‖ ^ 2) :
    u = 0 := by
  obtain ⟨C, hC0, hC⟩ := exists_deriv_chi_bound
  have hud : Differentiable ℝ u := fun x => (h1 x).differentiableAt
  have hu'd : Differentiable ℝ u' := fun x => (h2 x).differentiableAt
  have hu'cont : Continuous u' := hu'd.continuous
  have hg : Continuous fun x => ‖u' x‖ ^ 2 := by fun_prop
  set A : ℝ := ∫ x, ‖u x‖ ^ 2 with hAdef
  have hA0 : 0 ≤ A := integral_nonneg fun x => by positivity
  have hzero : ∀ n : ℕ, ∫ x in Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), ‖u' x‖ ^ 2 = 0 := by
    intro n
    set R0 : ℝ := (n : ℝ) + 1 with hR0def
    have hR0pos : (0 : ℝ) < R0 := by positivity
    have hle : ∀ m : ℕ, (∫ x in Set.Icc (-R0) R0, ‖u' x‖ ^ 2)
        ≤ 4 * C ^ 2 / ((m : ℝ) + R0) ^ 2 * A := by
      intro m
      have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hRpos : (0 : ℝ) < (m : ℝ) + R0 := by linarith
      have hsub : Set.Icc (-R0) R0 ⊆ Set.Icc (-((m : ℝ) + R0)) ((m : ℝ) + R0) :=
        Set.Icc_subset_Icc (by linarith) (by linarith)
      have hstep := setIntegral_mono_set (hg.integrableOn_Icc (μ := volume))
        (Filter.Eventually.of_forall fun x => by positivity) hsub.eventuallyLE
      exact le_trans hstep
        (cutoff_energy_core V hV z u u' u'' h1 h2 heq hVz hL2 hC hRpos).2
    have htend : Tendsto (fun m : ℕ => 4 * C ^ 2 / ((m : ℝ) + R0) ^ 2 * A) atTop (nhds 0) := by
      have hnn : Tendsto (fun m : ℕ => ((m : ℝ) + R0) ^ 2) atTop atTop :=
        (tendsto_pow_atTop (n := 2) (by norm_num)).comp
          (tendsto_atTop_add_const_right _ R0 tendsto_natCast_atTop_atTop)
      have h := (tendsto_const_nhds (x := 4 * C ^ 2 * A) (f := atTop (α := ℕ))).div_atTop hnn
      exact h.congr fun m => by ring
    have hle0 : (∫ x in Set.Icc (-R0) R0, ‖u' x‖ ^ 2) ≤ 0 :=
      ge_of_tendsto htend (Filter.Eventually.of_forall hle)
    have hge0 : (0 : ℝ) ≤ ∫ x in Set.Icc (-R0) R0, ‖u' x‖ ^ 2 :=
      setIntegral_nonneg measurableSet_Icc fun x _ => by positivity
    linarith
  have hu'zero : (fun x => ‖u' x‖ ^ 2) = 0 :=
    eq_zero_of_setIntegral_Icc_eq_zero hg (fun x => by positivity) hzero
  have hu'0 : ∀ x, u' x = 0 := by
    intro x
    have hx : ‖u' x‖ ^ 2 = 0 := congrFun hu'zero x
    have : ‖u' x‖ = 0 := by nlinarith [norm_nonneg (u' x)]
    simpa using this
  have hconst : ∀ x, u x = u 0 :=
    fun x => is_const_of_deriv_eq_zero hud (fun y => by rw [(h1 y).deriv, hu'0 y]) x 0
  have hL2' : Integrable fun _ : ℝ => ‖u 0‖ ^ 2 := by
    refine hL2.congr ?_
    filter_upwards with x using by rw [hconst x]
  have hc : ‖u 0‖ ^ 2 = 0 := by
    rcases integrable_const_iff.mp hL2' with h | h
    · exact h
    · exact absurd h.measure_univ_lt_top (by rw [Real.volume_univ]; exact lt_irrefl _)
  have hu0 : u 0 = 0 := by
    have : ‖u 0‖ = 0 := by nlinarith [norm_nonneg (u 0)]
    simpa using this
  funext x
  simpa [hu0] using hconst x

/-- **The free Laplacian on the line has trivial deficiency spaces** (for
classical square-integrable solutions).  If `-u'' = z u` with `Re z ≤ 0` and
`u ∈ L²(ℝ)` is twice differentiable, then `u = 0`.  This is the `V = 0` case of
`l2_classical_solution_eq_zero_of_nonneg`. -/
theorem laplacian_deficiency_trivial (z : ℂ) (hz : z.re ≤ 0)
    (u u' u'' : ℝ → ℂ)
    (h1 : ∀ x, HasDerivAt u (u' x) x)
    (h2 : ∀ x, HasDerivAt u' (u'' x) x)
    (heq : ∀ x, -u'' x = z * u x)
    (hL2 : Integrable fun x => ‖u x‖ ^ 2) :
    u = 0 :=
  l2_classical_solution_eq_zero_of_nonneg (fun _ => 0) continuous_const z u u' u''
    h1 h2 (fun x => by simpa using heq x) (fun _ => by simpa using hz) hL2

/-- Deficiency index `+i` for the free Laplacian: `-u'' = i u` in `L²(ℝ)` forces
`u = 0`. -/
theorem laplacian_deficiency_trivial_I
    (u u' u'' : ℝ → ℂ)
    (h1 : ∀ x, HasDerivAt u (u' x) x)
    (h2 : ∀ x, HasDerivAt u' (u'' x) x)
    (heq : ∀ x, -u'' x = Complex.I * u x)
    (hL2 : Integrable fun x => ‖u x‖ ^ 2) :
    u = 0 :=
  laplacian_deficiency_trivial Complex.I (by simp) u u' u'' h1 h2 heq hL2

/-- Deficiency index `-i` for the free Laplacian: `-u'' = -i u` in `L²(ℝ)` forces
`u = 0`. -/
theorem laplacian_deficiency_trivial_negI
    (u u' u'' : ℝ → ℂ)
    (h1 : ∀ x, HasDerivAt u (u' x) x)
    (h2 : ∀ x, HasDerivAt u' (u'' x) x)
    (heq : ∀ x, -u'' x = -Complex.I * u x)
    (hL2 : Integrable fun x => ‖u x‖ ^ 2) :
    u = 0 :=
  laplacian_deficiency_trivial (-Complex.I) (by simp) u u' u'' h1 h2 heq hL2

/-! ## Milestone 2: the operator on the smooth compactly supported core -/

/-- The Schrödinger operator `H f = -f'' + V f` on the line. -/
noncomputable def schrodingerOp (V : ℝ → ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -deriv (deriv f) x + (V x : ℂ) * f x

theorem schrodingerOp_apply (V : ℝ → ℝ) (f f' f'' : ℝ → ℂ)
    (hf1 : ∀ x, HasDerivAt f (f' x) x) (hf2 : ∀ x, HasDerivAt f' (f'' x) x) (x : ℝ) :
    schrodingerOp V f x = -f'' x + (V x : ℂ) * f x := by
  have hfd : deriv f = f' := funext fun y => (hf1 y).deriv
  simp only [schrodingerOp, hfd, (hf2 x).deriv]

/-- Integration by parts twice: `∫ conj (f'') g = ∫ conj f g''` for compactly
supported twice differentiable data. -/
theorem integral_conj_secondDeriv_comm
    (f g f' f'' g' g'' : ℝ → ℂ)
    (hf1 : ∀ x, HasDerivAt f (f' x) x) (hf2 : ∀ x, HasDerivAt f' (f'' x) x)
    (hg1 : ∀ x, HasDerivAt g (g' x) x) (hg2 : ∀ x, HasDerivAt g' (g'' x) x)
    (hf''c : Continuous f'') (hg''c : Continuous g'')
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    (∫ x, (starRingEnd ℂ) (f'' x) * g x) = ∫ x, (starRingEnd ℂ) (f x) * g'' x := by
  have hfd : Differentiable ℝ f := fun x => (hf1 x).differentiableAt
  have hf'd : Differentiable ℝ f' := fun x => (hf2 x).differentiableAt
  have hgd : Differentiable ℝ g := fun x => (hg1 x).differentiableAt
  have hg'd : Differentiable ℝ g' := fun x => (hg2 x).differentiableAt
  have hfc : Continuous f := hfd.continuous
  have hf'c : Continuous f' := hf'd.continuous
  have hgc : Continuous g := hgd.continuous
  have hg'c : Continuous g' := hg'd.continuous
  have hf's : HasCompactSupport f' := by
    rw [show f' = deriv f from funext fun x => ((hf1 x).deriv).symm]; exact hfs.deriv
  have hg's : HasCompactSupport g' := by
    rw [show g' = deriv g from funext fun x => ((hg1 x).deriv).symm]; exact hgs.deriv
  have hconjf : HasCompactSupport fun x => (starRingEnd ℂ) (f x) :=
    hfs.comp_left (g := starRingEnd ℂ) (by simp)
  -- first integration by parts, with `k = conj f' · g`
  have hk : ∀ x, HasDerivAt (fun y => (starRingEnd ℂ) (f' y) * g y)
      ((starRingEnd ℂ) (f'' x) * g x + (starRingEnd ℂ) (f' x) * g' x) x :=
    fun x => ((hf2 x).star).mul (hg1 x)
  have hk0 := integral_deriv_eq_zero_of_hasCompactSupport hk (by fun_prop) hgs.mul_left
  -- second integration by parts, with `m = conj f · g'`
  have hm : ∀ x, HasDerivAt (fun y => (starRingEnd ℂ) (f y) * g' y)
      ((starRingEnd ℂ) (f' x) * g' x + (starRingEnd ℂ) (f x) * g'' x) x :=
    fun x => ((hf1 x).star).mul (hg2 x)
  have hm0 := integral_deriv_eq_zero_of_hasCompactSupport hm (by fun_prop) hconjf.mul_right
  -- integrability of the three pieces
  have i1 : Integrable fun x => (starRingEnd ℂ) (f'' x) * g x :=
    (by fun_prop : Continuous fun x => (starRingEnd ℂ) (f'' x) * g x)
      |>.integrable_of_hasCompactSupport hgs.mul_left
  have i2 : Integrable fun x => (starRingEnd ℂ) (f' x) * g' x :=
    (by fun_prop : Continuous fun x => (starRingEnd ℂ) (f' x) * g' x)
      |>.integrable_of_hasCompactSupport hg's.mul_left
  have i3 : Integrable fun x => (starRingEnd ℂ) (f x) * g'' x :=
    (by fun_prop : Continuous fun x => (starRingEnd ℂ) (f x) * g'' x)
      |>.integrable_of_hasCompactSupport hconjf.mul_right
  rw [integral_add i1 i2] at hk0
  rw [integral_add i2 i3] at hm0
  linear_combination (norm := module) hk0 - hm0

/-- **Symmetry of `H = -d²/dx² + V` on the smooth compactly supported core.**
This is Milestone 2 of the plan: the operator is well defined and Hermitian on
compactly supported twice differentiable functions, for any real continuous `V`
(no growth restriction whatsoever). -/
theorem schrodingerOp_symmetric (V : ℝ → ℝ) (hV : Continuous V)
    (f g f' f'' g' g'' : ℝ → ℂ)
    (hf1 : ∀ x, HasDerivAt f (f' x) x) (hf2 : ∀ x, HasDerivAt f' (f'' x) x)
    (hg1 : ∀ x, HasDerivAt g (g' x) x) (hg2 : ∀ x, HasDerivAt g' (g'' x) x)
    (hf''c : Continuous f'') (hg''c : Continuous g'')
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    (∫ x, (starRingEnd ℂ) (schrodingerOp V f x) * g x)
      = ∫ x, (starRingEnd ℂ) (f x) * schrodingerOp V g x := by
  have hfd : Differentiable ℝ f := fun x => (hf1 x).differentiableAt
  have hgd : Differentiable ℝ g := fun x => (hg1 x).differentiableAt
  have hfc : Continuous f := hfd.continuous
  have hgc : Continuous g := hgd.continuous
  have hconjf : HasCompactSupport fun x => (starRingEnd ℂ) (f x) :=
    hfs.comp_left (g := starRingEnd ℂ) (by simp)
  have key := integral_conj_secondDeriv_comm f g f' f'' g' g'' hf1 hf2 hg1 hg2 hf''c hg''c hfs hgs
  have hcs : HasCompactSupport fun x => (starRingEnd ℂ) (f x) * g x := hgs.mul_left
  have iA0 : Integrable fun x => (starRingEnd ℂ) (f'' x) * g x :=
    (by fun_prop : Continuous fun x => (starRingEnd ℂ) (f'' x) * g x)
      |>.integrable_of_hasCompactSupport hgs.mul_left
  have iC0 : Integrable fun x => (starRingEnd ℂ) (f x) * g'' x :=
    (by fun_prop : Continuous fun x => (starRingEnd ℂ) (f x) * g'' x)
      |>.integrable_of_hasCompactSupport hconjf.mul_right
  have iB : Integrable fun x => (V x : ℂ) * ((starRingEnd ℂ) (f x) * g x) :=
    (by fun_prop : Continuous fun x => (V x : ℂ) * ((starRingEnd ℂ) (f x) * g x))
      |>.integrable_of_hasCompactSupport hcs.mul_left
  have e1 : ∀ x, (starRingEnd ℂ) (schrodingerOp V f x) * g x
      = -((starRingEnd ℂ) (f'' x) * g x) + (V x : ℂ) * ((starRingEnd ℂ) (f x) * g x) := by
    intro x
    rw [schrodingerOp_apply V f f' f'' hf1 hf2 x, map_add, map_neg, map_mul, Complex.conj_ofReal]
    ring
  have e2 : ∀ x, (starRingEnd ℂ) (f x) * schrodingerOp V g x
      = -((starRingEnd ℂ) (f x) * g'' x) + (V x : ℂ) * ((starRingEnd ℂ) (f x) * g x) := by
    intro x
    rw [schrodingerOp_apply V g g' g'' hg1 hg2 x]
    ring
  have iA : Integrable fun x => -((starRingEnd ℂ) (f'' x) * g x) := iA0.neg
  have iC : Integrable fun x => -((starRingEnd ℂ) (f x) * g'' x) := iC0.neg
  rw [integral_congr_ae (Filter.Eventually.of_forall e1),
      integral_congr_ae (Filter.Eventually.of_forall e2),
      integral_add iA iB, integral_add iC iB, integral_neg, integral_neg, key]

/-! ## The exponential potential -/

/-- The non-polynomial potential `V(x) = eˣ + e⁻ˣ` of the plan. -/
noncomputable def Vexp : ℝ → ℝ := fun x => Real.exp x + Real.exp (-x)

theorem Vexp_continuous : Continuous Vexp := by
  unfold Vexp; fun_prop

theorem two_le_Vexp (x : ℝ) : 2 ≤ Vexp x := by
  have hp : 0 < Real.exp x := Real.exp_pos x
  have hcancel : Real.exp x * (Real.exp x)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hp)
  rw [Vexp, Real.exp_neg]
  nlinarith [sq_nonneg (Real.exp x - 1), hp, hcancel]

/-- **The classical deficiency spaces of `-d²/dx² + (eˣ + e⁻ˣ)` are trivial.**
There is no nonzero square-integrable classical solution of `H u = z u` for any
`z` with `Re z ≤ 1`; in particular for `z = ± i`, which is exactly the
essential-self-adjointness condition. -/
theorem schrodinger_exp_deficiency_trivial
    (z : ℂ) (hz : z.re ≤ 1)
    (u u' u'' : ℝ → ℂ)
    (h1 : ∀ x, HasDerivAt u (u' x) x)
    (h2 : ∀ x, HasDerivAt u' (u'' x) x)
    (heq : ∀ x, -u'' x + (Vexp x : ℂ) * u x = z * u x)
    (hL2 : Integrable fun x => ‖u x‖ ^ 2) :
    u = 0 :=
  l2_classical_solution_eq_zero Vexp Vexp_continuous z u u' u'' h1 h2 heq
    (fun x => by linarith [two_le_Vexp x]) hL2

/-- The deficiency space at `+i`. -/
theorem schrodinger_exp_deficiency_trivial_I
    (u u' u'' : ℝ → ℂ)
    (h1 : ∀ x, HasDerivAt u (u' x) x)
    (h2 : ∀ x, HasDerivAt u' (u'' x) x)
    (heq : ∀ x, -u'' x + (Vexp x : ℂ) * u x = Complex.I * u x)
    (hL2 : Integrable fun x => ‖u x‖ ^ 2) :
    u = 0 :=
  schrodinger_exp_deficiency_trivial Complex.I (by simp) u u' u'' h1 h2 heq hL2

/-- The deficiency space at `-i`. -/
theorem schrodinger_exp_deficiency_trivial_negI
    (u u' u'' : ℝ → ℂ)
    (h1 : ∀ x, HasDerivAt u (u' x) x)
    (h2 : ∀ x, HasDerivAt u' (u'' x) x)
    (heq : ∀ x, -u'' x + (Vexp x : ℂ) * u x = (-Complex.I) * u x)
    (hL2 : Integrable fun x => ‖u x‖ ^ 2) :
    u = 0 :=
  schrodinger_exp_deficiency_trivial (-Complex.I) (by simp) u u' u'' h1 h2 heq hL2

end BookProof.SchrodingerCutoff
