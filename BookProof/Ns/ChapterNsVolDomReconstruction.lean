/-
Copyright (c) 2026.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BookProof

# The Fourier reconstruction of `det F − 1`, as far as it is algebraic

§63 was careful about where its proof stopped: `normForm_grad_sq` and `not_volDom_normForm` are
statements about the *normal form* `c(εt)²`, and the passage from the model's own penalty
`volPot kappa kv = (κ/2) Σ_q |(det F − 1)^(q)|²` to that normal form was measurement — the Fourier
reconstruction of `det F − 1` — not proof.

This file moves part of that boundary.  The five numbered statements below are what is proved here,
and nothing more.

**1. The discrete grid is orthogonal.**  On an `N`-point grid with `ω = exp(2πi/N)`,

  `∑_{j<N} ω^{mj} = 0` unless `N ∣ m`, and `= N` when `m = 0`      (`dft_orthogonal`, `dft_zero`),

which is the algebraic content of "the dual grid is orthogonal": a single mode is invisible to every
other mode's average.  No measure theory is involved — the grid is finite, and this is the geometric
series plus `ω^N = 1`.

**2. A single-mode residual is exactly its coefficient.**  If the residual's spectrum is supported at
the zero mode — the definition, on a finite grid, of a *spatially constant* residual — then the penalty
is the constant's square:

  `volPot kappa kv = (κ/2) Λ²`      (`volPot_of_single_mode`),

and with `Λ = c·ε·t` on §63's shear family,

  `volPot kappa kv = (κ/2)(c·ε·t)²`      (`volPot_of_shear_constant`),

i.e. exactly the coefficient `c` of the normal form `normForm c` that §63 refutes domination for.  So
the *transfer of the constant* is a theorem.

**3. `hspec` is derived, not assumed.**  §3 below is the assembly.  The discrete transform is
inverted on a grid — `coeff_eq_zero_of_grid_vanishing`, the step in which the identity
`(1/N) Σ_j |R(a_j)|² = Σ_q |R̂_q|²` is used — and a residual that is *spatially constant* on the grid
therefore has no nonzero frequency: `detCoef_eval_eq_zero_of_constant`, `volCoef_eq_zero_of_constant`,
`volCoef_zero_eq_of_constant`, hence `volPot_of_single_mode_of_constant` and
`volPot_of_shear_constant_of_const`, in which the former hypothesis `hspec` no longer appears.  The
inputs are now a modelling fact (`hconst`: `det F` is constant on the grid) and the unitarity of the
transform on that grid (`horth`) — not "the spectrum happens to be supported at the zero mode".

**4. `horth` is reduced to commensurability.**  §4 below discharges the abstract unitarity hypothesis at
the grid it is meant for: on the `N`-point grid `j ↦ j•e` along a direction `e ≠ 0`, the pairing of two
modes is `ζ^{m·j}` for `ζ = e^{2πi/N}` as soon as `⟨q − q', e⟩ = 2πm/N` (`phase_smul_eq_gridRoot`), the
geometric sum is `N` exactly when `N ∣ m` (`geom_sum_gridRoot`), and so **`horth_of_commensurate`**
derives `horth` from a labelling of the wave numbers by integers mod `N`.  `grid_card` and
`grid_nonempty` supply the cardinality and non-emptiness, and
`volPot_of_single_mode_of_commensurate` / `volPot_of_shear_constant_of_commensurate` are the §3 theorems
with `horth` replaced by that labelling.

**5. Aliasing across directions.**  §5 replaces the line by a three-dimensional box
`j ↦ Σ_x j x • e x` with `j x < N`, the coordinates of `e` being independent (`latPoint_injective`,
`gridBox_card`).  The phase factorises (`phase_latPoint`), so does the geometric sum
(`geom_sum_latBox`): it is `N³` exactly when *every* component of the residue vector vanishes, and one
non-commensurate direction sends the whole sum to zero.  Hence orthogonality on the box
(`horth_of_lattice_commensurate`) requires commensurability in all three directions at once, and
`latBox_character_one_iff` identifies the alias classes: two wave numbers are indistinguishable on the
box exactly when each dual component differs by a multiple of `2π`, i.e. `q − q' ∈ N·Λ*` — the total
wave number plays no role.  `volPot_of_single_mode_of_lattice_commensurate` is the assembly.

**What is still not proved.**  The labelling itself.  `horth` is gone from the statements, but its
replacement is a modelling hypothesis: that each pairwise difference of wave numbers is a *lattice
fraction* `2πm/N` along `e`, with the residue distinguishing the modes (`N ∤ m` iff `q ≠ q'`), and in
§5 that this holds in each of the three directions.  None of it is derived from `kv` — that would be a
statement about which modes the model is truncated to, and it is false for a generic choice.  The box
is one truncation and its coordinates are assumed independent; `latBox_character_one_iff` says which
modes collide *on that truncation*, not which modes the model has.  Nothing about ESA or about the
penalty's value off the constant family is claimed.
-/

import BookProof.Ns.ChapterNsLagrangianDetConvolution
import BookProof.Ns.ChapterNsVolDomExpansion
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace BookProof.NsVolDomReconstruction

open MvPolynomial
open BookProof.NsVolDomExpansion BookProof.NsLagrangianDet

noncomputable section

/-! ## 1. The discrete grid is orthogonal -/

/-- The `N`-th root of unity used by the grid. -/
def gridRoot (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- **Discrete orthogonality.**  The grid average of a nonzero mode vanishes: multiplying by
`ω^{m·j}` and summing over the grid kills everything the grid cannot resolve, i.e. everything whose
mode number is not a multiple of `N`. -/
theorem dft_orthogonal (N : ℕ) (hN : 0 < N) (m : ℕ) (h : ¬ N ∣ m) :
    ∑ j ∈ Finset.range N, gridRoot N ^ (m * j) = 0 := by
  have hζ := Complex.isPrimitiveRoot_exp N hN.ne'
  have hne : gridRoot N ^ m ≠ 1 := fun h1 => h ((hζ.pow_eq_one_iff_dvd m).mp h1)
  have hne' : Complex.exp (2 * Real.pi * Complex.I / N) ^ m ≠ 1 := hne
  simp only [gridRoot, pow_mul]
  rw [geom_sum_eq hne']
  have hpow : (Complex.exp (2 * Real.pi * Complex.I / N) ^ m) ^ N = 1 := by
    rw [← pow_mul, pow_mul', hζ.pow_eq_one, one_pow]
  rw [hpow]
  simp

/-- The zero mode is counted with full weight `N`: the grid is normalised so that a constant
survives its own average. -/
theorem dft_zero (N : ℕ) : ∑ _j ∈ Finset.range N, gridRoot N ^ (0 * _j) = (N : ℂ) := by
  simp

/-! ## 2. A single-mode residual is its coefficient -/

open Classical in
/-- **The reconstruction at a single mode.**  If the residual `det F − 1` has no nonzero Fourier
coefficient and its zero coefficient is the real constant `Λ`, then the penalty is `(κ/2)Λ²` — the
constant is carried through without distortion.  This is the step §63 called measurement; what is
assumed is the spectrum (`hspec`, `hz`), what is proved is that nothing else enters. -/
theorem volPot_of_single_mode {K : Type*} [Fintype K] (kappa Λ : ℝ) (kv : K → Fin 3 → ℝ)
    (h0 : ((0 : Fin 3 → ℝ) : Fin 3 → ℝ) ∈ waveSet kv)
    (hspec : ∀ q ∈ waveSet kv, q ≠ 0 → volCoef kv q = 0)
    (hz : volCoef kv 0 = MvPolynomial.C ((Λ : ℝ) : ℂ)) :
    volPot kappa kv = MvPolynomial.C (((kappa / 2) * Λ ^ 2 : ℝ) : ℂ) := by
  classical
  unfold volPot
  rw [Finset.sum_eq_single (0 : Fin 3 → ℝ)]
  · rw [hz]
    have hc : conjP (K := K) (MvPolynomial.C ((Λ : ℝ) : ℂ))
        = MvPolynomial.C ((Λ : ℝ) : ℂ) := by
      simp [conjP]
    rw [hc, MvPolynomial.smul_eq_C_mul]
    repeat rw [← map_mul]
    congr 1
    push_cast
    ring
  · intro q hq hq0
    rw [hspec q hq hq0]
    simp
  · intro hnot
    exact absurd h0 hnot

open Classical in
/-- **The constant transfers on the shear family.**  If the residual's spectrum is the single mode
`Λ = c·ε·t` — the shear amplitude times the tilt times `c` — then the model's penalty is
`(κ/2)(c·ε·t)²`, i.e. `(κ/2)` times the value of §63's normal form `normForm c` at `(t, ε)`.  So
the `c` that `not_volDom_normForm` refutes for every `c ≠ 0` is the *measured* constant, not a
re-scaling of the model. -/
theorem volPot_of_shear_constant {K : Type*} [Fintype K] (kappa c ε t : ℝ) (kv : K → Fin 3 → ℝ)
    (h0 : ((0 : Fin 3 → ℝ) : Fin 3 → ℝ) ∈ waveSet kv)
    (hspec : ∀ q ∈ waveSet kv, q ≠ 0 → volCoef kv q = 0)
    (hz : volCoef kv 0 = MvPolynomial.C (((c * ε * t : ℝ) : ℂ))) :
    volPot kappa kv
      = MvPolynomial.C (((kappa / 2) * (c * ε * t) ^ 2 : ℝ) : ℂ) :=
  volPot_of_single_mode kappa (c * ε * t) kv h0 hspec hz

/-- The same statement against §63's normal form: the penalty's value is `(κ/2)` times
`normForm c` evaluated at the shear amplitude and tilt. -/
theorem volPot_of_shear_constant_normForm {K : Type*} [Fintype K] (kappa c ε t : ℝ)
    (kv : K → Fin 3 → ℝ)
    (h0 : ((0 : Fin 3 → ℝ) : Fin 3 → ℝ) ∈ waveSet kv)
    (hspec : ∀ q ∈ waveSet kv, q ≠ 0 → volCoef kv q = 0)
    (hz : volCoef kv 0 = MvPolynomial.C (((c * ε * t : ℝ) : ℂ))) :
    volPot kappa kv = MvPolynomial.C ((kappa / 2 : ℝ) : ℂ) *
      MvPolynomial.C (((c * ε * t) ^ 2 : ℝ) : ℂ) := by
  rw [volPot_of_shear_constant kappa c ε t kv h0 hspec hz, ← map_mul]
  congr 1
  push_cast
  ring

/-! ## 3. The Plancherel assembly: a spatially constant residual has one frequency -/

/-- **Real points separate complex polynomials.**  General form of
`HermiteProductCore.mvpoly_eq_zero_of_eval_real` for an arbitrary index type: it suffices to test
against points whose coordinates are real. -/
theorem mvpoly_eq_zero_of_eval_real_fintype {σ : Type*} {p : MvPolynomial σ ℂ}
    (h : ∀ x : σ → ℝ, MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p = 0) : p = 0 := by
  classical
  refine MvPolynomial.funext_set (fun _ => Set.range ((↑) : ℝ → ℂ)) (fun _ => ?_) ?_
  · exact Set.infinite_range_of_injective Complex.ofReal_injective
  · intro x hx
    choose y hy using fun i => hx i (Set.mem_univ i)
    have hx' : x = fun i => ((y i : ℝ) : ℂ) := by funext i; exact (hy i).symm
    rw [hx']
    exact h y

/-- Conjugation of a plane wave is the plane wave at the negated wave vector. -/
theorem phase_conj (w a : Fin 3 → ℝ) : (starRingEnd ℂ) (phase w a) = phase (-w) a := by
  have hlin : ((∑ x, (-w) x * a x : ℝ) : ℂ) = -((∑ x, w x * a x : ℝ) : ℂ) := by
    push_cast
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by
      simp only [Pi.neg_apply]; push_cast; ring
  unfold phase
  rw [← Complex.exp_conj, hlin]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- The pairing of two plane waves is the plane wave at the difference of the wave vectors. -/
theorem phase_mul_conj (q q' a : Fin 3 → ℝ) :
    phase q a * (starRingEnd ℂ) (phase q' a) = phase (q - q') a := by
  rw [phase_conj]
  have hlin : ((∑ x, (q - q') x * a x : ℝ) : ℂ)
      = ((∑ x, q x * a x : ℝ) : ℂ) + ((∑ x, (-q') x * a x : ℝ) : ℂ) := by
    push_cast
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by
      simp only [Pi.sub_apply, Pi.neg_apply]; push_cast; ring
  unfold phase
  rw [hlin, ← Complex.exp_add]
  congr 1
  ring

/-- **Discrete Fourier inversion on a grid.**  `horth` is the unitarity of the discrete transform on
the grid — the assembly `(1/N) Σ_j |R(a_j)|² = Σ_q |R̂_q|²` in the form the argument needs.  Under
it, a residual whose Fourier series vanishes at every grid point has vanishing coefficients. -/
theorem coeff_eq_zero_of_grid_vanishing
    (S : Finset (Fin 3 → ℝ)) (c : (Fin 3 → ℝ) → ℂ) (G : Finset (Fin 3 → ℝ))
    (hG : G.Nonempty)
    (horth : ∀ q ∈ S, ∀ q' ∈ S,
      ∑ a ∈ G, phase (q - q') a = if q = q' then (G.card : ℂ) else 0)
    (hzero : ∀ a ∈ G, ∑ q ∈ S, c q * phase q a = 0) :
    ∀ q' ∈ S, c q' = 0 := by
  classical
  intro q' hq'
  have key : ∑ a ∈ G, (∑ q ∈ S, c q * phase q a) * (starRingEnd ℂ) (phase q' a) = 0 := by
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [hzero a ha, zero_mul]
  have h1 : ∑ a ∈ G, (∑ q ∈ S, c q * phase q a) * (starRingEnd ℂ) (phase q' a)
      = ∑ q ∈ S, c q * (∑ a ∈ G, phase (q - q') a) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => ?_
    rw [mul_assoc, phase_mul_conj]
  have hdiag : ∑ a ∈ G, phase ((q' - q') : Fin 3 → ℝ) a = (G.card : ℂ) := by
    have hh := horth q' hq' q' hq'
    rw [if_pos rfl, sub_self] at hh
    simpa using hh
  have h2 : ∑ q ∈ S, c q * (∑ a ∈ G, phase (q - q') a) = c q' * (G.card : ℂ) := by
    rw [Finset.sum_eq_single (f := fun q => c q * ∑ a ∈ G, phase (q - q') a) q']
    · rw [hdiag]
    · intro q hq hne
      rw [horth q hq q' hq', if_neg hne, mul_zero]
    · intro hnot
      exact absurd hq' hnot
  have h3 : c q' * (G.card : ℂ) = 0 := by rw [← h2, ← h1]; exact key
  have hcard : (G.card : ℂ) ≠ 0 := by
    have hpos : 0 < G.card := Finset.card_pos.mpr hG
    exact_mod_cast hpos.ne'
  exact (mul_eq_zero.mp h3).resolve_right hcard

/-- **The constant case.**  If the series equals the single mode `Λ` at every grid point — i.e. the
residual is spatially constant — then every nonzero coefficient vanishes. -/
theorem coeff_eq_zero_of_grid_const
    (S : Finset (Fin 3 → ℝ)) (c : (Fin 3 → ℝ) → ℂ) (G : Finset (Fin 3 → ℝ))
    (h0 : (0 : Fin 3 → ℝ) ∈ S) (hG : G.Nonempty)
    (horth : ∀ q ∈ S, ∀ q' ∈ S,
      ∑ a ∈ G, phase (q - q') a = if q = q' then (G.card : ℂ) else 0)
    (Λ : ℂ) (hconst : ∀ a ∈ G, ∑ q ∈ S, c q * phase q a = Λ) :
    ∀ q' ∈ S, q' ≠ 0 → c q' = 0 := by
  classical
  set c' : (Fin 3 → ℝ) → ℂ := fun q => c q - if q = 0 then Λ else 0 with hc'
  have hzero : ∀ a ∈ G, ∑ q ∈ S, c' q * phase q a = 0 := by
    intro a ha
    have hsplit : ∑ q ∈ S, c' q * phase q a
        = ∑ q ∈ S, c q * phase q a - Λ * phase (0 : Fin 3 → ℝ) a := by
      have h1 : ∑ q ∈ S, c' q * phase q a
          = ∑ q ∈ S, (c q * phase q a - (if q = 0 then Λ else 0) * phase q a) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [hc']
        ring
      rw [h1, Finset.sum_sub_distrib]
      congr 1
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq' S 0 (fun q => Λ * phase q a), if_pos h0]
    rw [hsplit, hconst a ha, phase_zero, mul_one, sub_self]
  have hres := coeff_eq_zero_of_grid_vanishing S c' G hG horth hzero
  intro q' hq' hq0
  have := hres q' hq'
  simpa [hc', hq0] using this

variable {K : Type*} [Fintype K]

/-- **Constancy on the grid kills the nonzero frequencies.**  If the deformation gradient's
determinant is the constant `1 + Λ` at every grid point, then the residual's Fourier coefficients
vanish away from the zero mode — this is the Plancherel assembly, and it is what the hypothesis
`hspec` used to assume. -/
theorem detCoef_eval_eq_zero_of_constant (kv : K → Fin 3 → ℝ) (Λ : ℝ)
    (G : Finset (Fin 3 → ℝ)) (hG : G.Nonempty)
    (horth : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv,
      ∑ a ∈ G, phase (q - q') a = if q = q' then (G.card : ℂ) else 0)
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ G →
      (1 + dispGrad kv y a).det = 1 + ((Λ : ℝ) : ℂ))
    (y : DIdx K → ℝ) (q : Fin 3 → ℝ) (hq : q ∈ waveSet kv) (hq0 : q ≠ 0) :
    ev y (detCoef kv q) = 0 := by
  refine coeff_eq_zero_of_grid_const (waveSet kv) (fun q => ev y (detCoef kv q)) G h0 hG horth
    (1 + ((Λ : ℝ) : ℂ)) ?_ q hq hq0
  intro a ha
  rw [← det_deformation_eq kv y a]
  exact hconst y a ha

/-- The residual's coefficients are polynomials, and vanishing at every real point is vanishing. -/
theorem volCoef_eq_zero_of_constant (kv : K → Fin 3 → ℝ) (Λ : ℝ)
    (G : Finset (Fin 3 → ℝ)) (hG : G.Nonempty)
    (horth : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv,
      ∑ a ∈ G, phase (q - q') a = if q = q' then (G.card : ℂ) else 0)
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ G →
      (1 + dispGrad kv y a).det = 1 + ((Λ : ℝ) : ℂ))
    (q : Fin 3 → ℝ) (hq : q ∈ waveSet kv) (hq0 : q ≠ 0) :
    volCoef kv q = 0 := by
  classical
  have h : volCoef kv q = detCoef kv q := by
    unfold volCoef
    rw [if_neg hq0, sub_zero]
  rw [h]
  exact mvpoly_eq_zero_of_eval_real_fintype fun y =>
    detCoef_eval_eq_zero_of_constant kv Λ G hG horth h0 hconst y q hq hq0

/-- The zero mode is the constant `Λ` itself. -/
theorem volCoef_zero_eq_of_constant (kv : K → Fin 3 → ℝ) (Λ : ℝ)
    (G : Finset (Fin 3 → ℝ)) (hG : G.Nonempty)
    (horth : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv,
      ∑ a ∈ G, phase (q - q') a = if q = q' then (G.card : ℂ) else 0)
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ G →
      (1 + dispGrad kv y a).det = 1 + ((Λ : ℝ) : ℂ)) :
    volCoef kv 0 = MvPolynomial.C ((Λ : ℝ) : ℂ) := by
  classical
  have hcoeval : ∀ y : DIdx K → ℝ, ev y (detCoef kv 0) = 1 + ((Λ : ℝ) : ℂ) := by
    intro y
    obtain ⟨a₀, ha₀⟩ := hG
    have hne : G.Nonempty := ⟨a₀, ha₀⟩
    have hh := hconst y a₀ ha₀
    rw [det_deformation_eq kv y a₀] at hh
    rw [Finset.sum_eq_single (0 : Fin 3 → ℝ)] at hh
    · rw [phase_zero, mul_one] at hh
      exact hh
    · intro q hq hqe
      have hz : ev y (detCoef kv q) = 0 :=
        detCoef_eval_eq_zero_of_constant kv Λ G hne horth h0 hconst y q hq hqe
      rw [hz, zero_mul]
    · intro hnot
      exact absurd h0 hnot
  have hsub : volCoef kv 0 - MvPolynomial.C ((Λ : ℝ) : ℂ) = 0 := by
    refine mvpoly_eq_zero_of_eval_real_fintype fun y => ?_
    have hv0 : ev y (volCoef kv 0) = ((Λ : ℝ) : ℂ) := by
      have hsplit : volCoef kv 0 = detCoef kv 0 - 1 := by
        unfold volCoef
        simp
      rw [hsplit, map_sub, hcoeval y, map_one]
      ring
    have hgoal : ev y (volCoef kv 0 - MvPolynomial.C ((Λ : ℝ) : ℂ)) = 0 := by
      rw [map_sub, hv0]
      have hC : ev y (MvPolynomial.C ((Λ : ℝ) : ℂ)) = ((Λ : ℝ) : ℂ) := by
        simp [ev]
      rw [hC, sub_self]
    exact hgoal
  exact sub_eq_zero.mp hsub

/-- **The penalty at a spatially constant residual**, with `hspec` derived rather than assumed: the
grid is orthogonal (`horth`), the residual is constant (`hconst`), and the penalty's value is the
constant's square. -/
theorem volPot_of_single_mode_of_constant (kappa Λ : ℝ) (kv : K → Fin 3 → ℝ)
    (G : Finset (Fin 3 → ℝ)) (hG : G.Nonempty)
    (horth : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv,
      ∑ a ∈ G, phase (q - q') a = if q = q' then (G.card : ℂ) else 0)
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ G →
      (1 + dispGrad kv y a).det = 1 + ((Λ : ℝ) : ℂ)) :
    volPot kappa kv = MvPolynomial.C (((kappa / 2) * Λ ^ 2 : ℝ) : ℂ) :=
  volPot_of_single_mode kappa Λ kv h0
    (fun q hq hq0 => volCoef_eq_zero_of_constant kv Λ G hG horth h0 hconst q hq hq0)
    (volCoef_zero_eq_of_constant kv Λ G hG horth h0 hconst)

/-- **The shear family**, reconstructed: a constant residual `Λ = c·ε·t` gives the penalty
`(κ/2)(c·ε·t)²` — the value of §63's normal form, with no `hspec` assumed. -/
theorem volPot_of_shear_constant_of_const (kappa c ε t : ℝ) (kv : K → Fin 3 → ℝ)
    (G : Finset (Fin 3 → ℝ)) (hG : G.Nonempty)
    (horth : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv,
      ∑ a ∈ G, phase (q - q') a = if q = q' then (G.card : ℂ) else 0)
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ G →
      (1 + dispGrad kv y a).det = 1 + (((c * ε * t : ℝ)) : ℂ)) :
    volPot kappa kv = MvPolynomial.C (((kappa / 2) * (c * ε * t) ^ 2 : ℝ) : ℂ) :=
  volPot_of_single_mode_of_constant kappa (c * ε * t) kv G hG horth h0 hconst

/-! ## 4. `horth` at the commensurate grid: the unitarity hypothesis is discharged -/

/-- **The grid along one direction**: `N` equally spaced points `j • e`, `j < N`. -/
noncomputable def grid (N : ℕ) (e : Fin 3 → ℝ) : Finset (Fin 3 → ℝ) :=
  (Finset.range N).image fun j : ℕ => (j : ℝ) • e

/-- The grid points are distinct as soon as the direction is nonzero: the `j`-th point is recovered
from any nonzero coordinate. -/
theorem grid_injOn {N : ℕ} {e : Fin 3 → ℝ} (he : e ≠ 0) :
    Set.InjOn (fun j : ℕ => (j : ℝ) • e) ↑(Finset.range N) := by
  obtain ⟨x, hx⟩ : ∃ x, e x ≠ 0 := by
    by_contra h
    push_neg at h
    exact he (funext h)
  intro j _ k _ hjk
  have h1 : (j : ℝ) * e x = (k : ℝ) * e x := by
    have := congrFun hjk x
    simpa only [Pi.smul_apply, smul_eq_mul] using this
  exact Nat.cast_injective (mul_right_cancel₀ hx h1)

theorem grid_card {N : ℕ} {e : Fin 3 → ℝ} (he : e ≠ 0) : (grid N e).card = N := by
  rw [grid, Finset.card_image_of_injOn (grid_injOn he), Finset.card_range]

theorem grid_nonempty {N : ℕ} (hN : 0 < N) (e : Fin 3 → ℝ) : (grid N e).Nonempty :=
  ⟨_, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hN, rfl⟩⟩

/-- **The geometric sum on the grid**, for an integer mode number: `Σ_{j<N} ζ^{mj}` is `N` exactly
when `N ∣ m` and zero otherwise.  This is §1's `dft_orthogonal` with the mode number allowed to be
negative (via `exp_int_mul` and conjugation), which is what a difference of two real wave numbers
produces. -/
theorem geom_sum_gridRoot (N : ℕ) (hN : 0 < N) (m : ℤ) :
    ∑ j ∈ Finset.range N, gridRoot N ^ (m * (j : ℤ))
      = if (N : ℤ) ∣ m then (N : ℂ) else 0 := by
  have hζ : IsPrimitiveRoot (gridRoot N) N := by
    simpa [gridRoot] using Complex.isPrimitiveRoot_exp N hN.ne'
  by_cases hdvd : (N : ℤ) ∣ m
  · rw [if_pos hdvd]
    have hone : gridRoot N ^ m = 1 := (hζ.zpow_eq_one_iff_dvd m).mpr hdvd
    have hterm : ∀ j ∈ Finset.range N, gridRoot N ^ (m * (j : ℤ)) = 1 := by
      intro j _
      rw [zpow_mul, hone, one_zpow]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · rw [if_neg hdvd]
    have hx : gridRoot N ^ m ≠ 1 := fun h => hdvd ((hζ.zpow_eq_one_iff_dvd m).mp h)
    have hterm : ∀ j ∈ Finset.range N, gridRoot N ^ (m * (j : ℤ)) = (gridRoot N ^ m) ^ j := by
      intro j _
      rw [zpow_mul, zpow_natCast]
    rw [Finset.sum_congr rfl hterm, geom_sum_eq hx]
    have hxN : (gridRoot N ^ m) ^ N = 1 := by
      have h1 : (gridRoot N ^ m) ^ (N : ℤ) = 1 := by
        rw [← zpow_mul, mul_comm, zpow_mul,
          (hζ.zpow_eq_one_iff_dvd (N : ℤ)).mpr (dvd_refl _), one_zpow]
      rwa [zpow_natCast] at h1
    rw [hxN]
    simp

/-- **A commensurate mode is a power of the grid's root of unity.**  If the two wave numbers differ
by `2πm/N` along the grid direction, the plane wave's value at the `j`-th grid point is `ζ^{mj}`. -/
theorem phase_smul_eq_gridRoot (N : ℕ) (hN : 0 < N) (e w : Fin 3 → ℝ) (m : ℤ)
    (h : (∑ x, w x * e x) = 2 * Real.pi * (m : ℝ) / N) (j : ℕ) :
    phase w ((j : ℝ) • e) = gridRoot N ^ (m * (j : ℤ)) := by
  have hsum : (∑ x, w x * (((j : ℝ) • e) x)) = (j : ℝ) * (∑ x, w x * e x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hNc : ((N : ℂ)) ≠ 0 := by exact_mod_cast hN.ne'
  unfold phase gridRoot
  rw [hsum, h, ← Complex.exp_int_mul]
  congr 1
  push_cast
  field_simp

/-- **The unitarity hypothesis is derived, not assumed.**  On the `N`-point grid along `e ≠ 0`,
orthogonality of the modes follows from a labelling of their pairwise differences by integers mod
`N`: `⟨q − q', e⟩ = 2πm/N`, with the residue `m` vanishing mod `N` exactly on the diagonal.  So the
Plancherel step needs no abstract `horth` — only that the model's wave numbers are commensurate with
the grid. -/
theorem horth_of_commensurate (N : ℕ) (hN : 0 < N) (e : Fin 3 → ℝ) (he : e ≠ 0)
    (S : Finset (Fin 3 → ℝ)) (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℤ)
    (hp : ∀ q ∈ S, ∀ q' ∈ S,
      (∑ x, (q - q') x * e x) = 2 * Real.pi * ((m q q' : ℤ) : ℝ) / N)
    (hdvd : ∀ q ∈ S, ∀ q' ∈ S, ((N : ℤ) ∣ m q q' ↔ q = q')) :
    ∀ q ∈ S, ∀ q' ∈ S, ∑ a ∈ grid N e, phase (q - q') a
      = if q = q' then ((grid N e).card : ℂ) else 0 := by
  intro q hq q' hq'
  rw [grid, Finset.sum_image (grid_injOn he)]
  rw [Finset.sum_congr rfl fun j _ =>
    phase_smul_eq_gridRoot N hN e (q - q') (m q q') (hp q hq q' hq') j]
  rw [geom_sum_gridRoot N hN (m q q')]
  by_cases h : q = q'
  · rw [if_pos ((hdvd q hq q' hq').mpr h), if_pos h]
    congr 1
    exact (grid_card he).symm
  · rw [if_neg (fun hd => h ((hdvd q hq q' hq').mp hd)), if_neg h]

/-- **The penalty at a constant residual, with no abstract unitarity input**: the grid is the
commensurate one, the residual is constant on it, and the penalty is the constant's square. -/
theorem volPot_of_single_mode_of_commensurate (kappa Λ : ℝ) (kv : K → Fin 3 → ℝ)
    (N : ℕ) (hN : 0 < N) (e : Fin 3 → ℝ) (he : e ≠ 0)
    (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℤ)
    (hp : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv,
      (∑ x, (q - q') x * e x) = 2 * Real.pi * ((m q q' : ℤ) : ℝ) / N)
    (hdvd : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv, ((N : ℤ) ∣ m q q' ↔ q = q'))
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ grid N e →
      (1 + dispGrad kv y a).det = 1 + ((Λ : ℝ) : ℂ)) :
    volPot kappa kv = MvPolynomial.C (((kappa / 2) * Λ ^ 2 : ℝ) : ℂ) :=
  volPot_of_single_mode_of_constant kappa Λ kv (grid N e) (grid_nonempty hN e)
    (horth_of_commensurate N hN e he (waveSet kv) m hp hdvd) h0 hconst

/-- The same on §63's shear family: `Λ = c·ε·t`, so the penalty is `(κ/2)(c·ε·t)²` with no `hspec`
and no abstract `horth`. -/
theorem volPot_of_shear_constant_of_commensurate (kappa c ε t : ℝ) (kv : K → Fin 3 → ℝ)
    (N : ℕ) (hN : 0 < N) (e : Fin 3 → ℝ) (he : e ≠ 0)
    (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℤ)
    (hp : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv,
      (∑ x, (q - q') x * e x) = 2 * Real.pi * ((m q q' : ℤ) : ℝ) / N)
    (hdvd : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv, ((N : ℤ) ∣ m q q' ↔ q = q'))
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ grid N e →
      (1 + dispGrad kv y a).det = 1 + (((c * ε * t : ℝ)) : ℂ)) :
    volPot kappa kv = MvPolynomial.C (((kappa / 2) * (c * ε * t) ^ 2 : ℝ) : ℂ) :=
  volPot_of_single_mode_of_commensurate kappa (c * ε * t) kv N hN e he m hp hdvd h0 hconst

/-! ## 5. A three-dimensional lattice: aliasing is a residue condition in every direction

§4 used a line of `N` points, so a mode `q − q'` had a single wave number to be commensurate with.
On the box `j ↦ Σ_x j x • e x` (`j x < N`) the exponent is a *sum* of three pairings, so the geometric
sum factorises into one factor per direction.  Two things follow and one does not:

* orthogonality needs commensurability in **every** direction — one non-commensurate direction makes
the whole sum vanish (`geom_sum_latBox`), so a mode cannot be repaired direction by direction;
* the alias classes are the residues mod `N` of the coefficient vector (`latBox_character_one_iff`):
`q` and `q'` are indistinguishable on the box exactly when each dual component differs by a multiple
of `N`, i.e. `q − q' ∈ N·Λ*`, and the *total* wave number plays no role.

What is still **not** proved: that the model's wave numbers land on this lattice at all.  The box is
one truncation; `latBox_character_one_iff` is a statement about it, and the independence hypothesis on
`e` is a property of the coordinates, not of `kv`. -/

/-- **A lattice-box point**: `Σ_x j x • e x`, with `j x < N` in each direction.  The first index of
`e` labels the basis vector, the second its spatial component. -/
noncomputable def latPoint (N : ℕ) (e : Fin 3 → Fin 3 → ℝ) (j : Fin 3 → Fin N) : Fin 3 → ℝ :=
  fun y => ∑ x, (j x : ℝ) * e x y

/-- **The lattice box**: the image of `j < N` in each direction. -/
noncomputable def gridBox (N : ℕ) (e : Fin 3 → Fin 3 → ℝ) : Finset (Fin 3 → ℝ) :=
  Finset.univ.image (latPoint N e)

/-- The box points are distinct as soon as the three directions are independent: the coefficient
vector of a vanishing combination is zero, and its entries are differences of natural numbers. -/
theorem latPoint_injective (N : ℕ) (e : Fin 3 → Fin 3 → ℝ)
    (hindep : ∀ c : Fin 3 → ℝ, (∀ y, ∑ x, c x * e x y = 0) → c = 0) :
    Function.Injective (latPoint N e) := by
  intro j j' h
  have hcoef : (fun x => (j x : ℝ) - (j' x : ℝ)) = 0 := by
    refine hindep _ fun y => ?_
    have h1 : (∑ x, ((j x : ℝ) - (j' x : ℝ)) * e x y)
        = (∑ x, (j x : ℝ) * e x y) - ∑ x, (j' x : ℝ) * e x y := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [h1]
    have h2 := congrFun h y
    simp only [latPoint] at h2
    rw [h2, sub_self]
  funext x
  have hx : (j x : ℝ) = (j' x : ℝ) := by
    have h := congrFun hcoef x
    simp only [Pi.zero_apply] at h
    exact sub_eq_zero.mp h
  have hv : (j x).val = (j' x).val := by exact_mod_cast hx
  exact Fin.ext hv

theorem gridBox_card (N : ℕ) (e : Fin 3 → Fin 3 → ℝ)
    (hindep : ∀ c : Fin 3 → ℝ, (∀ y, ∑ x, c x * e x y = 0) → c = 0) :
    (gridBox N e).card = N ^ 3 := by
  simp [gridBox, Finset.card_image_of_injective _ (latPoint_injective N e hindep)]

theorem gridBox_nonempty (N : ℕ) (hN : 0 < N) (e : Fin 3 → Fin 3 → ℝ) :
    (gridBox N e).Nonempty :=
  ⟨_, Finset.mem_image.mpr
    ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _, rfl⟩⟩

/-- **The phase on the box is a power of the root of unity**: with a per-direction pairing
`⟨w, e x⟩ = 2πm x/N`, the plane wave at `Σ_x j x • e x` is `ζ^{Σ_x m x · j x}`. -/
theorem phase_latPoint (N : ℕ) (_hN : 0 < N) (e : Fin 3 → Fin 3 → ℝ) (w : Fin 3 → ℝ)
    (m : Fin 3 → ℤ) (hin : ∀ x, ∑ y, w y * e x y = 2 * Real.pi * (m x : ℝ) / N)
    (j : Fin 3 → Fin N) :
    phase w (latPoint N e j) = gridRoot N ^ (∑ x, m x * (j x : ℤ)) := by
  have h1 : ∀ y : Fin 3, w y * (latPoint N e j) y = ∑ x, (j x : ℝ) * (w y * e x y) := by
    intro y
    rw [latPoint, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hsum : (∑ y, w y * (latPoint N e j) y) = ∑ x, (j x : ℝ) * (∑ y, w y * e x y) :=
    calc (∑ y, w y * (latPoint N e j) y)
        = ∑ y, ∑ x, (j x : ℝ) * (w y * e x y) := Finset.sum_congr rfl fun y _ => h1 y
      _ = ∑ x, ∑ y, (j x : ℝ) * (w y * e x y) := Finset.sum_comm
      _ = ∑ x, (j x : ℝ) * ∑ y, w y * e x y := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.mul_sum]
  have hsum' : (∑ y, w y * (latPoint N e j) y)
      = (2 * Real.pi / N) * ∑ x, (m x : ℝ) * (j x : ℝ) := by
    rw [hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hin x]
    ring
  have hexp : Complex.I * (((2 * Real.pi / N) * ∑ x, (m x : ℝ) * (j x : ℝ) : ℝ) : ℂ)
      = (((∑ x, m x * (j x : ℤ) : ℤ)) : ℂ)
        * (Complex.I * ((2 * Real.pi / N : ℝ) : ℂ)) := by
    push_cast
    ring
  unfold phase gridRoot
  rw [hsum', hexp, Complex.exp_int_mul]
  congr 2
  push_cast
  ring

/-- Summing a power over `Fin N` is summing it over `range N`. -/
theorem sum_fin_zpow' (N : ℕ) (c : ℂ) (a : ℤ) :
    (∑ j : Fin N, c ^ (a * (j : ℤ))) = ∑ j ∈ Finset.range N, c ^ (a * (j : ℤ)) := by
  rw [Finset.sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [dif_pos (Finset.mem_range.mp hj)]

/-- **The geometric sum factorises over the three directions**, and is `N³` exactly when the residue
vector vanishes: commensurability is needed in *every* direction, and one failure sends the whole sum
to zero. -/
theorem geom_sum_latBox (N : ℕ) (hN : 0 < N) (m : Fin 3 → ℤ) :
    ∑ j : Fin 3 → Fin N, gridRoot N ^ (∑ x, m x * (j x : ℤ))
      = if (∀ x, (N : ℤ) ∣ m x) then (N : ℂ) ^ 3 else 0 := by
  have hζ : gridRoot N ≠ 0 := by
    unfold gridRoot
    exact Complex.exp_ne_zero _
  have hfac : ∀ (j : Fin 3 → Fin N), gridRoot N ^ (∑ x, m x * (j x : ℤ))
      = ∏ x, gridRoot N ^ (m x * (j x : ℤ)) := by
    intro j
    rw [Fin.prod_univ_three, Fin.sum_univ_three, zpow_add₀ hζ, zpow_add₀ hζ]
  simp only [hfac]
  have hsingle : ∀ x : Fin 3, (∑ j : Fin N, gridRoot N ^ (m x * ((j : ℕ) : ℤ)))
      = if (N : ℤ) ∣ m x then (N : ℂ) else 0 := by
    intro x
    rw [sum_fin_zpow' N (gridRoot N) (m x)]
    exact geom_sum_gridRoot N hN (m x)
  have hbox := Finset.sum_prod_piFinset (Finset.univ : Finset (Fin N))
    (fun x j => gridRoot N ^ (m x * (j : ℤ)))
  rw [Fintype.piFinset_univ] at hbox
  rw [show (∑ j : Fin 3 → Fin N, ∏ x, gridRoot N ^ (m x * (j x : ℤ)))
      = ∏ x, ∑ j ∈ (Finset.univ : Finset (Fin N)), gridRoot N ^ (m x * (j : ℤ))
      from hbox]
  simp only [hsingle]
  by_cases hall : ∀ x, (N : ℤ) ∣ m x
  · rw [if_pos hall, Finset.prod_congr rfl fun x _ => if_pos (hall x), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hall]
    obtain ⟨x0, hx0⟩ : ∃ x, ¬ (N : ℤ) ∣ m x := by
      by_contra h
      push_neg at h
      exact hall h
    exact Finset.prod_eq_zero (Finset.mem_univ x0) (if_neg hx0)

/-- **Aliasing is a residue condition in each direction.**  On the box, two wave numbers are
indistinguishable exactly when each of their three dual pairings differs by a multiple of `2π`:
the alias classes are the residue vectors mod `N`, so `q − q' ∈ N·Λ*`, and the *total* wave number is
irrelevant. -/
theorem latBox_character_one_iff (N : ℕ) (hN : 0 < N) (e : Fin 3 → Fin 3 → ℝ) (w : Fin 3 → ℝ)
    (m : Fin 3 → ℤ) (hin : ∀ x, ∑ y, w y * e x y = 2 * Real.pi * (m x : ℝ) / N) :
    (∀ j : Fin 3 → Fin N, phase w (latPoint N e j) = 1) ↔ ∀ x, (N : ℤ) ∣ m x := by
  have hζ : IsPrimitiveRoot (gridRoot N) N := by
    simpa [gridRoot] using Complex.isPrimitiveRoot_exp N hN.ne'
  constructor
  · intro h
    have hconst : ∀ j : Fin 3 → Fin N,
        gridRoot N ^ (∑ x, m x * (j x : ℤ)) = 1 := fun j => by
      rw [← phase_latPoint N hN e w m hin j, h j]
    have hval : (∑ j : Fin 3 → Fin N, gridRoot N ^ (∑ x, m x * (j x : ℤ)))
        = ((Fintype.card (Fin 3 → Fin N) : ℕ) : ℂ) := by
      rw [Finset.sum_congr rfl fun j _ => hconst j, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
    rw [geom_sum_latBox N hN m] at hval
    by_cases hall : ∀ x, (N : ℤ) ∣ m x
    · exact hall
    · rw [if_neg hall] at hval
      have hne : ((Fintype.card (Fin 3 → Fin N) : ℕ) : ℂ) ≠ 0 := by
        simp [Fintype.card_fin, hN.ne']
      exact absurd hval.symm hne
  · intro hdiv j
    rw [phase_latPoint N hN e w m hin j]
    have hdvd : (N : ℤ) ∣ ∑ x, m x * (j x : ℤ) := by
      refine Finset.dvd_sum fun x _ => ?_
      exact Dvd.dvd.mul_right (hdiv x) ((j x : ℕ) : ℤ)
    rw [(hζ.zpow_eq_one_iff_dvd _).mpr hdvd]

/-- **The unitarity hypothesis on a three-dimensional lattice.**  As on the line, orthogonality of
the modes on the box follows from a per-direction labelling of their differences by integers mod
`N`; what is new is that the labelling must hold in all three directions at once. -/
theorem horth_of_lattice_commensurate (N : ℕ) (hN : 0 < N) (e : Fin 3 → Fin 3 → ℝ)
    (hindep : ∀ c : Fin 3 → ℝ, (∀ y, ∑ x, c x * e x y = 0) → c = 0)
    (S : Finset (Fin 3 → ℝ)) (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Fin 3 → ℤ)
    (hp : ∀ q ∈ S, ∀ q' ∈ S, ∀ x,
      ∑ y, (q - q') y * e x y = 2 * Real.pi * ((m q q' x : ℤ) : ℝ) / N)
    (hdvd : ∀ q ∈ S, ∀ q' ∈ S, (∀ x, (N : ℤ) ∣ m q q' x) ↔ q = q') :
    ∀ q ∈ S, ∀ q' ∈ S, ∑ a ∈ gridBox N e, phase (q - q') a
      = if q = q' then ((gridBox N e).card : ℂ) else 0 := by
  intro q hq q' hq'
  rw [gridBox, Finset.sum_image (latPoint_injective N e hindep).injOn]
  rw [Finset.sum_congr rfl fun j _ =>
    phase_latPoint N hN e (q - q') (m q q') (hp q hq q' hq') j]
  rw [geom_sum_latBox N hN (m q q')]
  have hcard : ((gridBox N e).card : ℂ) = (N : ℂ) ^ 3 := by
    rw [gridBox_card N e hindep, Nat.cast_pow]
  by_cases h : q = q'
  · rw [if_pos ((hdvd q hq q' hq').mpr h), if_pos h]
    exact hcard.symm
  · rw [if_neg (fun hd => h ((hdvd q hq q' hq').mp hd)), if_neg h]

/-- **The penalty at a constant residual on a three-dimensional lattice**, with no abstract unitarity
input: the box is commensurate in every direction and the residual is constant on it. -/
theorem volPot_of_single_mode_of_lattice_commensurate (kappa Λ : ℝ) (kv : K → Fin 3 → ℝ)
    (N : ℕ) (hN : 0 < N) (e : Fin 3 → Fin 3 → ℝ)
    (hindep : ∀ c : Fin 3 → ℝ, (∀ y, ∑ x, c x * e x y = 0) → c = 0)
    (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Fin 3 → ℤ)
    (hp : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv, ∀ x,
      ∑ y, (q - q') y * e x y = 2 * Real.pi * ((m q q' x : ℤ) : ℝ) / N)
    (hdvd : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv, (∀ x, (N : ℤ) ∣ m q q' x) ↔ q = q')
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ gridBox N e →
      (1 + dispGrad kv y a).det = 1 + ((Λ : ℝ) : ℂ)) :
    volPot kappa kv = MvPolynomial.C (((kappa / 2) * Λ ^ 2 : ℝ) : ℂ) :=
  volPot_of_single_mode_of_constant kappa Λ kv (gridBox N e) (gridBox_nonempty N hN e)
    (horth_of_lattice_commensurate N hN e hindep (waveSet kv) m hp hdvd) h0 hconst

end

end BookProof.NsVolDomReconstruction
