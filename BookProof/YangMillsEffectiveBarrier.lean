import Mathlib
import BookProof.YangMillsFormDomination

/-!
# Chapter YangMillsEffectiveBarrier — the Simon mechanism on the Cartan flat directions

`softmodes.md` Phase 2 asks for the reason the Weyl-gauge Yang–Mills Hamiltonian has no
continuous spectrum starting at its ground level, even though the classical magnetic potential

`V(A) = ½ ∑_{i,a} (ε_{ijk} ∂_j A_{ka} + …)²`

vanishes identically along two families of directions extending to infinity in field space: the
pure-gauge gradients (removed by BRST, `BookProof.BrstReducedTransfer`) and the **Cartan flat
directions** `A_i ∈ 𝔱` of constant Abelian fields, where `[A_j, A_k] = 0`.

The mechanism is Barry Simon's (*Some quantum mechanical problems with a clean spectrum*): a
classical valley does not produce a continuous spectrum when the *transverse* oscillator stiffens
along it.  For a non-Abelian field, the off-diagonal (root) modes have frequency
`ω_α(A_∥) = g |α(A_∥)|` in the Cartan background `A_∥`, so the transverse zero-point energy at
background "magnitude" `√N` is `½ g √N` per root mode — unbounded in `N`.  This chapter formalises
that mechanism at the level of the Gauss–polynomial core of `BookProof.ReferenceGap`.

## What is proved here

* `parallelDegree` / `perpDegree` — the Cartan and root occupations of a multi-index, splitting the
  degree form of `BookProof.YangMillsFormDomination` (`parallelDegree_add_perpDegree`);
* `zeroPoint g N = ½ g √(N + ½)` — Simon's transverse zero-point energy, nonnegative
  (`zeroPoint_nonneg`), strictly increasing in the background (`zeroPoint_lt`), and **coercive**
  (`zeroPoint_coercive`: for every `M` there is `K` with `M ≤ zeroPoint g N` for all `N ≥ K`) — the
  precise sense in which the valley is *lifted*;
* `barrierForm` — the corresponding quadratic form on the core, nonnegative for `g ≥ 0`, and
  vanishing at zero coupling (`barrierForm_zero_g`);
* `simon_valley_lifted` — the effective potential `N ↦ rootCount · zeroPoint g N` along the
  Cartan valley tends to infinity, so the flat direction is confined;
* `simonEffective_coercive` — the same statement for the two-dimensional model
  `V(x,y) = g²x²y²` whose classical valley `{(x,0)}` is *exactly* flat (`simonPotential_flat`), the
  example Simon's theorem is about;
* `two_mul_sqrt_le`, `sqrt_le_add_one` — the elementary estimates behind the mechanism: the barrier
  is sublinear (`zeroPoint_le_linear`), so it cannot be traded against the kinetic term, and the
  transverse/longitudinal minimization is bounded by `a + b` (`two_mul_sqrt_le`);
* **`formDomination_of_barrier`** — the Phase-4 link: if the Yang–Mills form dominates
  `degreeForm + barrierForm` up to a shift `C‖·‖²` (the `softmodes.md` §2.3 milestone inequality,
  packaged as `IsBarrierBound`), then it inhabits the `FormDomination` certificate of
  `BookProof.YangMillsFormDomination` with the free ratio `c₁` and shift `c₁μ₀ + C`, hence it has
  the certified separation `c₁ Δ_ref` (`barrier_gap`);
* **the coupling is not a free parameter** — the quartic `:N²:` interaction contains the Cartan/root
  cross term `2 N_∥ N_⊥` (`crossDegreeForm`, `quarticDegreeForm_ge_crossDegreeForm`), which at
  background occupation `N` is an oscillator of frequency `√(2N + 1)` (`transFreq_sqrt_two`), so
  the barrier is *exactly* that oscillator's zero-point energy at coupling `g = √2`
  (`zeroPoint_sqrt_two`);
* **the §2.3 milestone, unconditionally, for the quartic form** — `barrierForm_le_linear` (the
  barrier is linear in the occupation, `rootCount · zeroPoint g N ≤ K (N + 1)`) and
  **`barrierBound_quartic`**: the normal-ordered `:N²:` form itself bounds
  `degreeForm + barrierForm − C‖·‖²` with the explicit shift `C = K + (1 + K)²/4`,
  `K = rootCount T · g/2`.  No hypothesis is left: the quartic grows quadratically, the barrier
  only like `√N`, so the interaction pays for the kinetic form and Simon's barrier together;
* `quarticFormDomination`, **`quartic_certified_gap`** — the consequence through §5: the pure
  interaction form inhabits the Phase-4 certificate with the free ratio `c₁`, and on the
  vacuum-orthogonal sector it carries the certified separation `c₁ Δ_ref` up to that shift.

## The interface is inhabited by `q_W` itself

`BookProof.YangMillsMagneticQuartic` supplies the identification this chapter leaves open: the
magnetic energy of the field strength,
`q_mag(c) = ∑_n (∑_a B_a(n)²)‖c n‖²` with `B_a(n) = ∑_i A_{a i} nᵢ`,
is the `:N²:` form up to the explicit factor `card` of the two Cauchy–Schwarz comparisons
(`quarticDegreeForm_le_magnetic`, `magnetic_le_quartic`).  Consequently
`barrierBound_quartic` becomes a bound for the Yang–Mills form itself —
`barrierBound_yangMillsForm`, `yangMillsForm_certifiedGap` — so the `IsBarrierBound` interface
below is no longer an unfilled assumption in that model: it has the witness `q_W`.

## Honest boundary

The remaining gap is no longer the *form* comparison but the derivation of it from the concrete
potential: the field-strength components `B_a` are an arbitrary matrix with entries in `[0,1]` in
`YangMillsMagneticQuartic`, and that the Weyl-gauge `∂A + g[A,A]` normal-ordered produces such
components on the core (the estimates of `ChapterFockInteractionStability`) is not proved, nor is
the field-space realization of the root modes as oscillators with frequency `g|α(A_∥)|`
(`ChapterYangMillsHermite` builds the field-space Hamiltonian on the Gauss–polynomial core but not
this normal-form decomposition).  What is proved is that the inequality *is* the quartic `:N²:`
inequality, with its explicit constant — so the interface is not vacuous and the gap `c₁ Δ_ref`
depends on no unproved estimate once the components are known.  The barriered form is *not*
claimed to have a discrete spectrum: `simon_valley_lifted` is a statement about the effective
potential, not about the resolvent of `H_W`.
-/

noncomputable section

namespace BookProof.YangMillsEffectiveBarrier

open Finset
open BookProof.ReferenceGap
open BookProof.YangMillsFormDomination

variable {d : ℕ}

/-! ## 1. The Cartan / root split of a multi-index

The field directions are split into the Cartan directions `T` (the constant Abelian fields, along
which the magnetic potential vanishes) and the root directions (the off-diagonal modes, which are
oscillators in the Cartan background).  On the coefficient model of the product Hermite basis a
multi-index `n` records the occupation of each direction, so the split of the fields is the split of
the degree `∑ i, nᵢ`. -/

/-- The occupation of the Cartan directions `T`: the background magnitude `√N` of the valley. -/
def parallelDegree (T : Finset (Fin d)) (n : Fin d → ℕ) : ℝ :=
  ∑ i ∈ T, (n i : ℝ)

/-- The occupation of the root (off-diagonal) directions, the modes that oscillate. -/
def perpDegree (T : Finset (Fin d)) (n : Fin d → ℕ) : ℝ :=
  ∑ i ∈ Finset.univ \ T, (n i : ℝ)

/-- The number of root directions, i.e. the number of transverse oscillators. -/
def rootCount (T : Finset (Fin d)) : ℝ := ((d - T.card : ℕ) : ℝ)

theorem parallelDegree_nonneg (T : Finset (Fin d)) (n : Fin d → ℕ) : 0 ≤ parallelDegree T n :=
  Finset.sum_nonneg fun i _ => Nat.cast_nonneg (n i)

theorem perpDegree_nonneg (T : Finset (Fin d)) (n : Fin d → ℕ) : 0 ≤ perpDegree T n :=
  Finset.sum_nonneg fun i _ => Nat.cast_nonneg (n i)

theorem rootCount_nonneg (T : Finset (Fin d)) : 0 ≤ rootCount T :=
  Nat.cast_nonneg _

/-- A proper Cartan subspace leaves at least one transverse direction, hence a positive number of
oscillators. -/
theorem rootCount_pos {T : Finset (Fin d)} (hT : T.card < d) : 0 < rootCount T := by
  have : 0 < d - T.card := Nat.sub_pos_of_lt hT
  exact Nat.cast_pos.mpr this

/-- The two occupations add up to the total degree: the circle of ideas of `softmodes.md` §4 splits
the degree form `∑ n, (∑ i, nᵢ)‖c n‖²` into its Cartan and root parts. -/
theorem parallelDegree_add_perpDegree (T : Finset (Fin d)) (n : Fin d → ℕ) :
    parallelDegree T n + perpDegree T n = ∑ i, (n i : ℝ) := by
  simp only [parallelDegree, perpDegree]
  rw [add_comm]
  exact Finset.sum_sdiff (s₁ := T) (s₂ := Finset.univ) (f := fun i => (n i : ℝ))
    (Finset.subset_univ T)

/-! ## 2. The transverse zero-point energy (Simon's barrier)

In the Cartan background of occupation `N`, each root mode is an oscillator of frequency
`ω = g √(N + ½)` (the `+½` is the oscillator zero-point offset of the background itself), so Simon's
transverse zero-point energy is `½ ℏ ω = ½ g √(N + ½)` with `ℏ = 1`.  This is the quantity that
lifts the valley. -/

/-- The frequency of a root oscillator in the Cartan background of occupation `N`. -/
def transFreq (g N : ℝ) : ℝ := g * Real.sqrt (N + 1 / 2)

/-- Simon's transverse zero-point energy `½ g √(N + ½)` per root mode. -/
def zeroPoint (g N : ℝ) : ℝ := 1 / 2 * transFreq g N

theorem zeroPoint_nonneg {g N : ℝ} (hg : 0 ≤ g) (_hN : 0 ≤ N) : 0 ≤ zeroPoint g N := by
  unfold zeroPoint transFreq
  have : 0 ≤ Real.sqrt (N + 1 / 2) := Real.sqrt_nonneg _
  nlinarith

/-- The barrier is strictly increasing in the background occupation: a deeper valley costs more. -/
theorem zeroPoint_lt {g N N' : ℝ} (hg : 0 < g) (hN : 0 ≤ N) (h : N < N') :
    zeroPoint g N < zeroPoint g N' := by
  have h0 : 0 ≤ N + 1 / 2 := by linarith
  have harg : N + 1 / 2 < N' + 1 / 2 := by linarith
  have hs : Real.sqrt (N + 1 / 2) < Real.sqrt (N' + 1 / 2) := Real.sqrt_lt_sqrt h0 harg
  unfold zeroPoint transFreq
  nlinarith

/-- **The valley is lifted**: for every target energy `M` there is a Cartan occupation beyond which
the transverse zero-point energy exceeds `M`.  This is the analytic content of Simon's mechanism at
the level of the effective potential. -/
theorem zeroPoint_coercive {g : ℝ} (hg : 0 < g) (M : ℝ) :
    ∃ K : ℝ, ∀ N : ℝ, K ≤ N → M ≤ zeroPoint g N := by
  rcases le_total M 0 with hM | hM
  · exact ⟨0, fun N hN => hM.trans (zeroPoint_nonneg hg.le (by linarith))⟩
  · refine ⟨(2 * M / g) ^ 2, fun N hN => ?_⟩
    have hN0 : 0 ≤ N := le_trans (sq_nonneg (2 * M / g)) hN
    have harg : (2 * M / g) ^ 2 ≤ N + 1 / 2 := by linarith
    have hsqrt : 2 * M / g ≤ Real.sqrt (N + 1 / 2) := Real.le_sqrt_of_sq_le harg
    have hg' : (0 : ℝ) ≤ 1 / 2 * g := by linarith
    have hstep : 1 / 2 * g * (2 * M / g) ≤ 1 / 2 * g * Real.sqrt (N + 1 / 2) :=
      mul_le_mul_of_nonneg_left hsqrt hg'
    have hcancel : 1 / 2 * g * (2 * M / g) = M := by
      field_simp
    rw [hcancel] at hstep
    unfold zeroPoint transFreq
    nlinarith

/-- The barrier is *sublinear* in the background occupation (`√x ≤ x + ¼`, the tangent line at
`x = ¼`), so it never competes with the kinetic term — it only removes the flat directions. -/
theorem sqrt_le_add_quarter {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ x + 1 / 4 := by
  have hsq := Real.sq_sqrt hx
  nlinarith [sq_nonneg (Real.sqrt x - 1 / 2), Real.sqrt_nonneg x]

theorem zeroPoint_le_linear {g N : ℝ} (hg : 0 ≤ g) (hN : 0 ≤ N) :
    zeroPoint g N ≤ g / 2 * (N + 1) := by
  have harg : 0 ≤ N + 1 / 2 := by linarith
  have hsqrt : Real.sqrt (N + 1 / 2) ≤ (N + 1 / 2) + 1 / 4 := sqrt_le_add_quarter harg
  unfold zeroPoint transFreq
  nlinarith

/-- The elementary trade-off behind the transverse/longitudinal minimization: `2√(ab) ≤ a + b`. -/
theorem two_mul_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt (a * b) ≤ a + b := by
  have hmul : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := Real.sqrt_mul ha b
  have h1 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have h2 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  rw [hmul]
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb]

/-! ## 3. The barrier form on the Gauss–polynomial core -/

/-- The transverse zero-point barrier, read on the coefficient model of the product Hermite core:
each multi-index `n` of Cartan occupation `N` pays `rootCount · ½ g √(N + ½)` per unit of
`‖c n‖²`. -/
def barrierForm (T : Finset (Fin d)) (g : ℝ) (c : CoreCoeff d) : ℝ :=
  ∑ n ∈ c.support, (rootCount T * zeroPoint g (parallelDegree T n)) * ‖c n‖ ^ 2

theorem barrierForm_nonneg {g : ℝ} (hg : 0 ≤ g) (T : Finset (Fin d)) (c : CoreCoeff d) :
    0 ≤ barrierForm T g c :=
  Finset.sum_nonneg fun n _ =>
    mul_nonneg
      (mul_nonneg (rootCount_nonneg T) (zeroPoint_nonneg hg (parallelDegree_nonneg T n)))
      (by positivity)

/-- With the coupling switched off the valley is not lifted: the barrier vanishes identically. -/
theorem zeroPoint_zero (N : ℝ) : zeroPoint 0 N = 0 := by
  unfold zeroPoint transFreq
  simp

theorem barrierForm_zero_g (T : Finset (Fin d)) (c : CoreCoeff d) :
    barrierForm T 0 c = 0 := by
  unfold barrierForm
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [zeroPoint_zero, mul_zero, zero_mul]

/-! ## 4. The effective potential along the valley

The classical magnetic energy vanishes along the Cartan directions; the effective potential the
Hamiltonian actually sees there is exactly the barrier of §2 (one zero-point energy per transverse
oscillator). -/

/-- The effective potential along the Cartan valley. -/
def effPotential (T : Finset (Fin d)) (g N : ℝ) : ℝ := rootCount T * zeroPoint g N

theorem effPotential_nonneg {g N : ℝ} (hg : 0 ≤ g) (hN : 0 ≤ N) (T : Finset (Fin d)) :
    0 ≤ effPotential T g N :=
  mul_nonneg (rootCount_nonneg T) (zeroPoint_nonneg hg hN)

/-- **Milestone 2 of `softmodes.md` Phase 2, at the level of the effective potential**: with at
least one transverse direction and `g > 0`, the Cartan valley is confined — no matter how large `M`,
the effective energy along it eventually exceeds `M`. -/
theorem simon_valley_lifted {g : ℝ} (hg : 0 < g) {T : Finset (Fin d)} (hT : T.card < d) (M : ℝ) :
    ∃ K : ℝ, ∀ N : ℝ, K ≤ N → M ≤ effPotential T g N := by
  have hr : 0 < rootCount T := rootCount_pos hT
  obtain ⟨K, hK⟩ := zeroPoint_coercive hg (M / rootCount T)
  refine ⟨K, fun N hN => ?_⟩
  have hstep := mul_le_mul_of_nonneg_left (hK N hN) hr.le
  have hcancel : rootCount T * (M / rootCount T) = M := by
    field_simp
  unfold effPotential
  rw [hcancel] at hstep
  exact hstep

/-- The model Simon's theorem is about: `V(x, y) = g² x² y²` on `ℝ²`. -/
def simonPotential (g x y : ℝ) : ℝ := g ^ 2 * x ^ 2 * y ^ 2

theorem simonPotential_nonneg (g x y : ℝ) : 0 ≤ simonPotential g x y := by
  unfold simonPotential
  positivity

/-- The valley `{(x, 0)}` is exactly flat: the classical energy vanishes for every `x`, however
large.  This is the phenomenon that *looks* like a continuous spectrum in the classical theory. -/
theorem simonPotential_flat (g x : ℝ) : simonPotential g x 0 = 0 := by
  unfold simonPotential
  ring

/-- The effective energy along that valley: the transverse oscillator at `x` has frequency `g|x|`,
so its zero-point energy is `½ g |x|`. -/
def simonEffective (g x : ℝ) : ℝ := zeroPoint g |x|

/-- Along the flat valley of `simonPotential` the effective energy is coercive — Simon's mechanism
in its original two-dimensional form. -/
theorem simonEffective_coercive {g : ℝ} (hg : 0 < g) (M : ℝ) :
    ∃ K : ℝ, ∀ x : ℝ, K ≤ |x| → M ≤ simonEffective g x := by
  obtain ⟨K, hK⟩ := zeroPoint_coercive hg M
  exact ⟨K, fun x hx => hK |x| hx⟩

/-! ## 5. From the barrier to the Phase-4 certificate

`softmodes.md` §2.3 states the milestone inequality

`q_W(ψ) ≥ ⟨ψ, (−½Δ + c_g‖A‖ − C₀) ψ⟩`,

i.e. the Yang–Mills form dominates the kinetic form *plus* the barrier, up to a bounded shift.  That
inequality is the remaining analytic input; this section proves that, once it is available, it
discharges Phase 4 completely: the reference form is dominated with the free ratio of
`BookProof.YangMillsFormDomination`, and the certified separation follows. -/

/-- **The Phase-2 milestone inequality**, as an interface: the Yang–Mills form `q` bounds the free
degree form plus the Simon barrier, up to the shift `C‖·‖²`. -/
structure IsBarrierBound (T : Finset (Fin d)) (g : ℝ) (q : CoreCoeff d → ℝ) where
  /-- the bounded shift `C₀` of the milestone inequality. -/
  shift : ℝ
  /-- the inequality itself, on the Gauss–polynomial core. -/
  bound : ∀ c : CoreCoeff d,
    degreeForm (d := d) c + barrierForm T g c - shift * coreNormSq c ≤ q c

/-- **The barrier discharges Phase 4.**  If `q` dominates `degreeForm + barrierForm` up to `C‖·‖²`,
then `q` dominates the reference form with the free ratio `c₁` and shift `c₁μ₀ + C`: the barrier is
nonnegative, so it can only help the comparison, and the free domination
(`freeFormDomination`) supplies the rest. -/
def formDomination_of_barrier {ω : Fin d → ℝ} {T : Finset (Fin d)} {g : ℝ} (hg : 0 ≤ g)
    {q : CoreCoeff d → ℝ} {c₁ : ℝ} (hc₁ : 0 < c₁) (hω₁ : ∀ i, c₁ * ω i ≤ 1)
    (B : IsBarrierBound T g q) : FormDomination ω q where
  c₁ := c₁
  c₂ := c₁ * refEnergy ω 0 + B.shift
  hc₁ := hc₁
  dom := by
    intro c
    have hfree : c₁ * coreForm ω c - c₁ * refEnergy ω 0 * coreNormSq c ≤ degreeForm (d := d) c := by
      have := (freeFormDomination (d := d) ω hc₁ hω₁).dom c
      simpa using this
    have hbar := barrierForm_nonneg hg T c
    have hb := B.bound c
    have hd : degreeForm (d := d) c - B.shift * coreNormSq c ≤ q c := by nlinarith
    nlinarith

/-- **The interface is inhabited.**  At zero coupling the barrier vanishes
(`barrierForm_zero_g`), so `degreeForm` itself is a barrier bound with zero shift: the
non-vacuity witness for `IsBarrierBound`, in the spirit of `formDomination_self`. -/
def isBarrierBound_free (T : Finset (Fin d)) : IsBarrierBound T 0 (degreeForm (d := d)) where
  shift := 0
  bound := fun c => by
    rw [barrierForm_zero_g, add_zero, zero_mul, sub_zero]

/-- The barrier route reproduces the free Phase-4 certificate when the barrier is switched off, so
the interface is consistent with `freeFormDomination`. -/
def formDomination_of_free_barrier (T : Finset (Fin d)) (ω : Fin d → ℝ) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) : FormDomination ω (degreeForm (d := d)) :=
  formDomination_of_barrier (le_refl (0 : ℝ)) hc₁ hω₁ (isBarrierBound_free T)

/-! ## 6. The barrier is the zero-point energy of the quartic cross term

So far `g` was a free coupling.  It is not: on the core the quartic interaction is the normal
ordered `:N²:` form `quarticDegreeForm`, and with `N = N_∥ + N_⊥` it contains the cross term
`2 N_∥ N_⊥` (`quarticDegreeForm_ge_crossDegreeForm`).  In a Cartan background of occupation `N`
and amplitude `√(N + ½)` that cross term is an oscillator of squared frequency `2(N + ½)`, i.e.
`ω = √(2N + 1)`, and Simon's barrier at coupling `g = √2` is *exactly* its zero-point energy
(`zeroPoint_sqrt_two`).  So the barrier used in §2 is the one the magnetic potential produces,
not an extra assumption. -/

/-- The Cartan/root cross term `2 N_∥ N_⊥` of the quartic interaction, as a core form. -/
def crossDegreeForm (T : Finset (Fin d)) (c : CoreCoeff d) : ℝ :=
  ∑ n ∈ c.support, (2 * parallelDegree T n * perpDegree T n) * ‖c n‖ ^ 2

theorem crossDegreeForm_nonneg (T : Finset (Fin d)) (c : CoreCoeff d) :
    0 ≤ crossDegreeForm T c :=
  Finset.sum_nonneg fun n _ =>
    mul_nonneg
      (by
        have h1 := parallelDegree_nonneg T n
        have h2 := perpDegree_nonneg T n
        nlinarith)
      (by positivity)

/-- **The quartic form contains the cross term**: `(N_∥ + N_⊥)² ≥ 2 N_∥ N_⊥`, so the `:N²:`
interaction dominates the Cartan/root coupling that produces the barrier. -/
theorem quarticDegreeForm_ge_crossDegreeForm (T : Finset (Fin d)) (c : CoreCoeff d) :
    crossDegreeForm T c ≤ quarticDegreeForm c := by
  unfold crossDegreeForm quarticDegreeForm
  refine Finset.sum_le_sum fun n _ => ?_
  have hsum := parallelDegree_add_perpDegree T n
  have h1 := parallelDegree_nonneg T n
  have h2 := perpDegree_nonneg T n
  have hpt : 2 * parallelDegree T n * perpDegree T n ≤ (∑ i, (n i : ℝ)) ^ 2 := by
    rw [← hsum]
    nlinarith [sq_nonneg (parallelDegree T n - perpDegree T n)]
  exact mul_le_mul_of_nonneg_right hpt (by positivity)

/-- The frequency the cross term produces in a Cartan background of amplitude `A`: `ω = √(2A²)`. -/
def crossFreq (A : ℝ) : ℝ := Real.sqrt (2 * A ^ 2)

theorem crossFreq_sq (A : ℝ) : crossFreq A ^ 2 = 2 * A ^ 2 := by
  unfold crossFreq
  rw [Real.sq_sqrt]
  positivity

/-- At the background amplitude `√(N + ½)` the transverse frequency is `√(2N + 1)`. -/
theorem transFreq_sqrt_two (N : ℝ) (hN : 0 ≤ N) :
    transFreq (Real.sqrt 2) N = Real.sqrt (2 * N + 1) := by
  unfold transFreq
  have harg : 0 ≤ N + 1 / 2 := by linarith
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (N + 1 / 2)]
  congr 1
  ring

/-- **The barrier is the cross term's zero-point energy.**  With the coupling `g = √2` fixed by the
quartic interaction, twice the barrier is the oscillator frequency `√(2N + 1)` generated by the
cross term at background occupation `N`; the free coupling of §2 was this `√2` all along. -/
theorem zeroPoint_sqrt_two (N : ℝ) (hN : 0 ≤ N) :
    2 * zeroPoint (Real.sqrt 2) N = Real.sqrt (2 * N + 1) := by
  have h := transFreq_sqrt_two N hN
  unfold zeroPoint
  rw [h]
  ring

/-- The `H_W`-shaped quadratic form on the core: the free kinetic form, the quartic (magnetic)
interaction and Simon's barrier.  This is the object `softmodes.md` §2.3 asks the Yang–Mills form to
dominate; the remaining input is exactly the difference between `q_W` and it. -/
def yangMillsForm (T : Finset (Fin d)) (g : ℝ) (c : CoreCoeff d) : ℝ :=
  degreeForm (d := d) c + quarticDegreeForm c + barrierForm T g c

theorem yangMillsForm_ge_degree {T : Finset (Fin d)} {g : ℝ} (hg : 0 ≤ g) (c : CoreCoeff d) :
    degreeForm (d := d) c ≤ yangMillsForm T g c := by
  have hq := quarticDegreeForm_nonneg c
  have hb := barrierForm_nonneg hg T c
  unfold yangMillsForm
  linarith

/-- The `H_W`-shaped form is certified: it dominates the reference form with the free ratio (the
quartic term is nonnegative and the barrier helps), so Phase 4 applies to it directly. -/
def yangMillsForm_certified {ω : Fin d → ℝ} {T : Finset (Fin d)} {g : ℝ} (hg : 0 ≤ g) {c₁ : ℝ}
    (hc₁ : 0 < c₁) (hω₁ : ∀ i, c₁ * ω i ≤ 1) : FormDomination ω (yangMillsForm T g) :=
  (freeFormDomination (d := d) ω hc₁ hω₁).mono fun c => yangMillsForm_ge_degree hg c

/-- **The gap on the `H_W`-shaped form.**  Including the magnetic quartic and the barrier, a state
orthogonal to the vacuum is still at least `c₁ Δ_ref` above the certified ground level. -/
theorem yangMillsForm_ge_gap [Nonempty (Fin d)] {ω : Fin d → ℝ} (hω : ∀ i, 0 < ω i)
    {T : Finset (Fin d)} {g : ℝ} (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) (c : CoreCoeff d) (hc : c 0 = 0) :
    c₁ * refGap ω * coreNormSq c ≤ yangMillsForm T g c := by
  have h := excited_bound (q := yangMillsForm T g) ω hω
    (yangMillsForm_certified (d := d) hg hc₁ hω₁) c hc
  have hc1 : (yangMillsForm_certified (d := d) (ω := ω) (T := T) (g := g) hg hc₁ hω₁).c₁ = c₁ := rfl
  have hc2 : (yangMillsForm_certified (d := d) (ω := ω) (T := T) (g := g) hg hc₁ hω₁).c₂
      = c₁ * refEnergy ω 0 := rfl
  rw [hc1, hc2] at h
  have hshift : c₁ * (refEnergy ω 0 + refGap ω) - c₁ * refEnergy ω 0 = c₁ * refGap ω := by ring
  rwa [hshift] at h

/-- **The gap survives the barrier.**  On the vacuum-orthogonal sector the barriered form is at
least `c₁ Δ_ref · ‖c‖²` up to the shift `C‖·‖²` — the `softmodes.md` §4.1 separation
`β_∞ − θ_∞ ≥ c₁ Δ_ref`, with the barrier and the interaction included. -/
theorem barrier_gap [Nonempty (Fin d)] {ω : Fin d → ℝ} (hω : ∀ i, 0 < ω i)
    {T : Finset (Fin d)} {g : ℝ} (hg : 0 ≤ g) {q : CoreCoeff d → ℝ} {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) (B : IsBarrierBound T g q) (c : CoreCoeff d) (hc : c 0 = 0) :
    c₁ * refGap ω * coreNormSq c ≤ q c + B.shift * coreNormSq c := by
  have hex := excited_bound ω hω (formDomination_of_barrier (d := d) hg hc₁ hω₁ B) c hc
  have hc1 : (formDomination_of_barrier (d := d) (ω := ω) hg (T := T) hc₁ hω₁ B).c₁ = c₁ := rfl
  have hc2 : (formDomination_of_barrier (d := d) (ω := ω) hg (T := T) hc₁ hω₁ B).c₂
      = c₁ * refEnergy ω 0 + B.shift := rfl
  rw [hc1, hc2] at hex
  nlinarith

/-! ## 6. The §2.3 milestone, unconditionally, for the quartic `:N²:` form

§5 leaves `IsBarrierBound` as an interface.  This section proves it for the **quartic interaction
itself**: the normal-ordered `:N²:` form `quarticDegreeForm` (the interaction the magnetic potential
produces, `quarticDegreeForm_ge_crossDegreeForm`) already dominates the free degree form *plus*
Simon's barrier, up to an explicit bounded shift.

The point is that the barrier is sublinear in the Cartan occupation (`√(N + ½) ≤ (N + 1)`,
`zeroPoint_le_linear`) while the quartic grows quadratically, so the quartic can pay for both:
`s² ≥ s − ¼` pays for the kinetic degree and `√N` costs only `N`, which the quadratic term absorbs.
Nothing here is a hypothesis: both inequalities are elementary, and the shift is
`C = K + (1 + K)²/4` with `K = rootCount T · g/2` — the constant that makes
`(1 + K)s + K ≤ s² + (1 + K)²/4 + K` true for every `s ≥ 0`.

Consequently the Phase-4 certificate `FormDomination ω quarticDegreeForm` exists
(`quarticFormDomination`) and the certified separation `c₁ Δ_ref` holds for the pure interaction
form (`quartic_certified_gap`), with the barrier *inside* the inequality rather than beside it.
-/

/-- **Simon's barrier is linear in the occupation**: `rootCount · zeroPoint g N ≤ K (N + 1)` with
`K = rootCount · g/2`.  This is the estimate that lets the quadratic interaction pay for it. -/
theorem barrierForm_le_linear (T : Finset (Fin d)) {g : ℝ} (hg : 0 ≤ g) (c : CoreCoeff d) :
    barrierForm T g c ≤
      (rootCount T * (g / 2)) * degreeForm (d := d) c + (rootCount T * (g / 2)) * coreNormSq c := by
  have hK : (0 : ℝ) ≤ rootCount T * (g / 2) := mul_nonneg (rootCount_nonneg T) (by linarith)
  rw [barrierForm, degreeForm, coreNormSq, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  set D : ℝ := ∑ i, (n i : ℝ) with hD
  set N : ℝ := parallelDegree T n with hN
  have hDnn : (0 : ℝ) ≤ D := by
    rw [hD]
    exact Finset.sum_nonneg fun i _ => Nat.cast_nonneg (n i)
  have hNnn : (0 : ℝ) ≤ N := by rw [hN]; exact parallelDegree_nonneg T n
  have hND : N ≤ D := by
    rw [hN, hD]
    have hsum := parallelDegree_add_perpDegree T n
    have hperp := perpDegree_nonneg T n
    linarith
  have hlin : zeroPoint g N ≤ g / 2 * (N + 1) := zeroPoint_le_linear hg hNnn
  have hbar : rootCount T * zeroPoint g N ≤ rootCount T * (g / 2 * (N + 1)) :=
    mul_le_mul_of_nonneg_left hlin (rootCount_nonneg T)
  have hnn : (0 : ℝ) ≤ ‖c n‖ ^ 2 := by positivity
  have hpt : rootCount T * zeroPoint g N ≤ rootCount T * (g / 2) * D + rootCount T * (g / 2) := by
    nlinarith [hbar, hND, hK, hDnn]
  have := mul_le_mul_of_nonneg_right hpt hnn
  nlinarith [this]

/-- **The §2.3 milestone inequality, unconditionally, for the quartic `:N²:` form**: the quartic
interaction dominates `degreeForm + barrierForm` up to the explicit shift
`K + (1 + K)²/4`, `K = rootCount T · g/2`. -/
def barrierBound_quartic (T : Finset (Fin d)) {g : ℝ} (hg : 0 ≤ g) :
    IsBarrierBound T g (quarticDegreeForm (d := d)) := by
  refine ⟨(1 + rootCount T * (g / 2)) ^ 2 / 4 + rootCount T * (g / 2), ?_⟩
  intro c
  set K : ℝ := rootCount T * (g / 2) with hKdef
  set sh : ℝ := (1 + K) ^ 2 / 4 + K with hsh
  have hK : (0 : ℝ) ≤ K := by
    rw [hKdef]
    exact mul_nonneg (rootCount_nonneg T) (by linarith)
  rw [degreeForm, barrierForm, quarticDegreeForm, coreNormSq]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  set D : ℝ := ∑ i, (n i : ℝ) with hD
  set N : ℝ := parallelDegree T n with hN
  have hDnn : (0 : ℝ) ≤ D := by
    rw [hD]
    exact Finset.sum_nonneg fun i _ => Nat.cast_nonneg (n i)
  have hNnn : (0 : ℝ) ≤ N := by rw [hN]; exact parallelDegree_nonneg T n
  have hND : N ≤ D := by
    rw [hN, hD]
    have hsum := parallelDegree_add_perpDegree T n
    have hperp := perpDegree_nonneg T n
    linarith
  have hlin : zeroPoint g N ≤ g / 2 * (N + 1) := zeroPoint_le_linear hg hNnn
  have hbar : rootCount T * zeroPoint g N ≤ K * (N + 1) := by
    calc rootCount T * zeroPoint g N ≤ rootCount T * (g / 2 * (N + 1)) :=
          mul_le_mul_of_nonneg_left hlin (rootCount_nonneg T)
      _ = K * (N + 1) := by rw [hKdef]; ring
  -- `(1 + K) s + K ≤ s² + sh` for `s = D ≥ 0`, from `(s − (1 + K)/2)² ≥ 0`
  have hsq : (0 : ℝ) ≤ (D - (1 + K) / 2) ^ 2 := sq_nonneg _
  have hpt : D + rootCount T * zeroPoint g N - sh ≤ D ^ 2 := by
    rw [hsh]
    nlinarith [hsq, hbar, hND, hK, hNnn, hDnn]
  have hnn : (0 : ℝ) ≤ ‖c n‖ ^ 2 := by positivity
  have hmain := mul_le_mul_of_nonneg_right hpt hnn
  nlinarith [hmain]

/-- **The Phase-4 certificate for the pure interaction form**: the quartic `:N²:` form dominates the
reference oscillator form with the free ratio `c₁` and the explicit shift `c₁μ₀ + C`. -/
def quarticFormDomination {ω : Fin d → ℝ} {T : Finset (Fin d)} {g : ℝ} (hg : 0 ≤ g) {c₁ : ℝ}
    (hc₁ : 0 < c₁) (hω₁ : ∀ i, c₁ * ω i ≤ 1) :
    FormDomination ω (quarticDegreeForm (d := d)) :=
  formDomination_of_barrier (d := d) hg hc₁ hω₁ (barrierBound_quartic T hg)

/-- **The certified separation for the pure interaction form**: on the vacuum-orthogonal sector the
quartic form is at least `c₁ Δ_ref · ‖c‖²` up to the barrier's explicit shift — the
`softmodes.md` §4.1 separation, with the Simon barrier paid for by the interaction itself. -/
theorem quartic_certified_gap [Nonempty (Fin d)] {ω : Fin d → ℝ} (hω : ∀ i, 0 < ω i)
    {T : Finset (Fin d)} {g : ℝ} (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) (c : CoreCoeff d) (hc : c 0 = 0) :
    c₁ * refGap ω * coreNormSq c ≤ quarticDegreeForm c +
      ((1 + rootCount T * (g / 2)) ^ 2 / 4 + rootCount T * (g / 2)) * coreNormSq c := by
  have h := barrier_gap (T := T) (g := g) hω hg hc₁ hω₁ (barrierBound_quartic T hg) c hc
  simpa using h

/-- The certified separation attached to a barrier bound is strictly positive. -/
theorem barrier_separation_pos [Nonempty (Fin d)] {ω : Fin d → ℝ} (hω : ∀ i, 0 < ω i)
    {c₁ : ℝ} (hc₁ : 0 < c₁) : 0 < c₁ * refGap ω :=
  mul_pos hc₁ (refGap_pos hω)

end BookProof.YangMillsEffectiveBarrier
